﻿// The MIT License (MIT)
// 
// Copyright (c) 2014-2017, Institute for Software & Systems Engineering
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.

namespace SafetySharp.CaseStudies.HeightControl.Modeling.Vehicles
{
	using System;
	using System.Linq;
	using ISSE.SafetyChecking.Modeling;
	using SafetySharp.Modeling;
	using Sensors;

	/// <summary>
	///   Represents a set of vehicles.
	/// </summary>
	public sealed class VehicleSet : Component
	{
		/// <summary>
		///   Use state constraint to prevent overlapping. State constraints cannot be used
		///   with probabilistic models!
		/// </summary>
		[Hidden]
		public bool PreventOverlappingWithStateConstraint = false;

		[Hidden(HideElements=true)]
		private readonly Vehicle[] _orderedVehicles;

		/// <summary>
		///   Checks if all vehicles have finished.
		/// </summary>
		[Hidden]
		public FinishedObserver FinishedObserver;

		/// <summary>
		///   Allows high vehicles to drive on the left lane.
		/// </summary>
		public readonly Fault LeftHV = new TransientFault();

		/// <summary>
		///   Allows overheight vehicles to drive on the left lane.
		/// </summary>
		public readonly Fault LeftOHV = new TransientFault();

		/// <summary>
		///   Allows all kinds of vehicles to drive slower than expected.
		/// </summary>
		public readonly Fault SlowTraffic = new TransientFault();
		
		/// <summary>
		///   Initializes a new instance.
		/// </summary>
		public VehicleSet(Vehicle[] vehicles)
		{
			Vehicles = vehicles;
			_orderedVehicles=new Vehicle[Vehicles.Length];

			foreach (var vehicle in Vehicles)
				Bind(nameof(vehicle.IsTunnelClosed), nameof(ForwardIsTunnelClosed));

			LeftOHV.AddEffects<Vehicle.DriveLeftEffect>(vehicles.Where(vehicle => vehicle.Kind == VehicleKind.OverheightVehicle));
			LeftHV.AddEffects<Vehicle.DriveLeftEffect>(vehicles.Where(vehicle => vehicle.Kind == VehicleKind.HighVehicle));
			SlowTraffic.AddEffects<Vehicle.SlowTrafficEffect>(vehicles);

			if (PreventOverlappingWithStateConstraint)
			{
				for (var i = 0; i < Vehicles.Length; ++i)
				{
					for (var j = i + 1; j < Vehicles.Length; ++j)
					{
						AddSensorConstraint(Vehicles[i], Vehicles[j], Model.PreControlPosition);
						AddSensorConstraint(Vehicles[i], Vehicles[j], Model.MainControlPosition);
						AddSensorConstraint(Vehicles[i], Vehicles[j], Model.EndControlPosition);
					}
				}
			}
		}

		/// <summary>
		///   The vehicles contained in the set.
		/// </summary>
		[Hidden(HideElements = true), Subcomponent]
		public Vehicle[] Vehicles { get; }

		// TODO: Remove once S# supports port forwardings
		private bool ForwardIsTunnelClosed => IsTunnelClosed;

		/// <summary>
		///   Informs the vehicles contained in the set whether the tunnel is closed.
		/// </summary>
		public extern bool IsTunnelClosed { get; }

		/// <summary>
		///   Adds a state constraint ensuring that no two vehicles pass the same sensor on the same lane at the same time.
		/// </summary>
		private void AddSensorConstraint(Vehicle vehicle1, Vehicle vehicle2, int position)
		{
			AddStateConstraint(() => !vehicle1.IsAtPosition(position) || !vehicle2.IsAtPosition(position) || vehicle1.Lane != vehicle2.Lane);
		}

		/// <summary>
		///   Updates the state of the component.
		/// </summary>
		public override void Update()
		{
			FinishedObserver.Update(); //must be called before the update

			if (FinishedObserver.Finished)
				return;

			if (PreventOverlappingWithStateConstraint)
				Update(Vehicles);
			else
				UpdateWhichPreventsOverlappingExplicitly();
		}

		/// <summary>
		///   When no state constraint is used, overlapping must be prevented explicitly!
		/// </summary>
		private void UpdateWhichPreventsOverlappingExplicitly()
		{
			// Copy vehicle set. Order should be deterministic
			for (var i = 0; i < Vehicles.Length; i++)
				_orderedVehicles[i] = Vehicles[i];

			// Perform insertion sort (https://en.wikipedia.org/wiki/Insertion_sort). Try not to make garbage
			for (var i = 1; i < _orderedVehicles.Length; i++)
			{
				var x = _orderedVehicles[i];
				var j = i - 1;
				while (j >= 0 && _orderedVehicles[j].Position < x.Position)
				{
					_orderedVehicles[j + 1] = _orderedVehicles[j];
					j--;
				}
				_orderedVehicles[j + 1] = x;
			}

			// Now the first vehicle in _orderedVehicles is the vehicle with the highest position
			for (var i = 0; i < _orderedVehicles.Length; i++)
			{
				var oldPosition = _orderedVehicles[i].Position;
				var oldLane = _orderedVehicles[i].Lane;
				
				// Update the position of the vehicle
				_orderedVehicles[i].Update();

				if (oldPosition == Model.TunnelPosition)
					continue;

				// Check, if the position overlaps with another vehicle
				var fixedOverlap = false;
				for (var j = 0; j < i && !fixedOverlap; j++)
				{
					if (_orderedVehicles[j].Position != 0 &&
						 _orderedVehicles[j].Position < Model.TunnelPosition &&
						 _orderedVehicles[i].Position == _orderedVehicles[j].Position &&
						 _orderedVehicles[i].Lane == _orderedVehicles[j].Lane)
					{
						// Found an overlap. So reset the old vehicle to its old position.
						fixedOverlap = true;
						_orderedVehicles[i].Position = oldPosition;
						_orderedVehicles[i].Lane = oldLane;
						_orderedVehicles[i].Speed = 0;
					}
				}
			}
		}

		/// <summary>
		///   Checks whether the <paramref name="detector" /> detects any vehicles.
		/// </summary>
		/// <param name="detector">The detector that should observe the vehicles.</param>
		public bool ObserveVehicles(VehicleDetector detector)
		{
			// Ideally, we'd just use the following line instead of the for-loop below; however, it generates
			// a delegate and probably an interator each time the method is called, therefore increasing the 
			// pressure on the garbage collector; roughly 250 million heap allocations would be required to
			// check the case study's original design. All in all, model checking times increase noticeably, in 
			// some cases by 40% or more...

			// return Vehicles.Any(detector.DetectsVehicle);

			foreach (var vehicle in Vehicles)
			{
				if (detector.DetectsVehicle(vehicle))
					return true;
			}

			return false;
		}
	}
}