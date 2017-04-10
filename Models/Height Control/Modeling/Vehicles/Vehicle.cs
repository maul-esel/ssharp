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
	using SafetySharp.Modeling;

	/// <summary>
	///   Represents an overheight vehicle that is not allowed to enter the tunnel on the left lane.
	/// </summary>
	public class Vehicle : Component
	{
		[Hidden]
		public int Speed { get; set; }

		/// <summary>
		///   Gets the current lane of the vehicle.
		/// </summary>
		public Lane Lane { get; set; } = Lane.Right;

		/// <summary>
		///   Gets the kind the vehicle.
		/// </summary>
		[Hidden]
		public VehicleKind Kind { get; set; }

		/// <summary>
		///   Gets a value indicating whether the vehicle has collided with the tunnel.
		/// </summary>
		public bool IsCollided =>
			Kind == VehicleKind.OverheightVehicle && Position >= Model.TunnelPosition && Lane == Lane.Left;

		/// <summary>
		///   Informs the vehicle whether the tunnel is closed.
		/// </summary>
		public extern bool IsTunnelClosed { get; }

		/// <summary>
		///   Gets the vehicle's position.
		/// </summary>
		[Range(0, Model.TunnelPosition, OverflowBehavior.Clamp)]
		public int Position { get; set; }

		/// <summary>
		///   Chooses the lane the vehicle drives on. By default, vehicles always drive on the right lane.
		/// </summary>
		protected virtual Lane ChooseLane() => Lane.Right;

		/// <summary>
		///   Chooses the speed the vehicle drives with. By default, vehicles always drive with their maximum speed.
		/// </summary>
		protected virtual int ChooseSpeed() => Model.MaxSpeed;

		/// <summary>
		///   Checks whether the vehicle is at the <paramref name="position" />.
		/// </summary>
		/// <param name="position">The position that should be checked.</param>
		public bool IsAtPosition(int position) => Position - Speed < position && Position >= position;

		/// <summary>
		///   Moves the vehicle.
		/// </summary>
		public override void Update()
		{
			if (Position == 0 && Choose(false, true))
				return;

			// Once the tunnel is closed, all vehicles stop
			if (IsTunnelClosed)
				return;

			// The vehicle's speed is irrelevant once the end control has been passed
			Speed = Position >= Model.EndControlPosition ? Model.MaxSpeed : ChooseSpeed();
			Position += Speed;

			// The road layout makes lane changes impossible when the end control has been reached
			if (Position < Model.EndControlPosition)
				Lane = ChooseLane();
		}

		/// <summary>
		///   A fault effect representing the case where a vehicle drives on the left lane.
		/// </summary>
		[FaultEffect]
		public class DriveLeftEffect : Vehicle
		{
			protected override Lane ChooseLane() => Choose(Lane.Right, Lane.Left);
		}

		/// <summary>
		///   A fault effect representing the case where a vehicle is slowed down by traffic.
		/// </summary>
		[FaultEffect]
		public class SlowTrafficEffect : Vehicle
		{
			protected override int ChooseSpeed() => ChooseFromRange(Model.MinSpeed, Model.MaxSpeed);
		}
	}
}