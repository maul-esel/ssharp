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

namespace SafetySharp.CaseStudies.PillProduction.Modeling
{
	using SafetySharp.Modeling;

	public class Model : ModelBase
	{
		public const int MaximumRecipeLength = 30;
		public const int ContainerStorageSize = 30;
		public const int MaximumRoleCount = 100;
		public const int MaximumResourceCount = 30;
		public const uint InitialIngredientAmount = 100u;

		public Model(Station[] stations, ObserverController obsContr)
		{
			Stations = stations;
			foreach (var station in stations)
			{
				station.ObserverController = obsContr;
			}
			ObserverController = obsContr;
		}

		[Root(RootKind.Controller)]
		public Station[] Stations { get; }

		[Root(RootKind.Controller)]
		public ObserverController ObserverController { get; }

		public void ScheduleProduction(Recipe recipe)
		{
			ObserverController.ScheduleConfiguration(recipe);
		}

		public static Model NoRedundancyCircularModel()
		{
			// create 3 stations
			var dispenser = new ParticulateDispenser();
			var stations = new Station[]
			{
				new ContainerLoader(),
				dispenser,
				new PalletisationStation()
			};

			dispenser.SetStoredAmount(IngredientType.BlueParticulate, 50u);
			dispenser.SetStoredAmount(IngredientType.RedParticulate, 50u);
			dispenser.SetStoredAmount(IngredientType.YellowParticulate, 50u);

			// connect them to a circle
			for (var i = 0; i < stations.Length; ++i)
			{
				var next = stations[(i + 1) % stations.Length];
				stations[i].Outputs.Add(next);
				next.Inputs.Add(stations[i]);
			}

			var model = new Model(stations, new FastObserverController(stations));

			var recipe = new Recipe(ingredients: new[]
			{
				new Ingredient(IngredientType.BlueParticulate, 12),
				new Ingredient(IngredientType.RedParticulate, 4),
				new Ingredient(IngredientType.YellowParticulate, 5)
			}, amount: 3);
			model.ScheduleProduction(recipe);

			return model;
		}
	}
}