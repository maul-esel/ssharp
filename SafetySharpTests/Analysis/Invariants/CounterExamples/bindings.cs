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

namespace Tests.Analysis.Invariants.CounterExamples
{
	using SafetySharp.Modeling;
	using Shouldly;

	internal class Bindings : AnalysisTestObject
	{
		protected override void Check()
		{
			var c = new C();
			var d = new D();
			Component.Bind(nameof(c.Y), nameof(d.Z));

			CheckInvariant(c.X != 7, c, d);
			CounterExample.StepCount.ShouldBe(2);

			SimulateCounterExample(CounterExample, simulator =>
			{
				c = (C)simulator.Model.Roots[0];

				c.X.ShouldBe(0);
				simulator.IsCompleted.ShouldBe(false);

				simulator.SimulateStep();
				c.X.ShouldBe(7);
				simulator.IsCompleted.ShouldBe(true);
			});
		}

		private class C : Component
		{
			public int X;

			public extern int Y { get; }

			public override void Update()
			{
				X = Y;
			}
		}

		private class D : Component
		{
			public int Z => 7;
		}
	}
}