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

namespace Tests.Execution.Simulation
{
	using ISSE.SafetyChecking.Modeling;
	using SafetySharp.Analysis;
	using SafetySharp.Modeling;
	using Shouldly;
	using Utilities;

	internal class UnusedFaultsAndEffects : TestObject
	{
		protected override void Check()
		{
			var simulator = new SafetySharpSimulator(TestModel.InitializeModel(new C()));
			var c = (C)simulator.Model.Roots[0];

			c.F.Activation = Activation.Forced;
			simulator.SimulateStep();
			c.X.ShouldBe(1);

			c.F.Activation = Activation.Suppressed;
			simulator.SimulateStep();
			c.X.ShouldBe(1);

			simulator.Model.Faults.ShouldBeEmpty();
		}

		private class C : Component
		{
			public readonly Fault F = new TransientFault();
			public int X;

			public virtual int Y => 1;

			public override void Update()
			{
				X = Y;
			}

			[FaultEffect, Priority(1)]
			public class E1 : C
			{
				public override int Y => 71;
			}

			[FaultEffect, Priority(2)]
			public class E2 : C
			{
				public override int Y => 1;
			}
		}
	}
}