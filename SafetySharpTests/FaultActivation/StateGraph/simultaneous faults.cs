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

namespace Tests.FaultActivation.StateGraph
{
	using ISSE.SafetyChecking.Modeling;
	using SafetySharp.Modeling;
	using Shouldly;

	internal class SimultaneousFaults : FaultActivationTestObject
	{
		protected override void Check()
		{
			GenerateStateSpace(new C());

			StateCount.ShouldBe(2);
			TransitionCount.ShouldBe(4);
			ComputedTransitionCount.ShouldBe(17);
		}

		private class C : Component
		{
			public readonly Fault F1 = new TransientFault();
			public readonly Fault F2 = new TransientFault();
			public readonly Fault F3 = new TransientFault();
			public int X;
			public virtual int X1 => 0;
			public virtual int X2 => 0;
			public virtual int X3 => 0;

			public override void Update()
			{
				if (X1 == 2 & X2 == 2 & X3 == 2)
					X = 6;
			}

			[FaultEffect(Fault = nameof(F1))]
			private class E1 : C
			{
				public override int X1 => 2;
			}

			[FaultEffect(Fault = nameof(F2))]
			private class E2 : C
			{
				public override int X2 => 2;
			}

			[FaultEffect(Fault = nameof(F3))]
			private class E3 : C
			{
				public override int X3 => 2;
			}
		}
	}
}