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

	internal class UndoneFaultActivationObservable : FaultActivationTestObject
	{
		protected override void Check()
		{
			GenerateStateSpace(new C());

			StateCount.ShouldBe(6);
			TransitionCount.ShouldBe(26);
			ComputedTransitionCount.ShouldBe(31);
		}

		private class C : Component
		{
			private readonly Fault _f = new TransientFault();

			[Range(0, 5, OverflowBehavior.Clamp)]
			private int _x;

			public override void Update()
			{
				// When checking B, activation of _f is undone, fault might be activated again when retrieving Y
				if (B)
					_x += Y;
			}

			public virtual int Y => Choose(1, 2, 3, 4); 
			public virtual bool B => true;

			[FaultEffect(Fault = nameof(_f))]
			public class E1 : C
			{
				public override int Y => 5;
			}

			[FaultEffect(Fault = nameof(_f))]
			public class E2 : C
			{
				public override bool B => true;
			}
		}
	}
}