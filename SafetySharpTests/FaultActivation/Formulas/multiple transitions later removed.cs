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

namespace Tests.FaultActivation.Formulas
{
	using System.Diagnostics;
	using ISSE.SafetyChecking.Modeling;
	using SafetySharp.Modeling;
	using Shouldly;

	internal class MultipleTransitionsLaterRemovedBecauseNotActivationMinimal : AnalysisTestObject
	{
		protected override void Check()
		{
			var c = new C();
			Debugger.Break();
			CheckInvariant(!c.F1.IsActivated && !c.F2.IsActivated && !c.F3.IsActivated, c).ShouldBe(true);
		}

		private class C : Component
		{
			public readonly Fault F1 = new PermanentFault();
			public readonly Fault F2 = new PermanentFault();
			public readonly Fault F3 = new PermanentFault();

			private int _x;

			public override void Update()
			{
				if (_x != 0)
					return;

				if (Choose(true, false))
					_x = Value;
				else
					_x = ChooseFromRange(0, 5);
			}

			public virtual int Value => 1;

			[FaultEffect(Fault = nameof(F1)), Priority(1)]
			public class E1 : C
			{
				public override int Value => base.Value + 2;
			}

			[FaultEffect(Fault = nameof(F2)), Priority(2)]
			public class E2: C
			{
				public override int Value => base.Value + 1;
			}

			[FaultEffect(Fault = nameof(F3)), Priority(3)]
			public class E3 : C
			{
				public override int Value => base.Value + 1;
			}
		}
	}
}