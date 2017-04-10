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

namespace Tests.Execution.Faults.UpdateMethods
{
	using ISSE.SafetyChecking.Modeling;
	using SafetySharp.Modeling;
	using Shouldly;
	using Utilities;

	internal class X3 : TestModel
	{
		protected sealed override void Check()
		{
			Create(new C());
			var c = (C)RootComponents[0];

			c._f1.Activation = Activation.Suppressed;
			c._f2.Activation = Activation.Suppressed;
			c._f3.Activation = Activation.Suppressed;
			c.Update();
			c.X.ShouldBe(7);

			c._f1.Activation = Activation.Forced;
			c._f2.Activation = Activation.Suppressed;
			c._f3.Activation = Activation.Suppressed;
			c.Update();
			c.X.ShouldBe(17);

			c._f1.Activation = Activation.Suppressed;
			c._f2.Activation = Activation.Forced;
			c._f3.Activation = Activation.Suppressed;
			c.Update();
			c.X.ShouldBe(107);

			c._f1.Activation = Activation.Suppressed;
			c._f2.Activation = Activation.Suppressed;
			c._f3.Activation = Activation.Forced;
			c.Update();
			c.X.ShouldBe(1007);

			c._f1.Activation = Activation.Forced;
			c._f2.Activation = Activation.Forced;
			c._f3.Activation = Activation.Suppressed;
			c.Update();
			c.X.ShouldBe(117);

			c._f1.Activation = Activation.Forced;
			c._f2.Activation = Activation.Suppressed;
			c._f3.Activation = Activation.Forced;
			c.Update();
			c.X.ShouldBe(1017);

			c._f1.Activation = Activation.Suppressed;
			c._f2.Activation = Activation.Forced;
			c._f3.Activation = Activation.Forced;
			c.Update();
			c.X.ShouldBe(1107);

			c._f1.Activation = Activation.Forced;
			c._f2.Activation = Activation.Forced;
			c._f3.Activation = Activation.Forced;
			c.Update();
			c.X.ShouldBe(1117);
		}

		private class C : Component
		{
			public int X;
			public TransientFault _f1 { get; } = new TransientFault();
			public TransientFault _f2 { get; } = new TransientFault();
			public TransientFault _f3 { get; } = new TransientFault();

			public override void Update()
			{
				X = 7;
			}

			[FaultEffect(Fault = nameof(_f1))]
			[Priority(1)]
			private class F1 : C
			{
				public override void Update()
				{
					base.Update();
					X += 10;
				}
			}

			[FaultEffect(Fault = nameof(_f2))]
			[Priority(2)]
			private class F2 : C
			{
				public override void Update()
				{
					base.Update();
					X += 100;
				}
			}

			[FaultEffect(Fault = nameof(_f3))]
			[Priority(3)]
			private class F3 : C
			{
				public override void Update()
				{
					base.Update();
					X += 1000;
				}
			}
		}
	}
}