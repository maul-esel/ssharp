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

namespace Tests.Execution.Faults.ProvidedPorts
{
	using ISSE.SafetyChecking.Modeling;
	using SafetySharp.Modeling;
	using Shouldly;
	using Utilities;

	internal class X4 : TestModel
	{
		protected sealed override void Check()
		{
			Create(new C());
			var c = (C)RootComponents[0];

			c._f1.Activation = Activation.Suppressed;
			c._f2.Activation = Activation.Suppressed;
			c._f3.Activation = Activation.Suppressed;
			c.M.ShouldBe(1);

			c._f1.Activation = Activation.Forced;
			c._f2.Activation = Activation.Suppressed;
			c._f3.Activation = Activation.Suppressed;
			c.M.ShouldBe(101);

			c._f1.Activation = Activation.Suppressed;
			c._f2.Activation = Activation.Forced;
			c._f3.Activation = Activation.Suppressed;
			c.M.ShouldBe(1001);

			c._f1.Activation = Activation.Suppressed;
			c._f2.Activation = Activation.Suppressed;
			c._f3.Activation = Activation.Forced;
			c.M.ShouldBe(10001);

			c._f1.Activation = Activation.Forced;
			c._f2.Activation = Activation.Forced;
			c._f3.Activation = Activation.Suppressed;
			c.M.ShouldBe(1101);

			c._f1.Activation = Activation.Forced;
			c._f2.Activation = Activation.Suppressed;
			c._f3.Activation = Activation.Forced;
			c.M.ShouldBe(10101);

			c._f1.Activation = Activation.Suppressed;
			c._f2.Activation = Activation.Forced;
			c._f3.Activation = Activation.Forced;
			c.M.ShouldBe(11001);

			c._f1.Activation = Activation.Forced;
			c._f2.Activation = Activation.Forced;
			c._f3.Activation = Activation.Forced;
			c.M.ShouldBe(11101);
		}

		private class C : Component
		{
			public readonly TransientFault _f1 = new TransientFault();
			public readonly TransientFault _f2 = new TransientFault();
			public readonly TransientFault _f3 = new TransientFault();

			public virtual int M => 1;

			[FaultEffect(Fault = nameof(_f1))]
			[Priority(1)]
			private class F1 : C
			{
				public override int M => base.M + 100;
			}

			[FaultEffect(Fault = nameof(_f2))]
			[Priority(2)]
			private class F2 : C
			{
				public override int M => base.M + 1000;
			}

			[FaultEffect(Fault = nameof(_f3))]
			[Priority(3)]
			private class F3 : C
			{
				public override int M => base.M + 10000;
			}
		}
	}
}