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

namespace Tests.Execution.StateMachines
{
	using SafetySharp.Modeling;
	using Shouldly;
	using Utilities;

	internal class MultipleInitialStates : TestObject
	{
		protected override void Check()
		{
			var sm1 = new StateMachine<int>(17, 18);
			sm1.InitialStates.ShouldBe(new[] { 17, 18 });

			var sm2 = new StateMachine<E>(E.A, E.B, E.C);
			sm2.InitialStates.ShouldBe(new[] { E.A, E.B, E.C });

			StateMachine<int> sm3 = new[] { 17, 18 };
			sm3.InitialStates.ShouldBe(new[] { 17, 18 });

			StateMachine<E> sm4 = new[] { E.A, E.B, E.C };
			sm4.InitialStates.ShouldBe(new[] { E.A, E.B, E.C });
		}

		private enum E
		{
			A,
			B,
			C
		}
	}
}