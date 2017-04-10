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

namespace Tests.Serialization.RuntimeModels
{
	using System.Collections.Generic;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal class CyclicHierarchy : TestModel
	{
		private static bool _hasConstructorRun;

		protected override void Check()
		{
			var c = new C { F = 33 };
			var d = new D { C = c };
			var e = new E { C = new [] { c} };
			var f = new F { E = e };
			c.D = d;
			c.E = new List<E> {e};
			e.F = f;
			var m = InitializeModel(d);

			_hasConstructorRun = false;
			Create(m);

			ExecutableStateFormulas.ShouldBeEmpty();
			RootComponents.Length.ShouldBe(1);

			var root = RootComponents[0];
			root.ShouldBeOfType<D>();

			((D)root).C.ShouldBeOfType<C>();
			((D)root).C.D.ShouldBeOfType<D>();
			((D)root).C.D.ShouldBe((D)root);
			((D)root).C.F.ShouldBe(33);

			root.GetSubcomponents().ShouldBe(new[] { ((D)root).C });
			((D)root).C.GetSubcomponents().ShouldBe(new[] { root });

			_hasConstructorRun.ShouldBe(false);
		}

		private class C : Component
		{
			public D D;
			public int F;
			public List<E> E;

			public C()
			{
				_hasConstructorRun = true;
			}
		}

		private class D : Component
		{
			public C C;

			public D()
			{
				_hasConstructorRun = true;
			}
		}

		private class E
		{
			public C[] C;
			public F F;

			public E()
			{
				_hasConstructorRun = true;
			}
		}

		private class F
		{
			public E E;

			public F()
			{
				_hasConstructorRun = true;
			}
		}
	}
}