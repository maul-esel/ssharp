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
	using SafetySharp.Modeling;
	using Shouldly;
	using Utilities;

	internal class GenericComponents : TestModel
	{
		private static bool _hasConstructorRun;

		protected override void Check()
		{
			var c1 = new C<int> { F = 99 };
			var c2 = new C<bool> { F = true };
			var m = InitializeModel(c1, c2);

			_hasConstructorRun = false;
			Create(m);

			ExecutableStateFormulas.ShouldBeEmpty();
			RootComponents.Length.ShouldBe(2);

			var root1 = RootComponents[0];
			root1.ShouldBeOfType<C<int>>();
			((C<int>)root1).F.ShouldBe(99);

			var root2 = RootComponents[1];
			root2.ShouldBeOfType<C<bool>>();
			((C<bool>)root2).F.ShouldBe(true);

			_hasConstructorRun.ShouldBe(false);
		}

		private class C<T> : Component
		{
			public T F;

			public C()
			{
				_hasConstructorRun = true;
			}
		}
	}
}