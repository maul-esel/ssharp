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
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal class ReferenceToModel : TestModel
	{
		private static bool _hasConstructorRun;

		protected override void Check()
		{
			var m = new M();

			_hasConstructorRun = false;
			Create(m);

			ExecutableStateFormulas.ShouldBeEmpty();
			RootComponents.Length.ShouldBe(1);

			var root = RootComponents[0];
			root.ShouldBeOfType<C>();
			((C)root).F.ShouldBe((sbyte)99);
			((C)root).Model.Components.ShouldBe(new[] { root });
			((C)root).Model.Roots.ShouldBe(new[] { root });
			((C)root).Model.Faults.ShouldBeEmpty();
			((C)root).Model.ReferencedObjects.ShouldBe(new object[] { root, ((C)root).Model });
			root.GetSubcomponents().ShouldBeEmpty();

			_hasConstructorRun.ShouldBe(false);
		}

		private class C : Component
		{
			public sbyte F = 99;
			public ModelBase Model;

			public C()
			{
				_hasConstructorRun = true;
			}
		}

		class M : ModelBase
		{
			[Root(RootKind.Plant)]
			public C C = new C();

			public M()
			{
				C.Model = this;
			}
		}
	}
}