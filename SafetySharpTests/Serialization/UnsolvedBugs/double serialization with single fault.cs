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
	using System.Reflection;
	using ISSE.SafetyChecking.Modeling;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime;
	using Shouldly;
	using Utilities;

	internal class DoubleSerializationWithSingleFault : TestModel
	{
		private static bool _hasConstructorRun;

		protected override void Check()
		{
			var c = new C();
			var directModel = InitializeModel(c);

			((C.Effect1)c.FaultEffects[0]).F = 17;

			_hasConstructorRun = false;

			var newModelInstanceBySerializeDeserialize = SafetySharpRuntimeModel.CreateExecutedModelCreator(directModel).Create(0);

			//"Create" serializes and deserializes again (second time)
			Create(newModelInstanceBySerializeDeserialize.Model);

			ExecutableStateFormulas.ShouldBeEmpty();
			RootComponents.Length.ShouldBe(1);

			var root = RootComponents[0];
			root.ShouldBeOfType<C.Effect1>();
			root.GetSubcomponents().ShouldBeEmpty();

			((C)root).F1.ShouldBeOfType<TransientFault>();
			((C.Effect1)root).F.ShouldBe(17);

			root.FaultEffects.Count.ShouldBe(1);
			((C.Effect1)root.FaultEffects[0]).F.ShouldBe(17);

			typeof(C.Effect1).GetField("__fault__", BindingFlags.Instance | BindingFlags.NonPublic).GetValue(root).ShouldBe(((C)root).F1);

			_hasConstructorRun.ShouldBe(false);
		}

		private class C : Component
		{
			public readonly Fault F1 = new TransientFault();

			public C()
			{
				_hasConstructorRun = true;

				F1.AddEffect<Effect1>(this);
			}

			public virtual void M()
			{
			}

			[FaultEffect]
			public class Effect1 : C
			{
				public int F;

				public override void M()
				{
				}
			}
		}
	}
}