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

namespace Tests.Serialization.Enumerations
{
	using SafetySharp.Runtime.Serialization;
	using Shouldly;

	internal class Int64 : SerializationObject
	{
		protected override void Check()
		{
			var c = new C { F = E.B };

			GenerateCode(SerializationMode.Full, c);
			StateSlotCount.ShouldBe(2);

			Serialize();
			c.F = E.C;
			Deserialize();
			c.F.ShouldBe(E.B);

			c.F = E.D;
			Serialize();
			c.F = E.C;
			Deserialize();
			c.F.ShouldBe(E.D);

			c.F = E.E;
			Serialize();
			c.F = E.C;
			Deserialize();
			c.F.ShouldBe(E.E);

			c.F = E.F;
			Serialize();
			c.F = E.C;
			Deserialize();
			c.F.ShouldBe(E.F);
		}

		private enum E : long
		{
			A,
			B,
			C,
			D = -8,
			E = System.Int64.MaxValue,
			F = System.Int64.MinValue,
		}

		private class C
		{
			public E F;
		}
	}
}