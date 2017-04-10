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

namespace Tests.Serialization.Objects
{
	using SafetySharp.Runtime.Serialization;
	using Shouldly;

	internal class SerializedArrays : SerializationObject
	{
		protected override void Check()
		{
			var b = new bool[] { true, false, true, false, false, true, true };
			var c = new byte[] { 1, 0, 1, 12, 14 };
			var i = new int[] { 293580239, -912994792 };
			var s = new short[] { -30012, 30212 };

			GenerateCode(SerializationMode.Optimized, c, b, i, s);
			StateSlotCount.ShouldBe(5);

			Serialize();
			c[0] = 0;
			c[1] = 0;
			c[2] = 0;
			c[3] = 0;
			c[4] = 0;
			b[0] = false;
			b[1] = false;
			b[2] = false;
			b[3] = false;
			b[4] = false;
			b[5] = false;
			b[6] = false;
			i[0] = 0;
			i[1] = 0;
			s[0] = 0;
			s[1] = 0;

			Deserialize();
			c[0].ShouldBe((byte)1);
			c[1].ShouldBe((byte)0);
			c[2].ShouldBe((byte)1);
			c[3].ShouldBe((byte)12);
			c[4].ShouldBe((byte)14);
			b.ShouldBe(new[] { true, false, true, false, false, true, true });
			i[0].ShouldBe(293580239);
			i[1].ShouldBe(-912994792);
			s[0].ShouldBe((short)-30012);
			s[1].ShouldBe((short)30212);
		}
	}
}