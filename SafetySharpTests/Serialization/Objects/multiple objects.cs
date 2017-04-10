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

	internal class MultipleObjects : SerializationObject
	{
		protected override void Check()
		{
			var o1 = new object();
			var o2 = new object();
			var o3 = new object();
			var c = new C { O1 = o1, O2 = null, O3 = o1 };

			GenerateCode(SerializationMode.Full, c, o1, o2, o3);
			StateSlotCount.ShouldBe(2);

			Serialize();
			c.O1 = null;
			c.O2 = o3;
			c.O3 = null;
			Deserialize();
			c.O1.ShouldBe(o1);
			c.O2.ShouldBe(null);
			c.O3.ShouldBe(o1);

			c.O1 = null;
			c.O2 = o2;
			c.O3 = o3;
			Serialize();
			c.O1 = null;
			c.O2 = o3;
			c.O3 = null;
			Deserialize();
			c.O1.ShouldBe(null);
			c.O2.ShouldBe(o2);
			c.O3.ShouldBe(o3);

			c.O1 = o3;
			c.O2 = o1;
			c.O3 = o2;
			Serialize();
			c.O1 = null;
			c.O2 = null;
			c.O3 = null;
			Deserialize();
			c.O1.ShouldBe(o3);
			c.O2.ShouldBe(o1);
			c.O3.ShouldBe(o2);
		}

		internal class C
		{
			public object O1;
			public object O2;
			public object O3;
		}
	}
}