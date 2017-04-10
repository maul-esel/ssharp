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

namespace Tests
{
	using Xunit;

	public partial class SerializationTests
	{
		[Theory, MemberData(nameof(DiscoverTests), "Serialization/PrimitiveTypes")]
		public void PrimitiveTypes(string test, string file)
		{
			ExecuteDynamicTests(file);
		}

		[Theory, MemberData(nameof(DiscoverTests), "Serialization/Enumerations")]
		public void Enumerations(string test, string file)
		{
			ExecuteDynamicTests(file);
		}

		[Theory, MemberData(nameof(DiscoverTests), "Serialization/Misc")]
		public void Misc(string test, string file)
		{
			ExecuteDynamicTests(file);
		}

		[Theory, MemberData(nameof(DiscoverTests), "Serialization/Objects")]
		public void Objects(string test, string file)
		{
			ExecuteDynamicTests(file);
		}

		[Theory, MemberData(nameof(DiscoverTests), "Serialization/RuntimeModels")]
		public void RuntimeModels(string test, string file)
		{
			ExecuteDynamicTests(file);
		}

		[Theory, MemberData(nameof(DiscoverTests), "Serialization/StateLabels")]
		public void StateLabels(string test, string file)
		{
			ExecuteDynamicTests(file);
		}

		[Theory, MemberData(nameof(DiscoverTests), "Serialization/Ranges")]
		public void Ranges(string test, string file)
		{
			ExecuteDynamicTests(file);
		}

		[Theory, MemberData(nameof(DiscoverTests), "Serialization/Compaction")]
		public void Compaction(string test, string file)
		{
			ExecuteDynamicTests(file);
		}

		[Theory(Skip = "unsolved, but known bug"), MemberData(nameof(DiscoverTests), "Serialization/UnsolvedBugs")]
		public void UnsolvedBugs(string test, string file)
		{
			ExecuteDynamicTests(file);
		}
	}
}