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

	public partial class ExecutionTests
	{
		[Theory, MemberData(nameof(DiscoverTests), "Execution/StateMachines")]
		public void StateMachines(string test, string file)
		{
			ExecuteDynamicTests(file);
		}

		[Theory, MemberData(nameof(DiscoverTests), "Execution/ProvidedPorts")]
		public void ProvidedPorts(string test, string file)
		{
			ExecuteDynamicTests(file);
		}

		[Theory, MemberData(nameof(DiscoverTests), "Execution/Bindings")]
		public void Bindings(string test, string file)
		{
			ExecuteDynamicTests(file);
		}

		[Theory, MemberData(nameof(DiscoverTests), "Execution/RequiredPorts")]
		public void RequiredPorts(string test, string file)
		{
			ExecuteDynamicTests(file);
		}

		[Theory, MemberData(nameof(DiscoverTests), "Execution/UpdateMethods")]
		public void UpdateMethods(string test, string file)
		{
			ExecuteDynamicTests(file);
		}

		[Theory, MemberData(nameof(DiscoverTests), "Execution/Faults")]
		public void Faults(string test, string file)
		{
			ExecuteDynamicTests(file);
		}

		[Theory, MemberData(nameof(DiscoverTests), "Execution/Scheduling")]
		public void Scheduling(string test, string file)
		{
			ExecuteDynamicTests(file);
		}

		[Theory, MemberData(nameof(DiscoverTests), "Execution/Simulation")]
		public void Simulation(string test, string file)
		{
			ExecuteDynamicTests(file);
		}

		[Theory, MemberData(nameof(DiscoverTests), "Execution/Components")]
		public void Components(string test, string file)
		{
			ExecuteDynamicTests(file);
		}

		[Theory, MemberData(nameof(DiscoverTests), "Execution/Models")]
		public void Models(string test, string file)
		{
			ExecuteDynamicTests(file);
		}

		[Theory, MemberData(nameof(DiscoverTests), "Execution/ModelCopy")]
		public void ModelCopy(string test, string file)
		{
			ExecuteDynamicTests(file);
		}

		[Theory, MemberData(nameof(DiscoverTests), "Execution/RootDiscovery")]
		public void RootDiscovery(string test, string file)
		{
			ExecuteDynamicTests(file);
		}
	}
}