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

namespace Tests.DataStructures
{
	using System;
	using System.Linq;
	using ISSE.SafetyChecking.Utilities;
	using Shouldly;
	using Utilities;
	using Xunit;
	using Xunit.Abstractions;

	public unsafe class MemoryBufferTests
	{
		private const int NumberOfElements = 1024;
		public TestTraceOutput Output { get; }

		private readonly MemoryBuffer _memoryBuffer = new MemoryBuffer();
		private readonly int* _memoryPointer;

		public MemoryBufferTests(ITestOutputHelper output)
		{
			Output = new TestTraceOutput(output);

			_memoryBuffer.Resize(NumberOfElements * sizeof(int), zeroMemory: false);
			_memoryPointer = (int*)_memoryBuffer.Pointer;
		}

		[Fact]
		public void ZeroMemoryCheck()
		{
			MemoryBuffer.SetAllBitsMemoryWithInitblk.Delegate(new IntPtr(_memoryPointer), sizeof(int) * NumberOfElements);
			MemoryBuffer.ZeroMemoryWithInitblk.Delegate(new IntPtr(_memoryPointer), sizeof(int) * NumberOfElements);
			for (var i = 0; i < NumberOfElements; i++)
			{
				_memoryPointer[i].ShouldBe(0);
			}
		}

		[Fact]
		public void SetAllBitsMemoryCheck()
		{
			MemoryBuffer.ZeroMemoryWithInitblk.Delegate(new IntPtr(_memoryPointer), sizeof(int) * NumberOfElements);
			MemoryBuffer.SetAllBitsMemoryWithInitblk.Delegate(new IntPtr(_memoryPointer), sizeof(int) * NumberOfElements);
			for (var i = 0; i < NumberOfElements; i++)
			{
				_memoryPointer[i].ShouldBe(-1);
			}
		}

		[Fact]
		public void MixedCheck()
		{
			MemoryBuffer.ZeroMemoryWithInitblk.Delegate(new IntPtr(_memoryPointer), sizeof(int) * NumberOfElements);
			MemoryBuffer.SetAllBitsMemoryWithInitblk.Delegate(new IntPtr(_memoryPointer), sizeof(int) * NumberOfElements / 2);
			for (var i = 0; i < NumberOfElements/2; i++)
			{
				_memoryPointer[i].ShouldBe(-1);
			}
			for (var i = NumberOfElements / 2; i < NumberOfElements; i++)
			{
				_memoryPointer[i].ShouldBe(0);
			}
		}
	}
}
