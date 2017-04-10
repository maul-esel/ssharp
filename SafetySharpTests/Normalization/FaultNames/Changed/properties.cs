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

namespace Tests.Normalization.FaultNames.Changed
{
	using ISSE.SafetyChecking.Modeling;
	using SafetySharp.Modeling;

	public class In3
	{
		private PermanentFault F1 { get; set; } = new PermanentFault();
		private Fault F2 { get; } = new TransientFault();
		private Fault F3 { get; } = new TransientFault { Activation = Activation.Forced };
		private Fault F4 { get; }

		public In3()
		{
			F4 = new PermanentFault();
		}
	}

	public class Out3
	{
		private PermanentFault F1 { get; set; } = new PermanentFault() { Name = "F1" };
		private Fault F2 { get; } = new TransientFault() { Name = "F2" };
		private Fault F3 { get; } = new TransientFault { Activation = Activation.Forced, Name = "F3" };
		private Fault F4 { get; }

		public Out3()
		{
			F4 = new PermanentFault() { Name = "F4" };
		}
	}
}