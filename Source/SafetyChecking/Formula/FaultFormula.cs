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

namespace ISSE.SafetyChecking.Formula
{
	using Modeling;

	/// <summary>
	///   Represents a formula, which evaluates to true if a fault was activated in the step. Use
	///   only with caution, when activating a fault optimization.
	/// </summary>
	public class FaultFormula : AtomarPropositionFormula
	{
		public Fault Fault { get; }

		/// <summary>
		///   Initializes a new instance of the <see cref="FaultFormula" /> class.
		/// </summary>
		/// <param name="fault"> The fault for which activation should be checked </param>
		/// <param name="label">
		///   The name that should be used for the state label of the formula. If <c>null</c>, a unique name is generated.
		/// </param>
		public FaultFormula(Fault fault, string label = null) : base(label)
		{
			Fault = fault;
		}
	}
}