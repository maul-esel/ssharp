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

namespace ISSE.SafetyChecking.Modeling
{
	using System.Globalization;
	using Modeling;
	
	public struct ProbabilityRange
	{
		public static ProbabilityRange Zero = new ProbabilityRange(0.0, 0.0);

		public static ProbabilityRange One = new ProbabilityRange(1.0, 1.0);

		public static ProbabilityRange ZeroToOne = new ProbabilityRange(0.0, 1.0);


		public double MinValue { get; }

		public double MaxValue { get; }

		public ProbabilityRange(Probability minProbability, Probability maxProbability)
		{
			MinValue = minProbability.Value;
			MaxValue = maxProbability.Value;
		}

		public ProbabilityRange(double minProbability, Probability maxProbability)
		{
			MinValue = minProbability;
			MaxValue = maxProbability.Value;
		}

		public ProbabilityRange(Probability minProbability, double maxProbability)
		{
			MinValue = minProbability.Value;
			MaxValue = maxProbability;
		}

		public ProbabilityRange(double minProbability, double maxProbability)
		{
			MinValue = minProbability;
			MaxValue = maxProbability;
		}

		/// <summary>
		/// Returns the fully qualified type name of this instance.
		/// </summary>
		/// <returns>
		/// A <see cref="T:System.String"/> containing a fully qualified type name.
		/// </returns>
		public override string ToString()
		{
			return $"[{MinValue.ToString(CultureInfo.InvariantCulture)},{MaxValue.ToString(CultureInfo.InvariantCulture)}]";
		}
	}
}
