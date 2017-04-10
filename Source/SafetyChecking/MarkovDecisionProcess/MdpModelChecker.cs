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

namespace ISSE.SafetyChecking.MarkovDecisionProcess
{
	using System;
	using System.IO;
	using Modeling;
	using Formula;

	// Mrmc is in file ProbabilisticModelChecker.Mrmc.cs which is nested in ProbabilisticModelChecker.cs.
	// Open arrow of ProbabilisticModelChecker.cs in Solution Explorer to see nested files.
	

	/// <summary>
	///   Represents a base class for external probabilistic model checker tools.
	/// </summary>
	internal abstract class MdpModelChecker : IDisposable
	{
		protected TextWriter _output;

		internal MarkovDecisionProcess MarkovDecisionProcess { get; }
		
		// Note: Should be used with using(var modelchecker = new ...)
		protected MdpModelChecker(MarkovDecisionProcess mdp,TextWriter output =null)
		{
			MarkovDecisionProcess = mdp;
			_output = output;
		}

		public abstract void Dispose();

		internal abstract Probability CalculateMinimalProbability(Formula formulaToCheck);

		internal abstract Probability CalculateMaximalProbability(Formula formulaToCheck);

		internal abstract ProbabilityRange CalculateProbabilityRange(Formula formulaToCheck);

		internal abstract bool CalculateFormula(Formula formulaToCheck);

		internal abstract RewardResult CalculateReward(Formula formulaToCheck);
	}
}