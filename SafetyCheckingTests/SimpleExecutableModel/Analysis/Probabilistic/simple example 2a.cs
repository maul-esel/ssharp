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

namespace Tests.SimpleExecutableModel.Analysis.Probabilistic
{
	using System;
	using ISSE.SafetyChecking.DiscreteTimeMarkovChain;
	using ISSE.SafetyChecking.ExecutedModel;
	using ISSE.SafetyChecking.Formula;
	using ISSE.SafetyChecking.Modeling;
	using Shouldly;
	using Utilities;
	using Xunit;
	using Xunit.Abstractions;
	

	public class SimpleExample2a : AnalysisTest
	{
		public SimpleExample2a(ITestOutputHelper output = null) : base(output)
		{
		}

		[Fact]
		public void Check()
		{
			var m = new SharedModels.SimpleExample2a();
			Probability probabilityOfFinal0;
			Probability probabilityOfFinal1;
			Probability probabilityOfFinal2;

			var final0Formula = new UnaryFormula(new SimpleStateInRangeFormula(0), UnaryOperator.Finally);
			var final1Formula = new UnaryFormula(new SimpleStateInRangeFormula(1), UnaryOperator.Finally);
			var final2Formula = new UnaryFormula(new SimpleStateInRangeFormula(2), UnaryOperator.Finally);

			var markovChainGenerator = new SimpleDtmcFromExecutableModelGenerator(m);
			markovChainGenerator.Configuration.ModelCapacity = ModelCapacityByMemorySize.Small;
			markovChainGenerator.AddFormulaToCheck(final0Formula);
			markovChainGenerator.AddFormulaToCheck(final1Formula);
			markovChainGenerator.AddFormulaToCheck(final2Formula);
			var dtmc = markovChainGenerator.GenerateMarkovChain();
			var typeOfModelChecker = typeof(BuiltinDtmcModelChecker);
			var modelChecker = (DtmcModelChecker)Activator.CreateInstance(typeOfModelChecker, dtmc, Output.TextWriterAdapter());
			using (modelChecker)
			{
				probabilityOfFinal0 = modelChecker.CalculateProbability(final0Formula);
				probabilityOfFinal1 = modelChecker.CalculateProbability(final1Formula);
				probabilityOfFinal2 = modelChecker.CalculateProbability(final2Formula);
			}

			probabilityOfFinal0.Is(1.0, 0.000001).ShouldBe(true);
			probabilityOfFinal1.Is(0.5, 0.000001).ShouldBe(true);
			probabilityOfFinal2.Is(0.5, 0.000001).ShouldBe(true);
		}
	}
}