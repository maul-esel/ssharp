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
	using ISSE.SafetyChecking.AnalysisModelTraverser;
	using ISSE.SafetyChecking.DiscreteTimeMarkovChain;
	using ISSE.SafetyChecking.ExecutedModel;
	using ISSE.SafetyChecking.Formula;
	using ISSE.SafetyChecking.Modeling;
	using ISSE.SafetyChecking.Simulator;
	using ISSE.SafetyChecking.Utilities;
	using Shouldly;
	using Utilities;
	using Xunit;
	using Xunit.Abstractions;
	
	public class MakeChoiceDeterministic : AnalysisTest
	{
		public MakeChoiceDeterministic(ITestOutputHelper output = null) : base(output)
		{
		}

		[Fact]
		public void Check()
		{
			Probability probabilityOfFinal1;
			Probability probabilityOfFinal2;
			Probability probabilityOfFinal3;
			Probability probabilityOfFinal4;

			var m = new Model();
			
			var formula1 = new BinaryFormula(Model.FIs2, BinaryOperator.Or, Model.FIs3);
			var formula2 = Model.FIs1;
			var formula3 = new BinaryFormula(new BinaryFormula(Model.GIs0, BinaryOperator.Or, Model.GIs7), BinaryOperator.Or, Model.GIs8);
			var formula4 = Model.GIs7;

			var final1 = new UnaryFormula(formula1, UnaryOperator.Finally);
			var final2 = new UnaryFormula(formula2, UnaryOperator.Finally);
			var final3 = new UnaryFormula(formula3, UnaryOperator.Finally);
			var final4 = new UnaryFormula(formula4, UnaryOperator.Finally);

			var markovChainGenerator = new SimpleDtmcFromExecutableModelGenerator(m);
			markovChainGenerator.Configuration.ModelCapacity = ModelCapacityByMemorySize.Small;
			markovChainGenerator.AddFormulaToCheck(final1);
			markovChainGenerator.AddFormulaToCheck(final2);
			markovChainGenerator.AddFormulaToCheck(final3);
			markovChainGenerator.AddFormulaToCheck(final4);
			var dtmc = markovChainGenerator.GenerateMarkovChain();
			var typeOfModelChecker = typeof(BuiltinDtmcModelChecker);
			var modelChecker = (DtmcModelChecker)Activator.CreateInstance(typeOfModelChecker, dtmc, Output.TextWriterAdapter());
			using (modelChecker)
			{
				probabilityOfFinal1 = modelChecker.CalculateProbability(final1);
				probabilityOfFinal2 = modelChecker.CalculateProbability(final2);
				probabilityOfFinal3 = modelChecker.CalculateProbability(final3);
				probabilityOfFinal4 = modelChecker.CalculateProbability(final4);
			}

			probabilityOfFinal1.Is(0.0, tolerance: 0.0001).ShouldBe(true);
			probabilityOfFinal2.Is(1.0, tolerance: 0.0001).ShouldBe(true);
			probabilityOfFinal3.Is(1.0, tolerance: 0.0001).ShouldBe(true);
			probabilityOfFinal4.Is(0.8333333333, tolerance: 0.0001).ShouldBe(true);
		}

		public class Model : SimpleModelBase
		{
			public override Fault[] Faults { get; } = new Fault[0];
			public override bool[] LocalBools { get; } = new bool[0];
			public override int[] LocalInts { get; } = new int[] {0,0};

			public override void SetInitialState()
			{
				State = 0;
			}

			private int F
			{
				get { return LocalInts[0]; }
				set { LocalInts[0] = value; }
			}

			private int G
			{
				get { return LocalInts[1]; }
				set { LocalInts[1] = value; }
			}

			public override void Update()
			{
				if (State != 0)
					return;
				State = 1;

				G = Choice.Choose(3, 5);
				F = Choice.Choose(1, 2, 3);

				var index = Choice.Resolver.LastChoiceIndex;

				G = Choice.Choose(7, 8);

				Choice.Resolver.MakeChoiceAtIndexDeterministic(index);
			}

			public static Formula FIs1 = new SimpleLocalVarInRangeFormula(0,1);
			public static Formula FIs2 = new SimpleLocalVarInRangeFormula(0,2);
			public static Formula FIs3 = new SimpleLocalVarInRangeFormula(0,3);
			public static Formula GIs0 = new SimpleLocalVarInRangeFormula(1,0);
			public static Formula GIs7 = new SimpleLocalVarInRangeFormula(1,7);
			public static Formula GIs8 = new SimpleLocalVarInRangeFormula(1,8);
		}
	}
}