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

namespace Tests.SimpleExecutableModel.Analysis.Invariants.CounterExamples
{
	using System;
	using ISSE.SafetyChecking.AnalysisModelTraverser;
	using ISSE.SafetyChecking.ExecutedModel;
	using ISSE.SafetyChecking.Formula;
	using ISSE.SafetyChecking.Modeling;
	using ISSE.SafetyChecking.Simulator;
	using ISSE.SafetyChecking.Utilities;
	using Shouldly;
	using Utilities;
	using Xunit;
	using Xunit.Abstractions;
	
	public class Formulas : AnalysisTest
	{
		public Formulas(ITestOutputHelper output = null) : base(output)
		{
		}

		[Fact]
		public void CheckDirect()
		{
			var m = new Model();
			var formulaNotTwo = new UnaryFormula(Model.StateIsTwo,UnaryOperator.Not);
			var checker = new SimpleQualitativeChecker
			{
				Configuration = AnalysisConfiguration.Default
			};
			checker.Configuration.ModelCapacity = ModelCapacityByMemorySize.Small;
			checker.OutputWritten += output => Output.Log(output);

			var result = checker.CheckInvariant(m, formulaNotTwo);

			var simulator = new Simulator<SimpleExecutableModel>(result.CounterExample);
			var simulatedModel = simulator.RuntimeModel.Model;
			simulatedModel.State.ShouldBe(0);
			simulator.IsCompleted.ShouldBe(false);
			simulator.SimulateStep();
			simulatedModel.State.ShouldBe(1);
			simulator.IsCompleted.ShouldBe(false);
			simulator.SimulateStep();
			simulatedModel.State.ShouldBe(2);
			simulator.IsCompleted.ShouldBe(true);
		}

		[Fact]
		public void CheckSaved()
		{
			var m = new Model();
			var formulaNotTwo = new UnaryFormula(Model.StateIsTwo, UnaryOperator.Not);
			var checker = new SimpleQualitativeChecker
			{
				Configuration = AnalysisConfiguration.Default
			};
			checker.Configuration.ModelCapacity = ModelCapacityByMemorySize.Small;
			checker.OutputWritten += output => Output.Log(output);

			var result = checker.CheckInvariant(m, formulaNotTwo);

			// save and load counterexample
			using (var file = new TemporaryFile(".ssharp"))
			{
				result.CounterExample.Save(file.FilePath);
				var counterExampleSerialization = new SimpleExecutableModelCounterExampleSerialization();
				var simulator = new Simulator<SimpleExecutableModel>(counterExampleSerialization.Load(file.FilePath));
				var simulatedModel = simulator.RuntimeModel.Model;
				simulatedModel.State.ShouldBe(0);
				simulator.IsCompleted.ShouldBe(false);
				simulator.SimulateStep();
				simulatedModel.State.ShouldBe(1);
				simulator.IsCompleted.ShouldBe(false);
				simulator.SimulateStep();
				simulatedModel.State.ShouldBe(2);
				simulator.IsCompleted.ShouldBe(true);
			}
		}

		public class Model : SimpleModelBase
		{
			public override Fault[] Faults { get; } = new Fault[0];
			public override bool[] LocalBools { get; } = new bool[0];
			public override int[] LocalInts { get; } = new int[0];

			public override void SetInitialState()
			{
				State = 0;
			}

			public override void Update()
			{
				if (State >= 100)
					return;
				++State;
			}

			public static Formula StateIsTwo = new SimpleStateInRangeFormula(2);
		}
	}
}