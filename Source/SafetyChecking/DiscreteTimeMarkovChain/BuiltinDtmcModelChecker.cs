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

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace ISSE.SafetyChecking.DiscreteTimeMarkovChain
{
	using Modeling;
	using System.Diagnostics;
	using System.Globalization;
	using System.IO;
	using Utilities;
	using Formula;
	using GenericDataStructures;

	class BuiltinDtmcModelChecker : DtmcModelChecker
	{
		private readonly DiscreteTimeMarkovChain.UnderlyingDigraph _underlyingDigraph;

		// Note: Should be used with using(var modelchecker = new ...)
		public BuiltinDtmcModelChecker(DiscreteTimeMarkovChain markovChain, TextWriter output = null) : base(markovChain, output)
		{
			_underlyingDigraph = MarkovChain.CreateUnderlyingDigraph();
		}

		private SparseDoubleMatrix CreateDerivedMatrix(Dictionary<long, bool> exactlyOneStates, Dictionary<long, bool> exactlyZeroStates)
		{
			//Derived matrix is 0-based. Row i is equivalent to the probability distribution of state i (this is not the case for the Markov Chain). 

			var derivedMatrix = new SparseDoubleMatrix(MarkovChain.States, MarkovChain.Transitions+ MarkovChain.States); //Transitions+States is a upper limit

			var enumerator = MarkovChain.GetEnumerator();

			for (var sourceState = 0; sourceState < MarkovChain.States; sourceState++)
			{
				enumerator.SelectSourceState(sourceState);
				derivedMatrix.SetRow(sourceState);
				if (exactlyOneStates.ContainsKey(sourceState) || exactlyZeroStates.ContainsKey(sourceState))
				{
					// only add a self reference entry
					derivedMatrix.AddColumnValueToCurrentRow(new SparseDoubleMatrix.ColumnValue(sourceState,1.0));
				}
				else
				{
					// if state is neither exactlyOneStates nor exactlyZeroStates, it is a toCalculateState
					var selfReferenceAdded = false;
					while (enumerator.MoveNextTransition())
					{
						var columnValueEntry = enumerator.CurrentTransition;
						var targetState = columnValueEntry.Column;
						if (targetState == sourceState)
						{
							//this implements the removal of the identity matrix
							derivedMatrix.AddColumnValueToCurrentRow(new SparseDoubleMatrix.ColumnValue(sourceState, columnValueEntry.Value - 1.0));
							selfReferenceAdded = true;
						}
						else
						{
							derivedMatrix.AddColumnValueToCurrentRow(columnValueEntry);
						}
					}
					if (!selfReferenceAdded)
					{
						//this implements the removal of the identity matrix (if not already done)
						derivedMatrix.AddColumnValueToCurrentRow(new SparseDoubleMatrix.ColumnValue(sourceState, -1.0));
					}
				}
				derivedMatrix.FinishRow();
			}
			return derivedMatrix;
		}

		private double[] CreateDerivedVector(Dictionary<long, bool> exactlyOneStates)
		{
			var derivedVector = new double[MarkovChain.States];

			for (var i = 0L; i < MarkovChain.States; i++)
			{
				if (exactlyOneStates.ContainsKey(i))
					derivedVector[i] = 1.0;
				else
					derivedVector[i] = 0.0;
			}
			return derivedVector;
		}

		public Dictionary<long, bool> CreateComplement(Dictionary<long, bool> states)
		{
			var complement = new Dictionary<long, bool>();
			for (var i = 0L; i < MarkovChain.States; i++)
			{
				if (!states.ContainsKey(i))
					complement.Add(i, true);
			}
			return complement;
		}
		

		internal Dictionary<long, bool> CalculateSatisfiedStates(Func<long, bool> formulaEvaluator)
		{
			var satisfiedStates = new Dictionary<long, bool>();
			for (var i = 0L; i < MarkovChain.States; i++)
			{
				if (formulaEvaluator(i))
					satisfiedStates.Add(i,true);
			}
			return satisfiedStates;
		}
		
		private double[] GaussSeidel(SparseDoubleMatrix derivedMatrix, double[] derivedVector, int iterationsLeft)
		{
			var stopwatch = new Stopwatch();
			stopwatch.Start();

			var stateCount = MarkovChain.States;
			var resultVector = new double[stateCount];
			var fixPointReached = iterationsLeft <= 0;
			var iterations = 0;

			//Derived matrix is 0-based. Row i is equivalent to the probability distribution of state i (this is not the case for the Markov Chain). 
			var enumerator = derivedMatrix.GetEnumerator();

			for (var i = 0; i < stateCount; i++)
			{
				resultVector[i] = 0.0;
			}
			while (!fixPointReached)
			{
				for (var i = 0; i < stateCount; i++)
				{
					var reflexiveEntry = 0.0;
					var temporaryValue = derivedVector[i];

					enumerator.MoveRow(i);
					while (enumerator.MoveNextColumn())
					{
						var currentEntry = enumerator.CurrentColumnValue.Value;
						if (currentEntry.Column == i)
							reflexiveEntry = currentEntry.Value;
						else
							temporaryValue -= currentEntry.Value * resultVector[currentEntry.Column];
					}
					Assert.That(reflexiveEntry != 0.0, "entry must not be 0.0");

					resultVector[i] = temporaryValue/ reflexiveEntry;
				}

				iterationsLeft--;
				iterations++;
				if (iterations % 10 == 0)
				{
					stopwatch.Stop();
					var currentProbability = CalculateFinalProbability(resultVector);
					_output?.WriteLine($"Completed {iterations} Gauss-Seidel iterations in {stopwatch.Elapsed}.  Current probability={currentProbability.ToString(CultureInfo.InvariantCulture)}");
					stopwatch.Start();
				}
				if (iterationsLeft <= 0)
					fixPointReached = true;
			}
			stopwatch.Stop();

			return resultVector;
		}


		private double CalculateUnboundUntil(Formula psi, Formula phi, int iterationsLeft)
		{
			// On algorithmic verification methods for probabilistic systems (1998) by Christel Baier
			// Theorem 3.1.6 (page 36)
			// http://wwwneu.inf.tu-dresden.de/content/institutes/thi/algi/publikationen/texte/15_98.pdf

			// Pr[phi U psi]
			// calculate P [true U<=steps psi]

			var stopwatch = new Stopwatch();
			stopwatch.Start();

			var psiEvaluator = MarkovChain.CreateFormulaEvaluator(psi);
			var stateCount = MarkovChain.States;

			var fixPointReached = iterationsLeft <= 0;

			var directlySatisfiedStates = CalculateSatisfiedStates(psiEvaluator);
			Dictionary<long, bool> excludedStates;
			if (phi == null)
			{
				excludedStates = new Dictionary<long, bool>();
			}
			else
			{
				// excludedStates = Sat(\phi) \Cup Sat(psi)
				var phiEvaluator = MarkovChain.CreateFormulaEvaluator(phi);
				var phiOrPsiStates = CalculateSatisfiedStates(phiEvaluator);
				foreach (var directlySatisfiedState in directlySatisfiedStates)
				{
					phiOrPsiStates[directlySatisfiedState.Key] = true;
				}
				excludedStates = CreateComplement(phiOrPsiStates);
			}
			
			// calculate probabilityExactlyZero (prob0)
			var probabilityExactlyZero = ProbabilityExactlyZero(directlySatisfiedStates, excludedStates);

			// calculate probabilityExactlyOne (prob1)
			var probabilityExactlyOne = ProbabilityExactlyOne(directlySatisfiedStates, excludedStates, probabilityExactlyZero);


			var enumerator = MarkovChain.GetEnumerator();

			var xold = new double[stateCount];
			var xnew = CreateDerivedVector(probabilityExactlyOne);
			var loops = 0;
			while (!fixPointReached)
			{
				// switch xold and xnew
				var xtemp = xold;
				xold = xnew;
				xnew = xtemp;
				iterationsLeft--;
				loops++;
				for (var i = 0; i < stateCount; i++)
				{
					if (probabilityExactlyOne.ContainsKey(i))
					{
						//we could remove this line, because already set by CreateDerivedVector and never changed when we initialize xold with CreateDerivedVector(directlySatisfiedStates)
						xnew[i] = 1.0;
					}
					else if (probabilityExactlyZero.ContainsKey(i))
					{
						//we could remove this line, because already set by CreateDerivedVector and never changed when we initialize xold with CreateDerivedVector(directlySatisfiedStates)
						xnew[i] = 0.0;
					}
					else
					{
						enumerator.SelectSourceState(i);
						var sum = 0.0;
						while (enumerator.MoveNextTransition())
						{
							var entry = enumerator.CurrentTransition;
							sum += entry.Value * xold[entry.Column];
						}
						xnew[i] = sum;
					}
				}

				if (loops % 10 == 0)
				{
					stopwatch.Stop();
					var currentProbability = CalculateFinalProbability(xnew);
					_output?.WriteLine($"{loops} Fixpoint Until iterations in {stopwatch.Elapsed}. Current probability={currentProbability.ToString(CultureInfo.InvariantCulture)}");
					stopwatch.Start();
				}
				if (iterationsLeft <= 0)
					fixPointReached = true;
			}

			var finalProbability = CalculateFinalProbability(xnew);

			stopwatch.Stop();
			return finalProbability;
		}

		private double CalculateFinalProbability(double[] initialStateProbabilities)
		{
			var finalProbability = 0.0;

			var enumerator = MarkovChain.GetEnumerator();
			enumerator.SelectInitialDistribution();
			while (enumerator.MoveNextTransition())
			{
				var entry = enumerator.CurrentTransition;
				finalProbability += entry.Value * initialStateProbabilities[entry.Column];
			}
			return finalProbability;
		}

		private double CalculateProbabilityToReachStateFormulaInBoundedSteps(Formula psi, Formula phi, int steps)
		{
			// Pr[phi U psi]
			// calculate P [true U<=steps psi]
			
			var stopwatch = new Stopwatch();
			stopwatch.Start();

			var psiEvaluator = MarkovChain.CreateFormulaEvaluator(psi);
			var stateCount = MarkovChain.States;

			var directlySatisfiedStates = CalculateSatisfiedStates(psiEvaluator);
			Dictionary<long, bool> excludedStates;
			if (phi == null)
			{
				 excludedStates = new Dictionary<long, bool>();
			}
			else
			{
				// excludedStates = Sat(\phi) \Cup Sat(psi)
				var phiEvaluator = MarkovChain.CreateFormulaEvaluator(phi);
				var phiOrPsiStates = CalculateSatisfiedStates(phiEvaluator);
				foreach (var directlySatisfiedState in directlySatisfiedStates)
				{
					phiOrPsiStates[directlySatisfiedState.Key]=true;
				}
				excludedStates = CreateComplement(phiOrPsiStates);
			}
			
			var enumerator = MarkovChain.GetEnumerator();

			var xold = new double[stateCount];
			var xnew = CreateDerivedVector(directlySatisfiedStates);
			var loops = 0;
			while (loops < steps)
			{
				// switch xold and xnew
				var xtemp = xold;
				xold = xnew;
				xnew = xtemp;
				loops++;
				for (var i = 0; i < stateCount; i++)
				{
					if (directlySatisfiedStates.ContainsKey(i))
					{
						//we could remove this line, because already set by CreateDerivedVector and never changed when we initialize xold with CreateDerivedVector(directlySatisfiedStates)
						xnew[i] = 1.0;
					}
					else if (excludedStates.ContainsKey(i))
					{
						//we could remove this line, because already set by CreateDerivedVector and never changed when we initialize xold with CreateDerivedVector(directlySatisfiedStates)
						xnew[i] = 0.0;
					}
					else
					{
						enumerator.SelectSourceState(i);
						var sum = 0.0;
						while (enumerator.MoveNextTransition())
						{
							var entry = enumerator.CurrentTransition;
							sum += entry.Value * xold[entry.Column];
						}
						xnew[i] = sum;
					}
				}

				if (loops % 10 == 0)
				{
					stopwatch.Stop();
					var currentProbability = CalculateFinalProbability(xnew);
					_output?.WriteLine($"{loops} Bounded Until iterations in {stopwatch.Elapsed}. Current probability={currentProbability.ToString(CultureInfo.InvariantCulture)}");
					stopwatch.Start();
				}
			}

			var finalProbability=CalculateFinalProbability(xnew);
			
			stopwatch.Stop();
			return finalProbability;
		}

		private Dictionary<long, bool> ProbabilityExactlyZero(Dictionary<long, bool> directlySatisfiedStates , Dictionary<long, bool> excludedStates)
		{
			// calculate probabilityExactlyZero (prob0)
			Func<long, bool> nodesToIgnore =
				excludedStates.ContainsKey;
			var probabilityGreaterThanZero = _underlyingDigraph.BaseGraph.GetAncestors(directlySatisfiedStates.Keys, nodesToIgnore);
			var probabilityExactlyZero = CreateComplement(probabilityGreaterThanZero);
			return probabilityExactlyZero;
		}

		private Dictionary<long, bool> ProbabilityExactlyOne(Dictionary<long, bool> directlySatisfiedStates, Dictionary<long, bool> excludedStates, Dictionary<long, bool> probabilityExactlyZero)
		{
			// calculate probabilityExactlyOne (prob1)
			Func<long, bool> nodesToIgnore =
				node => excludedStates.ContainsKey(node) || directlySatisfiedStates.ContainsKey(node);
			var probabilitySmallerThanOne = _underlyingDigraph.BaseGraph.GetAncestors(probabilityExactlyZero.Keys, nodesToIgnore); ;
			var probabilityExactlyOne = CreateComplement(probabilitySmallerThanOne);
			return probabilityExactlyOne;
		}

		private double CalculateProbabilityToReachStateFormula(Formula psi)
		{
			// calculate P [true U psi]
			var psiEvaluator = MarkovChain.CreateFormulaEvaluator(psi);
			var directlySatisfiedStates = CalculateSatisfiedStates(psiEvaluator);
			var excludedStates = new Dictionary<long,bool>();  // change for \phi Until \psi. For classical "Finally", no states are excluded

			// calculate probabilityExactlyZero (prob0)
			var probabilityExactlyZero = ProbabilityExactlyZero(directlySatisfiedStates, excludedStates );

			// calculate probabilityExactlyOne (prob1)
			var probabilityExactlyOne = ProbabilityExactlyOne(directlySatisfiedStates, excludedStates , probabilityExactlyZero);

			//TODO: Do not calculate exact state probabilities, when _every_ initial state>0 is either in probabilityExactlyZero or in probabilityExactlyOne

			var derivedMatrix = CreateDerivedMatrix(probabilityExactlyOne, probabilityExactlyZero);
			var derivedVector = CreateDerivedVector(probabilityExactlyOne);

			var resultVector = GaussSeidel(derivedMatrix, derivedVector, 50);
			var finalProbability = CalculateFinalProbability(resultVector);

			return finalProbability;
		}

		internal override Probability CalculateProbability(Formula formulaToCheck)
		{
			_output.WriteLine($"Checking formula: {formulaToCheck}");
			var stopwatch = new Stopwatch();
			stopwatch.Start();

			var finallyUnboundUnaryFormula = formulaToCheck as UnaryFormula;
			var finallyBoundedUnaryFormula = formulaToCheck as BoundedUnaryFormula;
			var finallyBoundedBinaryFormula = formulaToCheck as BoundedBinaryFormula;

			double result;

			if (finallyUnboundUnaryFormula != null && finallyUnboundUnaryFormula.Operator == UnaryOperator.Finally)
			{
				result = CalculateProbabilityToReachStateFormula(finallyUnboundUnaryFormula.Operand);
			}
			else if (finallyBoundedUnaryFormula != null && finallyBoundedUnaryFormula.Operator == UnaryOperator.Finally)
			{
				result = CalculateProbabilityToReachStateFormulaInBoundedSteps(finallyBoundedUnaryFormula.Operand, null, finallyBoundedUnaryFormula.Bound);
			}
			else if (finallyBoundedBinaryFormula != null && finallyBoundedBinaryFormula.Operator == BinaryOperator.Until)
			{
				result = CalculateProbabilityToReachStateFormulaInBoundedSteps(finallyBoundedBinaryFormula.RightOperand, finallyBoundedBinaryFormula.LeftOperand, finallyBoundedBinaryFormula.Bound);
			}
			else
			{
				throw new NotImplementedException();
			}
			
			stopwatch.Stop();

			_output?.WriteLine($"Built-in probabilistic model checker model checking time: {stopwatch.Elapsed}");
			return new Probability(result);
		}

		private void ApproximateDelta(double target)
		{
			// https://en.wikipedia.org/wiki/Machine_epsilon
			//  Note: Result is even more inaccurate because in lines like
			//		newValue += verySmallValue1 * verySmallValue2
			//  as they appear in the iteration algorithm may already lead to epsilons which are ignored
			//  even if they would have an impact in sum ("sum+=100*epsilon" has an influence, but "for (i=1..100) {sum+=epsilon;}" not.

			double epsilon = 1.0;
			// ReSharper disable once CompareOfFloatsByEqualityOperator
			while ((target + (epsilon / 2.0)) != target)
				epsilon /= 2.0;

			_output?.WriteLine(epsilon);
		}

		internal override bool CalculateBoolean(Formula formulaToCheck)
		{
			throw new NotImplementedException();
		}

		internal override RewardResult CalculateReward(Formula formulaToCheck)
		{
			throw new NotImplementedException();
		}

		/// <summary>
		/// Performs application-defined tasks associated with freeing, releasing, or resetting unmanaged resources.
		/// </summary>
		public override void Dispose()
		{
		}
	}
}
