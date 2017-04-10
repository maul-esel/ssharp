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
	using ExecutableModel;
	using Modeling;
	using Utilities;
	using ExecutedModel;
	using System.Linq;
	using AnalysisModel;
	using Formula;

	/// <summary>
	///   Represents an <see cref="AnalysisModel" /> that computes its state by executing a <see cref="SafetySharpRuntimeModel" /> with
	///   probabilistic transitions.
	/// </summary>
	internal sealed class LtmdpExecutedModel<TExecutableModel> : ExecutedModel<TExecutableModel> where TExecutableModel : ExecutableModel<TExecutableModel>
	{

		internal enum EffectlessFaultsMinimizationMode
		{
			DontActivateEffectlessTransientFaults, //only restrict to transient faults
			Disable
		}

		private readonly EffectlessFaultsMinimizationMode _minimalizationMode = EffectlessFaultsMinimizationMode.DontActivateEffectlessTransientFaults;

		private readonly LtmdpCachedLabeledStates<TExecutableModel> _cachedLabeledStates;

		/// <summary>
		///   Initializes a new instance.
		/// </summary>
		/// <param name="runtimeModelCreator">A factory function that creates the model instance that should be executed.</param>
		/// <param name="successorStateCapacity">The maximum number of successor states supported per state.</param>
		/// <param name="stateHeaderBytes">
		///   The number of bytes that should be reserved at the beginning of each state vector for the model checker tool.
		/// </param>
		internal LtmdpExecutedModel(CoupledExecutableModelCreator<TExecutableModel> runtimeModelCreator, int stateHeaderBytes, long successorStateCapacity)
			: base(runtimeModelCreator,stateHeaderBytes)
		{
			var formulas = RuntimeModel.Formulas.Select(formula => FormulaCompilationVisitor<TExecutableModel>.Compile(RuntimeModel, formula)).ToArray();
			_cachedLabeledStates = new LtmdpCachedLabeledStates<TExecutableModel>(RuntimeModel, successorStateCapacity, formulas);

			ChoiceResolver = new LtmdpChoiceResolver();
			RuntimeModel.SetChoiceResolver(ChoiceResolver);

		}

		/// <summary>
		///   Gets the size of a single transition of the model in bytes.
		/// </summary>
		public override unsafe int TransitionSize => sizeof(LtmdpTransition);

		/// <summary>
		///   Disposes the object, releasing all managed and unmanaged resources.
		/// </summary>
		/// <param name="disposing">If true, indicates that the object is disposed; otherwise, the object is finalized.</param>
		protected override void OnDisposing(bool disposing)
		{
			if (disposing)
				_cachedLabeledStates.SafeDispose();

			base.OnDisposing(disposing);
		}

		/// <summary>
		///   Executes an initial transition of the model.
		/// </summary>
		protected override void ExecuteInitialTransition()
		{
			//TODO: _resetRewards();

			RuntimeModel.ExecuteInitialStep();

			switch (_minimalizationMode)
			{
				case EffectlessFaultsMinimizationMode.Disable:
					// Activate all faults
					// Note: Faults get activated and their effects occur, but they are not notified yet of their activation.
					foreach (var fault in RuntimeModel.NondeterministicFaults)
					{
						fault.TryActivate();
					}
					break;
				case EffectlessFaultsMinimizationMode.DontActivateEffectlessTransientFaults:
					// Activate all non-transient faults
					foreach (var fault in RuntimeModel.NondeterministicFaults)
					{
						if (!(fault is Modeling.TransientFault))
							fault.TryActivate();
					}
					break;
				default:
					throw new ArgumentOutOfRangeException();
			}
		}

		/// <summary>
		///   Executes a transition of the model.
		/// </summary>
		protected override void ExecuteTransition()
		{
			//TODO: _resetRewards();

			RuntimeModel.ExecuteStep();


			switch (_minimalizationMode)
			{
				case EffectlessFaultsMinimizationMode.Disable:
					// Activate all faults
					// Note: Faults get activated and their effects occur, but they are not notified yet of their activation.
					foreach (var fault in RuntimeModel.NondeterministicFaults)
					{
						fault.TryActivate();
					}
					break;
				case EffectlessFaultsMinimizationMode.DontActivateEffectlessTransientFaults:
					// Activate all non-transient faults
					foreach (var fault in RuntimeModel.NondeterministicFaults)
					{
						if (!(fault is Modeling.TransientFault))
							fault.TryActivate();
					}
					break;
				default:
					throw new ArgumentOutOfRangeException();
			}
		}
		
		/// <summary>
		///	  The probability to reach the current state from its predecessor from the last transition.
		/// </summary>
		public Probability GetProbability()
		{
			return ChoiceResolver.CalculateProbabilityOfPath();
		}

		/// <summary>
		///	  Get the continuation id of the current path from the choice resolver.
		/// </summary>
		public int GetContinuationId()
		{
			return ChoiceResolver.GetContinuationId();
		}

		/// <summary>
		///   Generates a transition from the model's current state.
		/// </summary>
		protected override void GenerateTransition()
		{
			_cachedLabeledStates.Add(RuntimeModel, GetProbability().Value, GetContinuationId());
		}

		/// <summary>
		///   Invoked before the execution of the next step is started on the model, i.e., before a set of initial
		///   states or successor states is computed.
		/// </summary>
		protected override void BeginExecution()
		{
			_cachedLabeledStates.Clear();
		}

		/// <summary>
		///   Invoked after the execution of a step is completed on the model, i.e., after a set of initial
		///   states or successor states have been computed.
		/// </summary>
		protected override TransitionCollection EndExecution()
		{
			_cachedLabeledStates.TransformContinuationIdsToDistributions(null);
			var transitions = _cachedLabeledStates.ToCollection();
			return transitions;
		}
	}
}