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

namespace ISSE.SafetyChecking.DiscreteTimeMarkovChain
{
	using System;
	using System.Diagnostics;
	using System.Runtime.CompilerServices;
	using AnalysisModel;
	using AnalysisModelTraverser;
	using ExecutableModel;
	using Utilities;



	//The LtmcBuilder is tightly coupled to LabeledTransitionMarkovChain, so we make it a nested class
	internal unsafe partial class LabeledTransitionMarkovChain
	{
		/// <summary>
		///   Builds up a <see cref="LabeledTransitionMarkovChain" /> instance during model traversal.
		///   Note: This only works single threaded
		/// </summary>
		internal class LtmcBuilder<TExecutableModel> : IBatchedTransitionAction<TExecutableModel>
			where TExecutableModel : ExecutableModel<TExecutableModel>
		{
			private readonly LabeledTransitionMarkovChain _markovChain;

			/// <summary>
			///   Initializes a new instance.
			/// </summary>
			/// <param name="markovChain">The Markov chain that should be built up.</param>
			public LtmcBuilder(LabeledTransitionMarkovChain markovChain)
			{
				Requires.NotNull(markovChain, nameof(markovChain));
				_markovChain = markovChain;
			}

			[Conditional("DEBUG")]
			private void CheckIfTransitionsCanBeProcessed(int transitionCount)
			{
				Assert.That(transitionCount > 0, "Cannot add deadlock state.");

				// Need to reserve the memory for the transitions
				var upperBoundaryForTransitions = _markovChain._transitionChainElementCount + transitionCount;
				if (upperBoundaryForTransitions < 0)
					throw new OutOfMemoryException("Unable to store transitions. Try increasing the transition capacity.");
			}

			[Conditional("DEBUG")]
			private void CheckIfTransitionIsValid(LtmcTransition* transition)
			{
				Assert.That(TransitionFlags.IsValid(transition->Flags), "Attempted to add an invalid transition.");
			}

			[MethodImpl(MethodImplOptions.AggressiveInlining)]
			private int GetStartPositionOfTransitionChain(int sourceState,bool areInitialTransitions)
			{
				if (areInitialTransitions)
					return _markovChain._indexOfFirstInitialTransition;
				return _markovChain._stateStorageStateToFirstTransitionChainElementMemory[sourceState];
			}

			[MethodImpl(MethodImplOptions.AggressiveInlining)]
			private TransitionChainElement GetTransitionChainElement(int index)
			{
				return _markovChain._transitionChainElementsMemory[index];
			}

			[MethodImpl(MethodImplOptions.AggressiveInlining)]
			private void CreateNewTransitionChainStartWithTransition(int sourceState, bool areInitialTransitions, LtmcTransition* transition)
			{
				var locationOfNewEntry = _markovChain.GetPlaceForNewTransitionChainElement();

				if (areInitialTransitions)
				{
					_markovChain._indexOfFirstInitialTransition = locationOfNewEntry;
				}
				else
				{
					_markovChain.SourceStates.Add(sourceState);
					_markovChain._stateStorageStateToFirstTransitionChainElementMemory[sourceState] = locationOfNewEntry;
				}

				_markovChain._transitionChainElementsMemory[locationOfNewEntry] =
					new TransitionChainElement
					{
						Formulas = transition->Formulas,
						NextElementIndex = -1,
						Probability = transition->Probability,
						TargetState = transition->GetTargetStateIndex()
					};
			}


			[MethodImpl(MethodImplOptions.AggressiveInlining)]
			private void AddTransitionToExistingTransitionChain(int startPositionOfTransitionChain, LtmcTransition* transition)
			{
				// Search for place to append is linear in number of existing transitions of state => O(n^2) 
				var currentTransitionElementIndex = startPositionOfTransitionChain;

				// merge or append
				while (true)
				{
					var currentElement = GetTransitionChainElement(currentTransitionElementIndex);
					if (currentElement.TargetState == transition->GetTargetStateIndex() && currentElement.Formulas == transition->Formulas)
					{
						//Case 1: Merge
						_markovChain._transitionChainElementsMemory[currentTransitionElementIndex].Probability =
							transition->Probability + currentElement.Probability;
						return;
					}
					if (currentElement.NextElementIndex == -1)
					{
						//Case 2: Append
						var locationOfNewEntry = _markovChain.GetPlaceForNewTransitionChainElement();
						_markovChain._transitionChainElementsMemory[currentTransitionElementIndex].NextElementIndex =
							locationOfNewEntry;
						_markovChain._transitionChainElementsMemory[locationOfNewEntry] =
							new TransitionChainElement
							{
								Formulas = transition->Formulas,
								NextElementIndex = -1,
								Probability = transition->Probability,
								TargetState = transition->GetTargetStateIndex()
							};
						return;
					}
					//else continue iteration
					currentTransitionElementIndex = currentElement.NextElementIndex;
				}
			}

			[MethodImpl(MethodImplOptions.AggressiveInlining)]
			private void AddTransitionToTransitionChain(int sourceState, bool areInitialTransitions, LtmcTransition* probTransition)
			{
				var startPositionOfTransitionChain = GetStartPositionOfTransitionChain(sourceState, areInitialTransitions);

				// startPositionOfTransitionChain == -1 indicates that no transition chain for state exists
				if (startPositionOfTransitionChain == -1)
				{
					CreateNewTransitionChainStartWithTransition(sourceState, areInitialTransitions, probTransition);
				}
				else
				{
					AddTransitionToExistingTransitionChain(startPositionOfTransitionChain, probTransition);
				}
			}

			/// <summary>
			///   Processes the new <paramref name="transitions" /> discovered by the <paramref name="worker " /> within the traversal
			///   <paramref name="context" />. Only transitions with <see cref="CandidateTransition.IsValid" /> set to <c>true</c> are
			///   actually new.
			/// </summary>
			/// <param name="context">The context of the model traversal.</param>
			/// <param name="worker">The worker that found the transition.</param>
			/// <param name="sourceState">The index of the transition's source state.</param>
			/// <param name="transitions">The new transitions that should be processed.</param>
			/// <param name="transitionCount">The actual number of valid transitions.</param>
			/// <param name="areInitialTransitions">
			///   Indicates whether the transitions are an initial transitions not starting in any valid source state.
			/// </param>
			public void ProcessTransitions(TraversalContext<TExecutableModel> context, Worker<TExecutableModel> worker, int sourceState,
										   TransitionCollection transitions, int transitionCount, bool areInitialTransitions)
			{
				// Note, other threads might access _markovChain at the same time
				CheckIfTransitionsCanBeProcessed(transitionCount);
				foreach (var transition in transitions)
				{
					var probTransition = (LtmcTransition*)transition;

					CheckIfTransitionIsValid(probTransition);

					AddTransitionToTransitionChain(sourceState, areInitialTransitions, probTransition);
				}
			}
		}
	}
}