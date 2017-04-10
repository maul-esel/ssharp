// The MIT License (MIT)
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

namespace ISSE.SafetyChecking.StateGraphModel
{
	using System;
	using System.Threading;
	using ExecutableModel;
	using AnalysisModel;
	using AnalysisModelTraverser;
	using Utilities;


	/// <summary>
	///   Represents the state graph of an <see cref="AnalysisModel" />.
	/// </summary>
	/// <remarks>
	///   Transitions are untyped as C# unfortunately does not support generic type arguments of pointer types.
	/// </remarks>

	internal sealed unsafe class StateGraph<TExecutableModel> : DisposableObject where TExecutableModel : ExecutableModel<TExecutableModel>
	{
		private readonly TransitionRange* _stateMap;
		private readonly MemoryBuffer _stateMapBuffer = new MemoryBuffer();
		private readonly StateStorage _stateStorage;
		private readonly long _transitionCapacity;
		private readonly byte* _transitions;
		private readonly MemoryBuffer _transitionsBuffer = new MemoryBuffer();
		private int _initialTransitionCount;
		private int _stateCount;
		private long _transitionCount;
		private long _transitionOffset;

		/// <summary>
		///   Initializes a new instance.
		/// </summary>
		/// <param name="context">The context of the traversal process.</param>
		/// <param name="transitionSizeInBytes">The size of a transition in bytes.</param>
		/// <param name="model">The runtime model the state graph is generated for.</param>
		/// <param name="createModel">
		///   The factory function that should be used to create instances of the <see cref="RuntimeModel" />
		///   the state graph is generated for.
		/// </param>
		internal StateGraph(TraversalContext<TExecutableModel> context, int transitionSizeInBytes,
							TExecutableModel model, CoupledExecutableModelCreator<TExecutableModel> createModel)
		{
			Requires.NotNull(context, nameof(context));
			
			TransitionSize = transitionSizeInBytes;
			RuntimeModel = model;
			RuntimeModelCreator = createModel;

			_stateStorage = context.States;
			_transitionCapacity = context.ModelCapacity.MemoryLimitTransitions.Value;

			_transitionsBuffer.Resize(_transitionCapacity, zeroMemory: false);
			_stateMapBuffer.Resize(context.ModelCapacity.NumberOfStates * sizeof(TransitionRange), zeroMemory: false);

			_transitions = _transitionsBuffer.Pointer;
			_stateMap = (TransitionRange*)_stateMapBuffer.Pointer;
		}

		/// <summary>
		///   Gets the runtime model that is directly or indirectly represented by this <see cref="StateGraph" />.
		/// </summary>
		public TExecutableModel RuntimeModel { get; }

		/// <summary>
		///   Gets the factory function that was used to create the runtime model that is directly or indirectly represented by this
		///   <see cref="StateGraph" />.
		/// </summary>
		public CoupledExecutableModelCreator<TExecutableModel> RuntimeModelCreator { get; }

		/// <summary>
		///   Gets the size of a single transition of the state graph in bytes.
		/// </summary>
		public int TransitionSize { get; }

		/// <summary>
		///   Gets the number of states contained in the state graph.
		/// </summary>
		public int StateCount => _stateCount;

		/// <summary>
		///   Gets the number of transitions contained in the state graph.
		/// </summary>
		public long TransitionCount => _transitionCount;

		/// <summary>
		///   Gets the number of initial transitions contained in the state graph.
		/// </summary>
		public long InitialTransitionCount => _initialTransitionCount;

		/// <summary>
		///   Adds the <paramref name="state" /> and all of its <see cref="transitions" /> to the state graph.
		/// </summary>
		/// <param name="state">The state that should be added.</param>
		/// <param name="isInitial">Indicates whether the state is an initial state.</param>
		/// <param name="transitions">The transitions leaving the state.</param>
		/// <param name="transitionCount">The number of valid transitions leaving the state.</param>
		internal void AddStateInfo(int state, bool isInitial, TransitionCollection transitions, int transitionCount)
		{
			Assert.That(!isInitial || _initialTransitionCount == 0, "Initial transitions can only be added once.");

			if (isInitial)
				_initialTransitionCount = transitionCount;
			else
				Interlocked.Increment(ref _stateCount);

			Interlocked.Add(ref _transitionCount, transitionCount);

			// Transitions are synchronized by atomatically incrementing the offset counter
			var offset = InterlockedExtensions.AddFetch(ref _transitionOffset, transitionCount);
			if (offset + transitionCount > _transitionCapacity)
				throw new OutOfMemoryException("Unable to store transitions. Try increasing the transition capacity.");

			// No need to synchronize state addition, as all states are only discovered once
			if (!isInitial)
				_stateMap[state] = new TransitionRange { StartIndex = offset, Count = transitionCount };

			// Copy the transitions into the buffer
			foreach (var transition in transitions)
			{
				Assert.That( TransitionFlags.IsValid(transition->Flags) , "Attempted to add an invalid transition.");

				MemoryBuffer.Copy((byte*)transition, _transitions + offset * TransitionSize, TransitionSize);
				++offset;
			}
		}

		/// <summary>
		///   Gets all initial transitions without any source state.
		/// </summary>
		internal TransitionCollection GetInitialTransitions()
		{
			return new TransitionCollection((Transition*)_transitions, _initialTransitionCount, TransitionSize);
		}

		/// <summary>
		///   Gets all transitions leaving the <paramref name="state" />.
		/// </summary>
		/// <param name="state">The state whose outgoing transitions should be returned.</param>
		internal TransitionCollection GetTransitions(int state)
		{
			var transitions = (Transition*)(_transitions + TransitionSize * _stateMap[state].StartIndex);
			return new TransitionCollection(transitions, _stateMap[state].Count, TransitionSize);
		}

		/// <summary>
		///   Gets the state of the model the state graph was generated from that corresponds to state graph <paramref name="state" />.
		/// </summary>
		/// <param name="state">The state the original state should be returned for.</param>
		internal byte* GetState(int state)
		{
			return _stateStorage[state];
		}

		/// <summary>
		///   Disposes the object, releasing all managed and unmanaged resources.
		/// </summary>
		/// <param name="disposing">If true, indicates that the object is disposed; otherwise, the object is finalized.</param>
		protected override void OnDisposing(bool disposing)
		{
			_stateStorage.SafeDispose();
			_transitionsBuffer.SafeDispose();
			_stateMapBuffer.SafeDispose();
		}
	}

	/// <summary>
	///   Represents a range within the <see cref="_transitions" /> buffer.
	/// </summary>
	internal struct TransitionRange
	{
		public long StartIndex;
		public int Count;
	}
}