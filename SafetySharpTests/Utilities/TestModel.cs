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

namespace Tests.Utilities
{
	using System;
	using System.Linq;
	using SafetySharp.Analysis;
	using SafetySharp.Modeling;
	using SafetySharp.Runtime;
	using ISSE.SafetyChecking.Formula;
	using ISSE.SafetyChecking.Utilities;
	/// <summary>
	///   Represents a base class for testable runtime models that are compiled and instantiated dynamically during test execution.
	/// </summary>
	internal abstract class TestModel : TestObject, IDisposable
	{
		/// <summary>
		///   Gets the instantiated runtime model.
		/// </summary>
		protected SafetySharpRuntimeModel RuntimeModel { get; private set; }

		/// <summary>
		///   Gets the model's root components once it has been instantiated.
		/// </summary>
		protected Component[] RootComponents => RuntimeModel.RootComponents;

		/// <summary>
		///   Gets the state formulas the model was instantiated with.
		/// </summary>
		protected ExecutableStateFormula[] ExecutableStateFormulas => RuntimeModel.ExecutableStateFormulas;

		/// <summary>
		///   Gets the formulas the model was instantiated with.
		/// </summary>
		protected Formula[] Formulas => RuntimeModel.Formulas;

		/// <summary>
		///   Gets the number of state slots required to serialize the model's state.
		/// </summary>
		protected int StateSlotCount => RuntimeModel.StateVectorSize / sizeof(int);

		/// <summary>
		///   Gets the the size of the model's state vector in bytes.
		/// </summary>
		protected int StateVectorSize => RuntimeModel.StateVectorSize;

		/// <summary>
		///   Performs application-defined tasks associated with freeing, releasing, or resetting unmanaged resources.
		/// </summary>
		public void Dispose()
		{
			RuntimeModel.SafeDispose();
		}

		/// <summary>
		///   Instantiates a runtime model.
		/// </summary>
		/// <param name="model">The model that should be instantiated.</param>
		/// <param name="formulas">The formulas the runtime model should be instantiated with.</param>
		protected void Create(ModelBase model, params Formula[] formulas)
		{
			RuntimeModel = SafetySharpRuntimeModel.Create(model, formulas);
		}

		/// <summary>
		///   Instantiates a runtime model.
		/// </summary>
		/// <param name="components">The root components of the model that should be instantiated.</param>
		protected void Create(params IComponent[] components)
		{
			Create(InitializeModel(components));
		}

		/// <summary>
		///   Instantiates a runtime model.
		/// </summary>
		/// <param name="components">The root components of the model that should be instantiated.</param>
		internal static ModelBase InitializeModel(params IComponent[] components)
		{
			var model = new Model { Roots = components };
			ModelBinder.Bind(model);

			return model;
		}

		/// <summary>
		///   Helper class to construct models with explicit root components.
		/// </summary>
		private class Model : ModelBase
		{
		}
	}
	
	public static class EmptyTestModelFactory
	{
		private const string EmptyTestModel = @"
namespace Tests.Utilities.EmptyModel
{
	using SafetySharp.Analysis;
	using SafetySharp.Runtime;
	using SafetySharp.Modeling;
	
	public class EmptyComponent : Component
	{
	}

	public class EmptyModel : ModelBase
	{
		[Root(RootKind.Controller)]
		public readonly EmptyComponent X = new EmptyComponent();
	}
}
";
		public static ModelBase CreateEmptyModel(TestTraceOutput output)
		{
			return Tests.GetModelBases(EmptyTestModel, output).First();
		}

		public static SafetySharpRuntimeModel CreateRuntimeModel(TestTraceOutput output)
		{
			return SafetySharpRuntimeModel.Create(CreateEmptyModel(output));
		}
	}
}