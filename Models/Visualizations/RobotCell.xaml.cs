// The MIT License (MIT)
// 
// Copyright (c) 2014-2016, Institute for Software & Systems Engineering
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

namespace SafetySharp.CaseStudies.Visualizations
{
	using System;
	using System.Collections.Generic;
	using System.Linq;
	using System.Windows;
	using System.Windows.Controls;
	using CaseStudies.RobotCell.Analysis;
	using CaseStudies.RobotCell.Modeling;
	using CaseStudies.RobotCell.Modeling.Controllers;
	using Odp;
	using FastController = CaseStudies.RobotCell.Modeling.Controllers.FastController;

	public partial class RobotCell
	{
		private Model _model;

		private readonly Dictionary<uint, RobotControl> _robots = new Dictionary<uint, RobotControl>();
		private readonly Dictionary<uint, CartControl> _carts = new Dictionary<uint, CartControl>();
		private readonly Dictionary<uint, WorkpieceControl> _workpieces = new Dictionary<uint, WorkpieceControl>();

		public RobotCell()
		{
			InitializeComponent();
			SimulationControls.ModelStateChanged += (o, e) => UpdateModelState();
			SimulationControls.Reset += (o, e) => OnModelStateReset();

			Model = SampleModels.Ictss6<FastController>(AnalysisMode.AllFaults);

			SimulationControls.MaxSpeed = 64;
			SimulationControls.ChangeSpeed(1);
		}
		
		public Model Model
		{
			get { return _model; }
			set
			{
				_model = value;
				InitializeVisualization();
				SimulationControls.SetModel(value);
			}
		}

		private void InitializeVisualization()
		{
			var robotCount = _model.RobotAgents.Count;

			// create grid large enough for robots, carts between
			double widthToHeightRatio = 2;
			var gridHeight = Math.Max((int)Math.Ceiling(Math.Sqrt(robotCount / widthToHeightRatio)), 1);
			var gridWidth = (int)(widthToHeightRatio * gridHeight);

			visualizationArea.RowDefinitions.Clear();
			visualizationArea.ColumnDefinitions.Clear();
			for (int i = 0; i < gridHeight; ++i)
			{
				CreateRow(1);
				CreateRow(2);
				CreateRow(1);
			}
			for (int i = 0; i < gridWidth; ++i)
			{
				CreateColumn(1);
				CreateColumn(2);
				CreateColumn(1);
			}

			// create and place robots
			for (int i = 0; i < robotCount; ++i)
			{
				var robot = new RobotControl(_model.RobotAgents[i]);
				_robots.Add(_model.RobotAgents[i].ID, robot);
				visualizationArea.Children.Add(robot);

				var row = 3 * (i / gridWidth) + 1;
				var col = 3 * (i % gridWidth) + 1;

				Grid.SetRow(robot, row);
				Grid.SetColumn(robot, col);
			}

			// create and place carts
			for (int i = 0; i < _model.CartAgents.Count; ++i)
			{
				var agent = _model.CartAgents[i];
				var ctrl = new CartControl(agent, this);
				_carts.Add(agent.ID, ctrl);
				visualizationArea.Children.Add(ctrl);

				var robot = _model.RobotAgents.First(r => agent.Cart.IsPositionedAt(r.Robot));
				int row, col;
				GetFreePosition(robot, out row, out col);

				Grid.SetRow(ctrl, row);
				Grid.SetColumn(ctrl, col);
			}

			// display tasks
		}

		private void CreateRow(double height)
		{
			var row = new RowDefinition() { Height = new GridLength(height, GridUnitType.Star) };
			visualizationArea.RowDefinitions.Add(row);
		}

		private void CreateColumn(double width)
		{
			var col = new ColumnDefinition() { Width = new GridLength(width, GridUnitType.Star) };
			visualizationArea.ColumnDefinitions.Add(col);
		}

		internal void GetFreePosition(RobotAgent robot, out int row, out int col)
		{
			var ctrl = _robots[robot.ID];
			var robotRow = Grid.GetRow(ctrl);
			var robotCol = Grid.GetColumn(ctrl);

			var pos = new[] { robotRow - 1, robotRow, robotRow + 1 }
				.Zip(new[] { robotCol - 1, robotCol, robotCol + 1 }, Tuple.Create)
				.First(coords => IsFreePosition(coords.Item1, coords.Item2));
			row = pos.Item1;
			col = pos.Item2;
		}

		private bool IsFreePosition(int row, int col)
		{
			return !visualizationArea.Children.Cast<UIElement>()
					.Any(ctrl => Grid.GetRow(ctrl) == row && Grid.GetColumn(ctrl) == col);
		}

		private void UpdateModelState()
		{
			// create / show workpiece controls for new workpieces
			// update each workpiece control

			foreach (var robot in _model.RobotAgents)
				_robots[robot.ID].Update(robot);
			foreach (var cart in _model.CartAgents)
				_carts[cart.ID].Update(cart);

			InvalidateArrange();
			InvalidateVisual();
			UpdateLayout();
			this.

			visualizationArea.InvalidateArrange();
			visualizationArea.UpdateLayout();
		}

		private void OnModelStateReset()
		{
			_model = (Model)SimulationControls.Model;
		}

		internal static string GetState(BaseAgent agent)
		{
			var agentType = typeof(BaseAgent);
			var machineField = agentType.GetField("_stateMachine", System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic);
			var machine = machineField.GetValue(agent);

			var machineType = machine.GetType();
			var stateField = machineType.GetProperty("State");
			return stateField.GetValue(machine).ToString();
		}
	}
}