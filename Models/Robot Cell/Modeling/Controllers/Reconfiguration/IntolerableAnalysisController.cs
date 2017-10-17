﻿// The MIT License (MIT)
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

namespace SafetySharp.CaseStudies.RobotCell.Modeling.Controllers.Reconfiguration
{
	using System;
	using System.Threading.Tasks;
	using SafetySharp.Modeling;
	using Odp;
	using Odp.Reconfiguration;

	class IntolerableAnalysisController : Component, IController
	{
		public const int MaxSteps = 350;

		[Range(0, MaxSteps, OverflowBehavior.Clamp)]
		public int StepCount { get; private set; }

		private readonly IController _controller;

		private bool _reconfHasFailed;

		public IntolerableAnalysisController(IController controller)
		{
			_controller = controller;
		}

		public override void Update()
		{
			StepCount++;
		}

		public event Action<ITask, ConfigurationUpdate> ConfigurationsCalculated
		{
			add { _controller.ConfigurationsCalculated += value; }
			remove { _controller.ConfigurationsCalculated -= value; }
		}

		public BaseAgent[] Agents => _controller.Agents;
		public async Task<ConfigurationUpdate> CalculateConfigurationsAsync(object context, ITask task)
		{
			if (_reconfHasFailed)
				return null;

			if (StepCount >= MaxSteps)
				return null;

			var config = await _controller.CalculateConfigurationsAsync(context, task);
			_reconfHasFailed |= config.Failed;
			return config;
		}
	}
}
