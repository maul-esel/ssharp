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

namespace SafetySharp.CaseStudies.RailroadCrossing.Analysis
{
	using FluentAssertions;
	using ISSE.SafetyChecking.Modeling;
	using Modeling;
	using NUnit.Framework;
	using SafetySharp.Analysis;
	using SafetySharp.Modeling;

	class HazardProbabilityRangeTests
	{
		[Test]
		public void Calculate()
		{
			var model = new Model();
			model.Channel.MessageDropped.ProbabilityOfOccurrence = new Probability(0.0001);
			model.CrossingController.Motor.BarrierMotorStuck.ProbabilityOfOccurrence = new Probability(0.001);
			model.CrossingController.Sensor.BarrierSensorFailure.ProbabilityOfOccurrence = new Probability(0.00003);
			model.CrossingController.TrainSensor.ErroneousTrainDetection.ProbabilityOfOccurrence = new Probability(0.0002);
			model.TrainController.Brakes.BrakesFailure.ProbabilityOfOccurrence = new Probability(0.00002);
			model.TrainController.Odometer.OdometerPositionOffset.ProbabilityOfOccurrence = new Probability(0.02);
			model.TrainController.Odometer.OdometerSpeedOffset.ProbabilityOfOccurrence = new Probability(0.02);

			var result = SafetySharpModelChecker.CalculateProbabilityRangeToReachState(model, model.PossibleCollision);
			Console.Write($"Probability of hazard: {result}");
		}
	}
}
