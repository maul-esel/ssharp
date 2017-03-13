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

namespace SafetySharp.CaseStudies.RobotCell
{
	using System;
	using System.Collections.Generic;
	using System.Linq;
	using ISSE.SafetyChecking.AnalysisModel;
	using ISSE.SafetyChecking.MinimalCriticalSetAnalysis;
	using ISSE.SafetyChecking.Modeling;

	using Modeling.Controllers;

	class MonitoringHeuristic : IFaultSetHeuristic
	{
		private FaultSet _deactivatedFaults = default(FaultSet);

		private readonly Fault[] _allFaults;
		private readonly FaultSet _allFaultsSet;
		private readonly Func<Agent, Role, IEnumerable<Fault>> _getCriticalFaults;

		public MonitoringHeuristic(Fault[] allFaults, Func<Agent, Role, IEnumerable<Fault>> getCriticalFaults)
		{
			_allFaults = allFaults;
			_allFaultsSet = new FaultSet(allFaults);
			_getCriticalFaults = getCriticalFaults;
		}

		public void ReportReconfiguration(Agent[] affectedAgents)
		{
			foreach (var agent in affectedAgents)
			{
				if (agent.AllocatedRoles.Count == 0)
					continue;

				lock (this)
				{
					_deactivatedFaults = new FaultSet(
						agent.AllocatedRoles.SelectMany(role => _getCriticalFaults(agent, role))
					).GetUnion(_deactivatedFaults);
				}
			}
		}

		private int counter = 0;

		public void Augment(uint cardinalityLevel, LinkedList<FaultSet> setsToCheck)
		{
			Console.WriteLine($"MonitoringHeuristic made {counter} suggestions.");
			counter = 0;
			_deactivatedFaults = default(FaultSet);
		}

		public void Update(LinkedList<FaultSet> setsToCheck, FaultSet checkedSet, bool isSafe)
		{
			if (isSafe)
			{
				var suggestion = _allFaultsSet.GetDifference(FaultSet.SubsumingFaults(_deactivatedFaults, _allFaults));
				if (suggestion != checkedSet)
				{
					setsToCheck.AddFirst(suggestion);
					counter++;
				}
			}
			_deactivatedFaults = default(FaultSet);
		}
	}
}
