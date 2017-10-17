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

namespace SafetySharp.Odp.Reconfiguration.CoalitionFormation
{
	using System.Collections.Generic;
	using System.Linq;
	using System.Threading.Tasks;

	class MissingCapabilitiesStrategy : IRecruitingStrategy
	{
		private MissingCapabilitiesStrategy() { }

		public static MissingCapabilitiesStrategy Instance { get; } = new MissingCapabilitiesStrategy();

		public async Task<TaskFragment> RecruitNecessaryAgents(Coalition coalition)
		{
			var availableCapabilities = new HashSet<ICapability>(
				coalition.Members.SelectMany(member => member.BaseAgentState.AvailableCapabilities)
			);

			foreach (var agent in new AgentQueue(coalition))
			{
				if (availableCapabilities.IsSupersetOf(coalition.CTF.Capabilities))
					break;

				var newMember = await coalition.Invite(agent);
				availableCapabilities.UnionWith(newMember.BaseAgentState.AvailableCapabilities);
			}

			// return empty fragment - positions where capability allocations change are included anyway
			return TaskFragment.Identity(coalition.Task);
		}
	}
}
