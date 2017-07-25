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

namespace SafetySharp.Odp
{
	using System.Collections.Generic;
	using System.Linq;

	public class SimpleCentralizedDeadlockAvoidance : IDeadlockAvoidanceStrategy
	{
		private SimpleCentralizedDeadlockAvoidance() { }
		public static SimpleCentralizedDeadlockAvoidance Instance { get; } = new SimpleCentralizedDeadlockAvoidance();

		public IEnumerable<BaseAgent.ResourceRequest> Filter(BaseAgent agent, IEnumerable<BaseAgent.ResourceRequest> requests)
		{
			return requests.Where(req => !IsWaitingFor(agent, req.Source));
		}

		private bool IsWaitingFor(BaseAgent waitingAgent, BaseAgent waitTarget)
		{
			while (waitingAgent != waitTarget)
			{
				// if agent has no active role, it is not waiting on anyone
				if (waitingAgent.CurrentRole == null)
					return false;

				// Indirect waiting: agent is waiting for PostCondition.Port, which might wait for waitTarget
				waitingAgent = waitingAgent.CurrentRole.Value.PostCondition.Port;
			}

			return true; // there is a chain of waiting agents from source to waitTarget
		}

		public void UpdateChosenRole(BaseAgent agent, Role role)
		{
		}
	}
}
