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

namespace SafetySharp.Odp
{
    using System.Linq;

	public partial class BaseAgent
	{
		public class State
		{
			public State(BaseAgent agent, IAgent requestSource = null, bool initialConf = false, params InvariantPredicate[] violatedPredicates)
			{
				ReconfRequestSource = requestSource;
				ViolatedPredicates = violatedPredicates;
			    IsInitialConfiguration = initialConf;

				Id = agent.Id;
				Resource = agent.Resource;
				Inputs = agent.Inputs.ToArray();
				Outputs = agent.Outputs.ToArray();
				AllocatedRoles = agent.AllocatedRoles.ToArray();
				AvailableCapabilities = agent.AvailableCapabilities.ToArray();
			}

			public IAgent ReconfRequestSource { get; }
			public InvariantPredicate[] ViolatedPredicates { get; }
            public bool IsInitialConfiguration { get; }

			public uint Id { get; }
			public Resource Resource { get; }
			public BaseAgent[] Inputs { get; }
			public BaseAgent[] Outputs { get; }
			public Role[] AllocatedRoles { get; }
			public ICapability[] AvailableCapabilities { get; }
		}
	}
}