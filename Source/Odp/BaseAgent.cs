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
	using System;
	using System.Collections.Generic;
	using System.Linq;
	using System.Threading.Tasks;
	using Modeling;

	public abstract partial class BaseAgent : Component, IAgent
	{
		// configuration options
		public static int MaximumAgentCount = 20;
		public static int MaximumResourceCount = 20;
		public static int MaximumRoleCount = 40;

		private static uint _maxId;
		public uint Id { get; }

		public abstract IEnumerable<ICapability> AvailableCapabilities { get; }

		private readonly List<Role> _allocatedRoles = new List<Role>(MaximumRoleCount);

		public IEnumerable<Role> AllocatedRoles => _allocatedRoles;

		[Hidden]
		public IRoleSelector RoleSelector { get; protected set; }

		protected BaseAgent()
		{
			Id = _maxId++;
			RoleSelector = new FairRoleSelector(this);
			RoleExecutor = new RoleExecutor(this);
		}

		public override void Update()
		{
			MicrostepScheduler.Schedule(UpdateAsync);
		}

		protected virtual async Task UpdateAsync()
		{
			await Observe();
			Work();
		}

		#region functional part

		public RoleExecutor RoleExecutor { get; }

		public Resource Resource { get; protected set; }

		private readonly StateMachine<States> _stateMachine = States.Idle;

		private enum States
		{
			Idle,
			ChooseRole,
			WaitingForResource,
			ExecuteRole,
			Output,
			ResourceGiven
		}

		private void Work()
		{
			_stateMachine.Transition( // abort work if current task has configuration issues
				from: new[] { States.ChooseRole, States.WaitingForResource, States.ExecuteRole, States.Output, States.ResourceGiven },
				to: States.Idle,
				guard: RoleExecutor.IsExecuting && _deficientConfiguration,
				action: () =>
				{
					if (Resource != null)
						DropResource();
					RoleExecutor.EndExecution();
					_deficientConfiguration = false;
				});

			_stateMachine
				.Transition( // see if there is work to do
					from: States.Idle,
					to: States.ChooseRole,
					action: ChooseRole)
				.Transition( // no work found (or deadlock avoidance or similar reasons)
					from: States.ChooseRole,
					to: States.Idle,
					guard: !RoleExecutor.IsExecuting)
				.Transition( // going to work on pre-existing resource (first transfer it)
					from: States.ChooseRole,
					to: States.WaitingForResource,
					guard: RoleExecutor.IsExecuting && RoleExecutor.Input != null,
					action: () => InitiateResourceTransfer(RoleExecutor.Input))
				.Transition( // going to produce new resource (no transfer necessary)
					from: States.ChooseRole,
					to: States.ExecuteRole,
					guard: RoleExecutor.IsExecuting && RoleExecutor.Input == null)
				.Transition( // actual work on resource
					from: States.ExecuteRole,
					to: States.ExecuteRole,
					guard: !RoleExecutor.IsCompleted,
					action: () => RoleExecutor.ExecuteStep())
				.Transition( // work is done -- pass resource on
					from: States.ExecuteRole,
					to: States.Output,
					guard: RoleExecutor.IsCompleted && RoleExecutor.Output != null,
					action: () => RoleExecutor.Output.ResourceReady(this, RoleExecutor.Role.Value.PostCondition))
				.Transition( // resource has been consumed
					from: States.ExecuteRole,
					to: States.Idle,
					guard: RoleExecutor.IsCompleted && Resource == null && RoleExecutor.Output == null,
					action: () => RoleExecutor.EndExecution());
		}

		protected virtual void DropResource()
		{
			Resource = null;
		}

		private void ChooseRole()
		{
			var role = RoleSelector.ChooseRole(_resourceRequests);
			if (!role.HasValue)
				return;

			RoleExecutor.BeginExecution(role.Value);
			_resourceRequests.RemoveAll(request => request.Source == role.Value.Input);
		}

		public virtual bool CanExecute(Role role)
		{
			// producer roles and roles with open resource requests can be executed, unless they're locked
			return !role.IsLocked
				   && (role.Input == null || _resourceRequests.Any(req => role.Equals(req.Role)));
		}

		private Role[] GetRoles(BaseAgent source, Condition condition)
		{
			return AllocatedRoles.Where(role =>
				!role.IsLocked && role.Input == source && role.PreCondition.StateMatches(condition)
			).ToArray();
		}

		#region resource flow

		private readonly List<BaseAgent> _inputs = new List<BaseAgent>(MaximumAgentCount);
		private readonly List<BaseAgent> _outputs = new List<BaseAgent>(MaximumAgentCount);

		public virtual IEnumerable<BaseAgent> Inputs => _inputs;
		public virtual IEnumerable<BaseAgent> Outputs => _outputs;

		public virtual void Connect(BaseAgent successor)
		{
			if (!_outputs.Contains(successor))
				_outputs.Add(successor);
			if (!successor._inputs.Contains(this))
				successor._inputs.Add(this);
		}

		public virtual void BidirectionallyConnect(BaseAgent neighbor)
		{
			Connect(neighbor);
			neighbor.Connect(this);
		}

		public virtual void Disconnect(BaseAgent successor)
		{
			_outputs.Remove(successor);
			successor._inputs.Remove(this);
		}

		public virtual void BidirectionallyDisconnect(BaseAgent neighbor)
		{
			Disconnect(neighbor);
			neighbor.Disconnect(this);
		}

		#endregion

		#region resource handshake

		private readonly List<ResourceRequest> _resourceRequests
			= new List<ResourceRequest>(MaximumResourceCount);

		public struct ResourceRequest
		{
			internal ResourceRequest(BaseAgent source, Role role)
			{
				Source = source;
				Role = role;
			}

			public BaseAgent Source { get; }
			public Role Role { get; }
		}

		protected virtual void InitiateResourceTransfer(BaseAgent source)
		{
			source.TransferResource();
		}

		private void ResourceReady(BaseAgent agent, Condition condition)
		{
			var roles = GetRoles(agent, condition);
			if (roles.Length == 0)
				throw new InvalidOperationException("no role found for resource request: invariant violated!");

			foreach (var role in roles)
			{
				_resourceRequests.Add(new ResourceRequest(agent, role));
			}
		}

		protected virtual void TransferResource()
		{
			_stateMachine.Transition(
				from: States.Output,
				to: States.ResourceGiven,
				action: () => RoleExecutor.Output.TakeResource(Resource)
			);
		}

		protected virtual void TakeResource(Resource resource)
		{
			// assert resource != null
			Resource = resource;

			_stateMachine.Transition(
				from: States.WaitingForResource,
				to: States.ExecuteRole,
				action: RoleExecutor.Input.ResourcePickedUp
			);
		}

		protected virtual void ResourcePickedUp()
		{
			Resource = null;

			_stateMachine.Transition(
				from: States.ResourceGiven,
				to: States.Idle,
				action: () => RoleExecutor.EndExecution()
			);
		}

		#endregion

		#endregion

		#region observer

		public virtual bool IsAlive => true;

		[Hidden]
		private bool _deficientConfiguration;

		[Hidden]
		public Reconfiguration.IReconfigurationStrategy ReconfigurationStrategy { get; set; }

		protected virtual InvariantPredicate[] MonitoringPredicates { get; } = {
			Invariant.IoConsistency,
			Invariant.NeighborsAliveGuarantee,
			Invariant.ResourceConsistency,
			Invariant.CapabilityConsistency
		};

		protected virtual InvariantPredicate[] ConsistencyPredicates { get; } = {
			Invariant.PrePostConditionConsistency,
			Invariant.TaskEquality,
			Invariant.StateConsistency
		};

		private async Task Observe()
		{
			var violations = FindInvariantViolations();

			await PerformReconfiguration(
				from vio in violations
				let state = new State(this, null, false, vio.Value.ToArray())
				select Tuple.Create(vio.Key, state)
			);
		}

		protected async Task PerformReconfiguration(IEnumerable<Tuple<ITask, State>> reconfigurations)
		{
            if (!reconfigurations.Any())
                return;

            // initiate reconfiguration to fix violations
            await ReconfigurationStrategy.Reconfigure(reconfigurations);
			// verify correctness of new configuration
			VerifyInvariants();
		}

        /// <summary>
        /// Prepares the agent for reconfiguration of some given <paramref name="task"/>.
        /// </summary>
	    public void PrepareReconfiguration(ITask task)
	    {
	        // stop work on deficient tasks
	        _resourceRequests.RemoveAll(request => request.Role.Task == task);
	        // abort execution of current role if necessary
	        _deficientConfiguration = RoleExecutor.IsExecuting && RoleExecutor.Task == task;
        }

		private void VerifyInvariants()
		{
			foreach (var predicate in MonitoringPredicates.Concat(ConsistencyPredicates))
				if (predicate(this).Any())
					throw new InvalidOperationException("New configuration violates invariant.");
		}

		private Dictionary<ITask, IEnumerable<InvariantPredicate>> FindInvariantViolations()
		{
			var violations = new Dictionary<ITask, IEnumerable<InvariantPredicate>>();
			foreach (var predicate in MonitoringPredicates)
			{
				foreach (var violatingTask in predicate(this))
				{
					if (!violations.ContainsKey(violatingTask))
						violations.Add(violatingTask, new HashSet<InvariantPredicate>());
					(violations[violatingTask] as HashSet<InvariantPredicate>).Add(predicate);
				}
			}
			return violations;
		}

		public virtual Task RequestReconfiguration(IAgent agent, ITask task)
		{
			return PerformReconfiguration(new[] {
				Tuple.Create(task, new State(this, agent))
			});
		}

		public virtual void AllocateRoles(IEnumerable<Role> roles)
		{
			_allocatedRoles.AddRange(roles);
			RoleSelector.OnRoleAllocationsChanged();
		}

		public virtual void RemoveAllocatedRoles(IEnumerable<Role> roles)
		{
			foreach (var role in roles.ToArray())
				_allocatedRoles.Remove(role);
			RoleSelector.OnRoleAllocationsChanged();
		}

		public void LockRoles(IEnumerable<Role> roles, bool locked = true)
		{
			var set = new HashSet<Role>(roles);
			for (var i = 0; i < _allocatedRoles.Count; ++i)
			{
				if (set.Contains(_allocatedRoles[i]))
					_allocatedRoles[i] = _allocatedRoles[i].Lock(locked);
			}
		}

		#endregion
    }
}