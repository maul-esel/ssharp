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

namespace SafetySharp.Modeling
{
	using System;
	using System.Collections.Generic;
	using System.Linq;
	using System.Diagnostics;
	using System.Runtime.Remoting.Messaging;
	using System.Threading;
	using System.Threading.Tasks;

    /// <summary>
	/// This class can be used to simulate parallel execution within a microstep.
	/// </summary>
	public static class MicrostepScheduler
	{
		private static readonly string _contextName = Guid.NewGuid().ToString();
		private static SingleThreadSynchronizationContext Context
			=> GetTaskData<SingleThreadSynchronizationContext>(_contextName);

		private static readonly string _tasksName = Guid.NewGuid().ToString();
		private static List<Task> Tasks => GetTaskData<List<Task>>(_tasksName);

		// TODO: in .NET 4.6, this can be replaced by AsyncLocal<T>
		private static T GetTaskData<T>(string name) where T : class, new()
		{
			var value = CallContext.LogicalGetData(name) as T;
			if (value == null)
				CallContext.LogicalSetData(name, value = new T());
			return value;
		}

		/// <summary>
		/// Schedules a callback for simulated asynchronous execution.
		/// </summary>
		/// <param name="action">The scheduled callback, which may use <c>await</c> statements.</param>
		public static void Schedule(Func<Task> action)
		{
			Context.Post(o =>
			{
			    var res = action();
                Debug.Assert(res != null);
                Tasks.Add(res);
            }, null);
		}

		/// <summary>
		/// Processes the scheduled callbacks.
		/// </summary>
		public static void CompleteSchedule()
		{
		    try
		    {
		        Context.Run();

		        // propagate exceptions
		        Task.WhenAll(Tasks.Where(task => task.IsFaulted)).GetAwaiter().GetResult();

		        // tasks should already be completed (faulted, cancelled, or successful) by now
		        if (!Tasks.All(task => task.IsCompleted))
		            throw new InvalidOperationException(
		                "Not all scheduled async tasks could be completed. This generally indicates a bug in the model.");
		    }
			finally
			{
				Tasks.Clear();
			}
		}

		private class SingleThreadSynchronizationContext : SynchronizationContext
		{
			private readonly Queue<Action> _queue = new Queue<Action>();

			public override void Post(SendOrPostCallback d, object state)
			{
				_queue.Enqueue(() => d(state));
			}

			public void Run()
			{
				var oldContext = Current;

				try
				{
					SetSynchronizationContext(this);
					while (_queue.Count > 0)
						_queue.Dequeue().Invoke();
				}
				finally
				{
					SetSynchronizationContext(oldContext);
				}
			}
		}
	}
}
