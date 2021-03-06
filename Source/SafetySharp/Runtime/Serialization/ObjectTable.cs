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

namespace SafetySharp.Runtime.Serialization
{
	using System;
	using System.Collections;
	using System.Collections.Generic;
	using System.Linq;
	using System.Runtime.CompilerServices;
	using System.Runtime.Serialization;
	using ISSE.SafetyChecking.Utilities;
	using Modeling;
	using Utilities;

	/// <summary>
	///   Maps objects to unique identifiers and vice versa for serialization.
	/// </summary>
	internal sealed class 
		
		ObjectTable : IEnumerable<object>
	{
		/// <summary>
		///   Gets the objects contained in the table.
		/// </summary>
		private readonly object[] _objects;

		/// <summary>
		///   Maps each object to its corresponding identifier.
		/// </summary>
		private readonly Dictionary<object, ushort> _objectToIdentifier = new Dictionary<object, ushort>(ReferenceEqualityComparer<object>.Default);

		/// <summary>
		///   Initializes a new instance.
		/// </summary>
		/// <param name="objects">The objects that should be mapped by the table.</param>
		public ObjectTable(IEnumerable<object> objects)
		{
			Requires.NotNull(objects, nameof(objects));

			// We make sure that we store each object only once
			var objs = objects.Distinct(ReferenceEqualityComparer<object>.Default);

			// Index 0 always maps to null
			_objects = new object[] { null }.Concat(objs).ToArray();
			Requires.That(_objects.Length < UInt16.MaxValue, nameof(objects), $"At most {UInt16.MaxValue} unique objects are supported.");

			// Generate the object to identifier lookup table; unfortunately, we can't have null keys
			for (var i = 1; i < _objects.Length; ++i)
				_objectToIdentifier.Add(_objects[i], (ushort)i);

			// Assign the identifiers of all delegates to their metadata objects
			foreach (var metadata in _objects.OfType<DelegateMetadata>())
				metadata.ObjectIdentifier = GetObjectIdentifier(metadata.Delegate);
		}

		/// <summary>
		///   Gets the number of objects contained in the table.
		/// </summary>
		public int Count => _objects.Length - 1;

		/// <summary>
		///   Returns an enumerator that iterates through all objects contained in the table.
		/// </summary>
		public IEnumerator<object> GetEnumerator()
		{
			// Skip the null value at index 0, obviously
			return _objects.Skip(1).GetEnumerator();
		}

		/// <summary>
		///   Returns an enumerator that iterates through all objects contained in the table.
		/// </summary>
		IEnumerator IEnumerable.GetEnumerator()
		{
			return GetEnumerator();
		}

		/// <summary>
		///   Gets the object corresponding to the <paramref name="identifier" />.
		/// </summary>
		[MethodImpl(MethodImplOptions.AggressiveInlining)]
		public object GetObject(ushort identifier)
		{
			return _objects[identifier];
		}

		/// <summary>
		///   Gets the identifier that has been assigned to <paramref name="obj" />.
		/// </summary>
		[MethodImpl(MethodImplOptions.AggressiveInlining)]
		public ushort GetObjectIdentifier(object obj)
		{
			// Since the map does not support null keys, we have to add a special case for a null object here...
			if (obj == null)
				return 0;

			ushort identifier;
			if (_objectToIdentifier.TryGetValue(obj, out identifier))
				return identifier;

			throw new InvalidOperationException(
				$"Unknown object of type '{obj.GetType().FullName}'. Creating new objects during model executions " +
				"(i.e., simulations or model checking runs) is not supported. If you did not allocate a new object " +
				$"yourself, the object was most likely created by a collection type such as '{typeof(List<>).FullName}'. " +
				"Set the capacity of these collections to the maximum number of elements " +
				"they are supposed to hold in order to prevent them from allocating during model execution.");
		}

		/// <summary>
		///   Substitutes the components and fault effects with their corresponding runtime instances.
		/// </summary>
		public  void SubstituteRuntimeInstances()
		{
			foreach (var component in _objects.OfType<Component>().ToArray())
			{
				if (component.IsFaultEffect())
					continue;

				var runtimeType = component.GetRuntimeType();
				var runtimeObj = (Component)FormatterServices.GetUninitializedObject(runtimeType);

				Substitute(component, runtimeObj);
				foreach (var faultEffect in component.FaultEffects)
					Substitute(faultEffect, runtimeObj);
			}
		}

		/// <summary>
		///   Substitutes the <paramref name="original" /> object with the <paramref name="replacement" /> object.
		/// </summary>
		/// <param name="original">The original object that should be substituted.</param>
		/// <param name="replacement">The replacement object the original one should be substituted with.</param>
		public void Substitute(object original, object replacement)
		{
			Requires.NotNull(original, nameof(original));
			Requires.NotNull(replacement, nameof(replacement));
			Requires.That(original != replacement, "Cannot substitute and object with itself.");

			for (var i = 0; i < _objects.Length; ++i)
			{
				if (_objects[i] != original)
					continue;

				_objects[i] = replacement;
				break;
			}

			// It is possible that we substitute multiple objects with the same replacement object; in that case
			// we map all of them to the same identifier
			if (!_objectToIdentifier.ContainsKey(replacement))
				_objectToIdentifier.Add(replacement, _objectToIdentifier[original]);

			// We have to remove the original mapping in any case, though
			_objectToIdentifier.Remove(original);
		}

		/// <summary>
		///   Substitutes the dummy <see cref="Delegate" /> objects in the table with actual instances created from the
		///   <see cref="DelegateMetadata" /> instances.
		/// </summary>
		public void SubstituteDelegates()
		{
			foreach (var info in _objects.OfType<DelegateMetadata>())
			{
				var d = info.CreateDelegate();
				_objects[info.ObjectIdentifier] = d;
				_objectToIdentifier.Add(d, info.ObjectIdentifier);
			}
		}
	}
}