# Exact external facts and why their signatures are sound

The internal proof retains three frozen principle signatures.  The first is
now kernel-proved; only the Hansen and quantitative ACC principles remain
external.  This explicit split prevents a convenient but too-strong black box
from silently absorbing the theorem being proved.

## Principle 1: zero minimum rotation genus is attained (proved internally)

Lean name:

```lean
RotationZeroPlanarityPrinciple
```

Exact content:

```text
for every finite ADR circuit C,
orientableCircuitGenus(C) = 0
implies that some orientable rotation r of C has rotationGenus(r) = 0.
```

Despite the historical word “planarity” in the Lean principle's name, this is
only the finite attainment step hidden by the `Nat.sInf` definition.  The
set of rotations is nonempty (choose a cyclic permutation independently at
each vertex), and it is finite, so the infimum is a minimum.  The conclusion
is a zero-genus rotation certificate.  It does not separately construct an
ordinary topological embedding, assert an ACC simulation, or contain a width
or complexity hypothesis.

## Fact 2: Hansen's incidence-order certificate

Lean name:

```lean
HansenArcOrderPrinciple
```

Exact content: a properly layered circuit graph that has a zero-genus rotation
and unique graph source and sink has an `IncidenceCylinder`.

The certificate is the correct finite form of geometric cylindricality, but it is
not equivalent to the all-pairs vertex predicate printed in HMV when two arcs
share an endpoint.  We therefore do not infer it from, or feed it into, that
printed predicate.  At each layer it stores a cyclic listing of vertices.  At each
transition it lists every arc in one block for its tail and in one block for
its head.  Flattening the tail blocks and head blocks gives the same cyclic
arc word.  This is exactly the common outgoing/incoming arc order constructed
inside Hansen's proof of Theorem 2.

This principle intentionally packages two literature steps: realization of a
zero-genus rotation as a plane embedding, and Hansen's extraction of the
common arc order.  Why the hypotheses suffice:

- proper layering makes the finite digraph acyclic;
- in a finite acyclic graph, unique source and sink force every vertex to lie
  on a source-to-sink path;
- a zero-genus rotation is a combinatorial plane embedding; its standard
  realization, followed by Hansen's st-layered argument, yields the common arc
  order.

The second principle returns only finite incidence data.  It does not perform
fanin reduction, compute Boolean values, or construct an ACC circuit.

## Fact 3: quantitative cylindrical circuits are in ACC

Lean name:

```lean
QuantitativeCylindricalACCPrinciple
```

The quantifier order is deliberately:

```text
for every fixed total width W,
there exist one modulus M, depth d, and exponent e,
such that for every input count n and every circuit C of width W,
an equivalent ACC[M] circuit exists with depth d and size (|C|+1)^e.
```

The circuit must already satisfy all three nontrivial premises:

- `HMVNormal`: well formed and computation fanin at most two;
- `TotalWidthAtMost C W`: every node, including intermediate input ports,
  counts toward the fixed width;
- `Nonempty (IncidenceCylinder C)`: the strong common arc-order certificate.

Thus this principle cannot be applied to the source circuits in OQ3.  The
internal proof still has to planarize by layers, isolate planar blocks, perform
the Hansen width induction, construct and refine beta ports, and compose a
polylogarithmic number of constant-state relations.

This external principle packages the geometric/incidence-order extension of
Hansen's cylindrical ACC theorem, the HMV reduction to the word problem of one
fixed finite solvable monoid, and the Barrington--Therien ACC upper bound.  It
should not be described as a literal application of HMV's printed predicate.
A separate optional project may eventually prove this principle internally
from the solvable-monoid word theorem; that transfer does not block OQ3.  A finite set of
fixed moduli can be consolidated to one fixed modulus.  The coefficient in a
polynomial size bound is absorbed by increasing `e`: every ADR circuit has at
least one gate because it contains `output : Fin gateCount`, so
`gateCount + 1 >= 2`.

The auxiliary words COPY/true/false used in the paper proof do not enlarge the
frozen gate syntax: COPY is a unary OR gate, true a nullary AND gate, and false
a nullary OR gate.  Thus `HMVNormal` is stated entirely for `ADRCircuit`.

## Boundary audit

The signatures explicitly avoid the recurrent errors in earlier sketches:

- `ADRHasWidthAtMost` and `TotalWidthAtMost` are not conflated;
- unbounded literal fanin is not handed to HMV;
- the arc-incidence word, not the insufficient vertex predicate, is required;
- the modulus, depth, and exponent precede all varying circuits;
- the output computes exact acceptance, not merely one modular representation;
- the principles are nonuniform, matching the corrected OQ3 target;
- no principle mentions polylogarithmic genus, exceptional layers, or the
  language family conclusion.

Primary sources:

- Hansen, *On the Complexity of Planar Boolean Circuits*, ECCC TR03-025,
  especially Theorem 2 and Corollary 9;
- Hansen--Miltersen--Vinay, *Circuits on Cylinders*, ECCC TR02-066,
  especially the fixed monoid construction and Propositions 8 and 13;
- Barrington--Therien, the characterization of fixed solvable-monoid word
  problems by `ACC^0`.
