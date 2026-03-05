/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Combinatorics.Digraph.Basic

/-!
# Challenge file for Comparator verification

This file states the definitions and main theorem from the "Claude's Cycles" formalization.
It is intended to be audited by a human to confirm that the definitions match the mathematical
objects described in Knuth's note, and that the theorem statement captures the intended claim.

The `Solution` module provides the proof, verified by Comparator.

## What to audit

1. `Vertex m` is (ZMod m)³.
2. `bumpAt b v` adds 1 to coordinate b of v.
3. `cubeDigraph m` has an arc from u to v iff v = bumpAt b u for some b ∈ Fin 3.
4. `IsDirectedHamiltonianCycle G σ` means σ follows arcs, is a single cycle, and visits all vertices.
5. The theorem states that for odd m > 1, the arcs of the cube digraph can be decomposed
   into three directed Hamiltonian cycles.
-/

open Finset

/-- The vertex type: triples in (ZMod m)³. -/
abbrev Vertex (m : ℕ) := ZMod m × ZMod m × ZMod m

/-- Bump coordinate `b` of vertex `v`: add 1 to the b-th component. -/
def bumpAt {m : ℕ} [NeZero m] (b : Fin 3) (v : Vertex m) : Vertex m :=
  match b with
  | 0 => (v.1 + 1, v.2.1, v.2.2)
  | 1 => (v.1, v.2.1 + 1, v.2.2)
  | 2 => (v.1, v.2.1, v.2.2 + 1)

/-- The cube digraph: vertices are (ZMod m)³, with an arc from u to v when v is obtained
from u by bumping one coordinate. -/
def cubeDigraph (m : ℕ) [NeZero m] : Digraph (Vertex m) where
  Adj u v := ∃ b : Fin 3, bumpAt b u = v

/-- A permutation σ on vertices of a digraph G is a directed Hamiltonian cycle if:
1. Every arc (v, σ v) is an edge of G
2. σ is a single cycle
3. σ moves every vertex (the cycle visits all vertices) -/
def IsDirectedHamiltonianCycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) (σ : Equiv.Perm V) : Prop :=
  (∀ v, G.Adj v (σ v)) ∧ σ.IsCycle ∧ σ.support = Finset.univ

/-! ## Main theorem -/

namespace ClaudesCycles

/-- **Headline theorem.** For odd m > 1, the arcs of the cube digraph on (ZMod m)³ can be
decomposed into three directed Hamiltonian cycles. -/
theorem hamiltonian_arc_decomposition
    {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m) :
    ∃ σ : Fin 3 → Equiv.Perm (Vertex m),
      (∀ c, IsDirectedHamiltonianCycle (cubeDigraph m) (σ c)) ∧
      (∀ v : Vertex m, ∀ b : Fin 3, ∃! c : Fin 3, σ c v = bumpAt b v) := by
  sorry

end ClaudesCycles
