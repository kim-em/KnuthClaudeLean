/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Combinatorics.Digraph.Basic

/-!
# Claude's Cycles

Formalization of the results in Don Knuth's note "Claude's Cycles" (February–March 2026).

The note describes a construction, found by Claude Opus 4.6, that decomposes the arcs of a
certain digraph into three directed Hamiltonian cycles for all odd m > 1.

## The digraph

The digraph has m³ vertices (i, j, k) for 0 ≤ i, j, k < m, with three arcs from each vertex:
to (i+1, j, k), (i, j+1, k), and (i, j, k+1), where arithmetic is mod m.

## The construction

Claude's direction function assigns to each vertex a permutation of {0, 1, 2} (the three arc
directions), depending on the fiber index s = (i+j+k) mod m and on whether i, j are 0 or m−1.
The step function for cycle c bumps the coordinate specified by this permutation applied to c.

## Main results

- `claudeDir_perm`: the direction function is a permutation at each vertex
- `claudeStep_isDirectedHamiltonianCycle`: each cycle is a directed Hamiltonian cycle (odd m > 1)
- `claude_arc_decomposition`: the three cycles partition all arcs
- `no_decomposition_two`: no such decomposition exists for m = 2
- Various counting results for m = 3
- The generalizability theorem
-/

open Finset

/-! ## Basic definitions -/

/-- The vertex type: triples in (ZMod m)³. -/
abbrev Vertex (m : ℕ) := ZMod m × ZMod m × ZMod m

/-- Bump coordinate `b` of vertex `v`: add 1 to the b-th component. -/
def bumpAt {m : ℕ} [NeZero m] (b : Fin 3) (v : Vertex m) : Vertex m :=
  match b with
  | 0 => (v.1 + 1, v.2.1, v.2.2)
  | 1 => (v.1, v.2.1 + 1, v.2.2)
  | 2 => (v.1, v.2.1, v.2.2 + 1)

/-- The fiber index: s = i + j + k. All arcs go from fiber s to fiber s + 1. -/
def fiber {m : ℕ} [NeZero m] (v : Vertex m) : ZMod m :=
  v.1 + v.2.1 + v.2.2

/-- The cube digraph: vertices are (ZMod m)³, with an arc from u to v when v is obtained
from u by bumping one coordinate. -/
def cubeDigraph (m : ℕ) [NeZero m] : Digraph (Vertex m) where
  Adj u v := ∃ b : Fin 3, bumpAt b u = v

/-! ## Directed Hamiltonian cycles -/

/-- A permutation σ on vertices of a digraph G is a directed Hamiltonian cycle if:
1. Every arc (v, σ v) is an edge of G
2. σ is a single cycle
3. σ moves every vertex (the cycle visits all vertices) -/
def IsDirectedHamiltonianCycle {V : Type*} [Fintype V] [DecidableEq V]
    (G : Digraph V) (σ : Equiv.Perm V) : Prop :=
  (∀ v, G.Adj v (σ v)) ∧ σ.IsCycle ∧ σ.support = Finset.univ

/-! ## Claude's construction -/

/-- Claude's direction function: at vertex v and for cycle c, returns which coordinate to bump.

This encodes the C program:
```
s = (i+j+k) % m;
if (s == 0) d = (j == m-1 ? "012" : "210");
else if (s == m-1) d = (i == 0 ? "210" : "120");
else d = (i == m-1 ? "201" : "102");
bump coordinate d[c];
```
In ZMod m, the condition `x == m-1` becomes `x = -1`, and `x == 0` becomes `x = 0`. -/
def claudeDir {m : ℕ} [NeZero m] (v : Vertex m) (c : Fin 3) : Fin 3 :=
  let s := fiber v
  let i := v.1
  let j := v.2.1
  if s = 0 then
    if j = -1 then ![0, 1, 2] c  -- "012"
    else ![2, 1, 0] c             -- "210"
  else if s = -1 then
    if i = 0 then ![2, 1, 0] c    -- "210"
    else ![1, 2, 0] c             -- "120"
  else
    if i = -1 then ![2, 0, 1] c   -- "201"
    else ![1, 0, 2] c             -- "102"

/-- Claude's step function: the successor of vertex v in cycle c. -/
def claudeStep {m : ℕ} [NeZero m] (c : Fin 3) (v : Vertex m) : Vertex m :=
  bumpAt (claudeDir v c) v

/-! ## Fiber structure -/

/-- All arcs go from fiber s to fiber s + 1. -/
theorem fiber_bumpAt {m : ℕ} [NeZero m] (b : Fin 3) (v : Vertex m) :
    fiber (bumpAt b v) = fiber v + 1 := by
  fin_cases b <;> simp [fiber, bumpAt] <;> ring

-- Helper: in ZMod m with m > 1, we have 1 ≠ 0.
private theorem zmod_one_ne_zero {m : ℕ} (hm : 1 < m) : (1 : ZMod m) ≠ 0 := by
  intro h; exact absurd (ZMod.one_eq_zero_iff.mp h) (by omega)

/-- Each `bumpAt b` is injective (adding 1 to one coordinate is injective). -/
theorem bumpAt_injective {m : ℕ} [NeZero m] (b : Fin 3) :
    Function.Injective (bumpAt b : Vertex m → Vertex m) := by
  intro ⟨i₁, j₁, k₁⟩ ⟨i₂, j₂, k₂⟩ h
  fin_cases b <;> simp_all [bumpAt]

/-- No vertex is a fixed point of `bumpAt`: bumping any coordinate by 1 gives a different
vertex when m > 1. -/
theorem bumpAt_ne_self {m : ℕ} [NeZero m] (hm : 1 < m) (b : Fin 3) (v : Vertex m) :
    bumpAt b v ≠ v := by
  have h10 := zmod_one_ne_zero hm
  obtain ⟨i, j, k⟩ := v
  intro h
  fin_cases b <;> simp_all [bumpAt]

theorem claudeStep_ne_self {m : ℕ} [NeZero m] (hm : 1 < m) (c : Fin 3) (v : Vertex m) :
    claudeStep c v ≠ v :=
  bumpAt_ne_self hm (claudeDir v c) v

/-- Each step advances the fiber by 1. -/
theorem fiber_claudeStep {m : ℕ} [NeZero m] (c : Fin 3) (v : Vertex m) :
    fiber (claudeStep c v) = fiber v + 1 :=
  fiber_bumpAt (claudeDir v c) v

/-- After n steps, the fiber advances by n. -/
theorem fiber_claudeStep_iter {m : ℕ} [NeZero m] (c : Fin 3) (v : Vertex m) (n : ℕ) :
    fiber ((claudeStep c)^[n] v) = fiber v + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    rw [fiber_claudeStep, ih]
    push_cast; ring

/-- In ZMod m, 2 is a unit when m is odd (i.e., coprime to 2). -/
theorem two_isUnit_of_odd {m : ℕ} [NeZero m] (hm : Odd m) : IsUnit (2 : ZMod m) :=
  (ZMod.isUnit_iff_coprime 2 m).mpr hm.coprime_two_left

/-! ## Arc partition -/

/-- At each vertex, Claude's direction function is a bijection on Fin 3: the three cycles
use three different arcs. This holds for all m, not just odd m. -/
theorem claudeDir_bijective {m : ℕ} [NeZero m] (v : Vertex m) :
    Function.Bijective (claudeDir v) := by
  constructor
  · -- Injective
    intro a b h
    simp only [claudeDir] at h
    split_ifs at h <;> fin_cases a <;> fin_cases b <;> simp_all
  · -- Surjective
    intro b
    simp only [claudeDir]
    split_ifs <;> fin_cases b <;> first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩

/-- At each vertex, Claude's direction function gives a permutation of Fin 3. -/
noncomputable def claudeDir_perm {m : ℕ} [NeZero m] (v : Vertex m) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (claudeDir v) (claudeDir_bijective v)

/-- The three cycles partition all arcs of the cube digraph: every arc is used by exactly
one cycle. This is a consequence of `claudeDir_bijective` and holds for all m. -/
theorem claude_arc_decomposition {m : ℕ} [NeZero m] :
    ∀ v : Vertex m, ∀ b : Fin 3, ∃! c : Fin 3, claudeDir v c = b := by
  intro v b
  obtain ⟨hinj, hsurj⟩ := claudeDir_bijective v
  obtain ⟨c, hc⟩ := hsurj b
  exact ⟨c, hc, fun c' hc' => hinj (hc' ▸ hc ▸ rfl)⟩

/-- Each step stays within the cube digraph (produces a valid arc). -/
theorem claudeStep_adj {m : ℕ} [NeZero m] (c : Fin 3) (v : Vertex m) :
    (cubeDigraph m).Adj v (claudeStep c v) := by
  exact ⟨claudeDir v c, rfl⟩

/-! ## The individual cycle rules

Knuth gives explicit descriptions of the three cycles' behavior, which we record here.

### Cycle 0 (c = 0)
- If s = 0: bump i when j = m−1, otherwise bump k
- If 0 < s < m−1: bump k when i = m−1, otherwise bump j
- If s = m−1: bump j when i > 0, otherwise bump k

### Cycle 1 (c = 1)
- If s = 0: bump j
- If 0 < s < m−1: bump i
- If s = m−1 and i > 0: bump k
- If s = m−1 and i = 0: bump j

### Cycle 2 (c = 2)
- If s = 0 and j < m−1: bump i
- If s = 0 and j = m−1: bump k
- If 0 < s < m−1 and i < m−1: bump k
- If 0 < s < m−1 and i = m−1: bump j
- If s = m−1: bump i
-/

-- Cycle 0 rules

/-- Cycle 0 bumps i when s = 0 and j = −1. -/
theorem claudeDir_cycle0_s0_j {m : ℕ} [NeZero m] (_hm : 1 < m) (v : Vertex m)
    (hs : fiber v = 0) (hj : v.2.1 = -1) :
    claudeDir v 0 = 0 := by
  simp [claudeDir, hs, hj]

/-- Cycle 0 bumps k when s = 0 and j ≠ −1. -/
theorem claudeDir_cycle0_s0_nj {m : ℕ} [NeZero m] (_hm : 1 < m) (v : Vertex m)
    (hs : fiber v = 0) (hj : v.2.1 ≠ -1) :
    claudeDir v 0 = 2 := by
  simp [claudeDir, hs, hj]

/-- Cycle 0 bumps j when 0 < s < m−1 and i ≠ −1. -/
theorem claudeDir_cycle0_mid_ni {m : ℕ} [NeZero m] (_hm : 1 < m) (v : Vertex m)
    (hs0 : fiber v ≠ 0) (hs1 : fiber v ≠ -1) (hi : v.1 ≠ -1) :
    claudeDir v 0 = 1 := by
  simp [claudeDir, hs0, hs1, hi]

/-- Cycle 0 bumps k when 0 < s < m−1 and i = −1. -/
theorem claudeDir_cycle0_mid_i {m : ℕ} [NeZero m] (_hm : 1 < m) (v : Vertex m)
    (hs0 : fiber v ≠ 0) (hs1 : fiber v ≠ -1) (hi : v.1 = -1) :
    claudeDir v 0 = 2 := by
  simp [claudeDir, hs0, hs1, hi]

/-- Cycle 0 bumps j when s = −1 and i ≠ 0. -/
theorem claudeDir_cycle0_s1_i {m : ℕ} [NeZero m] (hm : 1 < m) (v : Vertex m)
    (hs : fiber v = -1) (hi : v.1 ≠ 0) :
    claudeDir v 0 = 1 := by
  have h10 := zmod_one_ne_zero hm
  simp only [claudeDir]
  split_ifs <;> simp_all

/-- Cycle 0 bumps k when s = −1 and i = 0. -/
theorem claudeDir_cycle0_s1_ni {m : ℕ} [NeZero m] (hm : 1 < m) (v : Vertex m)
    (hs : fiber v = -1) (hi : v.1 = 0) :
    claudeDir v 0 = 2 := by
  have h10 := zmod_one_ne_zero hm
  simp only [claudeDir]
  split_ifs <;> simp_all

-- Cycle 1 rules

/-- Cycle 1 bumps j when s = 0. -/
theorem claudeDir_cycle1_s0 {m : ℕ} [NeZero m] (hm : 1 < m) (v : Vertex m)
    (hs : fiber v = 0) :
    claudeDir v 1 = 1 := by
  have h10 := zmod_one_ne_zero hm
  simp only [claudeDir]
  split_ifs <;> simp_all

/-- Cycle 1 bumps i when 0 < s < m−1. -/
theorem claudeDir_cycle1_mid {m : ℕ} [NeZero m] (_hm : 1 < m) (v : Vertex m)
    (hs0 : fiber v ≠ 0) (hs1 : fiber v ≠ -1) :
    claudeDir v 1 = 0 := by
  simp [claudeDir, hs0, hs1]

/-- Cycle 1 bumps k when s = −1 and i ≠ 0. -/
theorem claudeDir_cycle1_s1_i {m : ℕ} [NeZero m] (hm : 1 < m) (v : Vertex m)
    (hs : fiber v = -1) (hi : v.1 ≠ 0) :
    claudeDir v 1 = 2 := by
  have h10 := zmod_one_ne_zero hm
  simp only [claudeDir]
  split_ifs <;> simp_all

/-- Cycle 1 bumps j when s = −1 and i = 0. -/
theorem claudeDir_cycle1_s1_ni {m : ℕ} [NeZero m] (hm : 1 < m) (v : Vertex m)
    (hs : fiber v = -1) (hi : v.1 = 0) :
    claudeDir v 1 = 1 := by
  have h10 := zmod_one_ne_zero hm
  simp only [claudeDir]
  split_ifs <;> simp_all

-- Cycle 2 rules

/-- Cycle 2 bumps i when s = 0 and j ≠ −1. -/
theorem claudeDir_cycle2_s0_nj {m : ℕ} [NeZero m] (_hm : 1 < m) (v : Vertex m)
    (hs : fiber v = 0) (hj : v.2.1 ≠ -1) :
    claudeDir v 2 = 0 := by
  simp [claudeDir, hs, hj]

/-- Cycle 2 bumps k when s = 0 and j = −1. -/
theorem claudeDir_cycle2_s0_j {m : ℕ} [NeZero m] (_hm : 1 < m) (v : Vertex m)
    (hs : fiber v = 0) (hj : v.2.1 = -1) :
    claudeDir v 2 = 2 := by
  simp [claudeDir, hs, hj]

/-- Cycle 2 bumps k when 0 < s < m−1 and i ≠ −1. -/
theorem claudeDir_cycle2_mid_ni {m : ℕ} [NeZero m] (_hm : 1 < m) (v : Vertex m)
    (hs0 : fiber v ≠ 0) (hs1 : fiber v ≠ -1) (hi : v.1 ≠ -1) :
    claudeDir v 2 = 2 := by
  simp [claudeDir, hs0, hs1, hi]

/-- Cycle 2 bumps j when 0 < s < m−1 and i = −1. -/
theorem claudeDir_cycle2_mid_i {m : ℕ} [NeZero m] (_hm : 1 < m) (v : Vertex m)
    (hs0 : fiber v ≠ 0) (hs1 : fiber v ≠ -1) (hi : v.1 = -1) :
    claudeDir v 2 = 1 := by
  simp [claudeDir, hs0, hs1, hi]

/-- Cycle 2 bumps i when s = −1. -/
theorem claudeDir_cycle2_s1 {m : ℕ} [NeZero m] (hm : 1 < m) (v : Vertex m)
    (hs : fiber v = -1) :
    claudeDir v 2 = 0 := by
  have h10 := zmod_one_ne_zero hm
  simp only [claudeDir]
  split_ifs <;> simp_all

/-! ## Coordinate-level lemmas for claudeStep -/

/-- bumpAt 0 increments the first coordinate and preserves the others. -/
@[simp] theorem bumpAt_zero_fst {m : ℕ} [NeZero m] (v : Vertex m) :
    (bumpAt 0 v).1 = v.1 + 1 := rfl
@[simp] theorem bumpAt_zero_snd_fst {m : ℕ} [NeZero m] (v : Vertex m) :
    (bumpAt 0 v).2.1 = v.2.1 := rfl
@[simp] theorem bumpAt_zero_snd_snd {m : ℕ} [NeZero m] (v : Vertex m) :
    (bumpAt 0 v).2.2 = v.2.2 := rfl

/-- bumpAt 1 increments the second coordinate and preserves the others. -/
@[simp] theorem bumpAt_one_fst {m : ℕ} [NeZero m] (v : Vertex m) :
    (bumpAt 1 v).1 = v.1 := rfl
@[simp] theorem bumpAt_one_snd_fst {m : ℕ} [NeZero m] (v : Vertex m) :
    (bumpAt 1 v).2.1 = v.2.1 + 1 := rfl
@[simp] theorem bumpAt_one_snd_snd {m : ℕ} [NeZero m] (v : Vertex m) :
    (bumpAt 1 v).2.2 = v.2.2 := rfl

/-- bumpAt 2 increments the third coordinate and preserves the others. -/
@[simp] theorem bumpAt_two_fst {m : ℕ} [NeZero m] (v : Vertex m) :
    (bumpAt 2 v).1 = v.1 := rfl
@[simp] theorem bumpAt_two_snd_fst {m : ℕ} [NeZero m] (v : Vertex m) :
    (bumpAt 2 v).2.1 = v.2.1 := rfl
@[simp] theorem bumpAt_two_snd_snd {m : ℕ} [NeZero m] (v : Vertex m) :
    (bumpAt 2 v).2.2 = v.2.2 + 1 := rfl

/-- When claudeDir assigns coordinate b, bumping preserves the other coordinates. -/
theorem claudeStep_fst_of_dir_ne_zero {m : ℕ} [NeZero m] (c : Fin 3) (v : Vertex m)
    (h : claudeDir v c ≠ 0) : (claudeStep c v).1 = v.1 := by
  simp only [claudeStep]
  have : claudeDir v c = 1 ∨ claudeDir v c = 2 := by omega
  rcases this with h1 | h1 <;> simp [h1, bumpAt]

theorem claudeStep_snd_fst_of_dir_ne_one {m : ℕ} [NeZero m] (c : Fin 3) (v : Vertex m)
    (h : claudeDir v c ≠ 1) : (claudeStep c v).2.1 = v.2.1 := by
  simp only [claudeStep]
  have : claudeDir v c = 0 ∨ claudeDir v c = 2 := by omega
  rcases this with h1 | h1 <;> simp [h1, bumpAt]

theorem claudeStep_snd_snd_of_dir_ne_two {m : ℕ} [NeZero m] (c : Fin 3) (v : Vertex m)
    (h : claudeDir v c ≠ 2) : (claudeStep c v).2.2 = v.2.2 := by
  simp only [claudeStep]
  have : claudeDir v c = 0 ∨ claudeDir v c = 1 := by omega
  rcases this with h1 | h1 <;> simp [h1, bumpAt]

/-- For cycle 0, i only changes when s = 0 and j = -1. -/
theorem claudeStep_fst_cycle0 {m : ℕ} [NeZero m] (_hm : 1 < m) (v : Vertex m)
    (h : ¬(fiber v = 0 ∧ v.2.1 = -1)) : (claudeStep 0 v).1 = v.1 := by
  apply claudeStep_fst_of_dir_ne_zero
  push_neg at h
  simp only [claudeDir]
  split_ifs with hs hj hs' hi hi
  · exact absurd hj (h hs)
  · decide
  · decide
  · decide
  · decide
  · decide

/-! ## Bijectivity of claudeStep -/

/-- The step function for each cycle is bijective (hence a permutation).

Proof sketch: On a finite type, injective ↔ bijective. For injectivity, if
`claudeStep c u = claudeStep c v`, i.e. `bumpAt (claudeDir u c) u = bumpAt (claudeDir v c) v`:
- If same direction: `bumpAt b` is injective, so `u = v`.
- If different directions: the fiber equality `fiber u = fiber v` forces the same branch
  conditions, contradicting the direction difference. -/
theorem claudeStep_bijective {m : ℕ} [NeZero m] (_hm : Odd m) (hm' : 1 < m) (c : Fin 3) :
    Function.Bijective (claudeStep c : Vertex m → Vertex m) := by
  rw [← Finite.injective_iff_bijective]
  intro u v heq
  simp only [claudeStep] at heq
  have hf : fiber u = fiber v :=
    add_right_cancel (show fiber u + 1 = fiber v + 1 by
      have := congr_arg fiber heq; rwa [fiber_bumpAt, fiber_bumpAt] at this)
  suffices hd : claudeDir u c = claudeDir v c by
    rw [hd] at heq; exact bumpAt_injective _ heq
  have hfst := congr_arg Prod.fst heq
  have hsnd := congr_arg (fun p => p.2.1) heq
  have h10 := zmod_one_ne_zero hm'
  have hn1 : (-1 : ZMod m) ≠ 0 := neg_ne_zero.mpr h10
  simp only [claudeDir]
  rw [show fiber u = fiber v from hf]
  by_cases hs0 : fiber v = 0
  · simp only [hs0, ite_true]
    by_cases huj : u.2.1 = -1 <;> by_cases hvj : v.2.1 = -1 <;>
      simp only [huj, hvj, ite_true, ite_false]
    all_goals (simp only [huj, hvj, ite_true, ite_false, claudeDir, hs0,
      show fiber u = fiber v from hf] at hfst hsnd)
    all_goals (fin_cases c <;> simp_all [bumpAt])
  · by_cases hs1 : fiber v = -1
    · simp only [hs1, ite_true]
      by_cases hui : u.1 = 0 <;> by_cases hvi : v.1 = 0 <;>
        simp only [hui, hvi, ite_true, ite_false]
      all_goals (simp only [hui, hvi, ite_true, ite_false, claudeDir, hs1, hn1,
        show fiber u = fiber v from hf] at hfst hsnd)
      all_goals (fin_cases c <;> simp_all [bumpAt])
    · simp only [hs0, hs1, ite_false]
      by_cases hui : u.1 = -1 <;> by_cases hvi : v.1 = -1 <;>
        simp only [hui, hvi, ite_true, ite_false]
      all_goals (simp only [hui, hvi, ite_true, ite_false, claudeDir, hs0, hs1, hn1,
        show fiber u = fiber v from hf] at hfst hsnd)
      all_goals (fin_cases c <;> simp_all [bumpAt])

/-! ## Trajectory analysis for IsCycle

The key insight: to prove `claudeStepPerm` is a single cycle, we show the orbit of any
vertex covers all m³ vertices. We reduce this to showing the "return map"
`R = claudeStep^[m]` restricted to fiber-0 vertices is a single m²-cycle.
-/

/-- Iterating a bijection preserves surjectivity. -/
private theorem claudeStep_iter_surj {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (c : Fin 3) (n : ℕ) : Function.Surjective ((claudeStep c : Vertex m → Vertex m)^[n]) :=
  (claudeStep_bijective hm hm' c).surjective.iterate n

/-- Bridge lemma: if the orbit of (0,0,0) covers all fiber-0 vertices,
it covers all vertices. The argument: for any v with fiber r, bijectivity gives
a fiber-0 preimage w with f^[r] w = v, and if w is reachable then so is v. -/
private theorem claudeStep_orbit_surj_of_fiber0 {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (c : Fin 3)
    (h : ∀ v : Vertex m, fiber v = 0 → ∃ n : ℕ, (claudeStep c)^[n] (0, 0, 0) = v) :
    ∀ v : Vertex m, ∃ n : ℕ, (claudeStep c)^[n] (0, 0, 0) = v := by
  intro v
  -- Let r = ZMod.val (fiber v)
  set r := ZMod.val (fiber v) with hr_def
  -- f^[r] is surjective, so v has a preimage w
  obtain ⟨w, hw⟩ := claudeStep_iter_surj hm hm' c r v
  -- w is in fiber 0: fiber(f^[r] w) = fiber w + r = fiber v, and r = fiber v in ZMod m
  have hw_fiber : fiber w = 0 := by
    have h1 := fiber_claudeStep_iter c w r
    rw [hw, hr_def, ZMod.natCast_zmod_val] at h1
    -- h1 : fiber v = fiber w + fiber v
    exact add_right_cancel (show fiber w + fiber v = 0 + fiber v by rw [zero_add]; exact h1.symm)
  -- w is reachable from (0,0,0)
  obtain ⟨k, hk⟩ := h w hw_fiber
  -- So v is reachable: f^[k + r] (0,0,0) = f^[r] (f^[k] (0,0,0)) = f^[r] w = v
  exact ⟨k + r, by
    rw [show k + r = r + k from Nat.add_comm k r, Function.iterate_add_apply, hk, hw]⟩

/-! ### Return map infrastructure for Knuth's trajectory analysis -/

/-- Helper: a natural number strictly between 0 and m is nonzero in ZMod m. -/
private theorem zmod_natCast_ne_zero {m n : ℕ} [NeZero m] (h0 : 0 < n) (hm : n < m) :
    (n : ZMod m) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => absurd (Nat.le_of_dvd h0 h) (by omega)

/-- In ZMod m, casting (m - 1) gives -1. -/
private theorem zmod_natCast_m_sub_one {m : ℕ} [NeZero m] (hm : 1 ≤ m) :
    ((m - 1 : ℕ) : ZMod m) = -1 := by
  rw [Nat.cast_sub hm, ZMod.natCast_self, zero_sub]; push_cast; ring

/-- In ZMod m, casting (m - 2) gives -2. -/
private theorem zmod_natCast_m_sub_two {m : ℕ} [NeZero m] (hm : 2 ≤ m) :
    ((m - 2 : ℕ) : ZMod m) = -2 := by
  rw [Nat.cast_sub hm, ZMod.natCast_self, zero_sub]; push_cast; ring

/-- Decompose f^[n] into three phases: f ∘ f^[n-2] ∘ f, for n ≥ 2. -/
private theorem iterate_three_phases {α : Type*} (f : α → α) (n : ℕ) (hn : 2 ≤ n) (x : α) :
    f^[n] x = f (f^[n - 2] (f x)) := by
  conv_lhs => rw [show n = 1 + (n - 2) + 1 from by omega]
  simp only [Function.iterate_add_apply, Function.iterate_one]

/-- Phase 2 iterate for i ≠ m−1: starting at fiber s with 1 ≤ s and s + n ≤ m − 1,
claudeStep 0 bumps j for n steps. -/
private theorem claudeStep0_iter_bumpJ {m : ℕ} [NeZero m] (hm' : 1 < m)
    (i j k : ZMod m) (n s : ℕ) (hs : 1 ≤ s) (hsn : s + n ≤ m - 1)
    (hi : i ≠ (-1 : ZMod m))
    (hfib : fiber (i, j, k) = (s : ZMod m)) :
    (claudeStep 0)^[n] (i, j, k) = (i, j + (n : ZMod m), k) := by
  induction n generalizing j k s with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ, Function.comp_apply]
    have hs0 : fiber (i, j, k) ≠ 0 := by
      rw [hfib]; exact zmod_natCast_ne_zero (by omega) (by omega)
    have hs1 : fiber (i, j, k) ≠ -1 := by
      rw [hfib]; intro h
      have : ((s + 1 : ℕ) : ZMod m) = 0 := by
        have : (s : ZMod m) + 1 = 0 := by rw [h]; ring
        rwa [← Nat.cast_one, ← Nat.cast_add] at this
      exact absurd this (zmod_natCast_ne_zero (by omega) (by omega))
    have hdir : claudeDir (i, j, k) 0 = 1 := claudeDir_cycle0_mid_ni hm' _ hs0 hs1 hi
    simp only [claudeStep, hdir, bumpAt]
    have hfib' : fiber (i, j + 1, k) = ((s + 1 : ℕ) : ZMod m) := by
      simp only [fiber] at hfib ⊢
      rw [show i + (j + 1) + k = (i + j + k) + 1 from by ring, hfib]
      push_cast; ring
    rw [ih (j + 1) k (s + 1) (by omega) (by omega) hfib']
    refine Prod.ext rfl (Prod.ext ?_ rfl); push_cast; ring

/-- Phase 2 iterate for i = m−1: starting at fiber s with 1 ≤ s and s + n ≤ m − 1,
claudeStep 0 bumps k for n steps. -/
private theorem claudeStep0_iter_bumpK {m : ℕ} [NeZero m] (hm' : 1 < m)
    (j k : ZMod m) (n s : ℕ) (hs : 1 ≤ s) (hsn : s + n ≤ m - 1)
    (hfib : fiber ((-1 : ZMod m), j, k) = (s : ZMod m)) :
    (claudeStep 0)^[n] ((-1 : ZMod m), j, k) = ((-1 : ZMod m), j, k + (n : ZMod m)) := by
  induction n generalizing j k s with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ, Function.comp_apply]
    have hs0 : fiber ((-1 : ZMod m), j, k) ≠ 0 := by
      rw [hfib]; exact zmod_natCast_ne_zero (by omega) (by omega)
    have hs1 : fiber ((-1 : ZMod m), j, k) ≠ -1 := by
      rw [hfib]; intro h
      have : ((s + 1 : ℕ) : ZMod m) = 0 := by
        have : (s : ZMod m) + 1 = 0 := by rw [h]; ring
        rwa [← Nat.cast_one, ← Nat.cast_add] at this
      exact absurd this (zmod_natCast_ne_zero (by omega) (by omega))
    have hdir : claudeDir ((-1 : ZMod m), j, k) 0 = 2 :=
      claudeDir_cycle0_mid_i hm' _ hs0 hs1 rfl
    simp only [claudeStep, hdir, bumpAt]
    have hfib' : fiber ((-1 : ZMod m), j, k + 1) = ((s + 1 : ℕ) : ZMod m) := by
      simp only [fiber] at hfib ⊢
      rw [show (-1 : ZMod m) + j + (k + 1) = ((-1 : ZMod m) + j + k) + 1 from by ring, hfib]
      push_cast; ring
    rw [ih j (k + 1) (s + 1) (by omega) (by omega) hfib']
    refine Prod.ext rfl (Prod.ext rfl ?_); push_cast; ring

/-- Return map for cycle 0, generic case: j ≠ −1, 0 < i < m−1.
After m steps, (i, j, −i−j) ↦ (i, j−1, −i−(j−1)). -/
private theorem returnMap0_generic {m : ℕ} [NeZero m] (_hm : Odd m) (hm' : 1 < m)
    (i j : ZMod m) (hi0 : i ≠ 0) (hi1 : i ≠ -1) (hj : j ≠ -1) :
    (claudeStep 0)^[m] (i, j, -i - j) = (i, j - 1, -(i + (j - 1))) := by
  -- Decompose m = 1 + (m-2) + 1
  rw [iterate_three_phases _ m (by omega)]
  -- Phase 1: at fiber 0 with j ≠ -1, bump k
  have hfib0 : fiber (i, j, -i - j) = 0 := by simp [fiber]
  have hdir1 : claudeDir (i, j, -i - j) 0 = 2 := claudeDir_cycle0_s0_nj hm' _ hfib0 hj
  simp only [claudeStep, hdir1, bumpAt]
  -- Phase 2: m-2 steps, i ≠ -1, bump j
  have hfib1 : fiber (i, j, -i - j + 1) = ((1 : ℕ) : ZMod m) := by
    simp [fiber]; ring
  rw [claudeStep0_iter_bumpJ hm' i j (-i - j + 1) (m - 2) 1 (by omega) (by omega) hi1 hfib1]
  -- Phase 3: at fiber m-1 with i ≠ 0, bump j
  have hfib_last : fiber (i, j + ((m - 2 : ℕ) : ZMod m), -i - j + 1) = -1 := by
    simp only [fiber, zmod_natCast_m_sub_two (by omega : 2 ≤ m)]; ring
  have hdir3 : claudeDir (i, j + ((m - 2 : ℕ) : ZMod m), -i - j + 1) 0 = 1 :=
    claudeDir_cycle0_s1_i hm' _ hfib_last hi0
  simp only [hdir3]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> (rw [zmod_natCast_m_sub_two (by omega)]; try ring)

/-- Return map for cycle 0, i = 0 case: j ≠ −1.
After m steps, (0, j, −j) ↦ (0, j−2, −(j−2)). -/
private theorem returnMap0_i0 {m : ℕ} [NeZero m] (_hm : Odd m) (hm' : 1 < m)
    (j : ZMod m) (hj : j ≠ -1) :
    (claudeStep 0)^[m] ((0 : ZMod m), j, -j) = ((0 : ZMod m), j - 2, -(j - 2)) := by
  rw [iterate_three_phases _ m (by omega)]
  -- Phase 1: bump k (j ≠ -1)
  have hfib0 : fiber ((0 : ZMod m), j, -j) = 0 := by simp [fiber]
  have hdir1 : claudeDir ((0 : ZMod m), j, -j) 0 = 2 := claudeDir_cycle0_s0_nj hm' _ hfib0 hj
  simp only [claudeStep, hdir1, bumpAt]
  -- Phase 2: m-2 steps, bump j (i = 0 ≠ -1)
  have hi1 : (0 : ZMod m) ≠ -1 := by
    intro h; exact absurd (neg_eq_zero.mp h.symm) (zmod_one_ne_zero hm')
  have hfib1 : fiber ((0 : ZMod m), j, -j + 1) = ((1 : ℕ) : ZMod m) := by
    simp [fiber]
  rw [claudeStep0_iter_bumpJ hm' 0 j (-j + 1) (m - 2) 1 (by omega) (by omega) hi1 hfib1]
  -- Phase 3: bump k (i = 0 at fiber m-1)
  have hfib_last : fiber ((0 : ZMod m), j + ((m - 2 : ℕ) : ZMod m), -j + 1) = -1 := by
    simp only [fiber, zmod_natCast_m_sub_two (by omega : 2 ≤ m)]; ring
  have hdir3 : claudeDir ((0 : ZMod m), j + ((m - 2 : ℕ) : ZMod m), -j + 1) 0 = 2 :=
    claudeDir_cycle0_s1_ni hm' _ hfib_last rfl
  simp only [hdir3]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> (rw [zmod_natCast_m_sub_two (by omega)]; try ring)

/-- Return map for cycle 0, i = m−1 case: j ≠ −1.
After m steps, (−1, j, 1−j) ↦ (−1, j+1, −j). -/
private theorem returnMap0_im1 {m : ℕ} [NeZero m] (_hm : Odd m) (hm' : 1 < m)
    (j : ZMod m) (hj : j ≠ -1) :
    (claudeStep 0)^[m] ((-1 : ZMod m), j, 1 - j) = ((-1 : ZMod m), j + 1, -j) := by
  rw [iterate_three_phases _ m (by omega)]
  -- Phase 1: bump k (j ≠ -1)
  have hfib0 : fiber ((-1 : ZMod m), j, 1 - j) = 0 := by simp [fiber]
  have hdir1 : claudeDir ((-1 : ZMod m), j, 1 - j) 0 = 2 := claudeDir_cycle0_s0_nj hm' _ hfib0 hj
  simp only [claudeStep, hdir1, bumpAt]
  -- Phase 2: m-2 steps, bump k (i = -1)
  have hfib1 : fiber ((-1 : ZMod m), j, 1 - j + 1) = ((1 : ℕ) : ZMod m) := by
    simp [fiber]; ring
  rw [claudeStep0_iter_bumpK hm' j (1 - j + 1) (m - 2) 1 (by omega) (by omega) hfib1]
  -- Phase 3: bump j (i = -1 ≠ 0 at fiber m-1)
  have hfib_last : fiber ((-1 : ZMod m), j, 1 - j + 1 + ((m - 2 : ℕ) : ZMod m)) = -1 := by
    simp only [fiber, zmod_natCast_m_sub_two (by omega : 2 ≤ m)]; ring
  have hi0 : (-1 : ZMod m) ≠ 0 := by
    intro h; exact absurd (neg_eq_zero.mp h) (zmod_one_ne_zero hm')
  have hdir3 : claudeDir ((-1 : ZMod m), j, 1 - j + 1 + ((m - 2 : ℕ) : ZMod m)) 0 = 1 :=
    claudeDir_cycle0_s1_i hm' _ hfib_last hi0
  simp only [hdir3]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> (rw [zmod_natCast_m_sub_two (by omega)]; try ring)

/-- Return map for cycle 0, transition case: j = −1, i+1 ≠ −1, i+1 ≠ 0.
After m steps, (i, −1, 1−i) ↦ (i+1, −2, 1−i). -/
private theorem returnMap0_transition {m : ℕ} [NeZero m] (_hm : Odd m) (hm' : 1 < m)
    (i : ZMod m) (hi1 : i + 1 ≠ -1) (hi1_ne0 : i + 1 ≠ 0) :
    (claudeStep 0)^[m] (i, -1, 1 - i) = (i + 1, -2, 1 - i) := by
  rw [iterate_three_phases _ m (by omega)]
  -- Phase 1: bump i (j = -1)
  have hfib0 : fiber (i, -1, 1 - i) = 0 := by simp [fiber]; ring
  have hj : (i, (-1 : ZMod m), 1 - i).2.1 = -1 := rfl
  have hdir1 : claudeDir (i, -1, 1 - i) 0 = 0 := claudeDir_cycle0_s0_j hm' _ hfib0 hj
  simp only [claudeStep, hdir1, bumpAt]
  -- Phase 2: m-2 steps, bump j (i+1 ≠ -1)
  have hfib1 : fiber (i + 1, -1, 1 - i) = ((1 : ℕ) : ZMod m) := by
    simp [fiber]
  rw [claudeStep0_iter_bumpJ hm' (i + 1) (-1) (1 - i) (m - 2) 1 (by omega) (by omega) hi1 hfib1]
  -- Phase 3: bump j (i+1 ≠ 0 at fiber m-1)
  have hfib_last : fiber (i + 1, -1 + ((m - 2 : ℕ) : ZMod m), 1 - i) = -1 := by
    simp only [fiber, zmod_natCast_m_sub_two (by omega : 2 ≤ m)]; ring
  have hdir3 : claudeDir (i + 1, -1 + ((m - 2 : ℕ) : ZMod m), 1 - i) 0 = 1 :=
    claudeDir_cycle0_s1_i hm' _ hfib_last hi1_ne0
  simp only [hdir3]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> (rw [zmod_natCast_m_sub_two (by omega)]; try ring)

/-- Return map for cycle 0, transition to last block: j = −1, i = m−2.
After m steps, (−2, −1, 3−m) ↦ (−1, 0, 1). -/
private theorem returnMap0_transition_to_last {m : ℕ} [NeZero m] (_hm : Odd m) (hm' : 1 < m) :
    (claudeStep 0)^[m] ((-2 : ZMod m), -1, 3 - (m : ZMod m)) =
      ((-1 : ZMod m), 0, 1) := by
  rw [iterate_three_phases _ m (by omega)]
  -- Phase 1: bump i (j = -1). Note: (m : ZMod m) = 0
  have hm0 : (m : ZMod m) = 0 := ZMod.natCast_self m
  have hfib0 : fiber ((-2 : ZMod m), -1, 3 - (m : ZMod m)) = 0 := by
    simp [fiber]; ring
  have hj : ((-2 : ZMod m), (-1 : ZMod m), 3 - (m : ZMod m)).2.1 = -1 := rfl
  have hdir1 : claudeDir ((-2 : ZMod m), -1, 3 - (m : ZMod m)) 0 = 0 :=
    claudeDir_cycle0_s0_j hm' _ hfib0 hj
  simp only [claudeStep, hdir1, bumpAt]
  -- After phase 1: (-1, -1, 3 - (m : ZMod m)) = (-1, -1, 3)
  -- Phase 2: m-2 steps, bump k (i = -1)
  have hfib1 : fiber ((-1 : ZMod m), -1, 3 - (m : ZMod m)) = ((1 : ℕ) : ZMod m) := by
    simp [fiber]; ring
  rw [show (-2 : ZMod m) + 1 = -1 from by ring]
  rw [claudeStep0_iter_bumpK hm' (-1) (3 - (m : ZMod m)) (m - 2) 1 (by omega) (by omega) hfib1]
  -- Phase 3: bump j (i = -1 ≠ 0 at fiber m-1)
  have hfib_last : fiber ((-1 : ZMod m), -1, 3 - (m : ZMod m) + ((m - 2 : ℕ) : ZMod m)) = -1 := by
    simp only [fiber, zmod_natCast_m_sub_two (by omega : 2 ≤ m), hm0]; ring
  have hi0 : (-1 : ZMod m) ≠ 0 := by
    intro h; exact absurd (neg_eq_zero.mp h) (zmod_one_ne_zero hm')
  have hdir3 : claudeDir ((-1 : ZMod m), -1, 3 - (m : ZMod m) + ((m - 2 : ℕ) : ZMod m)) 0 = 1 :=
    claudeDir_cycle0_s1_i hm' _ hfib_last hi0
  simp only [hdir3]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;>
    simp only [zmod_natCast_m_sub_two (by omega : 2 ≤ m), hm0] <;> ring

/-- Return map for cycle 0, wrap case: j = −1, i = m−1.
After m steps, (−1, −1, 2) ↦ (0, −3, 3). -/
private theorem returnMap0_wrap {m : ℕ} [NeZero m] (_hm : Odd m) (hm' : 1 < m) :
    (claudeStep 0)^[m] ((-1 : ZMod m), -1, 2) = ((0 : ZMod m), -3, 3) := by
  rw [iterate_three_phases _ m (by omega)]
  -- Phase 1: bump i (j = -1)
  have hfib0 : fiber ((-1 : ZMod m), -1, 2) = 0 := by simp [fiber]; ring
  have hj : ((-1 : ZMod m), (-1 : ZMod m), (2 : ZMod m)).2.1 = -1 := rfl
  have hdir1 : claudeDir ((-1 : ZMod m), -1, 2) 0 = 0 := claudeDir_cycle0_s0_j hm' _ hfib0 hj
  simp only [claudeStep, hdir1, bumpAt]
  -- After phase 1: (0, -1, 2)
  -- Phase 2: m-2 steps, bump j (i = 0 ≠ -1)
  have hi1 : (0 : ZMod m) ≠ -1 := by
    intro h; exact absurd (neg_eq_zero.mp h.symm) (zmod_one_ne_zero hm')
  have hfib1 : fiber ((0 : ZMod m), -1, 2) = ((1 : ℕ) : ZMod m) := by
    simp [fiber]; ring
  rw [show (-1 : ZMod m) + 1 = 0 from by ring]
  rw [claudeStep0_iter_bumpJ hm' 0 (-1) 2 (m - 2) 1 (by omega) (by omega) hi1 hfib1]
  -- Phase 3: bump k (i = 0 at fiber m-1)
  have hfib_last : fiber ((0 : ZMod m), -1 + ((m - 2 : ℕ) : ZMod m), 2) = -1 := by
    simp only [fiber, zmod_natCast_m_sub_two (by omega : 2 ≤ m)]; ring
  have hdir3 : claudeDir ((0 : ZMod m), -1 + ((m - 2 : ℕ) : ZMod m), 2) 0 = 2 :=
    claudeDir_cycle0_s1_ni hm' _ hfib_last rfl
  simp only [hdir3]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> (rw [zmod_natCast_m_sub_two (by omega)]; try ring)

/-- Iterating the return map within a generic block: j decreases by 1 each step. -/
private theorem returnMap0_generic_iter {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (i j₀ : ZMod m) (k : ℕ) (hi0 : i ≠ 0) (hi1 : i ≠ -1)
    (hne : ∀ t : ℕ, t < k → j₀ - (t : ZMod m) ≠ -1) :
    ((claudeStep 0)^[m])^[k] (i, j₀, -i - j₀) =
      (i, j₀ - (k : ZMod m), -(i + (j₀ - (k : ZMod m)))) := by
  induction k with
  | zero => simp; ring
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply,
        ih (fun t ht => hne t (by omega))]
    have hj : j₀ - (k : ZMod m) ≠ -1 := hne k (by omega)
    conv_lhs => rw [show -(i + (j₀ - ↑k)) = -i - (j₀ - ↑k) from by ring]
    rw [returnMap0_generic hm hm' i (j₀ - k) hi0 hi1 hj]
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> push_cast <;> ring

/-- Iterating the return map in block i=0: j decreases by 2 each step. -/
private theorem returnMap0_i0_iter {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (j₀ : ZMod m) (k : ℕ)
    (hne : ∀ t : ℕ, t < k → j₀ - 2 * (t : ZMod m) ≠ -1) :
    ((claudeStep 0)^[m])^[k] ((0 : ZMod m), j₀, -j₀) =
      ((0 : ZMod m), j₀ - 2 * (k : ZMod m), -(j₀ - 2 * (k : ZMod m))) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply,
        ih (fun t ht => hne t (by omega))]
    have hj : j₀ - 2 * (k : ZMod m) ≠ -1 := hne k (by omega)
    rw [returnMap0_i0 hm hm' (j₀ - 2 * k) hj]
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> push_cast <;> ring

/-- Iterating the return map in block i=-1: j increases by 1 each step. -/
private theorem returnMap0_im1_iter {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (j₀ : ZMod m) (k : ℕ)
    (hne : ∀ t : ℕ, t < k → j₀ + (t : ZMod m) ≠ -1) :
    ((claudeStep 0)^[m])^[k] ((-1 : ZMod m), j₀, 1 - j₀) =
      ((-1 : ZMod m), j₀ + (k : ZMod m), 1 - (j₀ + (k : ZMod m))) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply,
        ih (fun t ht => hne t (by omega))]
    have hj : j₀ + (k : ZMod m) ≠ -1 := hne k (by omega)
    rw [returnMap0_im1 hm hm' (j₀ + k) hj]
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> push_cast <;> ring

/-- Key helper: if R^k(v) = w then f^[k*m](v) = w, where R = f^[m]. -/
private theorem iterate_return_map {α : Type*} (f : α → α) (m k : ℕ) (v w : α)
    (h : (f^[m])^[k] v = w) : f^[k * m] v = w := by
  rw [show k * m = m * k from Nat.mul_comm k m, Function.iterate_mul]; exact h

/-- In ZMod m with m > 1, -2 - (t : ℕ) ≠ -1 when t < m - 1.
    Equivalently, (t : ZMod m) ≠ (1 : ZMod m) when 0 ≤ t < m - 1. -/
private theorem neg_two_sub_ne_neg_one {m : ℕ} [NeZero m] (hm' : 1 < m) (t : ℕ) (ht : t < m - 1) :
    (-2 : ZMod m) - (t : ZMod m) ≠ -1 := by
  intro h
  have h1 : (t : ZMod m) = -1 := by
    calc (t : ZMod m) = -(-2 - (t : ZMod m)) - 2 := by ring
      _ = -(-1 : ZMod m) - 2 := by rw [h]
      _ = -1 := by ring
  have h2 : ((t + 1 : ℕ) : ZMod m) = 0 := by
    rw [Nat.cast_add, Nat.cast_one, h1]; ring
  exact absurd h2 (zmod_natCast_ne_zero (by omega) (by omega))

/-! ### Cycle 1 return map helpers -/

/-- In ZMod m with m odd and m > 1, -2 * (t : ℕ) ≠ 2 when t < m - 1. -/
private theorem neg_two_mul_ne_two {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (t : ℕ) (ht : t < m - 1) :
    (-2 : ZMod m) * (t : ZMod m) ≠ 2 := by
  intro h
  have h1 : (t : ZMod m) = -1 := by
    have h2 : (-2 : ZMod m) * (t : ZMod m) = (-2 : ZMod m) * (-1 : ZMod m) := by
      rw [h]; ring
    have hu : IsUnit ((-2 : ZMod m)) := (two_isUnit_of_odd hm).neg
    exact hu.mul_left_cancel h2
  have h3 : ((t + 1 : ℕ) : ZMod m) = 0 := by
    rw [Nat.cast_add, Nat.cast_one, h1]; ring
  exact absurd h3 (zmod_natCast_ne_zero (by omega) (by omega))

/-- Phase 2 iterate for cycle 1: at generic fibers (s ≠ 0, s ≠ -1), cycle 1 bumps i.
Starting at fiber s with 1 ≤ s and s + n ≤ m − 1, bumps i for n steps. -/
private theorem claudeStep1_iter_bumpI {m : ℕ} [NeZero m] (hm' : 1 < m)
    (i j k : ZMod m) (n s : ℕ) (hs : 1 ≤ s) (hsn : s + n ≤ m - 1)
    (hfib : fiber (i, j, k) = (s : ZMod m)) :
    (claudeStep 1)^[n] (i, j, k) = (i + (n : ZMod m), j, k) := by
  induction n generalizing i k s with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ, Function.comp_apply]
    have hs0 : fiber (i, j, k) ≠ 0 := by
      rw [hfib]; exact zmod_natCast_ne_zero (by omega) (by omega)
    have hs1 : fiber (i, j, k) ≠ -1 := by
      rw [hfib]; intro h
      have : ((s + 1 : ℕ) : ZMod m) = 0 := by
        have : (s : ZMod m) + 1 = 0 := by rw [h]; ring
        rwa [← Nat.cast_one, ← Nat.cast_add] at this
      exact absurd this (zmod_natCast_ne_zero (by omega) (by omega))
    have hdir : claudeDir (i, j, k) 1 = 0 := claudeDir_cycle1_mid hm' _ hs0 hs1
    simp only [claudeStep, hdir, bumpAt]
    have hfib' : fiber (i + 1, j, k) = ((s + 1 : ℕ) : ZMod m) := by
      simp only [fiber] at hfib ⊢
      rw [show (i + 1) + j + k = (i + j + k) + 1 from by ring, hfib]
      push_cast; ring
    rw [ih (i + 1) k (s + 1) (by omega) (by omega) hfib']
    refine Prod.ext ?_ (Prod.ext rfl rfl); push_cast; ring

/-- Return map for cycle 1, i ≠ 2 case.
After m steps, (i, j, −i−j) ↦ (i−2, j+1, 1−i−j). -/
private theorem returnMap1_ne2 {m : ℕ} [NeZero m] (_hm : Odd m) (hm' : 1 < m)
    (i j : ZMod m) (hi : i ≠ 2) :
    (claudeStep 1)^[m] (i, j, -i - j) = (i - 2, j + 1, -i - j + 1) := by
  rw [iterate_three_phases _ m (by omega)]
  -- Phase 1: at fiber 0, bump j
  have hfib0 : fiber (i, j, -i - j) = 0 := by simp [fiber]
  have hdir1 : claudeDir (i, j, -i - j) 1 = 1 := claudeDir_cycle1_s0 hm' _ hfib0
  simp only [claudeStep, hdir1, bumpAt]
  -- Phase 2: m-2 steps, bump i
  have hfib1 : fiber (i, j + 1, -i - j) = ((1 : ℕ) : ZMod m) := by
    simp [fiber]; ring
  rw [claudeStep1_iter_bumpI hm' i (j + 1) (-i - j) (m - 2) 1 (by omega) (by omega) hfib1]
  -- Phase 3: at fiber m-1, i-component is i + (m-2) = i - 2
  have hfib_last : fiber (i + ((m - 2 : ℕ) : ZMod m), j + 1, -i - j) = -1 := by
    simp only [fiber, zmod_natCast_m_sub_two (by omega : 2 ≤ m)]; ring
  have hi2 : i + ((m - 2 : ℕ) : ZMod m) ≠ 0 := by
    rw [zmod_natCast_m_sub_two (by omega : 2 ≤ m)]
    intro h; apply hi
    calc i = (i + (-2 : ZMod m)) + 2 := by ring
      _ = 0 + 2 := by rw [h]
      _ = 2 := by ring
  have hdir3 : claudeDir (i + ((m - 2 : ℕ) : ZMod m), j + 1, -i - j) 1 = 2 :=
    claudeDir_cycle1_s1_i hm' _ hfib_last hi2
  simp only [hdir3]
  refine Prod.ext ?_ (Prod.ext rfl ?_) <;> (rw [zmod_natCast_m_sub_two (by omega)]; try ring)

/-- Return map for cycle 1, i = 2 case.
After m steps, (2, j, −2−j) ↦ (0, j+2, −2−j). -/
private theorem returnMap1_eq2 {m : ℕ} [NeZero m] (_hm : Odd m) (hm' : 1 < m)
    (j : ZMod m) :
    (claudeStep 1)^[m] ((2 : ZMod m), j, -2 - j) = ((0 : ZMod m), j + 2, -2 - j) := by
  rw [iterate_three_phases _ m (by omega)]
  -- Phase 1: at fiber 0, bump j
  have hfib0 : fiber ((2 : ZMod m), j, -2 - j) = 0 := by simp [fiber]
  have hdir1 : claudeDir ((2 : ZMod m), j, -2 - j) 1 = 1 := claudeDir_cycle1_s0 hm' _ hfib0
  simp only [claudeStep, hdir1, bumpAt]
  -- Phase 2: m-2 steps, bump i
  have hfib1 : fiber ((2 : ZMod m), j + 1, -2 - j) = ((1 : ℕ) : ZMod m) := by
    simp [fiber]; ring
  rw [claudeStep1_iter_bumpI hm' 2 (j + 1) (-2 - j) (m - 2) 1 (by omega) (by omega) hfib1]
  -- Phase 3: at fiber m-1, i-component is 2 + (m-2) = 0
  have hfib_last : fiber ((2 : ZMod m) + ((m - 2 : ℕ) : ZMod m), j + 1, -2 - j) = -1 := by
    simp only [fiber, zmod_natCast_m_sub_two (by omega : 2 ≤ m)]; ring
  have hi0 : (2 : ZMod m) + ((m - 2 : ℕ) : ZMod m) = 0 := by
    rw [zmod_natCast_m_sub_two (by omega : 2 ≤ m)]; ring
  have hdir3 : claudeDir ((2 : ZMod m) + ((m - 2 : ℕ) : ZMod m), j + 1, -2 - j) 1 = 1 :=
    claudeDir_cycle1_s1_ni hm' _ hfib_last hi0
  simp only [hdir3]
  refine Prod.ext ?_ (Prod.ext ?_ rfl) <;> (rw [zmod_natCast_m_sub_two (by omega)]; try ring)

/-- Iterating the cycle 1 return map within a round: R₁^[k](0, n, −n) = (−2k, n+k, k−n). -/
private theorem returnMap1_ne2_iter {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (n : ZMod m) (k : ℕ) (hk : k ≤ m - 1) :
    ((claudeStep 1)^[m])^[k] ((0 : ZMod m), n, -n) =
      ((-2 : ZMod m) * (k : ZMod m), n + (k : ZMod m), (k : ZMod m) - n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply,
        ih (by omega)]
    have hi : (-2 : ZMod m) * (k : ZMod m) ≠ 2 := neg_two_mul_ne_two hm hm' k (by omega)
    conv_lhs => rw [show (k : ZMod m) - n = -((-2 : ZMod m) * (k : ZMod m)) - (n + (k : ZMod m)) from by ring]
    rw [returnMap1_ne2 hm hm' ((-2 : ZMod m) * k) (n + k) hi]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> push_cast <;> ring

/-- Generic helper: peel last application from iterate without rewriting n in types. -/
private theorem iterate_peel_last {α : Type*} (f : α → α) (n : ℕ) (hn : 0 < n) (x : α) :
    f^[n] x = f (f^[n - 1] x) := by
  conv_lhs => rw [show n = (n - 1) + 1 from by omega]
  simp only [Function.iterate_succ', Function.comp_apply]

/-- One full round of cycle 1 return map: R₁^[m](0, n, −n) = (0, n+1, −(n+1)). -/
private theorem returnMap1_round {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (n : ZMod m) :
    ((claudeStep 1)^[m])^[m] ((0 : ZMod m), n, -n) =
      ((0 : ZMod m), n + 1, -(n + 1)) := by
  rw [iterate_peel_last ((claudeStep 1)^[m]) m (by omega),
      returnMap1_ne2_iter hm hm' n (m - 1) (by omega)]
  -- State is now R₁(2, n-1, -1-n)
  have h1 : (-2 : ZMod m) * ((m - 1 : ℕ) : ZMod m) = 2 := by
    rw [zmod_natCast_m_sub_one (by omega)]; ring
  have h2 : n + ((m - 1 : ℕ) : ZMod m) = n - 1 := by
    rw [zmod_natCast_m_sub_one (by omega)]; ring
  have h3 : ((m - 1 : ℕ) : ZMod m) - n = -1 - n := by
    rw [zmod_natCast_m_sub_one (by omega)]
  rw [h1, h2, h3, show -1 - n = -2 - (n - 1) from by ring]
  rw [returnMap1_eq2 hm hm' (n - 1)]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> ring

/-- Iterating rounds of cycle 1: R₁^[nm](0, 0, 0) = (0, n, −n). -/
private theorem returnMap1_round_iter {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (n : ℕ) :
    ((claudeStep 1)^[m])^[n * m] ((0 : ZMod m), 0, 0) =
      ((0 : ZMod m), (n : ZMod m), -(n : ZMod m)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1) * m = m + n * m from by ring, Function.iterate_add_apply, ih,
        returnMap1_round hm hm' ↑n]
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> push_cast <;> ring

/-- The orbit of (0,0,0) under the return map (claudeStep c)^[m] covers all fiber-0 vertices.
This is the combinatorial core: Knuth's trajectory analysis shows that the fiber-0 checkpoints,
spaced m steps apart, eventually visit every (i, j, k) with i+j+k ≡ 0. -/
private theorem neg_two_mul_inv {m : ℕ} [NeZero m] (hm : Odd m) :
    (-2 : ZMod m) * (-2 : ZMod m)⁻¹ = 1 :=
  ZMod.mul_inv_of_unit (-2) ((two_isUnit_of_odd hm).neg)

private theorem two_mul_inv {m : ℕ} [NeZero m] (hm : Odd m) :
    (2 : ZMod m) * (2 : ZMod m)⁻¹ = 1 :=
  ZMod.mul_inv_of_unit 2 (two_isUnit_of_odd hm)

/-! ### Cycle 2 return map helpers -/

/-- Phase 2 iterate for cycle 2: at generic fibers (s ≠ 0, s ≠ -1), with i ≠ -1, cycle 2 bumps k. -/
private theorem claudeStep2_iter_bumpK {m : ℕ} [NeZero m] (hm' : 1 < m)
    (i j k : ZMod m) (n s : ℕ) (hs : 1 ≤ s) (hsn : s + n ≤ m - 1)
    (hi : i ≠ (-1 : ZMod m))
    (hfib : fiber (i, j, k) = (s : ZMod m)) :
    (claudeStep 2)^[n] (i, j, k) = (i, j, k + (n : ZMod m)) := by
  induction n generalizing j k s with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ, Function.comp_apply]
    have hs0 : fiber (i, j, k) ≠ 0 := by
      rw [hfib]; exact zmod_natCast_ne_zero (by omega) (by omega)
    have hs1 : fiber (i, j, k) ≠ -1 := by
      rw [hfib]; intro h
      have : ((s + 1 : ℕ) : ZMod m) = 0 := by
        have : (s : ZMod m) + 1 = 0 := by rw [h]; ring
        rwa [← Nat.cast_one, ← Nat.cast_add] at this
      exact absurd this (zmod_natCast_ne_zero (by omega) (by omega))
    have hdir : claudeDir (i, j, k) 2 = 2 := claudeDir_cycle2_mid_ni hm' _ hs0 hs1 hi
    simp only [claudeStep, hdir, bumpAt]
    have hfib' : fiber (i, j, k + 1) = ((s + 1 : ℕ) : ZMod m) := by
      simp only [fiber] at hfib ⊢
      rw [show i + j + (k + 1) = (i + j + k) + 1 from by ring, hfib]
      push_cast; ring
    rw [ih j (k + 1) (s + 1) (by omega) (by omega) hfib']
    refine Prod.ext rfl (Prod.ext rfl ?_); push_cast; ring

/-- Phase 2 iterate for cycle 2: at generic fibers, with i = -1, cycle 2 bumps j. -/
private theorem claudeStep2_iter_bumpJ {m : ℕ} [NeZero m] (hm' : 1 < m)
    (j k : ZMod m) (n s : ℕ) (hs : 1 ≤ s) (hsn : s + n ≤ m - 1)
    (hfib : fiber ((-1 : ZMod m), j, k) = (s : ZMod m)) :
    (claudeStep 2)^[n] ((-1 : ZMod m), j, k) = ((-1 : ZMod m), j + (n : ZMod m), k) := by
  induction n generalizing j k s with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ, Function.comp_apply]
    have hs0 : fiber ((-1 : ZMod m), j, k) ≠ 0 := by
      rw [hfib]; exact zmod_natCast_ne_zero (by omega) (by omega)
    have hs1 : fiber ((-1 : ZMod m), j, k) ≠ -1 := by
      rw [hfib]; intro h
      have : ((s + 1 : ℕ) : ZMod m) = 0 := by
        have : (s : ZMod m) + 1 = 0 := by rw [h]; ring
        rwa [← Nat.cast_one, ← Nat.cast_add] at this
      exact absurd this (zmod_natCast_ne_zero (by omega) (by omega))
    have hdir : claudeDir ((-1 : ZMod m), j, k) 2 = 1 := claudeDir_cycle2_mid_i hm' _ hs0 hs1 rfl
    simp only [claudeStep, hdir, bumpAt]
    have hfib' : fiber ((-1 : ZMod m), j + 1, k) = ((s + 1 : ℕ) : ZMod m) := by
      simp only [fiber] at hfib ⊢
      rw [show (-1 : ZMod m) + (j + 1) + k = ((-1) + j + k) + 1 from by ring, hfib]
      push_cast; ring
    rw [ih (j + 1) k (s + 1) (by omega) (by omega) hfib']
    refine Prod.ext rfl (Prod.ext ?_ rfl); push_cast; ring

/-- Return map for cycle 2, generic case: j ≠ -1, i ≠ -2.
After m steps, (i, j, −i−j) ↦ (i+2, j, −(i+2)−j). -/
private theorem returnMap2_generic {m : ℕ} [NeZero m] (_hm : Odd m) (hm' : 1 < m)
    (i j : ZMod m) (hj : j ≠ -1) (hi : i ≠ -2) :
    (claudeStep 2)^[m] (i, j, -i - j) = (i + 2, j, -(i + 2) - j) := by
  rw [iterate_three_phases _ m (by omega)]
  -- Phase 1: at fiber 0, j ≠ -1, bump i
  have hfib0 : fiber (i, j, -i - j) = 0 := by simp [fiber]
  have hdir1 : claudeDir (i, j, -i - j) 2 = 0 := claudeDir_cycle2_s0_nj hm' _ hfib0 hj
  simp only [claudeStep, hdir1, bumpAt]
  -- Phase 2: m-2 steps, i+1 ≠ -1 (since i ≠ -2), bump k
  have hi1 : i + 1 ≠ (-1 : ZMod m) := by
    intro h; apply hi
    have : i = (i + 1) - 1 := by ring
    rw [this, h]; ring
  have hfib1 : fiber (i + 1, j, -i - j) = ((1 : ℕ) : ZMod m) := by
    simp [fiber]
  rw [claudeStep2_iter_bumpK hm' (i + 1) j (-i - j) (m - 2) 1 (by omega) (by omega) hi1 hfib1]
  -- Phase 3: at fiber -1, bump i
  have hfib_last : fiber (i + 1, j, -i - j + ((m - 2 : ℕ) : ZMod m)) = -1 := by
    simp only [fiber, zmod_natCast_m_sub_two (by omega : 2 ≤ m)]; ring
  have hdir3 : claudeDir (i + 1, j, -i - j + ((m - 2 : ℕ) : ZMod m)) 2 = 0 :=
    claudeDir_cycle2_s1 hm' _ hfib_last
  simp only [hdir3]
  refine Prod.ext ?_ (Prod.ext rfl ?_) <;> (rw [zmod_natCast_m_sub_two (by omega)]; try ring)

/-- Return map for cycle 2, wrap case: j ≠ -1, i = -2.
After m steps, (−2, j, 2−j) ↦ (0, j−2, −(j−2)). -/
private theorem returnMap2_wrap {m : ℕ} [NeZero m] (_hm : Odd m) (hm' : 1 < m)
    (j : ZMod m) (hj : j ≠ -1) :
    (claudeStep 2)^[m] ((-2 : ZMod m), j, 2 - j) = ((0 : ZMod m), j - 2, -(j - 2)) := by
  rw [iterate_three_phases _ m (by omega)]
  -- Phase 1: bump i → (-1, j, 2-j)
  have hfib0 : fiber ((-2 : ZMod m), j, 2 - j) = 0 := by simp [fiber]
  have hdir1 : claudeDir ((-2 : ZMod m), j, 2 - j) 2 = 0 := claudeDir_cycle2_s0_nj hm' _ hfib0 hj
  simp only [claudeStep, hdir1, bumpAt, show (-2 : ZMod m) + 1 = -1 from by ring]
  -- Phase 2: m-2 steps, i = -1, bump j
  have hfib1 : fiber ((-1 : ZMod m), j, 2 - j) = ((1 : ℕ) : ZMod m) := by
    simp [fiber]; ring
  rw [claudeStep2_iter_bumpJ hm' j (2 - j) (m - 2) 1 (by omega) (by omega) hfib1]
  -- Phase 3: bump i
  have hfib_last : fiber ((-1 : ZMod m), j + ((m - 2 : ℕ) : ZMod m), 2 - j) = -1 := by
    simp only [fiber, zmod_natCast_m_sub_two (by omega : 2 ≤ m)]; ring
  have hdir3 : claudeDir ((-1 : ZMod m), j + ((m - 2 : ℕ) : ZMod m), 2 - j) 2 = 0 :=
    claudeDir_cycle2_s1 hm' _ hfib_last
  simp only [hdir3]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (rw [zmod_natCast_m_sub_two (by omega)]; try ring)

/-- Return map for cycle 2, transition case: j = -1, i ≠ -1.
After m steps, (i, −1, 1−i) ↦ (i+1, −1, −i). -/
private theorem returnMap2_transition {m : ℕ} [NeZero m] (_hm : Odd m) (hm' : 1 < m)
    (i : ZMod m) (hi : i ≠ -1) :
    (claudeStep 2)^[m] (i, -1, 1 - i) = (i + 1, -1, -i) := by
  rw [iterate_three_phases _ m (by omega)]
  -- Phase 1: j = -1, bump k → (i, -1, 2-i)
  have hfib0 : fiber (i, -1, 1 - i) = 0 := by simp [fiber]; ring
  have hdir1 : claudeDir (i, -1, 1 - i) 2 = 2 := claudeDir_cycle2_s0_j hm' _ hfib0 rfl
  simp only [claudeStep, hdir1, bumpAt, show (1 : ZMod m) - i + 1 = 2 - i from by ring]
  -- Phase 2: m-2 steps, i ≠ -1, bump k
  have hfib1 : fiber (i, -1, 2 - i) = ((1 : ℕ) : ZMod m) := by
    simp [fiber]; ring
  rw [claudeStep2_iter_bumpK hm' i (-1) (2 - i) (m - 2) 1 (by omega) (by omega) hi hfib1]
  -- Phase 3: bump i
  have hfib_last : fiber (i, -1, 2 - i + ((m - 2 : ℕ) : ZMod m)) = -1 := by
    simp only [fiber, zmod_natCast_m_sub_two (by omega : 2 ≤ m)]; ring
  have hdir3 : claudeDir (i, -1, 2 - i + ((m - 2 : ℕ) : ZMod m)) 2 = 0 :=
    claudeDir_cycle2_s1 hm' _ hfib_last
  simp only [hdir3]
  refine Prod.ext ?_ (Prod.ext rfl ?_) <;> (rw [zmod_natCast_m_sub_two (by omega)]; try ring)

/-- Return map for cycle 2, transition wrap: j = -1, i = -1.
After m steps, (−1, −1, 2) ↦ (0, −3, 3). -/
private theorem returnMap2_transition_wrap {m : ℕ} [NeZero m] (_hm : Odd m) (hm' : 1 < m) :
    (claudeStep 2)^[m] ((-1 : ZMod m), -1, 2) = ((0 : ZMod m), -3, 3) := by
  rw [iterate_three_phases _ m (by omega)]
  -- Phase 1: j = -1, bump k → (-1, -1, 3)
  have hfib0 : fiber ((-1 : ZMod m), -1, 2) = 0 := by simp [fiber]; ring
  have hdir1 : claudeDir ((-1 : ZMod m), -1, 2) 2 = 2 := claudeDir_cycle2_s0_j hm' _ hfib0 rfl
  simp only [claudeStep, hdir1, bumpAt, show (2 : ZMod m) + 1 = 3 from by ring]
  -- Phase 2: m-2 steps, i = -1, bump j
  have hfib1 : fiber ((-1 : ZMod m), -1, 3) = ((1 : ℕ) : ZMod m) := by
    simp [fiber]; ring
  rw [claudeStep2_iter_bumpJ hm' (-1) 3 (m - 2) 1 (by omega) (by omega) hfib1]
  -- Phase 3: bump i
  have hfib_last : fiber ((-1 : ZMod m), -1 + ((m - 2 : ℕ) : ZMod m), 3) = -1 := by
    simp only [fiber, zmod_natCast_m_sub_two (by omega : 2 ≤ m)]; ring
  have hdir3 : claudeDir ((-1 : ZMod m), -1 + ((m - 2 : ℕ) : ZMod m), 3) 2 = 0 :=
    claudeDir_cycle2_s1 hm' _ hfib_last
  simp only [hdir3]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> (rw [zmod_natCast_m_sub_two (by omega)]; try ring)

/-- 2 * (t : ℕ) ≠ -2 in ZMod m when t < m - 1. -/
private theorem two_mul_ne_neg_two {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (t : ℕ) (ht : t < m - 1) :
    (2 : ZMod m) * (t : ZMod m) ≠ -2 := by
  intro h
  have h1 : (t : ZMod m) = -1 := by
    have h2 : (2 : ZMod m) * (t : ZMod m) = (2 : ZMod m) * (-1 : ZMod m) := by
      rw [h]; ring
    have hu : IsUnit ((2 : ZMod m)) := two_isUnit_of_odd hm
    exact hu.mul_left_cancel h2
  have h3 : ((t + 1 : ℕ) : ZMod m) = 0 := by
    rw [Nat.cast_add, Nat.cast_one, h1]; ring
  exact absurd h3 (zmod_natCast_ne_zero (by omega) (by omega))

/-- Iterating cycle 2 return map within a generic j-block: R₂^[k](0, j, −j) = (2k, j, −2k−j). -/
private theorem returnMap2_generic_iter {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (j : ZMod m) (hj : j ≠ -1) (k : ℕ) (hk : k ≤ m - 1) :
    ((claudeStep 2)^[m])^[k] ((0 : ZMod m), j, -j) =
      ((2 : ZMod m) * (k : ZMod m), j, -(2 : ZMod m) * (k : ZMod m) - j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply, ih (by omega)]
    have hi : (2 : ZMod m) * (k : ZMod m) ≠ -2 := two_mul_ne_neg_two hm hm' k (by omega)
    conv_lhs => rw [show -(2 : ZMod m) * (k : ZMod m) - j =
        -((2 : ZMod m) * (k : ZMod m)) - j from by ring]
    rw [returnMap2_generic hm hm' ((2 : ZMod m) * k) j hj hi]
    refine Prod.ext ?_ (Prod.ext rfl ?_) <;> push_cast <;> ring

/-- Iterating cycle 2 transition steps within j=-1 block: R₂^[k](0, -1, 1) = (k, -1, 1-k). -/
private theorem returnMap2_transition_iter {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (k : ℕ) (hk : k ≤ m - 1) :
    ((claudeStep 2)^[m])^[k] ((0 : ZMod m), -1, 1) =
      ((k : ZMod m), -1, 1 - (k : ZMod m)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply, ih (by omega)]
    have hi : (k : ZMod m) ≠ -1 := by
      intro h
      have : ((k + 1 : ℕ) : ZMod m) = 0 := by rw [Nat.cast_add, Nat.cast_one, h]; ring
      exact absurd this (zmod_natCast_ne_zero (by omega) (by omega))
    rw [returnMap2_transition hm hm' ↑k hi]
    refine Prod.ext ?_ (Prod.ext rfl ?_) <;> push_cast <;> ring

/-- One full j-block of cycle 2: generic case (j ≠ -1).
R₂^[m](0, j, −j) = (0, j−2, −(j−2)). -/
private theorem returnMap2_jblock_ne {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (j : ZMod m) (hj : j ≠ -1) :
    ((claudeStep 2)^[m])^[m] ((0 : ZMod m), j, -j) =
      ((0 : ZMod m), j - 2, -(j - 2)) := by
  rw [iterate_peel_last ((claudeStep 2)^[m]) m (by omega),
      returnMap2_generic_iter hm hm' j hj (m - 1) (by omega)]
  have h1 : (2 : ZMod m) * ((m - 1 : ℕ) : ZMod m) = -2 := by
    rw [zmod_natCast_m_sub_one (by omega)]; ring
  have h2 : -(2 : ZMod m) * ((m - 1 : ℕ) : ZMod m) = 2 := by
    rw [show -(2 : ZMod m) * ((m - 1 : ℕ) : ZMod m) = -(2 * ((m - 1 : ℕ) : ZMod m)) from by ring, h1]; ring
  rw [h1, h2]
  exact returnMap2_wrap hm hm' j hj

/-- One full j-block of cycle 2: transition case (j = -1).
R₂^[m](0, −1, 1) = (0, −3, 3). -/
private theorem returnMap2_jblock_eq {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m) :
    ((claudeStep 2)^[m])^[m] ((0 : ZMod m), -1, 1) =
      ((0 : ZMod m), -3, 3) := by
  rw [iterate_peel_last ((claudeStep 2)^[m]) m (by omega),
      returnMap2_transition_iter hm hm' (m - 1) (by omega)]
  rw [zmod_natCast_m_sub_one (by omega)]
  rw [show (1 : ZMod m) - (-1 : ZMod m) = 2 from by ring]
  rw [returnMap2_transition_wrap hm hm']

/-- One j-block round of cycle 2 (any j):
R₂^[m](0, j, −j) = (0, j−2, −(j−2)). -/
private theorem returnMap2_jblock {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (j : ZMod m) :
    ((claudeStep 2)^[m])^[m] ((0 : ZMod m), j, -j) =
      ((0 : ZMod m), j - 2, -(j - 2)) := by
  by_cases hj : j = -1
  · subst hj
    simp only [neg_neg, show (-1 : ZMod m) - 2 = -3 from by ring]
    exact returnMap2_jblock_eq hm hm'
  · exact returnMap2_jblock_ne hm hm' j hj

/-- Iterating j-block rounds of cycle 2: R₂^[nm](0, 0, 0) = (0, −2n, 2n). -/
private theorem returnMap2_jblock_iter {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (n : ℕ) :
    ((claudeStep 2)^[m])^[n * m] ((0 : ZMod m), 0, 0) =
      ((0 : ZMod m), -2 * (n : ZMod m), 2 * (n : ZMod m)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1) * m = m + n * m from by ring, Function.iterate_add_apply, ih]
    conv_lhs => rw [show (2 : ZMod m) * (n : ZMod m) = -(-2 * (n : ZMod m)) from by ring]
    rw [returnMap2_jblock hm hm' (-2 * ↑n)]
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> push_cast <;> ring

/-! ### Cycle 0 column traversal and chain -/

/-- One generic column traversal for cycle 0: m return-map steps take
(i, -2, 2-i) to (i+1, -2, 2-(i+1)), provided i ≠ 0, ≠ -1, and i+1 ≠ -1, ≠ 0. -/
private theorem returnMap0_column_traversal {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (i : ZMod m) (hi0 : i ≠ 0) (hi1 : i ≠ -1) (hi1' : i + 1 ≠ -1) (hi0' : i + 1 ≠ 0) :
    ((claudeStep 0)^[m])^[m] (i, -2, 2 - i) = (i + 1, -2, 2 - (i + 1)) := by
  conv_lhs => rw [show (2 : ZMod m) - i = -i - (-2 : ZMod m) from by ring]
  rw [iterate_peel_last ((claudeStep 0)^[m]) m (by omega),
      returnMap0_generic_iter hm hm' i (-2) (m - 1) hi0 hi1
        (fun t ht => neg_two_sub_ne_neg_one hm' t ht),
      zmod_natCast_m_sub_one (by omega)]
  simp only [show (-2 : ZMod m) - -1 = -1 from by ring,
             show -(i + (-1 : ZMod m)) = 1 - i from by ring]
  rw [returnMap0_transition hm hm' i hi1' hi0']
  refine Prod.ext rfl (Prod.ext rfl ?_); ring

/-- Chain of k generic column traversals for cycle 0.
Starting from (1, -2, 1), after k*m return-map steps, we reach (1+k, -2, 1-k). -/
private theorem returnMap0_column_chain {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (k : ℕ) (hk : ∀ t : ℕ, t < k →
      (1 : ZMod m) + (t : ZMod m) ≠ 0 ∧
      (1 : ZMod m) + (t : ZMod m) ≠ -1 ∧
      (1 : ZMod m) + (t : ZMod m) + 1 ≠ -1 ∧
      (1 : ZMod m) + (t : ZMod m) + 1 ≠ 0) :
    ((claudeStep 0)^[m])^[k * m] ((1 : ZMod m), -2, 1) =
      ((1 : ZMod m) + (k : ZMod m), -2, 1 - (k : ZMod m)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * m = m + k * m from by ring,
        Function.iterate_add_apply,
        ih (fun t ht => hk t (by omega))]
    have ⟨h0, h1, h1', h0'⟩ := hk k (by omega)
    conv_lhs => rw [show (1 : ZMod m) + ↑k = 1 + ↑k from rfl,
                     show (1 : ZMod m) - (k : ZMod m) = 2 - (1 + ↑k) from by ring]
    rw [returnMap0_column_traversal hm hm' (1 + ↑k) h0 h1 h1' h0']
    refine Prod.ext ?_ (Prod.ext rfl ?_) <;> push_cast <;> ring

/-- Non-hitting condition for i=0 iteration: 0 - 2*t ≠ -1 for t < val(inv2). -/
private theorem i0_nonhit {m : ℕ} [NeZero m] (hm : Odd m)
    (t : ℕ) (ht : t < ZMod.val ((2 : ZMod m)⁻¹)) :
    (0 : ZMod m) - 2 * (t : ZMod m) ≠ -1 := by
  intro h
  have h1 : (2 : ZMod m) * t = 1 := by
    calc (2 : ZMod m) * t = -(0 - 2 * ↑t) := by ring
      _ = -(-1 : ZMod m) := by rw [h]
      _ = 1 := by ring
  have h2 : (↑t : ZMod m) = (2 : ZMod m)⁻¹ :=
    (two_isUnit_of_odd hm).mul_left_cancel (by rw [h1, two_mul_inv hm])
  have h3 : t = ZMod.val ((2 : ZMod m)⁻¹) := by
    have := congr_arg ZMod.val h2
    rwa [ZMod.val_natCast_of_lt (by have := ZMod.val_lt ((2 : ZMod m)⁻¹); omega)] at this
  omega

/-- Non-hitting condition for i=0 iteration from j₀=-3: -3 - 2*t ≠ -1 for t < m-1. -/
private theorem i0_nonhit_from_neg3 {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (t : ℕ) (ht : t < m - 1) :
    (-3 : ZMod m) - 2 * (t : ZMod m) ≠ -1 := by
  intro h
  have h1 : (2 : ZMod m) * ↑t = 2 * (-1 : ZMod m) := by
    calc (2 : ZMod m) * ↑t = -(-3 - 2 * ↑t) - 3 := by ring
      _ = -(-1 : ZMod m) - 3 := by rw [h]
      _ = 2 * (-1 : ZMod m) := by ring
  have h2 : (↑t : ZMod m) = -1 := (two_isUnit_of_odd hm).mul_left_cancel h1
  have h3 : ((t + 1 : ℕ) : ZMod m) = 0 := by rw [Nat.cast_add, Nat.cast_one, h2]; ring
  exact absurd h3 (zmod_natCast_ne_zero (by omega) (by omega))

/-- 1 ≠ -1 in ZMod m when m is odd and m > 1 (equivalently, 2 ≠ 0). -/
private theorem zmod_one_ne_neg_one {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m) :
    (1 : ZMod m) ≠ -1 := by
  intro h
  have h2 : (2 : ZMod m) = 0 := by
    calc (2 : ZMod m) = 1 - (-1) := by ring
      _ = 0 := sub_eq_zero.mpr h
  have hm3 : 2 < m := by obtain ⟨k, hk⟩ := hm; omega
  exact absurd (show ((2 : ℕ) : ZMod m) = 0 from by push_cast; exact h2)
    (zmod_natCast_ne_zero (by omega) hm3)

/-- From (0,0,0), reach (1,-2,1) via val(inv2) i=0 steps + 1 transition. -/
private theorem returnMap0_reach_col1 {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m) :
    ((claudeStep 0)^[m])^[ZMod.val ((2 : ZMod m)⁻¹) + 1] ((0 : ZMod m), 0, 0) =
      ((1 : ZMod m), -2, 1) := by
  set inv2 := (2 : ZMod m)⁻¹ with inv2_def
  -- Step 1: val(inv2) i=0 steps to (0, -1, 1)
  have h1 : ((claudeStep 0)^[m])^[ZMod.val inv2] ((0 : ZMod m), 0, 0) =
      ((0 : ZMod m), -1, 1) := by
    conv_lhs => rw [show ((0 : ZMod m), (0 : ZMod m), (0 : ZMod m)) =
      ((0 : ZMod m), 0, -(0 : ZMod m)) from by simp]
    rw [returnMap0_i0_iter hm hm' 0 (ZMod.val inv2) (fun t ht => i0_nonhit hm t ht)]
    have : (↑(ZMod.val inv2) : ZMod m) = inv2 := ZMod.natCast_zmod_val _
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp only [this]
    · calc (0 : ZMod m) - 2 * inv2 = -(2 * inv2) := by ring
        _ = -1 := by rw [two_mul_inv hm]
    · calc -((0 : ZMod m) - 2 * inv2) = 2 * inv2 := by ring
        _ = 1 := two_mul_inv hm
  -- Step 2: 1 transition to (1, -2, 1)
  have h2 : (claudeStep 0)^[m] ((0 : ZMod m), -1, 1) = ((1 : ZMod m), -2, 1) := by
    have := returnMap0_transition hm hm' 0
      (by rw [zero_add]; exact zmod_one_ne_neg_one hm hm')
      (by rw [zero_add]; exact zmod_one_ne_zero hm')
    simp only [sub_zero, zero_add] at this; exact this
  -- Compose
  rw [show ZMod.val inv2 + 1 = 1 + ZMod.val inv2 from by omega,
      Function.iterate_add_apply, Function.iterate_one, h1, h2]

/-- Column chain conditions: for t < val(i-1) with i ≠ 0, i ≠ -1, all four conditions hold. -/
private theorem column_chain_conds {m : ℕ} [NeZero m] (hm' : 1 < m)
    (i : ZMod m) (hi0 : i ≠ 0) (hi1 : i ≠ -1) (t : ℕ) (ht : t < ZMod.val (i - 1)) :
    (1 : ZMod m) + ↑t ≠ 0 ∧ (1 : ZMod m) + ↑t ≠ -1 ∧
    (1 : ZMod m) + ↑t + 1 ≠ -1 ∧ (1 : ZMod m) + ↑t + 1 ≠ 0 := by
  -- val(i-1) ≤ m-3 because i ≠ 0 (so i-1 ≠ -1) and i ≠ -1 (so i-1 ≠ -2)
  have hv := ZMod.val_lt (i - 1)
  have hne1 : ZMod.val (i - 1) ≠ m - 1 := by
    intro h; apply hi0
    have := ZMod.natCast_zmod_val (i - 1)
    rw [h, zmod_natCast_m_sub_one (by omega)] at this
    calc i = (i - 1) + 1 := by ring
      _ = -1 + 1 := by rw [← this]
      _ = 0 := by ring
  have hne2 : ZMod.val (i - 1) ≠ m - 2 := by
    intro h; apply hi1
    have := ZMod.natCast_zmod_val (i - 1)
    rw [h, zmod_natCast_m_sub_two (by omega)] at this
    calc i = (i - 1) + 1 := by ring
      _ = -2 + 1 := by rw [← this]
      _ = -1 := by ring
  -- So t + 4 ≤ m
  have htb : t + 4 ≤ m := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 1 + t ≠ 0
    intro h
    exact absurd (show ((t + 1 : ℕ) : ZMod m) = 0 from by
      rw [show ((t + 1 : ℕ) : ZMod m) = (1 : ZMod m) + ↑t from by push_cast; ring]; exact h)
      (zmod_natCast_ne_zero (by omega) (by omega))
  · -- 1 + t ≠ -1
    intro h
    have : ((t + 2 : ℕ) : ZMod m) = 0 := by
      have : (1 : ZMod m) + ↑t + 1 = -1 + 1 := by rw [h]
      rw [show (-1 : ZMod m) + 1 = 0 from by ring] at this
      rw [show ((t + 2 : ℕ) : ZMod m) = (1 : ZMod m) + ↑t + 1 from by push_cast; ring]
      exact this
    exact absurd this (zmod_natCast_ne_zero (by omega) (by omega))
  · -- 2 + t ≠ -1
    intro h
    have : ((t + 3 : ℕ) : ZMod m) = 0 := by
      have : (1 : ZMod m) + ↑t + 1 + 1 = -1 + 1 := by rw [h]
      rw [show (-1 : ZMod m) + 1 = 0 from by ring] at this
      rw [show ((t + 3 : ℕ) : ZMod m) = (1 : ZMod m) + ↑t + 1 + 1 from by push_cast; ring]
      exact this
    exact absurd this (zmod_natCast_ne_zero (by omega) (by omega))
  · -- 2 + t ≠ 0
    intro h
    exact absurd (show ((t + 2 : ℕ) : ZMod m) = 0 from by
      rw [show ((t + 2 : ℕ) : ZMod m) = (1 : ZMod m) + ↑t + 1 from by push_cast; ring]; exact h)
      (zmod_natCast_ne_zero (by omega) (by omega))

/-- Reach generic (i, j, -i-j) for i ≠ 0, i ≠ -1 via cycle 0 return map. -/
private theorem returnMap0_reach_generic {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (i j : ZMod m) (hi0 : i ≠ 0) (hi1 : i ≠ -1) :
    ∃ n, ((claudeStep 0)^[m])^[n] ((0 : ZMod m), 0, 0) = (i, j, -i - j) := by

  set k_col := ZMod.val (i - 1)
  set k_j := ZMod.val (-2 - j)
  -- Step 1: R^(val inv2 + 1)(0,0,0) = (1,-2,1)
  have h1 := returnMap0_reach_col1 hm hm'
  -- Step 2: R^(k_col*m)(1,-2,1) = (i,-2,2-i)
  have hk_col_val : (k_col : ZMod m) = i - 1 := ZMod.natCast_zmod_val _
  have h2 : ((claudeStep 0)^[m])^[k_col * m] ((1 : ZMod m), -2, 1) = (i, -2, 2 - i) := by
    rw [returnMap0_column_chain hm hm' k_col (fun t ht => column_chain_conds hm' i hi0 hi1 t ht)]
    refine Prod.ext ?_ (Prod.ext rfl ?_) <;> rw [hk_col_val] <;> ring
  -- Step 3: R^k_j(i,-2,2-i) = (i,j,-i-j)
  have h3 : ((claudeStep 0)^[m])^[k_j] (i, -2, 2 - i) = (i, j, -i - j) := by
    conv_lhs => rw [show (2 : ZMod m) - i = -i - (-2 : ZMod m) from by ring]
    rw [returnMap0_generic_iter hm hm' i (-2) k_j hi0 hi1
          (fun t ht => neg_two_sub_ne_neg_one hm' t (by have := ZMod.val_lt (-2 - j); omega))]
    have hk_j_val : (k_j : ZMod m) = -2 - j := ZMod.natCast_zmod_val _
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> rw [hk_j_val] <;> ring
  -- Compose: total = k_j + k_col*m + (val inv2 + 1)
  refine ⟨k_j + k_col * m + (ZMod.val ((2 : ZMod m)⁻¹) + 1), ?_⟩
  rw [show k_j + k_col * m + (ZMod.val ((2 : ZMod m)⁻¹) + 1) =
        k_j + (k_col * m + (ZMod.val ((2 : ZMod m)⁻¹) + 1)) from by omega,
      Function.iterate_add_apply,
      show k_col * m + (ZMod.val ((2 : ZMod m)⁻¹) + 1) =
        k_col * m + (ZMod.val ((2 : ZMod m)⁻¹) + 1) from rfl,
      Function.iterate_add_apply, h1, h2, h3]

/-- Reach (-1, 0, 1) via cycle 0 return map. -/
private theorem returnMap0_reach_im1_base {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m) :
    ∃ n, ((claudeStep 0)^[m])^[n] ((0 : ZMod m), 0, 0) = ((-1 : ZMod m), 0, 1) := by

  set inv2 := (2 : ZMod m)⁻¹
  have hm3 : 2 < m := by obtain ⟨k, hk⟩ := hm; omega
  -- Step 1: R^(val inv2+1)(0,0,0) = (1,-2,1)
  have h1 := returnMap0_reach_col1 hm hm'
  -- Step 2: R^((m-3)*m)(1,-2,1) = (-2,-2,4)
  have hm3_val : ((m - 3 : ℕ) : ZMod m) = -3 := by
    have : ((m - 3 : ℕ) : ZMod m) = (m : ZMod m) - 3 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this, ZMod.natCast_self, zero_sub]
  have hi0_neg2 : (-2 : ZMod m) ≠ 0 := by
    intro h
    exact absurd (show ((2 : ℕ) : ZMod m) = 0 from by
      have : (2 : ZMod m) = 0 := by
        calc (2 : ZMod m) = -(-2 : ZMod m) := by ring
          _ = -(0 : ZMod m) := by rw [h]
          _ = 0 := by ring
      push_cast; exact this) (zmod_natCast_ne_zero (by omega) hm3)
  have hi1_neg2 : (-2 : ZMod m) ≠ -1 := by
    intro h
    exact absurd (show ((1 : ℕ) : ZMod m) = 0 from by
      have : (1 : ZMod m) = 0 := by
        have h2 : (2 : ZMod m) = 1 := by
          calc (2 : ZMod m) = -(-2 : ZMod m) := by ring
            _ = -(-1 : ZMod m) := by rw [h]
            _ = 1 := by ring
        calc (1 : ZMod m) = 2 - 1 := by ring
          _ = 1 - 1 := by rw [h2]
          _ = 0 := by ring
      push_cast; exact this) (zmod_natCast_ne_zero (by omega) (by omega))
  have h2 : ((claudeStep 0)^[m])^[(m - 3) * m] ((1 : ZMod m), -2, 1) = ((-2 : ZMod m), -2, 4) := by
    rw [returnMap0_column_chain hm hm' (m - 3) (fun t ht => by
          refine column_chain_conds hm' (-2 : ZMod m) hi0_neg2 hi1_neg2 t ?_
          have : ZMod.val ((-2 : ZMod m) - 1) = m - 3 := by
            rw [show (-2 : ZMod m) - 1 = -3 from by ring, ← hm3_val,
                ZMod.val_natCast_of_lt (by omega)]
          omega)]
    refine Prod.ext ?_ (Prod.ext rfl ?_) <;> rw [hm3_val] <;> ring
  -- Step 3: R^(m-1)(-2,-2,4) = (-2,-1,3)
  have h3 : ((claudeStep 0)^[m])^[m - 1] ((-2 : ZMod m), -2, 4) = ((-2 : ZMod m), -1, 3) := by
    conv_lhs => rw [show (4 : ZMod m) = -(-2) - (-2 : ZMod m) from by ring]
    rw [returnMap0_generic_iter hm hm' (-2) (-2) (m - 1) hi0_neg2 hi1_neg2
          (fun t ht => neg_two_sub_ne_neg_one hm' t (by omega)),
        zmod_natCast_m_sub_one (by omega)]
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> ring
  -- Step 4: R(-2,-1,3) = (-1,0,1)
  have h4 : (claudeStep 0)^[m] ((-2 : ZMod m), -1, 3) = ((-1 : ZMod m), 0, 1) := by
    conv_lhs => rw [show (3 : ZMod m) = 3 - (m : ZMod m) from by rw [ZMod.natCast_self]; ring]
    exact returnMap0_transition_to_last hm hm'
  -- Compose: total = 1 + (m-1) + (m-3)*m + (val inv2+1) [rightmost applied first]
  refine ⟨1 + (m - 1) + (m - 3) * m + (ZMod.val inv2 + 1), ?_⟩
  rw [show 1 + (m - 1) + (m - 3) * m + (ZMod.val inv2 + 1) =
        1 + ((m - 1) + ((m - 3) * m + (ZMod.val inv2 + 1))) from by omega,
      Function.iterate_add_apply, Function.iterate_one,
      show (m - 1) + ((m - 3) * m + (ZMod.val inv2 + 1)) =
        (m - 1) + ((m - 3) * m + (ZMod.val inv2 + 1)) from rfl,
      Function.iterate_add_apply,
      show (m - 3) * m + (ZMod.val inv2 + 1) =
        (m - 3) * m + (ZMod.val inv2 + 1) from rfl,
      Function.iterate_add_apply, h1, h2, h3, h4]

/-- Reach any (-1, j, 1-j) via cycle 0 return map. -/
private theorem returnMap0_reach_im1 {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (j : ZMod m) :
    ∃ n, ((claudeStep 0)^[m])^[n] ((0 : ZMod m), 0, 0) = ((-1 : ZMod m), j, 1 - j) := by

  obtain ⟨n₀, hn₀⟩ := returnMap0_reach_im1_base hm hm'
  set k := ZMod.val j
  -- R^k(-1,0,1) = (-1,j,1-j)
  have hk : ((claudeStep 0)^[m])^[k] ((-1 : ZMod m), 0, 1) = ((-1 : ZMod m), j, 1 - j) := by
    conv_lhs => rw [show ((-1 : ZMod m), (0 : ZMod m), (1 : ZMod m)) =
      ((-1 : ZMod m), 0, 1 - 0) from Prod.ext rfl (Prod.ext rfl (sub_zero _).symm)]
    rw [returnMap0_im1_iter hm hm' 0 k (fun t ht => by
          intro h
          have : ((t + 1 : ℕ) : ZMod m) = 0 := by
            rw [show ((t + 1 : ℕ) : ZMod m) = (0 : ZMod m) + ↑t + 1 from by push_cast; ring, h]
            ring
          exact absurd this (zmod_natCast_ne_zero (by omega) (by have := ZMod.val_lt j; omega)))]
    have hk_val : (k : ZMod m) = j := ZMod.natCast_zmod_val _
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> rw [hk_val] <;> ring
  -- Compose: k + n₀ (rightmost n₀ applied first)
  exact ⟨k + n₀, by rw [Function.iterate_add_apply, hn₀, hk]⟩

/-- Reach any (0, j, -j) via cycle 0 return map. -/
private theorem returnMap0_reach_i0 {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (j : ZMod m) :
    ∃ n, ((claudeStep 0)^[m])^[n] ((0 : ZMod m), 0, 0) = ((0 : ZMod m), j, -j) := by

  -- Step 1: reach (-1, -1, 2)
  obtain ⟨n₀, hn₀⟩ := returnMap0_reach_im1 hm hm' (-1 : ZMod m)
  have h_start : ((-1 : ZMod m), (-1 : ZMod m), 1 - (-1 : ZMod m)) = ((-1 : ZMod m), -1, 2) :=
    Prod.ext rfl (Prod.ext rfl (by ring))
  rw [h_start] at hn₀
  -- Step 2: R(-1,-1,2) = (0,-3,3)
  have h_wrap := returnMap0_wrap hm hm'
  -- Step 3: R^k(0,-3,3) = (0,j,-j)
  set inv2 := (2 : ZMod m)⁻¹
  set k := ZMod.val (inv2 * (-3 - j))
  have h3 : ((claudeStep 0)^[m])^[k] ((0 : ZMod m), -3, 3) = ((0 : ZMod m), j, -j) := by
    rw [show ((0 : ZMod m), (-3 : ZMod m), (3 : ZMod m)) =
          ((0 : ZMod m), -3, -(-3 : ZMod m)) from
        Prod.ext rfl (Prod.ext rfl (neg_neg (3 : ZMod m)).symm)]
    rw [returnMap0_i0_iter hm hm' (-3) k (fun t ht =>
          i0_nonhit_from_neg3 hm hm' t (by have := ZMod.val_lt (inv2 * (-3 - j)); omega))]
    have hk_val : (k : ZMod m) = inv2 * (-3 - j) := ZMod.natCast_zmod_val _
    have h_j : (-3 : ZMod m) - 2 * (inv2 * (-3 - j)) = j := by
      calc (-3 : ZMod m) - 2 * (inv2 * (-3 - j)) = -3 + 2 * inv2 * (3 + j) := by ring
        _ = -3 + 1 * (3 + j) := by rw [two_mul_inv hm]
        _ = j := by ring
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> rw [hk_val]
    · exact h_j
    · rw [show -(-3 - 2 * (inv2 * (-3 - j))) = -((-3 : ZMod m) - 2 * (inv2 * (-3 - j))) from rfl,
          h_j]
  -- Compose: k + 1 + n₀
  have h_mid : ((claudeStep 0)^[m])^[1 + n₀] ((0 : ZMod m), 0, 0) = ((0 : ZMod m), -3, 3) := by
    rw [Function.iterate_add_apply, Function.iterate_one, hn₀, h_wrap]
  exact ⟨k + (1 + n₀), by rw [Function.iterate_add_apply, h_mid, h3]⟩

private theorem claudeStep_fiber0_orbit {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (c : Fin 3) (v : Vertex m) (hv : fiber v = 0) :
    ∃ n : ℕ, (claudeStep c)^[n] (0, 0, 0) = v := by
  obtain ⟨i, j, k⟩ := v
  simp only [fiber] at hv
  have hk : k = -i - j := by
    calc k = i + j + k + (-i - j) := by ring
      _ = 0 + (-i - j) := by rw [hv]
      _ = -i - j := by ring
  subst hk
  fin_cases c
  · -- c = 0
    by_cases hi0 : i = 0
    · subst hi0
      obtain ⟨n, hn⟩ := returnMap0_reach_i0 hm hm' j
      have : -(0 : ZMod m) - j = -j := by ring
      rw [this]
      exact ⟨n * m, iterate_return_map _ m _ _ _ hn⟩
    · by_cases hi1 : i = -1
      · subst hi1
        obtain ⟨n, hn⟩ := returnMap0_reach_im1 hm hm' j
        have : (1 : ZMod m) - j = -(-1 : ZMod m) - j := by ring
        rw [this] at hn
        exact ⟨n * m, iterate_return_map _ m _ _ _ hn⟩
      · obtain ⟨n, hn⟩ := returnMap0_reach_generic hm hm' i j hi0 hi1
        exact ⟨n * m, iterate_return_map _ m _ _ _ hn⟩
  · -- c = 1
    -- Use cycle 1 return map: after n₀ rounds and k₀ within-round steps,
    -- we reach any fiber-0 vertex.
    -- Key: (-2) is a unit mod odd m, so -2k ranges over all of ZMod m.
    set inv2 := (-2 : ZMod m)⁻¹ with inv2_def
    by_cases hi : i = 2
    · -- i = 2: need k₀ = m - 1 return map steps within a round
      subst hi
      set n₀ := ZMod.val (j + 1)
      -- After n₀ rounds: (0, ↑n₀, -↑n₀)
      -- After m-1 more return map steps: (2, ↑n₀ - 1, -1 - ↑n₀) = (2, j, -2-j)
      suffices h : ((claudeStep 1)^[m])^[(m - 1) + n₀ * m] ((0 : ZMod m), 0, 0) =
          ((2 : ZMod m), j, -2 - j) from
        ⟨((m - 1) + n₀ * m) * m, iterate_return_map _ m _ _ _ h⟩
      rw [Function.iterate_add_apply, returnMap1_round_iter hm hm' n₀,
          returnMap1_ne2_iter hm hm' ↑n₀ (m - 1) (by omega)]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · -- -2 * (m-1) = 2
        rw [zmod_natCast_m_sub_one (by omega)]; ring
      · -- ↑n₀ + (m-1) = j
        rw [zmod_natCast_m_sub_one (by omega)]
        rw [ZMod.natCast_zmod_val]; ring
      · -- (m-1) - ↑n₀ = -2 - j
        rw [zmod_natCast_m_sub_one (by omega)]
        rw [ZMod.natCast_zmod_val]; ring
    · -- i ≠ 2: use (-2)⁻¹ * i to find the within-round step
      set k₀ := ZMod.val (inv2 * i) with k₀_def
      set n₀ := ZMod.val (j - (k₀ : ZMod m)) with n₀_def
      suffices h : ((claudeStep 1)^[m])^[n₀ * m + k₀] ((0 : ZMod m), 0, 0) =
          (i, j, -i - j) from
        ⟨(n₀ * m + k₀) * m, iterate_return_map _ m _ _ _ h⟩
      rw [show n₀ * m + k₀ = k₀ + n₀ * m from by omega,
          Function.iterate_add_apply, returnMap1_round_iter hm hm' n₀,
          returnMap1_ne2_iter hm hm' ↑n₀ k₀ (by exact Nat.le_sub_one_of_lt (ZMod.val_lt _))]
      have hk₀_val : (k₀ : ZMod m) = inv2 * i := ZMod.natCast_zmod_val _
      have hn₀_val : (n₀ : ZMod m) = j - inv2 * i := by
        rw [n₀_def, ZMod.natCast_zmod_val, hk₀_val]
      have h2inv : (2 : ZMod m) * inv2 = -1 := by
        calc (2 : ZMod m) * inv2 = -((-2) * inv2) := by ring
          _ = -(1 : ZMod m) := by rw [neg_two_mul_inv hm]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · -- -2 * ↑k₀ = i
        rw [hk₀_val]
        calc (-2 : ZMod m) * (inv2 * i) = ((-2) * inv2) * i := by ring
          _ = 1 * i := by rw [neg_two_mul_inv hm]
          _ = i := one_mul i
      · -- ↑n₀ + ↑k₀ = j
        rw [hn₀_val, hk₀_val]; ring
      · -- ↑k₀ - ↑n₀ = -i - j
        rw [hk₀_val, hn₀_val]
        calc inv2 * i - (j - inv2 * i) = 2 * inv2 * i - j := by ring
          _ = (-1) * i - j := by rw [h2inv]
          _ = -i - j := by ring
  · -- c = 2
    -- Use cycle 2 return map: j-blocks of m² return map steps, within-block generic/transition.
    set inv2 := (2 : ZMod m)⁻¹ with inv2_def
    by_cases hj : j = -1
    · -- j = -1: use transition within j=-1 block
      subst hj
      set n₀ := ZMod.val inv2 with n₀_def
      set k₀ := ZMod.val i with k₀_def
      suffices h : ((claudeStep 2)^[m])^[n₀ * m + k₀] ((0 : ZMod m), 0, 0) =
          (i, -1, -i - (-1 : ZMod m)) from
        ⟨(n₀ * m + k₀) * m, iterate_return_map _ m _ _ _ h⟩
      rw [show n₀ * m + k₀ = k₀ + n₀ * m from by omega,
          Function.iterate_add_apply, returnMap2_jblock_iter hm hm' n₀]
      -- After n₀ j-blocks: (0, -2*↑n₀, 2*↑n₀). Need -2*↑n₀ = -1 and 2*↑n₀ = 1.
      have hn₀_val : (n₀ : ZMod m) = inv2 := ZMod.natCast_zmod_val _
      have h_j : (-2 : ZMod m) * ↑n₀ = -1 := by
        rw [hn₀_val]; calc (-2 : ZMod m) * inv2 = -(2 * inv2) := by ring
          _ = -(1 : ZMod m) := by rw [two_mul_inv hm]
          _ = -1 := by ring
      have h_k : (2 : ZMod m) * ↑n₀ = 1 := by
        rw [hn₀_val, two_mul_inv hm]
      simp only [h_j, h_k]
      -- Now at (0, -1, 1). Use transition iteration.
      rw [returnMap2_transition_iter hm hm' k₀ (by exact Nat.le_sub_one_of_lt (ZMod.val_lt _))]
      have hk₀_val : (k₀ : ZMod m) = i := ZMod.natCast_zmod_val _
      refine Prod.ext ?_ (Prod.ext rfl ?_)
      · exact hk₀_val
      · rw [hk₀_val]; ring
    · -- j ≠ -1: use generic iteration within a j-block
      set n₀ := ZMod.val (-(inv2 * j)) with n₀_def
      set k₀ := ZMod.val (inv2 * i) with k₀_def
      suffices h : ((claudeStep 2)^[m])^[n₀ * m + k₀] ((0 : ZMod m), 0, 0) =
          (i, j, -i - j) from
        ⟨(n₀ * m + k₀) * m, iterate_return_map _ m _ _ _ h⟩
      rw [show n₀ * m + k₀ = k₀ + n₀ * m from by omega,
          Function.iterate_add_apply, returnMap2_jblock_iter hm hm' n₀]
      -- After n₀ j-blocks: (0, -2*↑n₀, 2*↑n₀). Need -2*↑n₀ = j.
      have hn₀_val : (n₀ : ZMod m) = -(inv2 * j) := ZMod.natCast_zmod_val _
      have h_j : (-2 : ZMod m) * ↑n₀ = j := by
        rw [hn₀_val]; calc (-2 : ZMod m) * (-(inv2 * j)) = 2 * inv2 * j := by ring
          _ = 1 * j := by rw [two_mul_inv hm]
          _ = j := one_mul j
      have h_nj : (-2 : ZMod m) * ↑n₀ ≠ -1 := by rw [h_j]; exact hj
      have h_negj : (2 : ZMod m) * ↑n₀ = -j := by
        calc (2 : ZMod m) * ↑n₀ = -((-2) * ↑n₀) := by ring
          _ = -j := by rw [h_j]
      simp only [h_j, h_negj]
      -- Now at (0, j, -j) with j ≠ -1. Use generic iteration.
      rw [returnMap2_generic_iter hm hm' j hj k₀
          (by exact Nat.le_sub_one_of_lt (ZMod.val_lt _))]
      have hk₀_val : (k₀ : ZMod m) = inv2 * i := ZMod.natCast_zmod_val _
      have h_i : (2 : ZMod m) * ↑k₀ = i := by
        rw [hk₀_val]; calc (2 : ZMod m) * (inv2 * i) = (2 * inv2) * i := by ring
          _ = 1 * i := by rw [two_mul_inv hm]
          _ = i := one_mul i
      refine Prod.ext ?_ (Prod.ext rfl ?_)
      · exact h_i
      · show -2 * ↑k₀ - j = -i - j
        have : -2 * (k₀ : ZMod m) = -i := by rw [show (-2 : ZMod m) * ↑k₀ = -(2 * ↑k₀) from by ring, h_i]
        rw [this]

/-- The orbit of (0,0,0) under `claudeStep c` covers all vertices.
This is the core lemma needed for IsCycle. -/
theorem claudeStep_orbit_surj {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m) (c : Fin 3)
    (v₀ : Vertex m) : ∀ v : Vertex m, ∃ n : ℕ, (claudeStep c)^[n] v₀ = v := by
  -- Suffices to prove for v₀ = (0,0,0) since claudeStep is bijective
  suffices h0 : ∀ v, ∃ n, (claudeStep c)^[n] (0, 0, 0) = v by
    intro v
    obtain ⟨a, ha⟩ := h0 v₀      -- f^[a](0,0,0) = v₀
    obtain ⟨b, hb⟩ := h0 v        -- f^[b](0,0,0) = v
    obtain ⟨w, hw⟩ := claudeStep_iter_surj hm hm' c a (0, 0, 0)  -- f^[a](w) = (0,0,0)
    obtain ⟨d, hd⟩ := h0 w        -- f^[d](0,0,0) = w
    -- f^[d+b](v₀) = f^[d+b](f^[a](0)) = f^[b](f^[d](f^[a](0))) ... but iterate_add goes left
    -- Use: f^[d+b](v₀) = f^[d+b](f^[a](0,0,0)). Rewrite as f^[a+(d+b)](0,0,0).
    -- Step 1: f^[d](v₀) = (0,0,0)
    -- f^[d](v₀) = f^[d](f^[a](0,0,0)) = f^[d+a](0,0,0) = f^[a+d](0,0,0)
    --           = f^[a](f^[d](0,0,0)) = f^[a](w) = (0,0,0)
    have step1 : (claudeStep c)^[d] v₀ = (0, 0, 0) := by
      conv_lhs => rw [← ha]
      rw [← Function.iterate_add_apply]
      rw [show d + a = a + d from Nat.add_comm d a]
      rw [Function.iterate_add_apply, hd, hw]
    -- Step 2: f^[b+d](v₀) = f^[b](f^[d](v₀)) = f^[b](0,0,0) = v
    exact ⟨b + d, by rw [Function.iterate_add_apply, step1, hb]⟩
  -- Now prove the orbit of (0,0,0) covers everything
  exact claudeStep_orbit_surj_of_fiber0 hm hm' c (claudeStep_fiber0_orbit hm hm' c)

/-! ## Hamiltonian cycle theorems -/

/-- The step function for each cycle, packaged as a permutation. -/
noncomputable def claudeStepPerm {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m) (c : Fin 3) :
    Equiv.Perm (Vertex m) :=
  Equiv.ofBijective (claudeStep c) (claudeStep_bijective hm hm' c)

/-- Power of claudeStepPerm applied to a vertex equals iteration of claudeStep. -/
private theorem claudeStepPerm_pow_apply {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m)
    (c : Fin 3) (n : ℕ) (v : Vertex m) :
    (claudeStepPerm hm hm' c ^ n) v = (claudeStep c)^[n] v := by
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ, Equiv.Perm.mul_apply, Function.iterate_succ, Function.comp_apply, ih]
    simp [claudeStepPerm, Equiv.ofBijective_apply]

/-- **Main theorem.** For odd m > 1, each of the three cycles defined by Claude's
construction is a directed Hamiltonian cycle on the cube digraph. -/
theorem claudeStep_isDirectedHamiltonianCycle
    {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m) (c : Fin 3) :
    IsDirectedHamiltonianCycle (cubeDigraph m) (claudeStepPerm hm hm' c) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Adjacency: each step is a valid arc
    intro v
    simp only [claudeStepPerm, Equiv.ofBijective_apply]
    exact claudeStep_adj c v
  · -- IsCycle: the permutation is a single cycle
    -- We use claudeStep_orbit_surj to show the orbit covers everything.
    have hsurj := claudeStep_orbit_surj hm hm' c (0, 0, 0)
    refine ⟨(0, 0, 0), ?_, fun y _ => ?_⟩
    · simp only [claudeStepPerm, Equiv.ofBijective_apply, ne_eq]
      exact claudeStep_ne_self hm' c _
    · obtain ⟨n, hn⟩ := hsurj y
      exact ⟨↑n, by rw [zpow_natCast, claudeStepPerm_pow_apply, hn]⟩
  · -- Full support: every vertex is moved
    ext v
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
    simp only [claudeStepPerm, Equiv.ofBijective_apply, ne_eq]
    exact claudeStep_ne_self hm' c v

/-- The cardinality of the vertex type is m³. -/
theorem vertex_card (m : ℕ) [NeZero m] : Fintype.card (Vertex m) = m ^ 3 := by
  simp [Vertex, Fintype.card_prod, ZMod.card]
  ring

