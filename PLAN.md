# Plan: Proof Order for KnuthClaudeLean

## Context

We want to reach a sorry-free proof of the **headline theorem** as quickly as possible:

```
claudeStep_isDirectedHamiltonianCycle:
  For odd m > 1, each of Claude's three cycles is a directed Hamiltonian cycle
  on the cube digraph (ZMod m)³.
```

This requires proving `IsDirectedHamiltonianCycle (cubeDigraph m) (claudeStepPerm hm hm' c)`,
which unfolds to three conjuncts:
1. **Adjacency**: `∀ v, (cubeDigraph m).Adj v (σ v)` — each step is a valid arc
2. **Single cycle**: `σ.IsCycle` — the permutation is a single cycle
3. **Full support**: `σ.support = Finset.univ` — every vertex is moved

## Revised Strategy (incorporating Codex feedback)

### Key insight: fiber dynamics approach

Following Knuth's proof structure more closely:

1. **`fiber_bumpAt`** (done): `fiber (bumpAt b v) = fiber v + 1` — each step advances the fiber
2. Therefore `step^[m]` maps fiber s back to fiber s
3. **No fixed points**: `claudeStep c v ≠ v` for `m > 1` (bumping any coordinate by 1 gives a different vertex)
4. **Single cycle via Knuth's column argument**: For cycle 0, coordinate i changes only when s = 0 and j = m−1. So m² vertices with a given i-value appear consecutively. Within each i-column, j advances while k adjusts, with k advancing by 2 mod m at each s = 0 return. Since m is odd, all residues are hit.

### `claudeStep_bijective` is NOT needed as a standalone theorem

If we prove the orbit of any vertex has size m³, bijectivity follows for free (orbit ⊆ m³ vertices, and the map is a permutation iff the single orbit covers everything). We can construct `claudeStepPerm` from the cycle proof itself.

### Uniform `1 < m` hypothesis on cycle rules

All cycle rule lemmas assume `(hm : 1 < m)` uniformly. This ensures `(1 : ZMod m) ≠ 0` (equivalently `(-1 : ZMod m) ≠ 0`), which is needed for branch separation in `claudeDir` when `fiber v = -1` and `fiber v = 0` branches would otherwise collapse. The headline theorem has `m > 1`, so this is a natural requirement.

## Phase 1: Easy foundations ✓ (mostly done)

### 1a. `fiber_bumpAt` ✓
### 1b. `vertex_card` ✓
### 1c. 15 cycle rule lemmas (in progress — need uniform `hm : 1 < m` fix)
- Add helper lemma: `zmod_one_ne_zero : 1 < m → (1 : ZMod m) ≠ 0`
- Add `(hm : 1 < m)` to all 15 cycle rule theorems
- Proofs become uniform: `simp only [claudeDir]; split_ifs <;> simp_all` (with `zmod_one_ne_zero hm` in context)

### 1d. `claudeStep_adj` ✓

## Phase 2: Arc partition (moderate, independent of headline)

### 2a. `claudeDir_bijective`
- **Difficulty**: Moderate
- **Strategy**: Case-split on the 6 branches. Each is a permutation of `Fin 3` — use `decide` or `Fin.cases`.

### 2b. `claude_arc_decomposition`
- **Difficulty**: Easy (given 2a)
- **Strategy**: Bijective → surjective gives existence, injective gives uniqueness → `∃!`.

## Phase 3: The headline — proving IsCycle

The only remaining `sorry` in the headline theorem is the `IsCycle` conjunct.
Adjacency and full support are already proved. We need to show `claudeStepPerm` is
a single cycle, i.e. the orbit of any vertex covers all m³ vertices.

### Strategy: orbit-covers-univ → IsCycle

We follow Knuth's proof from claude-cycles.md. The argument has three layers:

1. **One coordinate is "slow"**: it only changes at a specific fiber value.
   For cycle 0, `i` changes only when `s = 0 ∧ j = -1`. So vertices with the
   same `i` are consecutive in the orbit ("i-blocks" of m² steps each).

2. **Within each i-block, all m² pairs (j,k) appear**: Between consecutive
   s=0 checkpoints (m steps apart), j sweeps through values. At each s=0
   return, k advances by 2 mod m.

3. **Since m is odd, gcd(2,m) = 1**: iterating +2 hits all residues mod m,
   so all k values are reached. Combined with j sweeping, all m² pairs appear.

Total: m i-values × m² per block = m³ = |Vertex m| → single cycle.

### 3a. Bridge lemma ✓ (already available in Mathlib)

- **`isCycle_of_support_eq_univ`**: If σ.support = univ and the orbit of some
  vertex has size = Fintype.card, then σ.IsCycle. (Or: if support = univ and
  there exists a ∈ σ.support with ∀ b, ∃ n, (σ ^ n) a = b.)

### 3b. Trajectory lemmas for cycle 0

These formalize Knuth's proof for c = 0. Key lemmas:

**Layer 1 — i-block structure:**
- `cycle0_bumps_i_iff`: `claudeDir v 0 = 0 ↔ fiber v = 0 ∧ v.2.1 = -1`
  (follows from existing cycle rule lemmas)
- `cycle0_i_stable`: If `claudeDir v 0 ≠ 0` then `(claudeStep 0 v).1 = v.1`
  (i unchanged when not bumped)

**Layer 2 — Within a fiber pass (m steps from one s=0 to the next):**
- `cycle0_mid_bumps_j`: When `s ≠ 0, s ≠ -1, i ≠ -1`: step bumps j
- `cycle0_s1_bumps_j_or_k`: When `s = -1`: step bumps j (if i ≠ 0) or k (if i = 0)
- `cycle0_fiber_pass_trajectory`: Explicit description of m steps within a fiber pass

**Layer 3 — Checkpoint dynamics (what happens at each s=0 return):**
- `cycle0_checkpoint_k_shift`: At consecutive s=0 checkpoints within an i-block,
  k advances by 2 mod m
- `cycle0_all_checkpoints_distinct`: Since 2 is a unit mod odd m, all m checkpoints
  within an i-block have distinct (j,k) values

**Layer 4 — Complete coverage within i-block:**
- `cycle0_iblock_covers_all`: The m² steps of an i-block visit all m² vertices
  with that i-value
- Start vertex for i=0 block: (0, m-1, 2); for general 0 < i < m-1: (i, m-1, 2-i);
  for i = m-1: (m-1, m-1, 3)

**Layer 5 — Assembly:**
- `cycle0_orbit_eq_univ`: The orbit of (0, m-1, 2) under claudeStep 0 is all of Vertex m
- Therefore `claudeStepPerm` for c=0 is IsCycle

### 3c. Trajectory lemmas for cycles 1 and 2

Analogous to 3b but following Knuth's appendix:

**Cycle 1 (c = 1):** "slow coordinate" is also structured by fiber.
- s = 0: bump j. s ∈ (0, m-1): bump i. s = m-1: bump k (i ≠ 0) or j (i = 0).
- Checkpoint pattern: vertices at s=0 follow
  0·k(−k), (−2)(1+k)(1−k), (−4)(2+k)(2−k), ..., 2(−1+k)(−1−k)
  for k = 0, 1, ..., m−1.

**Cycle 2 (c = 2):** "slow coordinate" structure from appendix.
- s = 0, j < m-1: bump i. s = 0, j = m-1: bump k.
  s ∈ (0, m-1), i < m-1: bump k. s ∈ (0, m-1), i = m-1: bump j.
  s = m-1: bump i.
- Checkpoint pattern: vertices at s=0, j < m-1 follow
  0·j(−j), 2·j(−2−j), 4·j(−4−j), ..., (−2)j(2−j)

### 3d. Unifying the three cycles

Option A: Prove each cycle separately (3 similar proofs).
Option B: Abstract the common "layered orbit" pattern into a general lemma,
then instantiate for each cycle. Cleaner but more up-front work.

Decision: Start with cycle 0 in full detail. If the proof shape is clear enough,
refactor into a general lemma before doing cycles 1 and 2.

### Key Mathlib dependencies

- `Equiv.Perm.IsCycle` characterization
- `ZMod.isUnit_iff_coprime` (for 2 being a unit mod odd m — already have `two_isUnit_of_odd`)
- `ZMod.val_natCast`, `ZMod.natCast_zmod_eq_zero_iff_dvd` for modular arithmetic
- Possibly `MulAction.orbit` or `Equiv.Perm.cycleOf` machinery

### Key risks

1. **Formalizing "j sweeps all values"** within a fiber pass requires careful
   induction on the number of steps, tracking how j evolves through the cycle rules.
2. **The three cycles differ in detail**: cycle 2's appendix proof is more complex
   (two sub-patterns at s=0 depending on j).
3. **ZMod arithmetic**: converting between "k advances by 2" and "all residues hit"
   needs the right lemmas about units in ZMod.

## Phase 4: Optional extras (after headline is done)

### 4a. `no_decomposition_two` — finite computation for m = 2
### 4b. Counting theorems (11502, 4554, 1012, 996, 760) — `native_decide`
### 4c. `generalizable_five_seven_iff_all` — computational + combinatorial
### 4d. `claudeLike_valid_iff_generalizable` — generalizability characterization
### 4e. Symmetry theorems — computational

## Recommended proving order

| Step | Theorem(s) | Difficulty | Status |
|------|-----------|------------|--------|
| 1 | `fiber_bumpAt` | Easy | ✓ Done |
| 2 | `vertex_card` | Easy | ✓ Done |
| 3 | 15 cycle rule lemmas | Easy (batch) | ✓ Done |
| 4 | `claudeStep_adj` | Trivial | ✓ Done |
| 5 | `claudeStep_ne_self` | Easy | ✓ Done |
| 5b | `claudeStep_bijective` | Moderate | ✓ Done |
| 5c | `fiber_claudeStep`, `fiber_claudeStep_iter` | Easy | ✓ Done |
| 5d | `two_isUnit_of_odd` | Easy | ✓ Done |
| 6 | Trajectory helper lemmas (3b-3c) | Moderate-Hard | **IN PROGRESS** |
| 7 | **`claudeStep_isDirectedHamiltonianCycle`** | Hard | **2/3 done, IsCycle remains** |
| 8 | `claudeDir_bijective` | Moderate | ✓ Done |
| 9 | `claude_arc_decomposition` | Easy | ✓ Done |
| 10+ | Optional extras (4a–4e) | Various | Bonus |

## Key risks

1. **Formalizing Knuth's trajectory argument** (Step 6-7): The combinatorial argument about j,k evolution within i-columns requires careful modular arithmetic. The "k advances by 2" fact and "m odd → all residues hit" are clean but need the right Mathlib lemmas about `ZMod`.

2. **Three cycles, not just one**: Knuth proves cycle 0 in detail and defers cycles 1 and 2 to an appendix. We need analogous trajectory arguments for all three (or find a symmetry argument).

## Verification

After each theorem: check `lake build` compiles without errors. After the headline: verify zero `sorry`s remain in the critical path.
