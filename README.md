# KnuthClaudeLean

Formalization of the results in Don Knuth's note "Claude's Cycles" (February-March 2026).

The note describes a construction, found by Claude Opus 4.6, that decomposes the arcs of a
certain digraph into three directed Hamiltonian cycles for all odd m > 1.

## The digraph

The digraph has m^3 vertices (i, j, k) for 0 <= i, j, k < m, with three arcs from each vertex:
to (i+1, j, k), (i, j+1, k), and (i, j, k+1), where arithmetic is mod m.

## Main result

`ClaudesCycles.hamiltonian_arc_decomposition`: For odd m > 1, the arcs of the cube digraph
can be decomposed into three directed Hamiltonian cycles.

## Verification with Comparator

This project is set up for independent verification using
[Comparator](https://github.com/leanprover/comparator), a trustworthy judge specifically
designed for verifying potentially adversarial proofs, including AI-generated proofs.

### Trust model

To trust the results of this formalization, you need to trust:

1. **The Lean kernel** (and optionally nanoda, if running in dual-kernel mode).
2. **Mathlib** (specifically the imports used: `ZMod`, `Equiv.Perm`, `Digraph`, etc.),
   or at least trust that Mathlib's definitions match standard mathematics.
3. **`Challenge.lean`** -- this is the key file to audit. It contains:
   - The definition of the cube digraph (`cubeDigraph`)
   - The definition of "directed Hamiltonian cycle" (`IsDirectedHamiltonianCycle`)
   - The theorem statement claiming the decomposition exists
4. **Comparator** itself, and its dependencies (`landrun`, `lean4export`).

You do **not** need to trust the ~1600 lines of proof in `KnuthClaudeLean/Basic.lean`.
Comparator verifies that the proof in the `Solution` module establishes the same theorem
stated in `Challenge.lean`, using only the permitted axioms (`propext`, `Quot.sound`,
`Classical.choice`).

### Installing dependencies

Comparator and lean4export should be checked out at the tag matching your Lean version
(this project uses v4.28.0):

```bash
git clone --branch v4.28.0 --depth 1 https://github.com/leanprover/comparator /tmp/comparator
git clone --branch v4.28.0 --depth 1 https://github.com/leanprover/lean4export /tmp/lean4export
cd /tmp/comparator && lake build
cd /tmp/lean4export && lake build
```

Download [landrun](https://github.com/Zouuup/landrun) (v0.1.14 or later):

```bash
gh release download v0.1.14 -R Zouuup/landrun -p "landrun-linux-amd64" -D /tmp/
chmod +x /tmp/landrun-linux-amd64
ln -s /tmp/landrun-linux-amd64 /usr/local/bin/landrun  # or add to PATH
```

### Running Comparator

```bash
# Ensure landrun and lean4export are in PATH
export PATH="/tmp/lean4export/.lake/build/bin:$PATH"

# Fetch the Mathlib cache
lake exe cache get

# Run Comparator
lake env /tmp/comparator/.lake/build/bin/comparator comparator.json
```

Expected output:
```
Building Challenge
Building Solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

### File layout

| File | Role | Trusted? |
|------|------|----------|
| `Challenge.lean` | Definitions + theorem statement (with `sorry`) | Yes -- audit this |
| `Solution.lean` | Wraps the proof to match Challenge's statement | No -- verified by Comparator |
| `KnuthClaudeLean/Basic.lean` | The actual proof | No -- verified by Comparator |
| `comparator.json` | Comparator configuration | Yes -- lists theorem name and permitted axioms |
