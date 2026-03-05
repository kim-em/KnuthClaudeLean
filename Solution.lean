import KnuthClaudeLean

namespace ClaudesCycles

theorem hamiltonian_arc_decomposition
    {m : ℕ} [NeZero m] (hm : Odd m) (hm' : 1 < m) :
    ∃ σ : Fin 3 → Equiv.Perm (Vertex m),
      (∀ c, IsDirectedHamiltonianCycle (cubeDigraph m) (σ c)) ∧
      (∀ v : Vertex m, ∀ b : Fin 3, ∃! c : Fin 3, σ c v = bumpAt b v) :=
  cube_hamiltonian_arc_decomposition hm hm'

end ClaudesCycles
