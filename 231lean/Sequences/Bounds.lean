import «231lean».Sequences.Convergence

def bounded_above (b : ℝ) (a : ℕ → ℝ) :=
  ∀ n, a n ≤ b

example (a : ℕ → ℝ) (h : ∀ n : ℕ, a n = a 0) :
    bounded_above (a 0) a := by
      unfold bounded_above
      intro n 
      rw[h]
