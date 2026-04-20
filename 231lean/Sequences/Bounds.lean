import «231lean».Sequences.Convergence

def bounded_above (b : ℝ) (a : ℕ → ℝ) :=
  ∀ n, a n ≤ b

def bounded_below (b : ℝ) (a : ℕ → ℝ) :=
  ∀ n, b ≤ a n

example (a : ℕ → ℝ) (h : ∀ n : ℕ, a n = a 0) :
    bounded_above (a 0) a := by
      intro n 
      rw[h]

example (a : ℕ → ℝ) (h : ∀ n : ℕ, a n = a 0) :
    bounded_below (a 0) a := by
      intro n 
      rw[← h]
