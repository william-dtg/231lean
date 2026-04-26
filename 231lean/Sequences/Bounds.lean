import «231lean».Sequences.Convergence

def bounded_above (a : ℕ → ℝ) (b : ℝ) :=
  ∀ n, a n ≤ b

def bounded_below (a : ℕ → ℝ) (b : ℝ) :=
  ∀ n, b ≤ a n

def bounded (a : ℕ → ℝ) :=
  ∃ above, ∃ below, bounded_above a above ∧ bounded_below a below

lemma const_bounded_above (a : ℕ → ℝ) (h : ∀ n : ℕ, a n = a 0) :
    bounded_above a (a 0) := by
      intro n 
      rw[h]

lemma const_bounded_below (a : ℕ → ℝ) (h : ∀ n : ℕ, a n = a 0) :
    bounded_below  a (a 0) := by
      intro n 
      rw[← h]

theorem const_bounded (a : ℕ → ℝ) (h : ∀ n : ℕ, a n = a 0) :
    bounded a := by 
      use (a 0), (a 0)
      exact ⟨const_bounded_above a h, const_bounded_below a h⟩ 
