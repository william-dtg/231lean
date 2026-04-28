import «231lean».Sequences.Convergence

def bounded_above (a : ℕ → ℝ) (b : ℝ) :=
  ∀ n, a n ≤ b

def bounded_below (a : ℕ → ℝ) (b : ℝ) :=
  ∀ n, b ≤ a n

def bounded (a : ℕ → ℝ) :=
  ∃ above, ∃ below, bounded_above a above ∧ bounded_below a below

def supremum (a : ℕ → ℝ) (s : ℝ) :=
  bounded_above a s ∧ ∀ b, bounded_above a b → s ≤ b

def infimum (a : ℕ → ℝ) (i : ℝ) :=
  bounded_below a i ∧ ∀ b, bounded_below a b → b ≤ i

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

theorem const_sup (a : ℕ → ℝ) (h : ∀ n : ℕ, a n = a 0) :
    supremum a (a 0) := by 
      unfold supremum
      constructor
      · exact const_bounded_above a h
      · intro b b_bounds
        unfold bounded_above at b_bounds
        exact b_bounds 0

theorem const_inf (a : ℕ → ℝ) (h : ∀ n : ℕ, a n = a 0) :
    infimum a (a 0) := by 
      unfold infimum
      constructor
      · exact const_bounded_below a h
      · intro b b_bounds
        unfold bounded_below at b_bounds
        exact b_bounds 0

