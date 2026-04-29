import «231lean».Sequences.Convergence

def bounded_above (a : ℕ → ℝ) (b : ℝ) :=
  ∀ n, a n ≤ b

def bounded_below (a : ℕ → ℝ) (b : ℝ) :=
  ∀ n, b ≤ a n

def bounded (a : ℕ → ℝ) :=
  ∃ above, ∃ below, bounded_above a above ∧ bounded_below a below

def supremum (a : ℕ → ℝ) (s : ℝ) :=
  bounded_above a s ∧ ∀ b, bounded_above a b → s ≤ b

-- Not proven in the course but used
theorem sup_ex : ∀ a, ∀ b, bounded_above a b → ∃ s, supremum a s := sorry

def increasing (a : ℕ → ℝ) := ∀ n : ℕ, a n ≤ a (n+1)

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

lemma increasing_le (a : ℕ → ℝ) (inc : increasing a) :
    ∀ n N, N < n → a N ≤ a n := by
      intro n N N_lt_n
      unfold increasing at inc
      apply Nat.exists_eq_add_of_lt at N_lt_n
      obtain ⟨k, hk⟩ := N_lt_n
      induction k with
      | zero =>
        simp at hk
        rw[hk]
        exact inc N
      | succ c ih =>
        have h2 : a (N + c + 1) ≤ a (N + (c+1) + 1) := by
          exact inc (N + c + 1)
        rw[hk]
        -- This follows very clearly from ih but I don't know
        -- how lean wants me to state it
        have ih' : a N ≤ a (N + c + 1) := by sorry
        linarith
        

theorem increasing_bounded_converges 
  (a : ℕ → ℝ)
  (b : ℝ) 
  (b_bounds : bounded_above a b)
  (h : increasing a) :
    ∃ L, seq_converge a L := by
      obtain ⟨s, s_sup⟩ := sup_ex a b b_bounds
      obtain ⟨s_bounds, s_lowest⟩ := s_sup 
      use s
      unfold seq_converge
      intro ε ε_pos
      norm_num at ε_pos 
      have ex_an_gt_sε : ∃ N, s - ε < a N := by
        have s_ε_no_bound : ¬(bounded_above a (s-ε)) := by
          by_contra c
          apply s_lowest at c
          linarith
        unfold bounded_above at s_ε_no_bound
        simp at s_ε_no_bound
        exact s_ε_no_bound 
      obtain ⟨N, hn⟩ := ex_an_gt_sε  
      use N
      intro n N_le_n
      norm_num at N_le_n
      have han : a N ≤ a n := increasing_le a h n N N_le_n
      unfold bounded_above at s_bounds
      have hans : a n ≤ s := s_bounds n 
      rw[abs_lt]
      constructor
      · linarith
      · linarith
