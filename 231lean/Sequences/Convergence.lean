import Mathlib.Analysis.AbsoluteValue.Equivalence

def seq_converge (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n > N, |a n - L| < ε 

def seq_convergent (a : ℕ → ℝ) : Prop :=
  ∃ L, ∀ ε > 0, ∃ N, ∀ n > N, |a n - L| < ε 

noncomputable def harmonic_seq (n : ℕ) : ℝ := 
  if n = 0 then 0 else 1/n

noncomputable def sin_harmonic_seq (n : ℕ) : ℝ := 
  if n = 0 then 0 else (Real.sin n)/n

example (n : ℕ) (n_pos : n > 0) : 0 < 1 / (↑n : ℝ) := by
  -- cast n to ℝ first
  exact one_div_pos.mpr (Nat.cast_pos.mpr n_pos)

theorem harmonic_seq_converge_0 :
  seq_converge (harmonic_seq) 0 := by
    unfold seq_converge
    intro ε ε_pos 
    norm_num at ε_pos 
    have ε_add_1_pos : 0 < ε + 1 := by 
      rw[← add_zero 0]
      apply add_lt_add ε_pos zero_lt_one
    let N := Nat.ceil (1/ε + 1)
    use N
    have ε_inv_add_one_pos : 0 < 1/ε + 1 := by
      have ε_inv_pos : 0 < 1 / ε := one_div_pos.mpr ε_pos  
      exact add_pos ε_inv_pos one_pos
    have N_pos : 0 < N := by
      apply Nat.ceil_pos.mpr ε_inv_add_one_pos
    intro n ngtN
    norm_num at ngtN
    dsimp [harmonic_seq]
    have n_pos : 0 < n := by
      apply lt_trans N_pos ngtN
    have n_ne_zero: n ≠ 0 := Nat.pos_iff_ne_zero.mp n_pos
    rw [if_neg n_ne_zero, sub_eq_add_neg, neg_zero, add_zero]
    have n_inv_pos : 0 < 1 / (↑n : ℝ) := 
      one_div_pos.mpr (Nat.cast_pos.mpr n_pos)
    rw[abs_of_pos n_inv_pos]
    have lt_N_inv : 1 / (↑n : ℝ) < 1 / (↑N : ℝ) := by
      apply (one_div_lt_one_div
        (Nat.cast_pos.mpr n_pos) (Nat.cast_pos.mpr N_pos)).mpr
      exact_mod_cast ngtN
    apply lt_trans lt_N_inv 
    dsimp [N]
    have hN : 1/ε + 1 ≤ ↑⌈1/ε + 1⌉₊ := Nat.le_ceil (1/ε + 1)
    have hN1 : 1 / ↑⌈1/ε + 1⌉₊ ≤ 1/(1/ε + 1) := by
      have h_this : (0 : ℝ) < ↑⌈1/ε + 1⌉₊ := by
        linarith
      exact (one_div_le_one_div h_this ε_inv_add_one_pos).mpr hN
    have hN2 : 1/(1/ε + 1) < ε := by
      ring_nf
      field_simp
      exact lt_add_of_pos_of_le ε_pos le_rfl
    exact lt_of_le_of_lt hN1 hN2

theorem squeeze (a b c : ℕ → ℝ) (L : ℝ)
  (aleb : a ≤ b) (blec : b ≤ c)
  (aL : seq_converge a L)
  (cL : seq_converge c L)
  : seq_converge b L := by
    intro ε ε_pos
    obtain ⟨N1, hN1⟩ := cL ε ε_pos
    obtain ⟨N2, hN2⟩ := aL ε ε_pos
    let N : ℕ := max N1 N2
    have N1_le_N : N1 ≤ N := by
      exact Nat.le_max_left N1 N2
    have N2_le_N : N2 ≤ N := by
      exact Nat.le_max_right N1 N2
    use N
    intro n n_gt_N
    have N_lt_n : N < n := Lean.Omega.Nat.lt_of_gt n_gt_N
    have n_gt_N1 : n > N1 := by
      have h : N1 < n := lt_of_le_of_lt N1_le_N N_lt_n
      exact Lean.Omega.Nat.lt_of_gt h
    have n_gt_N2 : n > N2 := by
      have h : N2 < n := lt_of_le_of_lt N2_le_N N_lt_n
      exact Lean.Omega.Nat.lt_of_gt h
    rw[abs_lt]
    constructor
    · have an_fits : |a n - L| < ε := by
        exact hN2 n n_gt_N2
      rw [abs_lt] at an_fits
      obtain ⟨h1, h2⟩ := an_fits
      have hle : a n - L ≤ b n - L := by
        have h : a n ≤ b n := aleb n
        exact sub_le_sub_right h L
      exact lt_of_lt_of_le h1 hle
    · have cn_fits : |c n - L| < ε := by
        exact hN1 n n_gt_N1  
      rw [abs_lt] at cn_fits
      obtain ⟨h1, h2⟩ := cn_fits
      have hge : b n - L ≤ c n - L := by
        have h : b n ≤ c n := blec n
        exact sub_le_sub_right h L
      exact lt_of_le_of_lt hge h2

theorem const_seq_converge (a : ℕ → ℝ) (h : ∀ n : ℕ, a n = a 0):
    seq_converge a (a 0) := by
      unfold seq_converge
      intro ε ε_pos 
      norm_num at ε_pos 
      use 0
      intro m m_pos
      rw[h m, sub_eq_add_neg, add_neg_cancel (a 0), abs_zero]
      exact ε_pos 


theorem mul_convergent_seq (m : ℝ) (a : ℕ → ℝ) (L : ℕ) :
    seq_converge a L → seq_converge (m • a) (m • L) := by
      unfold seq_converge
      intro a_to_L ε1 ε1_pos 
      norm_num at ε1_pos
      by_cases m0 : m ≠ 0
      · let ε := (ε1 / (|(m : ℝ)| + 1))
        have d_pos : 0 < |(m : ℝ)| + 1 := add_pos_of_nonneg_of_pos (abs_nonneg (m : ℝ)) one_pos
        have ε_pos : 0 < ε := div_pos ε1_pos d_pos
        obtain ⟨N1, hN1⟩ := a_to_L ε ε_pos 
        use N1
        intro n n_gt_N
        norm_num
        rw[← mul_sub, abs_mul]
        have hε : |a n - ↑L| < ε := hN1 n n_gt_N
        have hε1 : |↑m| * ε < ε1 := by
          dsimp [ε] 
          field_simp
          linarith
        have hε_le : |a n - ↑L| ≤ ε := le_of_lt hε
        have h1 : |↑m| * |a n - ↑L| ≤ |↑m| * ε := by
          exact mul_le_mul_of_nonneg_left hε_le (abs_nonneg _)
        exact lt_of_le_of_lt h1 hε1
      · apply Classical.not_not.mp at m0
        have a0 : ∀ n : ℕ, (m • a) n = 0 := by
          intro n
          rw[Pi.smul_apply, m0, zero_smul]
        use 0
        intro c m_pos
        rw[a0 c, m0, zero_smul]
        simp only [sub_self, abs_zero]
        exact ε1_pos 

theorem neg_harmonic_seq_converge_0 :
    seq_converge ((-1 : ℝ) • harmonic_seq) 0 := by
      let h := (mul_convergent_seq (-1) harmonic_seq (0 : ℕ))
      rw[Nat.cast_zero, smul_zero] at h
      apply h
      exact harmonic_seq_converge_0

example : 
    seq_converge ((fun n => Real.sin n : ℕ → ℝ) • harmonic_seq) 0 := by
      let s := ((fun n => Real.sin n : ℕ → ℝ) • harmonic_seq)
      have h_pos : ∀ n, 0 ≤ harmonic_seq n := by 
        intro n 
        unfold harmonic_seq
        by_cases n0 : n = 0
        · simp [n0]
        · simp [n0]
      apply squeeze 
        ((-1 : ℝ) • harmonic_seq)
        s
        harmonic_seq
      · intro n
        have h : ((-1 : ℝ) • harmonic_seq) n ≤ s n := by
          dsimp [s]
          exact mul_le_mul_of_nonneg_right
            (Real.neg_one_le_sin (n : ℝ))
            (h_pos n)
        exact h
      · intro n
        have h : s n ≤ harmonic_seq n := by
          dsimp [s]
          nth_rw 2 [← one_mul (harmonic_seq n)]
          exact mul_le_mul_of_nonneg_right
            (Real.sin_le_one (n : ℝ))
            (h_pos n)
        exact h
      · exact neg_harmonic_seq_converge_0
      · exact harmonic_seq_converge_0
