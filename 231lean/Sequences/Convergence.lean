import Mathlib.Analysis.AbsoluteValue.Equivalence

def seq_converge (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n > N, |a n - L| < ε 

noncomputable def harmonic_seq (n : ℕ) : ℝ := 
  if n = 0 then 0 else 1/n

example (n : ℕ) (n_pos : n > 0) : 0 < 1 / (↑n : ℝ) := by
  -- cast n to ℝ first
  exact one_div_pos.mpr (Nat.cast_pos.mpr n_pos)

example :
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

