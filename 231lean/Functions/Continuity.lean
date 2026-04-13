import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.NormNum.Core
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Order.Interval.Set.Defs
import «231lean».Functions.Limits

def f_is_continuous_at_a (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ L, ε_δ_limit (Set.univ : Set ℝ) f a L 

def f_is_continuous (f : ℝ → ℝ) : Prop :=
  ∀ a, ∃ L, ε_δ_limit (Set.univ : Set ℝ) f a L 

#check fun_apply

-- Example proof that all constant functions are continuous
example : 
    ∀ C, f_is_continuous (f := Function.const ℝ C) := by
      unfold f_is_continuous
      intro C a
      use C
      unfold ε_δ_limit
      intro ε ε_pos
      use 1 
      intro x _ _
      simp only [Function.const_apply, sub_self, abs_zero]
      exact ε_pos

theorem f_g_f_plus_g_cont_at_c 
  (f : ℝ → ℝ) 
  (g : ℝ → ℝ) 
  (f_c : f_is_continuous_at_a f c)
  (g_c : f_is_continuous_at_a g c) :
  f_is_continuous_at_a (fun x => f x + g x) c := by
    let fpg : ℝ → ℝ := fun x => f x + g x
    unfold f_is_continuous_at_a at f_c
    unfold f_is_continuous_at_a at g_c
    obtain ⟨fl, f_lim⟩ := f_c
    obtain ⟨gl, g_lim⟩ := g_c
    unfold f_is_continuous_at_a 
    use gl + fl
    unfold ε_δ_limit
    intro ε ε_pos 
    unfold ε_δ_limit at f_lim
    unfold ε_δ_limit at g_lim
    let half_ε := ε / 2
    have half_ε_pos : half_ε > 0 := by positivity
    obtain ⟨δ_f, hf⟩ := f_lim half_ε half_ε_pos 
    obtain ⟨δ_g, hg⟩ := g_lim half_ε half_ε_pos
    let δ := min δ_f δ_g
    use δ 
    intro x x_in_R x_ne_c_diff_le_δ 
    obtain ⟨x_ne_c, diff_le_δ⟩ := x_ne_c_diff_le_δ
    have hδ := lt_min_iff.1 diff_le_δ
    have hδf := hδ.1
    have hδg := hδ.2
    have h1 : |f x - fl| < ε / 2 := hf x trivial ⟨x_ne_c, hδf⟩
    have h2 : |g x - gl| < ε / 2 := hg x trivial ⟨x_ne_c, hδg⟩
    have hsum : |f x - fl| + |g x - gl| < ε / 2 + ε / 2 := add_lt_add h1 h2
    simp 
    calc
      |f x + g x - (gl + fl)| 
          = |(f x - fl) + (g x - gl)| := by abel  -- rearrange
      _ ≤ |f x - fl| + |g x - gl| := abs_add_le _ _
      _ < ε/2 + ε/2  := hsum
      _ = ε := by ring

theorem f_g_f_minus_g_cont_at_c 
  (f : ℝ → ℝ) 
  (g : ℝ → ℝ) 
  (f_c : f_is_continuous_at_a f c)
  (g_c : f_is_continuous_at_a g c) :
  f_is_continuous_at_a (fun x => f x - g x) c := by
    let fpg : ℝ → ℝ := fun x => f x - g x
    unfold f_is_continuous_at_a at f_c
    unfold f_is_continuous_at_a at g_c
    obtain ⟨fl, f_lim⟩ := f_c
    obtain ⟨gl, g_lim⟩ := g_c
    unfold f_is_continuous_at_a 
    use fl - gl
    unfold ε_δ_limit
    intro ε ε_pos 
    unfold ε_δ_limit at f_lim
    unfold ε_δ_limit at g_lim
    let half_ε := ε / 2
    have half_ε_pos : half_ε > 0 := by positivity
    obtain ⟨δ_f, hf⟩ := f_lim half_ε half_ε_pos 
    obtain ⟨δ_g, hg⟩ := g_lim half_ε half_ε_pos
    let δ := min δ_f δ_g
    use δ 
    intro x x_in_R x_ne_c_diff_le_δ 
    obtain ⟨x_ne_c, diff_le_δ⟩ := x_ne_c_diff_le_δ
    have hδ := lt_min_iff.1 diff_le_δ
    have hδf := hδ.1
    have hδg := hδ.2
    have h1 : |f x - fl| < ε / 2 := hf x trivial ⟨x_ne_c, hδf⟩
    have h2 : |g x - gl| < ε / 2 := hg x trivial ⟨x_ne_c, hδg⟩
    have hsum : |f x - fl| + |g x - gl| < ε / 2 + ε / 2 := add_lt_add h1 h2
    simp 
    calc
      |f x - g x - (fl - gl)| 
        = |(f x - fl) - (g x - gl)| := by ring
      _ ≤ |f x - fl| + |g x - gl| := abs_sub (f x - fl) (g x - gl)
      _ < ε/2 + ε/2  := hsum
      _ = ε := by ring
