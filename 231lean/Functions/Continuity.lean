import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.NormNum.Core
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Order.Interval.Set.Defs
import «231lean».Functions.Limits

def f_is_continuous_at_a (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∃ L, ε_δ_limit (Set.univ : Set ℝ) f a L 

def f_is_continuous (f : ℝ → ℝ) : Prop :=
  ∀ a, ∃ L, ε_δ_limit (Set.univ : Set ℝ) f a L 

-- Example proof that all constant functions are continuous
example : 
    ∀ C, f_is_continuous (f := Function.const ℝ C) := by
      unfold f_is_continuous
      intro C a
      use C
      unfold ε_δ_limit
      intro ε ε_pos
      use 1, zero_lt_one 
      intro x _ _
      simp only [Function.const_apply, sub_self, abs_zero]
      exact ε_pos
