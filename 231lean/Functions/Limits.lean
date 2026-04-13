import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.NormNum.Core
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Order.Interval.Set.Defs

def ε_δ_limit (I : Set ℝ) (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ I, x ≠ a ∧ |x - a| < δ → |f x - L| < ε

-- Example proof that all constant functions have their constant as limit for all a
example : 
    ∀ L, ∀ a, ε_δ_limit (Set.univ : Set ℝ) (f := Function.const ℝ L) a L := by
    unfold ε_δ_limit
    intro a y ε ε_pos
    use 1, zero_lt_one 
    intro x _ _
    simp only [Function.const_apply, sub_self, abs_zero]
    exact ε_pos 
