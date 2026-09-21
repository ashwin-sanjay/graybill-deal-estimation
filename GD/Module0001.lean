import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic




















set_option autoImplicit false

namespace GD.N0106.N0428.N0765.N1540


theorem d000001 (p : ℕ) :
    Real.cos ((p : ℝ) * Real.pi / 28) =
      Real.cos (((min (p % 56) (56 - p % 56) : ℕ) : ℝ) * Real.pi / 28) := by
  have hsplitNat : p = p % 56 + 56 * (p / 56) :=
    (Nat.mod_add_div p 56).symm
  have hsplit : (p : ℝ) = ((p % 56 : ℕ) : ℝ) + 56 * ((p / 56 : ℕ) : ℝ) := by
    exact_mod_cast hsplitNat
  have hperiod :
      Real.cos ((p : ℝ) * Real.pi / 28) =
        Real.cos (((p % 56 : ℕ) : ℝ) * Real.pi / 28) := by
    calc
      Real.cos ((p : ℝ) * Real.pi / 28) =
          Real.cos (((p % 56 : ℕ) : ℝ) * Real.pi / 28 +
            ((p / 56 : ℕ) : ℝ) * (2 * Real.pi)) := by
        congr 1
        rw [hsplit]
        ring
      _ = Real.cos (((p % 56 : ℕ) : ℝ) * Real.pi / 28) :=
        Real.cos_add_nat_mul_two_pi _ (p / 56)
  rw [hperiod]
  by_cases hleft : p % 56 ≤ 56 - p % 56
  · rw [min_eq_left hleft]
  · have hright : 56 - p % 56 ≤ p % 56 := by omega
    have hresidue : p % 56 ≤ 56 := (Nat.mod_lt p (by norm_num : 0 < 56)).le
    have hreflect :
        (((56 - p % 56 : ℕ) : ℝ) * Real.pi / 28) =
          2 * Real.pi - ((p % 56 : ℕ) : ℝ) * Real.pi / 28 := by
      rw [Nat.cast_sub hresidue]
      push_cast
      ring
    rw [min_eq_right hright, hreflect, Real.cos_two_pi_sub]

end GD.N0106.N0428.N0765.N1540

#print axioms _root_.GD.N0106.N0428.N0765.N1540.d000001
