import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith




set_option autoImplicit false
set_option warningAsError true

namespace GD.N0008

theorem d005008 :
    (5223903223377 : ℝ) / 2687038914560 ≤ Real.log 7 := by
  have h := Real.sum_range_le_log_div
    (x := (3 : ℝ) / 4) (by norm_num) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem d005009 : (2721 : ℝ) / 1400 < Real.log 7 := by
  have h := _root_.GD.N0008.d005008
  linarith


theorem d005010 :
    (96 - 28 * Real.log 7) / 27 < (77 : ℝ) / 50 := by
  have h := _root_.GD.N0008.d005009
  linarith

end GD.N0008

#print axioms _root_.GD.N0008.d005008
#print axioms _root_.GD.N0008.d005009
#print axioms _root_.GD.N0008.d005010
