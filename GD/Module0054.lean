import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring























namespace GD
namespace N0230
namespace N0693

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]


def d000667 (x p q : E) : ℝ :=
  ‖x - q‖ ^ 2 - ‖x - p‖ ^ 2


theorem d000668
    (x p q : E) :
    _root_.GD.N0230.N0693.d000667 x p q =
      ‖q - p‖ ^ 2 - 2 * inner ℝ (x - p) (q - p) := by
  have hdecomp : x - q = (x - p) - (q - p) := by
    abel
  rw [_root_.GD.N0230.N0693.d000667, hdecomp, norm_sub_sq_real]
  ring






theorem d000669
    (x p q : E)
    (hprojection : inner ℝ (x - p) (q - p) ≤ 0) :
    ‖q - p‖ ^ 2 ≤ _root_.GD.N0230.N0693.d000667 x p q := by
  rw [_root_.GD.N0230.N0693.d000668]
  linarith


theorem d000670
    (x p q : E)
    (hprojection : inner ℝ (x - p) (q - p) ≤ 0) :
    0 ≤ _root_.GD.N0230.N0693.d000667 x p q := by
  exact le_trans (sq_nonneg ‖q - p‖)
    (_root_.GD.N0230.N0693.d000669 x p q hprojection)





theorem d000671
    (x p q : E)
    (hprojection : inner ℝ (x - p) (q - p) ≤ 0)
    (hne : q ≠ p) :
    0 < _root_.GD.N0230.N0693.d000667 x p q := by
  have hnorm : 0 < ‖q - p‖ ^ 2 := by
    apply sq_pos_of_ne_zero
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  exact lt_of_lt_of_le hnorm
    (_root_.GD.N0230.N0693.d000669 x p q hprojection)

end N0693
end N0230
end GD
