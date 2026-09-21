import GD.Module1398










set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory

namespace GD.N0192
noncomputable section
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0180 _root_.GD.N0163 _root_.GD.N0201
open _root_.GD.N0016 _root_.GD.N0013


def d022554 (q : ℝ) : ℝ :=
  (1 - q) / (1 + q) ^ 3 *
    ((1 - Real.pi / 4) + (3 * Real.pi / 2 - 4) * q +
      (5 / 3 - Real.pi / 4) * q ^ 2)


theorem d022555 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    let q : ℝ := (2 * (t : ℝ) - 1) ^ 2
    _root_.GD.N0180.d022173 t (_root_.GD.N0163.d022211 _root_.GD.N0201.d022510.1) =
      -(1 - q) ^ 2 / (1 + q) ^ 2 +
        (Real.pi / 2) * (5 * q ^ 2 - 2 * q + 1) / (1 + q) ^ 3 +
        (4 * q * (1 - q) ^ 2 / (1 + q) ^ 3) * _root_.GD.N0013.d005011 q := by
  dsimp only
  exact (_root_.GD.N0201.d022511 t).trans (_root_.GD.N0016.d008318 t.property)


theorem d022556 {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Real.pi / 4 - _root_.GD.N0016.d008316 q (1 + q / (3 * (1 - q))) = _root_.GD.N0192.d022554 q ∧
      0 < _root_.GD.N0192.d022554 q := by
  have hplus : 0 < 1 + q := by positivity
  have hminus : 0 < 1 - q := sub_pos.mpr hq1
  have hid : Real.pi / 4 - _root_.GD.N0016.d008316 q (1 + q / (3 * (1 - q))) =
      _root_.GD.N0192.d022554 q := by
    unfold _root_.GD.N0016.d008316 _root_.GD.N0192.d022554
    field_simp [hplus.ne', hminus.ne']
    ring
  refine ⟨hid, ?_⟩
  rw [← hid]
  exact sub_pos.mpr (_root_.GD.N0016.d008319 hq0 hq1 le_rfl)


theorem d022557 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    let q : ℝ := (2 * (t : ℝ) - 1) ^ 2
    0 < _root_.GD.N0192.d022554 q ∧
      _root_.GD.N0192.d022554 q ≤ Real.pi / 4 - _root_.GD.N0180.d022173 t (_root_.GD.N0163.d022211 _root_.GD.N0201.d022510.1) := by
  dsimp only
  let q : ℝ := (2 * (t : ℝ) - 1) ^ 2
  have hq0 : 0 ≤ q := sq_nonneg _
  have hq1 : q < 1 := by
    dsimp only [q]
    nlinarith [mul_pos t.property.1 (sub_pos.mpr t.property.2)]
  have hrem := _root_.GD.N0192.d022556 hq0 hq1
  refine ⟨hrem.2, ?_⟩
  have hj := _root_.GD.N0013.d005017 hq0 hq1
  have hcoef : 0 ≤ 4 * q * (1 - q) ^ 2 / (1 + q) ^ 3 := by positivity
  have hbound : _root_.GD.N0016.d008316 q (_root_.GD.N0013.d005011 q) ≤
      _root_.GD.N0016.d008316 q (1 + q / (3 * (1 - q))) := by
    unfold _root_.GD.N0016.d008316
    linarith [mul_le_mul_of_nonneg_left hj hcoef]
  have hformula : _root_.GD.N0180.d022173 t (_root_.GD.N0163.d022211 _root_.GD.N0201.d022510.1) =
      _root_.GD.N0016.d008316 q (_root_.GD.N0013.d005011 q) :=
    (_root_.GD.N0201.d022511 t).trans (_root_.GD.N0016.d008318 t.property)
  rw [← hrem.1, hformula]
  exact sub_le_sub_left hbound (Real.pi / 4)

end
end GD.N0192

#print axioms _root_.GD.N0192.d022555
#print axioms _root_.GD.N0192.d022556
#print axioms _root_.GD.N0192.d022557
