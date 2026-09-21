import GD.Module1609
import GD.Module1566
import GD.Module1610
import GD.Module1611











set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped BigOperators

namespace GD.N0106.N0428.N0770.N1713
noncomputable section

open _root_.GD.N0106.N0428.N0770.N1725
open _root_.GD.N0106.N0428.N0770.N1728
open _root_.GD.N0106.N0428.N0770.N1709
open _root_.GD.N0106.N0428.N0770.N1710

theorem d027520 (q e F : ℝ) : _root_.GD.N0106.N0428.N0770.N1725.d024169 (1 - q) (1 - e) F = _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F := by
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024169
  ring

theorem d027521 (q e F : ℝ) : _root_.GD.N0106.N0428.N0770.N1725.d024170 (1 - q) (1 - e, F) = _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) := by
  show Real.sqrt (F / ((1 - e) * (1 - (1 - e)))) * _root_.GD.N0106.N0428.N0770.N1725.d024169 (1 - q) (1 - e) F ^ (-(5 / 2 : ℝ)) =
    Real.sqrt (F / (e * (1 - e))) * _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ (-(5 / 2 : ℝ))
  rw [_root_.GD.N0106.N0428.N0770.N1713.d027520, show (1 - e) * (1 - (1 - e)) = e * (1 - e) by ring]

theorem d027522 (q e F : ℝ) : _root_.GD.N0106.N0428.N0770.N1709.d027470 (1 - q) (1 - e, F) = _root_.GD.N0106.N0428.N0770.N1709.d027470 q (e, F) := by
  have h : _root_.GD.N0106.N0428.N0770.N1725.d024130 (1 - e, F) = -_root_.GD.N0106.N0428.N0770.N1725.d024130 (e, F) := _root_.GD.N0106.N0428.N0770.N1725.d024146 (e, F)
  show 2 * ((1 - e) - (1 - q)) * _root_.GD.N0106.N0428.N0770.N1725.d024130 (1 - e, F) + _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1725.d024130 (1 - e, F) ^ 2 =
    2 * (e - q) * _root_.GD.N0106.N0428.N0770.N1725.d024130 (e, F) + _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1725.d024130 (e, F) ^ 2
  rw [h]
  ring

theorem d027523 (q e F : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024170 (1 - q) (1 - e, F) * _root_.GD.N0106.N0428.N0770.N1709.d027470 (1 - q) (1 - e, F) = _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1709.d027470 q (e, F) := by
  rw [_root_.GD.N0106.N0428.N0770.N1713.d027521, _root_.GD.N0106.N0428.N0770.N1713.d027522]


theorem d027524 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : _root_.GD.N0106.N0428.N0770.N1709.d027471 (1 - q) = _root_.GD.N0106.N0428.N0770.N1709.d027471 q := by
  have hq' : (1 - q) ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hq.2], by linarith [hq.1]⟩
  rw [_root_.GD.N0106.N0428.N0770.N1709.d027481, _root_.GD.N0106.N0428.N0770.N1709.d027481]
  congr 1
  rw [integral_prod _ (_root_.GD.N0106.N0428.N0770.N1709.d027495 hq' _root_.GD.N0106.N0428.N0770.N1710.d027506),
    integral_prod _ (_root_.GD.N0106.N0428.N0770.N1709.d027495 hq _root_.GD.N0106.N0428.N0770.N1710.d027506)]
  calc (∫ e, ∫ F, _root_.GD.N0106.N0428.N0770.N1725.d024170 (1 - q) (e, F) * _root_.GD.N0106.N0428.N0770.N1709.d027470 (1 - q) (e, F))
      = ∫ e, ∫ F, _root_.GD.N0106.N0428.N0770.N1725.d024170 (1 - q) (1 - e, F) * _root_.GD.N0106.N0428.N0770.N1709.d027470 (1 - q) (1 - e, F) :=
        (integral_sub_left_eq_self
          (fun e => ∫ F, _root_.GD.N0106.N0428.N0770.N1725.d024170 (1 - q) (e, F) * _root_.GD.N0106.N0428.N0770.N1709.d027470 (1 - q) (e, F)) volume 1).symm
    _ = ∫ e, ∫ F, _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1709.d027470 q (e, F) := by
        simp only [_root_.GD.N0106.N0428.N0770.N1713.d027523]


theorem d027525 (q : ℝ) : _root_.GD.N0106.N0428.N0770.N1728.d024397 (1 - q) = _root_.GD.N0106.N0428.N0770.N1728.d024397 q := by
  rw [_root_.GD.N0106.N0428.N0770.N1728.d024397, _root_.GD.N0106.N0428.N0770.N1728.d024397, _root_.GD.N0106.N0428.N0770.N1728.d024407, _root_.GD.N0106.N0428.N0770.N1728.d024407, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  have h1 : _root_.GD.N0106.N0428.N0770.N1725.d024170 (1 - q) (1 - _root_.GD.N0106.N0428.N0770.N1725.d024127 r, _root_.GD.N0106.N0428.N0770.N1725.d024128 r) =
      _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1725.d024127 r, _root_.GD.N0106.N0428.N0770.N1725.d024128 r) :=
    _root_.GD.N0106.N0428.N0770.N1713.d027521 q _ _
  have h2 : _root_.GD.N0106.N0428.N0770.N1725.d024170 (1 - q) (_root_.GD.N0106.N0428.N0770.N1725.d024127 r, _root_.GD.N0106.N0428.N0770.N1725.d024128 r) =
      _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 - _root_.GD.N0106.N0428.N0770.N1725.d024127 r, _root_.GD.N0106.N0428.N0770.N1725.d024128 r) := by
    have := _root_.GD.N0106.N0428.N0770.N1713.d027521 q (1 - _root_.GD.N0106.N0428.N0770.N1725.d024127 r) (_root_.GD.N0106.N0428.N0770.N1725.d024128 r)
    rwa [sub_sub_cancel] at this
  simp only [_root_.GD.N0106.N0428.N0770.N1728.d024389, _root_.GD.N0106.N0428.N0770.N1728.d024388, _root_.GD.N0106.N0428.N0770.N1728.d024390, _root_.GD.N0106.N0428.N0770.N1728.d024387, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, h1, h2]
  ring


theorem d027526 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : |_root_.GD.N0106.N0428.N0770.N1709.d027471 q - _root_.GD.N0106.N0428.N0770.N1728.d024397 q| < 1 / 1000 := by
  rcases le_or_gt q (1 / 2) with h | h
  · exact _root_.GD.N0106.N0428.N0770.N1710.d027518 ⟨hq.1, h⟩
  · have hq' : 1 - q ∈ Icc (0 : ℝ) (1 / 2) := ⟨by linarith [hq.2], by linarith⟩
    have hthis := _root_.GD.N0106.N0428.N0770.N1710.d027518 hq'
    rwa [_root_.GD.N0106.N0428.N0770.N1713.d027524 hq, _root_.GD.N0106.N0428.N0770.N1713.d027525] at hthis


theorem d027527 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (hS0 : _root_.GD.N0106.N0428.N0770.N1728.d024397 q < -47 / 200) :
    _root_.GD.N0106.N0428.N0770.N1709.d027471 q < -117 / 500 := by
  have h := _root_.GD.N0106.N0428.N0770.N1713.d027526 hq
  rw [abs_lt] at h
  linarith [h.2]

end
end GD.N0106.N0428.N0770.N1713

#print axioms _root_.GD.N0106.N0428.N0770.N1713.d027524
#print axioms _root_.GD.N0106.N0428.N0770.N1713.d027525
#print axioms _root_.GD.N0106.N0428.N0770.N1713.d027526
#print axioms _root_.GD.N0106.N0428.N0770.N1713.d027527
