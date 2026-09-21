import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic





set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory Set

namespace GD.N0106.N0428.N0770.N1702
noncomputable section

def d006767 (b x : ℝ) : ℝ := Real.exp (-(x ^ 2 + b ^ 2 / x ^ 2) / 2)
def d006768 (b x : ℝ) : ℝ := b / x
def d006769 (b x : ℝ) : ℝ := x - b / x

theorem d006770 (b : ℝ) : IntegrableOn (_root_.GD.N0106.N0428.N0770.N1702.d006767 b) (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)).integrableOn
  apply hg.mono' (by unfold _root_.GD.N0106.N0428.N0770.N1702.d006767; fun_prop)
  filter_upwards with x
  dsimp only [_root_.GD.N0106.N0428.N0770.N1702.d006767]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h := div_nonneg (sq_nonneg b) (sq_nonneg x)
  linarith

theorem d006771 {b : ℝ} (hb : 0 < b) (x : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1702.d006767 b (_root_.GD.N0106.N0428.N0770.N1702.d006768 b x) = _root_.GD.N0106.N0428.N0770.N1702.d006767 b x := by
  by_cases hx : x = 0
  · simp [hx, _root_.GD.N0106.N0428.N0770.N1702.d006767, _root_.GD.N0106.N0428.N0770.N1702.d006768]
  · unfold _root_.GD.N0106.N0428.N0770.N1702.d006767 _root_.GD.N0106.N0428.N0770.N1702.d006768
    congr 1
    field_simp [hb.ne', hx]
    ring

theorem d006772 {b x : ℝ} (hx : 0 < x) :
    HasDerivAt (_root_.GD.N0106.N0428.N0770.N1702.d006768 b) (-(b / x ^ 2)) x := by
  have h := (hasDerivAt_const x b).div (hasDerivAt_id x) hx.ne'
  convert! h using 1 <;> (try simp only [_root_.GD.N0106.N0428.N0770.N1702.d006768, id_eq]) <;> ring

theorem d006773 {b : ℝ} (hb : 0 < b) : InjOn (_root_.GD.N0106.N0428.N0770.N1702.d006768 b) (Ioi 0) := by
  intro x hx y hy hxy
  unfold _root_.GD.N0106.N0428.N0770.N1702.d006768 at hxy
  have hm := (div_eq_div_iff hx.ne' hy.ne').mp hxy
  nlinarith

theorem d006774 {b : ℝ} (hb : 0 < b) : _root_.GD.N0106.N0428.N0770.N1702.d006768 b '' Ioi 0 = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact div_pos hb hx
  · intro hy
    refine ⟨b / y, div_pos hb hy, ?_⟩
    unfold _root_.GD.N0106.N0428.N0770.N1702.d006768
    field_simp [hb.ne', (show 0 < y from hy).ne']

theorem d006775 {b x : ℝ} (hx : 0 < x) :
    HasDerivAt (_root_.GD.N0106.N0428.N0770.N1702.d006769 b) (1 + b / x ^ 2) x := by
  have h := (hasDerivAt_id x).sub (_root_.GD.N0106.N0428.N0770.N1702.d006772 (b := b) hx)
  convert! h using 1 <;> (try simp only [_root_.GD.N0106.N0428.N0770.N1702.d006769, _root_.GD.N0106.N0428.N0770.N1702.d006768, id_eq]) <;> ring

theorem d006776 {b : ℝ} (hb : 0 < b) : StrictMonoOn (_root_.GD.N0106.N0428.N0770.N1702.d006769 b) (Ioi 0) := by
  intro x hx y hy hxy
  have hr : b / y < b / x := (div_lt_div_iff₀ hy hx).mpr (by nlinarith)
  unfold _root_.GD.N0106.N0428.N0770.N1702.d006769
  linarith

theorem d006777 {b : ℝ} (hb : 0 < b) : _root_.GD.N0106.N0428.N0770.N1702.d006769 b '' Ioi 0 = univ := by
  apply eq_univ_of_forall
  intro y
  let q := Real.sqrt (y ^ 2 + 4 * b)
  have hq2 : q ^ 2 = y ^ 2 + 4 * b := Real.sq_sqrt (by positivity)
  have hq : |y| < q := by
    simpa only [Real.sqrt_sq_eq_abs] using
      (Real.sqrt_lt_sqrt (sq_nonneg y) (show y ^ 2 < y ^ 2 + 4 * b by linarith))
  have hx : 0 < (y + q) / 2 := by linarith [neg_le_abs y]
  refine ⟨(y + q) / 2, hx, ?_⟩
  unfold _root_.GD.N0106.N0428.N0770.N1702.d006769
  have hp : ((y + q) / 2) ^ 2 - y * ((y + q) / 2) = b := by nlinarith
  field_simp [show y + q ≠ 0 by linarith]
  nlinarith

theorem d006778 {b : ℝ} (hb : 0 < b) (x : ℝ) :
    |-(b / x ^ 2)| • _root_.GD.N0106.N0428.N0770.N1702.d006767 b (_root_.GD.N0106.N0428.N0770.N1702.d006768 b x) = (b / x ^ 2) * _root_.GD.N0106.N0428.N0770.N1702.d006767 b x := by
  rw [abs_neg, abs_of_nonneg (div_nonneg hb.le (sq_nonneg x)), _root_.GD.N0106.N0428.N0770.N1702.d006771 hb]
  rfl



theorem d006779 {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x => (b / x ^ 2) * _root_.GD.N0106.N0428.N0770.N1702.d006767 b x) (Ioi 0) ∧
    (∫ x in Ioi 0, (b / x ^ 2) * _root_.GD.N0106.N0428.N0770.N1702.d006767 b x) = ∫ x in Ioi 0, _root_.GD.N0106.N0428.N0770.N1702.d006767 b x := by
  have hd := fun x (hx : x ∈ Ioi (0 : ℝ)) =>
    (_root_.GD.N0106.N0428.N0770.N1702.d006772 (b := b) hx).hasDerivWithinAt (s := Ioi 0)
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi hd (_root_.GD.N0106.N0428.N0770.N1702.d006773 hb) (_root_.GD.N0106.N0428.N0770.N1702.d006767 b)
  have he := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hd (_root_.GD.N0106.N0428.N0770.N1702.d006773 hb) (_root_.GD.N0106.N0428.N0770.N1702.d006767 b)
  simp_rw [_root_.GD.N0106.N0428.N0770.N1702.d006774 hb, _root_.GD.N0106.N0428.N0770.N1702.d006778 hb] at hi he
  exact ⟨hi.mp (_root_.GD.N0106.N0428.N0770.N1702.d006770 b), he.symm⟩

theorem d006780 {b x : ℝ} (hx : 0 < x) :
    Real.exp (-b) * Real.exp (-(1 / 2 : ℝ) * (_root_.GD.N0106.N0428.N0770.N1702.d006769 b x) ^ 2) = _root_.GD.N0106.N0428.N0770.N1702.d006767 b x := by
  rw [← Real.exp_add]
  unfold _root_.GD.N0106.N0428.N0770.N1702.d006767 _root_.GD.N0106.N0428.N0770.N1702.d006769
  congr 1
  field_simp [hx.ne']
  ring



theorem d006781 {b : ℝ} (hb : 0 < b) :
    (∫ x in Ioi 0, _root_.GD.N0106.N0428.N0770.N1702.d006767 b x) = Real.sqrt (Real.pi / 2) * Real.exp (-b) := by
  have hd := fun x (hx : x ∈ Ioi (0 : ℝ)) =>
    (_root_.GD.N0106.N0428.N0770.N1702.d006775 (b := b) hx).hasDerivWithinAt (s := Ioi 0)
  have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd
    (_root_.GD.N0106.N0428.N0770.N1702.d006776 hb).injOn
    (fun y : ℝ => Real.exp (-b) * Real.exp (-(1 / 2 : ℝ) * y ^ 2))
  rw [_root_.GD.N0106.N0428.N0770.N1702.d006777 hb, Measure.restrict_univ, integral_const_mul, integral_gaussian] at he
  have hi := _root_.GD.N0106.N0428.N0770.N1702.d006770 b
  obtain ⟨hw, hwval⟩ := _root_.GD.N0106.N0428.N0770.N1702.d006779 hb
  have heq : (∫ x in Ioi 0,
      |1 + b / x ^ 2| • (Real.exp (-b) * Real.exp (-(1 / 2 : ℝ) * (_root_.GD.N0106.N0428.N0770.N1702.d006769 b x) ^ 2))) =
      2 * ∫ x in Ioi 0, _root_.GD.N0106.N0428.N0770.N1702.d006767 b x := by
    calc
      _ = ∫ x in Ioi 0, _root_.GD.N0106.N0428.N0770.N1702.d006767 b x + (b / x ^ 2) * _root_.GD.N0106.N0428.N0770.N1702.d006767 b x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp only
        rw [_root_.GD.N0106.N0428.N0770.N1702.d006780 hx, abs_of_nonneg (by positivity), smul_eq_mul]
        ring
      _ = _ := by rw [integral_add hi hw, hwval]; ring
  rw [heq] at he
  have hsqrt : Real.sqrt (Real.pi / (1 / 2 : ℝ)) = 2 * Real.sqrt (Real.pi / 2) := by
    rw [show Real.pi / (1 / 2 : ℝ) = 4 * (Real.pi / 2) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [hsqrt] at he
  nlinarith

end
end GD.N0106.N0428.N0770.N1702

#print axioms _root_.GD.N0106.N0428.N0770.N1702.d006770
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d006779
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d006781
