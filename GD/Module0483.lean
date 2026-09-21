import GD.Module0161
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic






set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory Set

namespace GD.N0106.N0428.N0770.N1752
noncomputable section

open _root_.GD.N0232.N0719.N1023

def d007497 (c C t : ℝ) : ℝ :=
  c / (2 * Real.sqrt t) * Real.exp (-C * Real.sqrt t)

def d007498 (c C t : ℝ) : ℝ :=
  t * ((c ^ 2 / (4 * t) + c / (4 * t * Real.sqrt t)) * Real.exp (-C * Real.sqrt t))

def d007499 (c d C t : ℝ) : ℝ :=
  t * (c * d / (4 * t) * Real.exp (-C * Real.sqrt t))

theorem d007500 : (fun u : ℝ => u ^ 2) '' Ioi 0 = Ioi 0 := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    change 0 < u ^ 2
    exact pow_pos (show 0 < u from hu) 2
  · intro ht
    exact ⟨Real.sqrt t, Real.sqrt_pos.2 ht, Real.sq_sqrt ht.le⟩

theorem d007501 : InjOn (fun u : ℝ => u ^ 2) (Ioi 0) := by
  intro u hu v hv huv
  exact (sq_eq_sq₀ hu.le hv.le).mp huv


theorem d007502 (g h : ℝ → ℝ)
    (hgh : ∀ u > 0, (2 * u) * g (u ^ 2) = h u)
    (hh : IntegrableOn h (Ioi 0)) :
    IntegrableOn g (Ioi 0) ∧ (∫ t in Ioi 0, g t) = ∫ u in Ioi 0, h u := by
  have hd : ∀ u ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun v : ℝ => v ^ 2) (2 * u) (Ioi 0) u := by
    intro u _
    simpa using (hasDerivWithinAt_pow (s := Ioi 0) 2 u)
  have hi := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi hd _root_.GD.N0106.N0428.N0770.N1752.d007501 g
  have he := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hd _root_.GD.N0106.N0428.N0770.N1752.d007501 g
  rw [_root_.GD.N0106.N0428.N0770.N1752.d007500] at hi he
  have hEq : ∀ u ∈ Ioi (0 : ℝ), |2 * u| • g (u ^ 2) = h u := by
    intro u hu
    rw [abs_of_pos (mul_pos (by norm_num) hu), smul_eq_mul]
    exact hgh u hu
  exact ⟨hi.mpr (hh.congr_fun (fun u hu => (hEq u hu).symm) measurableSet_Ioi),
    he.trans (setIntegral_congr_fun measurableSet_Ioi hEq)⟩

theorem d007503 {u : ℝ} (hu : 0 < u) (c C : ℝ) :
    (2 * u) * _root_.GD.N0106.N0428.N0770.N1752.d007497 c C (u ^ 2) = c * Real.exp (-(C * u)) := by
  unfold _root_.GD.N0106.N0428.N0770.N1752.d007497
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hu]
  simp only [neg_mul]
  field_simp [hu.ne']

theorem d007504 {u : ℝ} (hu : 0 < u) (c C : ℝ) :
    (2 * u) * _root_.GD.N0106.N0428.N0770.N1752.d007498 c C (u ^ 2) = _root_.GD.N0232.N0719.N1023.d001842 c C u := by
  unfold _root_.GD.N0106.N0428.N0770.N1752.d007498 _root_.GD.N0232.N0719.N1023.d001842
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hu]
  simp only [neg_mul]
  field_simp [hu.ne']
  ring

theorem d007505 {u : ℝ} (hu : 0 < u) (c d C : ℝ) :
    (2 * u) * _root_.GD.N0106.N0428.N0770.N1752.d007499 c d C (u ^ 2) =
      (c * d / 2) * (u * Real.exp (-(C * u))) := by
  unfold _root_.GD.N0106.N0428.N0770.N1752.d007499
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hu]
  simp only [neg_mul]
  field_simp [hu.ne']
  ring


theorem d007506 {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    IntegrableOn (_root_.GD.N0106.N0428.N0770.N1752.d007497 c C) (Ioi 0) ∧
      (∫ t in Ioi 0, _root_.GD.N0106.N0428.N0770.N1752.d007497 c C t) = c / C := by
  have h0 : (∫ u : ℝ in Ioi 0, Real.exp (-(C * u))) = 1 / C := by
    simpa using (Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := 1) (r := C) (by norm_num) hC)
  have hv : (∫ u : ℝ in Ioi 0, c * Real.exp (-(C * u))) = c / C := by
    rw [integral_const_mul, h0]
    ring
  have hh : IntegrableOn (fun u : ℝ => c * Real.exp (-(C * u))) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [hv]
    positivity
  obtain ⟨hi, he⟩ := _root_.GD.N0106.N0428.N0770.N1752.d007502 (_root_.GD.N0106.N0428.N0770.N1752.d007497 c C)
    (fun u => c * Real.exp (-(C * u))) (fun _ hu => _root_.GD.N0106.N0428.N0770.N1752.d007503 hu c C) hh
  exact ⟨hi, he.trans hv⟩



theorem d007507 {c C : ℝ} (hc : 0 < c) (hC : 0 < C) :
    IntegrableOn (_root_.GD.N0106.N0428.N0770.N1752.d007498 c C) (Ioi 0) ∧
      (∫ t in Ioi 0, _root_.GD.N0106.N0428.N0770.N1752.d007498 c C t) = ((c / C) ^ 2 + c / C) / 2 := by
  have hh : IntegrableOn (_root_.GD.N0232.N0719.N1023.d001842 c C) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [_root_.GD.N0232.N0719.N1023.d001843 hC]
    positivity
  obtain ⟨hi, he⟩ := _root_.GD.N0106.N0428.N0770.N1752.d007502 (_root_.GD.N0106.N0428.N0770.N1752.d007498 c C) (_root_.GD.N0232.N0719.N1023.d001842 c C)
    (fun _ hu => _root_.GD.N0106.N0428.N0770.N1752.d007504 hu c C) hh
  exact ⟨hi, he.trans (_root_.GD.N0232.N0719.N1023.d001843 hC)⟩


theorem d007508 {c d C : ℝ} (hc : 0 < c) (hd : 0 < d) (hC : 0 < C) :
    IntegrableOn (_root_.GD.N0106.N0428.N0770.N1752.d007499 c d C) (Ioi 0) ∧
      (∫ t in Ioi 0, _root_.GD.N0106.N0428.N0770.N1752.d007499 c d C t) = c * d / (2 * C ^ 2) := by
  have h1 : (∫ u : ℝ in Ioi 0, u * Real.exp (-(C * u))) = (1 / C) ^ 2 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
      show Real.Gamma 2 = 1 by norm_num, mul_one] using
      (Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := C) (by norm_num) hC)
  have hv : (∫ u : ℝ in Ioi 0, (c * d / 2) * (u * Real.exp (-(C * u)))) =
      c * d / (2 * C ^ 2) := by
    rw [integral_const_mul, h1]
    ring
  have hh : IntegrableOn (fun u : ℝ => (c * d / 2) * (u * Real.exp (-(C * u))))
      (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [hv]
    positivity
  obtain ⟨hi, he⟩ := _root_.GD.N0106.N0428.N0770.N1752.d007502 (_root_.GD.N0106.N0428.N0770.N1752.d007499 c d C)
    (fun u => (c * d / 2) * (u * Real.exp (-(C * u))))
    (fun _ hu => _root_.GD.N0106.N0428.N0770.N1752.d007505 hu c d C) hh
  exact ⟨hi, he.trans hv⟩

end
end GD.N0106.N0428.N0770.N1752

#print axioms _root_.GD.N0106.N0428.N0770.N1752.d007502
#print axioms _root_.GD.N0106.N0428.N0770.N1752.d007506
#print axioms _root_.GD.N0106.N0428.N0770.N1752.d007507
#print axioms _root_.GD.N0106.N0428.N0770.N1752.d007508
