import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper












set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1550
noncomputable section

open MeasureTheory Filter Set Complex
open scoped Topology FourierTransform

def d005473 (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * Complex.I

def d005474 (f : ℂ → ℂ) (y x : ℝ) : ℂ := f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x y)

def d005475 (f : ℂ → ℂ) (x y : ℝ) : ℂ :=
  ∫ s : ℝ in 0..y, f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x s)

@[simp] theorem d005476 (x y : ℝ) : (_root_.GD.N0106.N0428.N0765.N1550.d005473 x y).re = x := by simp [_root_.GD.N0106.N0428.N0765.N1550.d005473]
@[simp] theorem d005477 (x y : ℝ) : (_root_.GD.N0106.N0428.N0765.N1550.d005473 x y).im = y := by simp [_root_.GD.N0106.N0428.N0765.N1550.d005473]
@[simp] theorem d005478 (x : ℝ) : _root_.GD.N0106.N0428.N0765.N1550.d005473 x 0 = (x : ℂ) := by simp [_root_.GD.N0106.N0428.N0765.N1550.d005473]

private theorem d005479 {d y s : ℝ} (hd : 0 ≤ d)
    (hy : |y| ≤ d) (hs : s ∈ uIcc 0 y) : |s| ≤ d := by
  have hy' := abs_le.mp hy
  change min 0 y ≤ s ∧ s ≤ max 0 y at hs
  exact abs_le.mpr ⟨(le_min (by linarith) hy'.1).trans hs.1,
    hs.2.trans (max_le hd hy'.2)⟩



theorem d005480 {f : ℂ → ℂ} {d y : ℝ} (hd : 0 ≤ d)
    (hy : |y| ≤ d)
    (hf : ∀ z : ℂ, |z.im| ≤ d → DifferentiableAt ℂ f z) (R : ℝ) :
    (∫ x : ℝ in -R..R, _root_.GD.N0106.N0428.N0765.N1550.d005474 f 0 x) -
      (∫ x : ℝ in -R..R, _root_.GD.N0106.N0428.N0765.N1550.d005474 f y x) +
      Complex.I * _root_.GD.N0106.N0428.N0765.N1550.d005475 f R y - Complex.I * _root_.GD.N0106.N0428.N0765.N1550.d005475 f (-R) y = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    f (_root_.GD.N0106.N0428.N0765.N1550.d005473 (-R) 0) (_root_.GD.N0106.N0428.N0765.N1550.d005473 R y) (by
      intro z hz
      apply (hf z ?_).differentiableWithinAt
      apply _root_.GD.N0106.N0428.N0765.N1550.d005479 hd hy
      simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005477, Set.mem_preimage] using hz.2)
  simpa [_root_.GD.N0106.N0428.N0765.N1550.d005474, _root_.GD.N0106.N0428.N0765.N1550.d005475, _root_.GD.N0106.N0428.N0765.N1550.d005473, smul_eq_mul] using h



theorem d005481 {g : ℝ → ℝ → ℂ} {y K b : ℝ}
    (hb : 0 < b)
    (hbound : ∀ R : ℝ, 0 ≤ R → ∀ s ∈ uIoc 0 y,
      ‖g R s‖ ≤ K * Real.exp (-b * R)) :
    Tendsto (fun R : ℝ => ∫ s : ℝ in 0..y, g R s) atTop (𝓝 0) := by
  have hmajorant : Tendsto (fun R : ℝ =>
      (K * Real.exp (-b * R)) * |y|) atTop (𝓝 0) := by
    have hlinear : Tendsto (fun R : ℝ => -b * R) atTop atBot :=
      Filter.Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_id
    simpa only [mul_zero, zero_mul, Function.comp_apply] using
      ((Real.tendsto_exp_atBot.comp hlinear).const_mul K).mul_const |y|
  apply squeeze_zero_norm' _ hmajorant
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  simpa only [sub_zero] using
    intervalIntegral.norm_integral_le_of_norm_le_const (hbound R hR)



theorem d005482 {f : ℂ → ℂ} {d y AL AR a b : ℝ}
    (hd : 0 ≤ d) (hy : |y| ≤ d)
    (hf : ∀ z : ℂ, |z.im| ≤ d → DifferentiableAt ℂ f z)
    (h0 : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 f 0)) (hyint : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 f y))
    (ha : 0 < a) (hb : 0 < b)
    (hleft : ∀ z : ℂ, |z.im| ≤ d → z.re ≤ 0 →
      ‖f z‖ ≤ AL * Real.exp (a * z.re))
    (hright : ∀ z : ℂ, |z.im| ≤ d → 0 ≤ z.re →
      ‖f z‖ ≤ AR * Real.exp (-b * z.re)) :
    (∫ x : ℝ, _root_.GD.N0106.N0428.N0765.N1550.d005474 f 0 x) = ∫ x : ℝ, _root_.GD.N0106.N0428.N0765.N1550.d005474 f y x := by
  have hR : Tendsto (fun R : ℝ => _root_.GD.N0106.N0428.N0765.N1550.d005475 f R y) atTop (𝓝 0) := by
    apply _root_.GD.N0106.N0428.N0765.N1550.d005481 (K := AR) hb
    intro R hR s hs
    have hs' : s ∈ uIcc 0 y := ⟨le_of_lt hs.1, hs.2⟩
    have hstrip := _root_.GD.N0106.N0428.N0765.N1550.d005479 hd hy hs'
    simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005476, _root_.GD.N0106.N0428.N0765.N1550.d005477] using hright (_root_.GD.N0106.N0428.N0765.N1550.d005473 R s) (by simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005477] using hstrip)
      (by simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005476] using hR)
  have hL : Tendsto (fun R : ℝ => _root_.GD.N0106.N0428.N0765.N1550.d005475 f (-R) y) atTop (𝓝 0) := by
    apply _root_.GD.N0106.N0428.N0765.N1550.d005481 (K := AL) ha
    intro R hR s hs
    have hs' : s ∈ uIcc 0 y := ⟨le_of_lt hs.1, hs.2⟩
    have hstrip := _root_.GD.N0106.N0428.N0765.N1550.d005479 hd hy hs'
    have h := hleft (_root_.GD.N0106.N0428.N0765.N1550.d005473 (-R) s) (by simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005477] using hstrip)
      (by simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005476] using neg_nonpos.mpr hR)
    simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005476, mul_neg, neg_mul] using h
  have hbase : Tendsto (fun R : ℝ => ∫ x : ℝ in -R..R, _root_.GD.N0106.N0428.N0765.N1550.d005474 f 0 x)
      atTop (𝓝 (∫ x : ℝ, _root_.GD.N0106.N0428.N0765.N1550.d005474 f 0 x)) :=
    intervalIntegral_tendsto_integral h0 tendsto_neg_atTop_atBot tendsto_id
  have hshift : Tendsto (fun R : ℝ => ∫ x : ℝ in -R..R, _root_.GD.N0106.N0428.N0765.N1550.d005474 f y x)
      atTop (𝓝 (∫ x : ℝ, _root_.GD.N0106.N0428.N0765.N1550.d005474 f y x)) :=
    intervalIntegral_tendsto_integral hyint tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hbase.sub hshift).add (hR.const_mul Complex.I)).sub
    (hL.const_mul Complex.I)
  have hzero : Tendsto (fun R : ℝ =>
      (∫ x : ℝ in -R..R, _root_.GD.N0106.N0428.N0765.N1550.d005474 f 0 x) -
        (∫ x : ℝ in -R..R, _root_.GD.N0106.N0428.N0765.N1550.d005474 f y x) +
        Complex.I * _root_.GD.N0106.N0428.N0765.N1550.d005475 f R y - Complex.I * _root_.GD.N0106.N0428.N0765.N1550.d005475 f (-R) y)
      atTop (𝓝 0) := by
    simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005480 hd hy hf] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 0))
  have heq := tendsto_nhds_unique hlim hzero
  simpa only [mul_zero, add_zero, sub_zero, sub_eq_zero] using heq


def d005483 (xi : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (((-2 * Real.pi * xi : ℝ) : ℂ) * (z * Complex.I)) * f z

theorem d005484 (xi : ℝ) (f : ℂ → ℂ) (z : ℂ) :
    ‖_root_.GD.N0106.N0428.N0765.N1550.d005483 xi f z‖ = Real.exp (2 * Real.pi * xi * z.im) * ‖f z‖ := by
  have hre : (((-2 * Real.pi * xi : ℝ) : ℂ) * (z * Complex.I)).re =
      2 * Real.pi * xi * z.im := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [_root_.GD.N0106.N0428.N0765.N1550.d005483, norm_mul, Complex.norm_exp, hre]

theorem d005485 {f : ℂ → ℂ} {d : ℝ} (xi : ℝ)
    {z : ℂ} (hz : |z.im| ≤ d) :
    ‖_root_.GD.N0106.N0428.N0765.N1550.d005483 xi f z‖ ≤ Real.exp (2 * Real.pi * |xi| * d) * ‖f z‖ := by
  rw [_root_.GD.N0106.N0428.N0765.N1550.d005484]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hmul : xi * z.im ≤ |xi| * d := by
    calc
      _ ≤ |xi * z.im| := le_abs_self _
      _ = |xi| * |z.im| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ 2 * Real.pi)

theorem d005486 {f : ℂ → ℂ} {z : ℂ}
    (xi : ℝ) (hf : DifferentiableAt ℂ f z) : DifferentiableAt ℂ (_root_.GD.N0106.N0428.N0765.N1550.d005483 xi f) z := by
  have hexp : DifferentiableAt ℂ (fun z : ℂ =>
      Complex.exp (((-2 * Real.pi * xi : ℝ) : ℂ) * (z * Complex.I))) z := by
    fun_prop
  exact hexp.mul hf

theorem d005487 {f : ℂ → ℂ} {y : ℝ} (xi : ℝ)
    (hf : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 f y)) : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1550.d005483 xi f) y) := by
  have he : Continuous (fun x : ℝ =>
      Complex.exp (((-2 * Real.pi * xi : ℝ) : ℂ) * (_root_.GD.N0106.N0428.N0765.N1550.d005473 x y * Complex.I))) := by
    unfold _root_.GD.N0106.N0428.N0765.N1550.d005473
    fun_prop
  have hm : AEStronglyMeasurable (_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1550.d005483 xi f) y) := by
    exact he.aestronglyMeasurable.mul hf.aestronglyMeasurable
  refine Integrable.mono' (hf.norm.const_mul (Real.exp (2 * Real.pi * xi * y))) hm ?_
  filter_upwards [] with x
  exact le_of_eq (by simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005474, _root_.GD.N0106.N0428.N0765.N1550.d005477] using _root_.GD.N0106.N0428.N0765.N1550.d005484 xi f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x y))

theorem d005488 (f : ℂ → ℂ) (xi : ℝ) :
    𝓕 (_root_.GD.N0106.N0428.N0765.N1550.d005474 f 0) xi = ∫ x : ℝ, _root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1550.d005483 xi f) 0 x := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [_root_.GD.N0106.N0428.N0765.N1550.d005474, _root_.GD.N0106.N0428.N0765.N1550.d005483, _root_.GD.N0106.N0428.N0765.N1550.d005478, smul_eq_mul]
  congr 1
  congr 1
  push_cast
  ring



theorem d005489 {f : ℂ → ℂ} {d y AL AR a b : ℝ}
    (hd : 0 ≤ d) (hy : |y| ≤ d)
    (hf : ∀ z : ℂ, |z.im| ≤ d → DifferentiableAt ℂ f z)
    (h0 : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 f 0)) (hyint : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 f y))
    (ha : 0 < a) (hb : 0 < b)
    (hleft : ∀ z : ℂ, |z.im| ≤ d → z.re ≤ 0 →
      ‖f z‖ ≤ AL * Real.exp (a * z.re))
    (hright : ∀ z : ℂ, |z.im| ≤ d → 0 ≤ z.re →
      ‖f z‖ ≤ AR * Real.exp (-b * z.re)) (xi : ℝ) :
    ‖𝓕 (_root_.GD.N0106.N0428.N0765.N1550.d005474 f 0) xi‖ ≤
      Real.exp (2 * Real.pi * xi * y) * ∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1550.d005474 f y x‖ := by
  have htwist : ∀ z : ℂ, |z.im| ≤ d → DifferentiableAt ℂ (_root_.GD.N0106.N0428.N0765.N1550.d005483 xi f) z :=
    fun z hz => _root_.GD.N0106.N0428.N0765.N1550.d005486 xi (hf z hz)
  have htwleft : ∀ z : ℂ, |z.im| ≤ d → z.re ≤ 0 →
      ‖_root_.GD.N0106.N0428.N0765.N1550.d005483 xi f z‖ ≤ (Real.exp (2 * Real.pi * |xi| * d) * AL) *
        Real.exp (a * z.re) := by
    intro z hz hc
    calc
      _ ≤ Real.exp (2 * Real.pi * |xi| * d) * ‖f z‖ := _root_.GD.N0106.N0428.N0765.N1550.d005485 xi hz
      _ ≤ Real.exp (2 * Real.pi * |xi| * d) * (AL * Real.exp (a * z.re)) :=
        mul_le_mul_of_nonneg_left (hleft z hz hc) (Real.exp_pos _).le
      _ = _ := by ring
  have htwright : ∀ z : ℂ, |z.im| ≤ d → 0 ≤ z.re →
      ‖_root_.GD.N0106.N0428.N0765.N1550.d005483 xi f z‖ ≤ (Real.exp (2 * Real.pi * |xi| * d) * AR) *
        Real.exp (-b * z.re) := by
    intro z hz hc
    calc
      _ ≤ Real.exp (2 * Real.pi * |xi| * d) * ‖f z‖ := _root_.GD.N0106.N0428.N0765.N1550.d005485 xi hz
      _ ≤ Real.exp (2 * Real.pi * |xi| * d) * (AR * Real.exp (-b * z.re)) :=
        mul_le_mul_of_nonneg_left (hright z hz hc) (Real.exp_pos _).le
      _ = _ := by ring
  have hshift := _root_.GD.N0106.N0428.N0765.N1550.d005482 hd hy htwist
    (_root_.GD.N0106.N0428.N0765.N1550.d005487 xi h0) (_root_.GD.N0106.N0428.N0765.N1550.d005487 xi hyint)
    ha hb htwleft htwright
  rw [_root_.GD.N0106.N0428.N0765.N1550.d005488, hshift]
  calc
    _ ≤ ∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1550.d005474 (_root_.GD.N0106.N0428.N0765.N1550.d005483 xi f) y x‖ := norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, Real.exp (2 * Real.pi * xi * y) * ‖_root_.GD.N0106.N0428.N0765.N1550.d005474 f y x‖ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simpa only [_root_.GD.N0106.N0428.N0765.N1550.d005474, _root_.GD.N0106.N0428.N0765.N1550.d005477] using _root_.GD.N0106.N0428.N0765.N1550.d005484 xi f (_root_.GD.N0106.N0428.N0765.N1550.d005473 x y)
    _ = _ := integral_const_mul _ _



theorem d005490 {f : ℂ → ℂ} {d AL AR a b : ℝ}
    (hd : 0 ≤ d)
    (hf : ∀ z : ℂ, |z.im| ≤ d → DifferentiableAt ℂ f z)
    (h0 : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 f 0))
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 f (-d))) (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1550.d005474 f d))
    (ha : 0 < a) (hb : 0 < b)
    (hleft : ∀ z : ℂ, |z.im| ≤ d → z.re ≤ 0 →
      ‖f z‖ ≤ AL * Real.exp (a * z.re))
    (hright : ∀ z : ℂ, |z.im| ≤ d → 0 ≤ z.re →
      ‖f z‖ ≤ AR * Real.exp (-b * z.re)) (xi : ℝ) :
    ‖𝓕 (_root_.GD.N0106.N0428.N0765.N1550.d005474 f 0) xi‖ ≤ Real.exp (-2 * Real.pi * d * |xi|) *
      ∫ x : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1550.d005474 f (if 0 ≤ xi then -d else d) x‖ := by
  by_cases hxi : 0 ≤ xi
  · have hy : |(-d)| ≤ d := by simpa only [abs_neg, abs_of_nonneg hd] using (le_refl d)
    have h := _root_.GD.N0106.N0428.N0765.N1550.d005489 hd hy hf h0 hminus ha hb hleft hright xi
    have he : 2 * Real.pi * xi * (-d) = -2 * Real.pi * d * |xi| := by
      rw [abs_of_nonneg hxi]
      ring
    simpa only [if_pos hxi, he] using h
  · have hy : |d| ≤ d := by simpa only [abs_of_nonneg hd] using (le_refl d)
    have h := _root_.GD.N0106.N0428.N0765.N1550.d005489 hd hy hf h0 hplus ha hb hleft hright xi
    have he : 2 * Real.pi * xi * d = -2 * Real.pi * d * |xi| := by
      rw [abs_of_neg (lt_of_not_ge hxi)]
      ring
    simpa only [if_neg hxi, he] using h

end
end GD.N0106.N0428.N0765.N1550

#print axioms _root_.GD.N0106.N0428.N0765.N1550.d005476
#print axioms _root_.GD.N0106.N0428.N0765.N1550.d005477
#print axioms _root_.GD.N0106.N0428.N0765.N1550.d005478
#print axioms _root_.GD.N0106.N0428.N0765.N1550.d005480
#print axioms _root_.GD.N0106.N0428.N0765.N1550.d005481
#print axioms _root_.GD.N0106.N0428.N0765.N1550.d005482
#print axioms _root_.GD.N0106.N0428.N0765.N1550.d005484
#print axioms _root_.GD.N0106.N0428.N0765.N1550.d005485
#print axioms _root_.GD.N0106.N0428.N0765.N1550.d005486
#print axioms _root_.GD.N0106.N0428.N0765.N1550.d005487
#print axioms _root_.GD.N0106.N0428.N0765.N1550.d005488
#print axioms _root_.GD.N0106.N0428.N0765.N1550.d005489
#print axioms _root_.GD.N0106.N0428.N0765.N1550.d005490
