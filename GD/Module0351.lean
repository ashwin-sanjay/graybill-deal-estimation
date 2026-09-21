import GD.Module0349
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Group.Integral













set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1530
noncomputable section

open MeasureTheory Set Complex
open _root_.GD.N0106.N0428.N0765.N1533
open Complex.HadamardThreeLines

def d005194 (f : ℂ → ℂ) (y : ℝ) (t : ℝ) : ℂ :=
  f ((t : ℂ) + (y : ℂ) * Complex.I)

def d005195 (f : ℂ → ℂ) (y : ℝ) : ℝ :=
  ∫ t : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1530.d005194 f y t‖

def d005196 (f : ℂ → ℂ) (d y : ℝ) : ℝ :=
  ((d - y) / (2 * d)) * _root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d) +
    ((d + y) / (2 * d)) * _root_.GD.N0106.N0428.N0765.N1530.d005195 f d

theorem d005197 (f : ℂ → ℂ) (y : ℝ) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1530.d005195 f y :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem d005198 (f : ℂ → ℂ) (z : ℂ) (t : ℝ) :
    f ((t : ℂ) + z) = _root_.GD.N0106.N0428.N0765.N1530.d005194 f z.im (t + z.re) := by
  unfold _root_.GD.N0106.N0428.N0765.N1530.d005194
  congr 1
  apply Complex.ext <;> simp


theorem d005199 {f : ℂ → ℂ} {z : ℂ}
    (hf : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f z.im)) :
    Integrable (fun t : ℝ => f ((t : ℂ) + z)) := by
  have h := hf.comp_add_right z.re
  simpa only [_root_.GD.N0106.N0428.N0765.N1530.d005198] using h

theorem d005200 (f : ℂ → ℂ) (z : ℂ) :
    (∫ t : ℝ, ‖f ((t : ℂ) + z)‖) = _root_.GD.N0106.N0428.N0765.N1530.d005195 f z.im := by
  simp_rw [_root_.GD.N0106.N0428.N0765.N1530.d005198]
  exact integral_add_right_eq_self (fun t : ℝ => ‖_root_.GD.N0106.N0428.N0765.N1530.d005194 f z.im t‖) z.re

theorem d005201 {f : ℂ → ℂ} {u : ℝ → ℂ} {T : ℝ}
    (hu : Measurable u) (hunorm : ∀ t : ℝ, ‖u t‖ ≤ 1)
    {z : ℂ} (hf : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f z.im)) :
    ‖_root_.GD.N0106.N0428.N0765.N1533.d005165 T u f z‖ ≤ _root_.GD.N0106.N0428.N0765.N1530.d005195 f z.im := by
  calc
    _ ≤ ∫ t : ℝ, ‖f ((t : ℂ) + z)‖ :=
      _root_.GD.N0106.N0428.N0765.N1533.d005176 hu hunorm (_root_.GD.N0106.N0428.N0765.N1530.d005199 (z := z) hf)
    _ = _ := _root_.GD.N0106.N0428.N0765.N1530.d005200 f z

theorem d005202 {d : ℝ} {z : ℂ}
    (hz : z ∈ verticalStrip (-d) d) : Complex.I * z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005163 d := by
  change |(Complex.I * z).im| < d
  rw [Complex.I_mul_im]
  exact abs_lt.mpr hz

theorem d005203 {d : ℝ} {z : ℂ}
    (hz : z ∈ verticalClosedStrip (-d) d) : Complex.I * z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d := by
  change |(Complex.I * z).im| ≤ d
  rw [Complex.I_mul_im]
  exact abs_le.mpr hz

theorem d005204 {f : ℂ → ℂ} {u : ℝ → ℂ} {d M T : ℝ}
    (hT : 0 ≤ T) (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hu : Measurable u) (hunorm : ∀ t : ℝ, ‖u t‖ ≤ 1)
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖f z‖ ≤ M) :
    DiffContOnCl ℂ (fun z : ℂ => _root_.GD.N0106.N0428.N0765.N1533.d005165 T u f (Complex.I * z))
      (verticalStrip (-d) d) ∧
      BddAbove ((fun z : ℂ => ‖_root_.GD.N0106.N0428.N0765.N1533.d005165 T u f (Complex.I * z)‖) ''
        verticalClosedStrip (-d) d) := by
  obtain ⟨hG, _hGB, _hGnorm⟩ := _root_.GD.N0106.N0428.N0765.N1533.d005182 hT hc hf hu hunorm hM
  constructor
  · have hrot : Differentiable ℂ (fun z : ℂ => Complex.I * z) := by fun_prop
    exact hG.comp hrot.diffContOnCl (fun _ hz => _root_.GD.N0106.N0428.N0765.N1530.d005202 hz)
  · refine ⟨2 * T * M, ?_⟩
    rintro b ⟨z, hz, rfl⟩
    exact _root_.GD.N0106.N0428.N0765.N1533.d005175 hT hunorm hM (_root_.GD.N0106.N0428.N0765.N1530.d005203 hz)



theorem d005205 {f : ℂ → ℂ} {u : ℝ → ℂ} {d M T y : ℝ}
    (hd : 0 < d) (hT : 0 ≤ T) (hy : |y| ≤ d)
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hu : Measurable u) (hunorm : ∀ t : ℝ, ‖u t‖ ≤ 1)
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖f z‖ ≤ M)
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (-d)))
    (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f d)) :
    ‖_root_.GD.N0106.N0428.N0765.N1533.d005165 T u f ((y : ℂ) * Complex.I)‖ ≤
      (_root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d)) ^ ((d - y) / (2 * d)) *
      (_root_.GD.N0106.N0428.N0765.N1530.d005195 f d) ^ ((d + y) / (2 * d)) := by
  obtain ⟨hG, hGB⟩ := _root_.GD.N0106.N0428.N0765.N1530.d005204 hT hc hf hu hunorm hM
  have hz : (y : ℂ) ∈ verticalClosedStrip (-d) d := by
    simpa only [verticalClosedStrip, mem_preimage, mem_Icc, Complex.ofReal_re] using abs_le.mp hy
  have hleft : ∀ z ∈ Complex.re ⁻¹' {(-d)},
      ‖_root_.GD.N0106.N0428.N0765.N1533.d005165 T u f (Complex.I * z)‖ ≤ _root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d) := by
    intro z hzleft
    have hre : z.re = -d := hzleft
    have him : (Complex.I * z).im = -d := by simpa only [Complex.I_mul_im] using hre
    have hi : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (Complex.I * z).im) := by
      rw [him]
      exact hminus
    simpa only [him] using _root_.GD.N0106.N0428.N0765.N1530.d005201 (T := T) (z := Complex.I * z) hu hunorm hi
  have hright : ∀ z ∈ Complex.re ⁻¹' {d},
      ‖_root_.GD.N0106.N0428.N0765.N1533.d005165 T u f (Complex.I * z)‖ ≤ _root_.GD.N0106.N0428.N0765.N1530.d005195 f d := by
    intro z hzright
    have hre : z.re = d := hzright
    have him : (Complex.I * z).im = d := by simpa only [Complex.I_mul_im] using hre
    have hi : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (Complex.I * z).im) := by
      rw [him]
      exact hplus
    simpa only [him] using _root_.GD.N0106.N0428.N0765.N1530.d005201 (T := T) (z := Complex.I * z) hu hunorm hi
  have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := fun z : ℂ => _root_.GD.N0106.N0428.N0765.N1533.d005165 T u f (Complex.I * z))
    (by linarith : -d < d) hz hG hGB hleft hright
  have heleft : 1 - ((y : ℂ).re - -d) / (d - -d) = (d - y) / (2 * d) := by
    simp only [Complex.ofReal_re, sub_neg_eq_add]
    field_simp [ne_of_gt hd, show d + d ≠ 0 by linarith]
    ring
  have heright : ((y : ℂ).re - -d) / (d - -d) = (d + y) / (2 * d) := by
    simp only [Complex.ofReal_re, sub_neg_eq_add]
    congr 1 <;> ring
  rw [heleft, heright] at h
  simpa only [mul_comm Complex.I (y : ℂ)] using h



theorem d005206 {f : ℂ → ℂ} {d y : ℝ}
    (hd : 0 < d) (hy : |y| ≤ d) :
    (_root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d)) ^ ((d - y) / (2 * d)) *
      (_root_.GD.N0106.N0428.N0765.N1530.d005195 f d) ^ ((d + y) / (2 * d)) ≤ _root_.GD.N0106.N0428.N0765.N1530.d005196 f d y := by
  have hy' := abs_le.mp hy
  have hwminus : 0 ≤ (d - y) / (2 * d) :=
    div_nonneg (by linarith) (by positivity)
  have hwplus : 0 ≤ (d + y) / (2 * d) :=
    div_nonneg (by linarith) (by positivity)
  have hsum : (d - y) / (2 * d) + (d + y) / (2 * d) = 1 := by
    field_simp [ne_of_gt hd]
    ring
  exact Real.geom_mean_le_arith_mean2_weighted hwminus hwplus
    (_root_.GD.N0106.N0428.N0765.N1530.d005197 f (-d)) (_root_.GD.N0106.N0428.N0765.N1530.d005197 f d) hsum

theorem d005207 {f : ℂ → ℂ} {u : ℝ → ℂ} {d M T y : ℝ}
    (hd : 0 < d) (hT : 0 ≤ T) (hy : |y| ≤ d)
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hu : Measurable u) (hunorm : ∀ t : ℝ, ‖u t‖ ≤ 1)
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖f z‖ ≤ M)
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (-d)))
    (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f d)) :
    ‖_root_.GD.N0106.N0428.N0765.N1533.d005165 T u f ((y : ℂ) * Complex.I)‖ ≤ _root_.GD.N0106.N0428.N0765.N1530.d005196 f d y :=
  (_root_.GD.N0106.N0428.N0765.N1530.d005205 hd hT hy hc hf hu hunorm hM hminus hplus).trans
    (_root_.GD.N0106.N0428.N0765.N1530.d005206 hd hy)

end
end GD.N0106.N0428.N0765.N1530

#print axioms _root_.GD.N0106.N0428.N0765.N1530.d005199
#print axioms _root_.GD.N0106.N0428.N0765.N1530.d005204
#print axioms _root_.GD.N0106.N0428.N0765.N1530.d005205
#print axioms _root_.GD.N0106.N0428.N0765.N1530.d005207
