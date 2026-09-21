import GD.Module0837
import GD.Module0543
import GD.Module0535
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals





set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GD.N0101.N0359
noncomputable section

open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0217
open _root_.GD.N0213.N0493

def d021659 (z : ℝ × ℝ) : ℝ := Real.log (z.1 / z.2)

@[fun_prop] theorem d021660 : Measurable _root_.GD.N0101.N0359.d021659 := by
  unfold _root_.GD.N0101.N0359.d021659
  fun_prop

def d021661 (z : ℝ × ℝ) : ℝ :=
  gammaPDFReal (1 / 2) (1 / 2) z.1 * gammaPDFReal (1 / 2) (1 / 2) z.2

@[fun_prop] theorem d021662 : Measurable _root_.GD.N0101.N0359.d021661 := by
  unfold _root_.GD.N0101.N0359.d021661
  fun_prop

theorem d021663 :
    _root_.GD.N0232.N0720.N1091.d012754 (1 / 2) (1 / 2) =
      _root_.GD.N0217.d008089.withDensity (fun z => ENNReal.ofReal (_root_.GD.N0101.N0359.d021661 z)) := by
  have hh : (0 : ℝ) < 1 / 2 := by norm_num
  rw [_root_.GD.N0232.N0720.N1091.d012754, _root_.GD.N0125.d008871 hh hh]
  unfold _root_.GD.N0125.d008870
  rw [prod_withDensity (by fun_prop) (by fun_prop)]
  apply congrArg (fun d => _root_.GD.N0217.d008089.withDensity d)
  funext z
  exact (ENNReal.ofReal_mul (gammaPDFReal_nonneg hh hh z.1)).symm

theorem d021664 :
    (((1 / 2 : ℝ) ^ (1 / 2 : ℝ)) / Real.Gamma (1 / 2)) ^ 2 =
      1 / (2 * Real.pi) := by
  have hp : ((1 / 2 : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = 1 / 2 := by
    rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2)]
    norm_num
  rw [div_pow, Real.Gamma_one_half_eq, hp, Real.sq_sqrt Real.pi_pos.le]
  ring


theorem d021665 (s v : ℝ) :
    (2 * Real.exp (2 * s)) * _root_.GD.N0101.N0359.d021661 (_root_.GD.N0217.d008091 (s, v)) =
      Real.exp s / Real.pi * Real.exp (-Real.exp s * Real.cosh v) := by
  let C : ℝ := (1 / 2 : ℝ) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2)
  have hC : C ^ 2 = 1 / (2 * Real.pi) := _root_.GD.N0101.N0359.d021664
  have hp : Real.exp (s + v) ^ (-(1 / 2 : ℝ)) *
      Real.exp (s - v) ^ (-(1 / 2 : ℝ)) = Real.exp (-s) := by
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
    congr 1
    ring
  have he : Real.exp (-((1 / 2 : ℝ) * Real.exp (s + v))) *
      Real.exp (-((1 / 2 : ℝ) * Real.exp (s - v))) =
      Real.exp (-Real.exp s * Real.cosh v) := by
    rw [← Real.exp_add]
    congr 1
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.cosh_eq]
    ring
  unfold _root_.GD.N0101.N0359.d021661 _root_.GD.N0217.d008091
  simp only [gammaPDFReal, if_pos (Real.exp_pos (s + v)).le,
    if_pos (Real.exp_pos (s - v)).le,
    show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num]
  change 2 * Real.exp (2 * s) *
    ((C * Real.exp (s + v) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-((1 / 2 : ℝ) * Real.exp (s + v)))) *
     (C * Real.exp (s - v) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-((1 / 2 : ℝ) * Real.exp (s - v))))) = _
  calc
    _ = 2 * C ^ 2 * (Real.exp (2 * s) *
      (Real.exp (s + v) ^ (-(1 / 2 : ℝ)) * Real.exp (s - v) ^ (-(1 / 2 : ℝ)))) *
      (Real.exp (-((1 / 2 : ℝ) * Real.exp (s + v))) *
        Real.exp (-((1 / 2 : ℝ) * Real.exp (s - v)))) := by ring
    _ = _ := by
      rw [hC, hp, he, ← Real.exp_add, show 2 * s + -s = s by ring]
      ring

theorem d021666 (s v : ℝ) : _root_.GD.N0101.N0359.d021659 (_root_.GD.N0217.d008091 (s, v)) = 2 * v := by
  unfold _root_.GD.N0101.N0359.d021659 _root_.GD.N0217.d008091
  rw [Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
  ring



theorem d021667 {c : ℝ} (hc : 0 < c) :
    (∫⁻ s : ℝ, ENNReal.ofReal (Real.exp s * Real.exp (-c * Real.exp s))) =
      ENNReal.ofReal (1 / c) := by
  have hi : Integrable (fun x : ℝ => Real.exp (-c * x)) (volume.restrict (Ioi 0)) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos hc) 0
  have hr : (∫ x : ℝ in Ioi 0, Real.exp (-c * x)) = 1 / c := by
    simpa using integral_exp_mul_Ioi (neg_neg_of_pos hc) 0
  have h := _root_.GD.N0217.d008093 (fun x => ENNReal.ofReal (Real.exp (-c * x)))
  simp_rw [← ENNReal.ofReal_mul (Real.exp_pos _).le] at h
  rw [← h, ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => (Real.exp_pos _).le), hr]

theorem d021668 (v : ℝ) :
    (∫⁻ s : ℝ, ENNReal.ofReal
      (Real.exp s / Real.pi * Real.exp (-Real.exp s * Real.cosh v))) =
      ENNReal.ofReal (1 / (Real.pi * Real.cosh v)) := by
  have he : (fun s : ℝ => ENNReal.ofReal
      (Real.exp s / Real.pi * Real.exp (-Real.exp s * Real.cosh v))) =
      fun s => ENNReal.ofReal Real.pi⁻¹ * ENNReal.ofReal
        (Real.exp s * Real.exp (-Real.cosh v * Real.exp s)) := by
    funext s
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr Real.pi_pos.le)]
    congr 1
    rw [show -Real.exp s * Real.cosh v = -Real.cosh v * Real.exp s by ring]
    ring
  rw [he, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    _root_.GD.N0101.N0359.d021667 (Real.cosh_pos v),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr Real.pi_pos.le)]
  congr 1
  ring



theorem d021669 (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z, f (_root_.GD.N0101.N0359.d021659 z) ∂_root_.GD.N0232.N0720.N1091.d012754 (1 / 2) (1 / 2)) =
      ∫⁻ ell : ℝ, ENNReal.ofReal (_root_.GD.N0213.N0493.d007990 ell) * f ell := by
  rw [_root_.GD.N0101.N0359.d021663]
  rw [lintegral_withDensity_eq_lintegral_mul _root_.GD.N0217.d008089
    (f := fun z => ENNReal.ofReal (_root_.GD.N0101.N0359.d021661 z)) _root_.GD.N0101.N0359.d021662.ennreal_ofReal
    (g := fun z => f (_root_.GD.N0101.N0359.d021659 z)) (hf.comp _root_.GD.N0101.N0359.d021660)]
  change (∫⁻ z, ENNReal.ofReal (_root_.GD.N0101.N0359.d021661 z) * f (_root_.GD.N0101.N0359.d021659 z) ∂_root_.GD.N0217.d008089) = _
  rw [_root_.GD.N0217.d008098 _root_.GD.N0101.N0359.d021661 _root_.GD.N0101.N0359.d021662
    (fun z => f (_root_.GD.N0101.N0359.d021659 z)) (hf.comp _root_.GD.N0101.N0359.d021660)]
  change (∫⁻ z, ENNReal.ofReal ((2 * Real.exp (2 * z.1)) * _root_.GD.N0101.N0359.d021661 (_root_.GD.N0217.d008091 z)) *
    f (_root_.GD.N0101.N0359.d021659 (_root_.GD.N0217.d008091 z)) ∂(volume : Measure ℝ).prod volume) = _
  rw [lintegral_prod _ (by fun_prop)]
  simp_rw [_root_.GD.N0101.N0359.d021665, _root_.GD.N0101.N0359.d021666]
  rw [lintegral_lintegral_swap (by fun_prop : Measurable
    (fun z : ℝ × ℝ => ENNReal.ofReal
      (Real.exp z.1 / Real.pi * Real.exp (-Real.exp z.1 * Real.cosh z.2)) *
      f (2 * z.2))).aemeasurable]
  calc
    _ = ∫⁻ v : ℝ, ENNReal.ofReal (1 / (Real.pi * Real.cosh v)) * f (2 * v) := by
      apply lintegral_congr
      intro v
      rw [lintegral_mul_const _ (by fun_prop), _root_.GD.N0101.N0359.d021668]
    _ = ∫⁻ v : ℝ, 2 * (ENNReal.ofReal (_root_.GD.N0213.N0493.d007990 (2 * v)) * f (2 * v)) := by
      apply lintegral_congr
      intro v
      have hd : (1 / (Real.pi * Real.cosh v)) = 2 * _root_.GD.N0213.N0493.d007990 (2 * v) := by
        unfold _root_.GD.N0213.N0493.d007990
        rw [show 2 * v / 2 = v by ring]
        ring
      rw [hd, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_assoc]
    _ = _ := by
      simpa only [sub_zero] using
        (_root_.GD.N0217.d008094 (fun ell => ENNReal.ofReal (_root_.GD.N0213.N0493.d007990 ell) * f ell) 0).symm

def d021670 : Measure ℝ :=
  volume.withDensity (fun ell => ENNReal.ofReal (_root_.GD.N0213.N0493.d007990 ell))

theorem d021671 :
    (_root_.GD.N0232.N0720.N1091.d012754 (1 / 2) (1 / 2)).map _root_.GD.N0101.N0359.d021659 = _root_.GD.N0101.N0359.d021670 := by
  apply Measure.ext_of_lintegral _root_.GD.N0101.N0359.d021670
  intro f hf
  rw [lintegral_map hf _root_.GD.N0101.N0359.d021660, _root_.GD.N0101.N0359.d021670,
    lintegral_withDensity_eq_lintegral_mul _ (by unfold _root_.GD.N0213.N0493.d007990; fun_prop) hf]
  exact _root_.GD.N0101.N0359.d021669 f hf

theorem d021672 : IsProbabilityMeasure _root_.GD.N0101.N0359.d021670 := by
  have hh : (0 : ℝ) < 1 / 2 := by norm_num
  letI := isProbabilityMeasure_gammaMeasure hh hh
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1091.d012754 (1 / 2) (1 / 2)) := by
    unfold _root_.GD.N0232.N0720.N1091.d012754
    infer_instance
  rw [← _root_.GD.N0101.N0359.d021671]
  exact Measure.isProbabilityMeasure_map _root_.GD.N0101.N0359.d021660.aemeasurable

end
end GD.N0101.N0359

#print axioms _root_.GD.N0101.N0359.d021663
#print axioms _root_.GD.N0101.N0359.d021665
#print axioms _root_.GD.N0101.N0359.d021668
#print axioms _root_.GD.N0101.N0359.d021669
#print axioms _root_.GD.N0101.N0359.d021671
#print axioms _root_.GD.N0101.N0359.d021672
