import GD.Module1289
import GD.Module1290
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Bochner.Basic













set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace GD.N0106.N0428.N0765.N1558
noncomputable section

open MeasureTheory _root_.GD.N0106.N0428.N0765.N1616



theorem d021014 {eta u v w d t : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2) (ht : |t| ≤ d)
    (a : ℝ) (n : ℕ) :
    Continuous (fun c : ℝ =>
      _root_.GD.N0106.N0428.N0765.N1563.d020973 a n eta u v w ((c : ℂ) + (t : ℂ) * Complex.I)) := by
  have hline : Continuous (fun c : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) := by
    fun_prop
  have hQ : Continuous (fun c : ℝ =>
      _root_.GD.N0106.N0428.N0765.N1563.d020972 eta u v w ((c : ℂ) + (t : ℂ) * Complex.I)) :=
    (_root_.GD.N0106.N0428.N0765.N1563.d020988 eta u v w).continuous.comp hline
  have hslit (c : ℝ) :
      _root_.GD.N0106.N0428.N0765.N1563.d020972 eta u v w ((c : ℂ) + (t : ℂ) * Complex.I) ∈
        Complex.slitPlane := by
    apply _root_.GD.N0106.N0428.N0765.N1563.d020987 heta hu hv hw hd0 hd
    simpa using ht
  have hpow : Continuous (fun c : ℝ =>
      _root_.GD.N0106.N0428.N0765.N1563.d020972 eta u v w ((c : ℂ) + (t : ℂ) * Complex.I) ^
        ((-21 / 2 : ℝ) : ℂ)) :=
    hQ.cpow continuous_const hslit
  have hnum : Continuous (fun c : ℝ =>
      Complex.exp ((a : ℂ) * ((c : ℂ) + (t : ℂ) * Complex.I)) *
        (1 + Complex.exp ((c : ℂ) + (t : ℂ) * Complex.I)) ^ n) := by
    fun_prop
  exact hnum.mul hpow

theorem d021015 {eta u v w d t : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2) (ht : |t| ≤ d) :
    Continuous (fun c : ℝ =>
      _root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w ((c : ℂ) + (t : ℂ) * Complex.I)) := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1563.d020974] using
    _root_.GD.N0106.N0428.N0765.N1558.d021014 heta hu hv hw hd0 hd ht (11 / 2) 10

theorem d021016 {eta u v w d t : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2) (ht : |t| ≤ d) :
    Continuous (fun c : ℝ =>
      _root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w ((c : ℂ) + (t : ℂ) * Complex.I)) := by
  simpa only [_root_.GD.N0106.N0428.N0765.N1563.d020975] using
    _root_.GD.N0106.N0428.N0765.N1558.d021014 heta hu hv hw hd0 hd ht (13 / 2) 9

theorem d021017 {eta u v w d : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2)
    {z : ℂ} (hz : |z.im| ≤ d) :
    ‖_root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w z‖ ≤
      (Real.cos d) ^ (-21 / 2 : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w z.re := by
  simpa only [show (-21 / 2 : ℝ) = -(21 / 2) by ring,
    Real.rpow_neg_eq_inv_rpow] using
      _root_.GD.N0106.N0428.N0765.N1563.d020994 heta hu hv hw hd0 hd hz

theorem d021018 {eta u v w d : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2)
    {z : ℂ} (hz : |z.im| ≤ d) :
    ‖_root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w z‖ ≤
      (Real.cos d) ^ (-21 / 2 : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w z.re := by
  simpa only [show (-21 / 2 : ℝ) = -(21 / 2) by ring,
    Real.rpow_neg_eq_inv_rpow] using
      _root_.GD.N0106.N0428.N0765.N1563.d020995 heta hu hv hw hd0 hd hz

theorem d021019 {eta u v w d t : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2) (ht : |t| ≤ d) (c : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (Real.cos d) ^ (-21 / 2 : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c := by
  have hz : |((c : ℂ) + (t : ℂ) * Complex.I).im| ≤ d := by simpa using ht
  simpa using _root_.GD.N0106.N0428.N0765.N1558.d021017 heta hu hv hw hd0 hd hz

theorem d021020 {eta u v w d t : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2) (ht : |t| ≤ d) (c : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (Real.cos d) ^ (-21 / 2 : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c := by
  have hz : |((c : ℂ) + (t : ℂ) * Complex.I).im| ≤ d := by simpa using ht
  simpa using _root_.GD.N0106.N0428.N0765.N1558.d021018 heta hu hv hw hd0 hd hz

theorem d021021 {eta u v w d t : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2) (ht : |t| ≤ d) :
    Integrable (fun c : ℝ =>
      _root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w ((c : ℂ) + (t : ℂ) * Complex.I)) := by
  have hg := (_root_.GD.N0106.N0428.N0765.N1564.d021012 heta hu hv hw).const_mul
    ((Real.cos d) ^ (-21 / 2 : ℝ))
  refine Integrable.mono' hg
    (_root_.GD.N0106.N0428.N0765.N1558.d021015 heta hu hv hw hd0 hd ht).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (_root_.GD.N0106.N0428.N0765.N1558.d021019 heta hu hv hw hd0 hd ht)

theorem d021022 {eta u v w d t : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2) (ht : |t| ≤ d) :
    Integrable (fun c : ℝ =>
      _root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w ((c : ℂ) + (t : ℂ) * Complex.I)) := by
  have hg := (_root_.GD.N0106.N0428.N0765.N1564.d021013 heta hu hv hw).const_mul
    ((Real.cos d) ^ (-21 / 2 : ℝ))
  refine Integrable.mono' hg
    (_root_.GD.N0106.N0428.N0765.N1558.d021016 heta hu hv hw hd0 hd ht).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (_root_.GD.N0106.N0428.N0765.N1558.d021020 heta hu hv hw hd0 hd ht)

theorem d021023 {eta u v w d t : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2) (ht : |t| ≤ d) :
    (∫ c : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w ((c : ℂ) + (t : ℂ) * Complex.I)‖) ≤
      (Real.cos d) ^ (-21 / 2 : ℝ) * ∫ c : ℝ, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c := by
  have hf := (_root_.GD.N0106.N0428.N0765.N1558.d021021 heta hu hv hw hd0 hd ht).norm
  have hg := (_root_.GD.N0106.N0428.N0765.N1564.d021012 heta hu hv hw).const_mul
    ((Real.cos d) ^ (-21 / 2 : ℝ))
  calc
    _ ≤ ∫ c : ℝ, (Real.cos d) ^ (-21 / 2 : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c :=
      integral_mono hf hg (_root_.GD.N0106.N0428.N0765.N1558.d021019 heta hu hv hw hd0 hd ht)
    _ = _ := integral_const_mul _ _

theorem d021024 {eta u v w d t : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2) (ht : |t| ≤ d) :
    (∫ c : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w ((c : ℂ) + (t : ℂ) * Complex.I)‖) ≤
      (Real.cos d) ^ (-21 / 2 : ℝ) * ∫ c : ℝ, _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c := by
  have hf := (_root_.GD.N0106.N0428.N0765.N1558.d021022 heta hu hv hw hd0 hd ht).norm
  have hg := (_root_.GD.N0106.N0428.N0765.N1564.d021013 heta hu hv hw).const_mul
    ((Real.cos d) ^ (-21 / 2 : ℝ))
  calc
    _ ≤ ∫ c : ℝ, (Real.cos d) ^ (-21 / 2 : ℝ) * _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c :=
      integral_mono hf hg (_root_.GD.N0106.N0428.N0765.N1558.d021020 heta hu hv hw hd0 hd ht)
    _ = _ := integral_const_mul _ _

theorem d021025 {eta u v w d t : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2) (ht : |t| ≤ d) :
    ‖∫ c : ℝ, _root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (Real.cos d) ^ (-21 / 2 : ℝ) * ∫ c : ℝ, _root_.GD.N0106.N0428.N0765.N1616.d020957 eta u v w c := by
  exact (norm_integral_le_integral_norm _).trans
    (_root_.GD.N0106.N0428.N0765.N1558.d021023 heta hu hv hw hd0 hd ht)

theorem d021026 {eta u v w d t : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2) (ht : |t| ≤ d) :
    ‖∫ c : ℝ, _root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (Real.cos d) ^ (-21 / 2 : ℝ) * ∫ c : ℝ, _root_.GD.N0106.N0428.N0765.N1616.d020958 eta u v w c := by
  exact (norm_integral_le_integral_norm _).trans
    (_root_.GD.N0106.N0428.N0765.N1558.d021024 heta hu hv hw hd0 hd ht)

theorem d021027 {eta u v w d : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2)
    {z : ℂ} (hz : |z.im| ≤ d) (hc : z.re ≤ 0) :
    ‖_root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w z‖ ≤ (Real.cos d) ^ (-21 / 2 : ℝ) *
      ((2 : ℝ) ^ 10 * v ^ (-21 / 2 : ℝ) * Real.exp (11 * z.re / 2)) := by
  have hcpos : 0 ≤ Real.cos d :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hd⟩).le
  exact (_root_.GD.N0106.N0428.N0765.N1558.d021017 heta hu hv hw hd0 hd hz).trans
    (mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1564.d021003 heta hu hv hw hc)
      (Real.rpow_nonneg hcpos _))

theorem d021028 {eta u v w d : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2)
    {z : ℂ} (hz : |z.im| ≤ d) (hc : z.re ≤ 0) :
    ‖_root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w z‖ ≤ (Real.cos d) ^ (-21 / 2 : ℝ) *
      ((2 : ℝ) ^ 9 * v ^ (-21 / 2 : ℝ) * Real.exp (13 * z.re / 2)) := by
  have hcpos : 0 ≤ Real.cos d :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hd⟩).le
  exact (_root_.GD.N0106.N0428.N0765.N1558.d021018 heta hu hv hw hd0 hd hz).trans
    (mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1564.d021004 heta hu hv hw hc)
      (Real.rpow_nonneg hcpos _))

theorem d021029 {eta u v w d : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2)
    {z : ℂ} (hz : |z.im| ≤ d) (hc : 0 ≤ z.re) :
    ‖_root_.GD.N0106.N0428.N0765.N1563.d020974 eta u v w z‖ ≤ (Real.cos d) ^ (-21 / 2 : ℝ) *
      ((2 : ℝ) ^ 10 * (eta * w) ^ (-21 / 2 : ℝ) * Real.exp (-11 * z.re / 2)) := by
  have hcpos : 0 ≤ Real.cos d :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hd⟩).le
  exact (_root_.GD.N0106.N0428.N0765.N1558.d021017 heta hu hv hw hd0 hd hz).trans
    (mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1564.d021005 heta hu hv hw hc)
      (Real.rpow_nonneg hcpos _))

theorem d021030 {eta u v w d : ℝ}
    (heta : 0 < eta) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hd0 : 0 ≤ d) (hd : d < Real.pi / 2)
    {z : ℂ} (hz : |z.im| ≤ d) (hc : 0 ≤ z.re) :
    ‖_root_.GD.N0106.N0428.N0765.N1563.d020975 eta u v w z‖ ≤ (Real.cos d) ^ (-21 / 2 : ℝ) *
      ((2 : ℝ) ^ 9 * (eta * w) ^ (-21 / 2 : ℝ) * Real.exp (-11 * z.re / 2)) := by
  have hcpos : 0 ≤ Real.cos d :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hd⟩).le
  exact (_root_.GD.N0106.N0428.N0765.N1558.d021018 heta hu hv hw hd0 hd hz).trans
    (mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1564.d021006 heta hu hv hw hc)
      (Real.rpow_nonneg hcpos _))

end
end GD.N0106.N0428.N0765.N1558

#print axioms _root_.GD.N0106.N0428.N0765.N1558.d021014
#print axioms _root_.GD.N0106.N0428.N0765.N1558.d021015
#print axioms _root_.GD.N0106.N0428.N0765.N1558.d021016
#print axioms _root_.GD.N0106.N0428.N0765.N1558.d021017
#print axioms _root_.GD.N0106.N0428.N0765.N1558.d021018
#print axioms _root_.GD.N0106.N0428.N0765.N1558.d021019
#print axioms _root_.GD.N0106.N0428.N0765.N1558.d021020
#print axioms _root_.GD.N0106.N0428.N0765.N1558.d021021
#print axioms _root_.GD.N0106.N0428.N0765.N1558.d021022
#print axioms _root_.GD.N0106.N0428.N0765.N1558.d021023
#print axioms _root_.GD.N0106.N0428.N0765.N1558.d021024
#print axioms _root_.GD.N0106.N0428.N0765.N1558.d021025
#print axioms _root_.GD.N0106.N0428.N0765.N1558.d021026
#print axioms _root_.GD.N0106.N0428.N0765.N1558.d021027
#print axioms _root_.GD.N0106.N0428.N0765.N1558.d021028
#print axioms _root_.GD.N0106.N0428.N0765.N1558.d021029
#print axioms _root_.GD.N0106.N0428.N0765.N1558.d021030
