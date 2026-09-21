import GD.Module0274
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace GD.N0053
noncomputable section

theorem d005105 (a b : ℝ) : ∀ᵐ u ∂betaMeasure a b, u ∈ Ioo (0 : ℝ) 1 := by
  unfold betaMeasure betaPDF
  rw [ae_withDensity_iff ((measurable_betaPDFReal a b).ennreal_ofReal)]
  filter_upwards with u
  intro hu
  by_contra hnot
  have hout : ¬ (0 < u ∧ u < 1) := hnot
  simp [betaPDFReal, hout] at hu

theorem d005106 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    Integrable (fun u : ℝ => u ^ n) (betaMeasure a b) := by
  letI := isProbabilityMeasureBeta ha hb
  apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
  filter_upwards [_root_.GD.N0053.d005105 a b] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hu.1.le n)]
  exact pow_le_one₀ hu.1.le hu.2.le

def d005107 (u : ℝ) : ℝ := u + u * (1-u) * (u-3/5)
def d005108 (u : ℝ) : ℝ := 1 + (1-u) * (u-3/5)
def d005109 (u : ℝ) : ℝ := 1 - u * (u-3/5)

theorem d005110 (u : ℝ) : _root_.GD.N0053.d005107 u = u * _root_.GD.N0053.d005108 u := by
  unfold _root_.GD.N0053.d005107 _root_.GD.N0053.d005108
  ring

theorem d005111 (u : ℝ) : 1-_root_.GD.N0053.d005107 u = (1-u)*_root_.GD.N0053.d005109 u := by
  unfold _root_.GD.N0053.d005107 _root_.GD.N0053.d005109
  ring

theorem d005112 {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0053.d005107 u ∈ Icc (0 : ℝ) 1 := by
  have hp : 0 ≤ u*(1-u) := mul_nonneg hu.1 (sub_nonneg.mpr hu.2)
  have hlo := mul_nonneg hp hu.1
  have hhi := mul_nonneg hp (sub_nonneg.mpr hu.2)
  unfold _root_.GD.N0053.d005107
  constructor <;> nlinarith [mul_nonneg hu.1 hu.1,
    mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hu.2)]

theorem d005113 {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    |_root_.GD.N0053.d005107 u-u| ≤ u*(1-u) := by
  have hp : 0 ≤ u*(1-u) := mul_nonneg hu.1.le (sub_nonneg.mpr hu.2.le)
  have hlo := mul_nonneg hp hu.1.le
  have hhi := mul_nonneg hp (sub_nonneg.mpr hu.2.le)
  rw [abs_le]
  unfold _root_.GD.N0053.d005107
  constructor <;> nlinarith

private theorem d005114 :
    (∫ u : ℝ, u ∂betaMeasure (3/2) (1/2)) = 3/4 ∧
    (∫ u : ℝ, u^2 ∂betaMeasure (3/2) (1/2)) = 5/8 ∧
    (∫ u : ℝ, u^3 ∂betaMeasure (3/2) (1/2)) = 35/64 ∧
    (∫ u : ℝ, u^4 ∂betaMeasure (3/2) (1/2)) = 63/128 := by
  have h0 := (beta_pos (by norm_num : (0:ℝ)<3/2) (by norm_num : (0:ℝ)<1/2)).ne'
  have h1 := _root_.GD.N0235.d004038
    (by norm_num : (0:ℝ)<3/2) (by norm_num : (0:ℝ)<1/2)
  have h2 := _root_.GD.N0235.d004038
    (by norm_num : (0:ℝ)<5/2) (by norm_num : (0:ℝ)<1/2)
  have h3 := _root_.GD.N0235.d004038
    (by norm_num : (0:ℝ)<7/2) (by norm_num : (0:ℝ)<1/2)
  have h4 := _root_.GD.N0235.d004038
    (by norm_num : (0:ℝ)<9/2) (by norm_num : (0:ℝ)<1/2)
  norm_num at h1 h2 h3 h4
  have hm (n : ℕ) := _root_.GD.N0235.d004044
    (by norm_num : (0:ℝ)<3/2) (by norm_num : (0:ℝ)<1/2) n 0
  have hm1 := hm 1
  have hm2 := hm 2
  have hm3 := hm 3
  have hm4 := hm 4
  norm_num at hm1 hm2 hm3 hm4
  rw [h1] at hm1
  rw [h2,h1] at hm2
  rw [h3,h2,h1] at hm3
  rw [h4,h3,h2,h1] at hm4
  field_simp [h0] at hm1 hm2 hm3 hm4
  exact ⟨by linarith [hm1],by linarith [hm2],by linarith [hm3],by linarith [hm4]⟩

theorem d005115 :
    (∫ u, (_root_.GD.N0053.d005108 u)^2 ∂betaMeasure (3/2) (1/2)) = 3079/3200 := by
  letI := isProbabilityMeasureBeta (by norm_num : (0:ℝ)<3/2)
    (by norm_num : (0:ℝ)<1/2)
  have hp (n : ℕ) := _root_.GD.N0053.d005106
    (by norm_num : (0:ℝ)<3/2) (by norm_num : (0:ℝ)<1/2) n
  have hid : Integrable (fun u : ℝ => u) (betaMeasure (3/2) (1/2)) := by simpa using hp 1
  have heq : (fun u => (_root_.GD.N0053.d005108 u)^2) =
      (fun u : ℝ => 4/25 + (32/25)*u + (44/25)*u^2 - (16/5)*u^3 + u^4) := by
    funext u
    unfold _root_.GD.N0053.d005108
    ring
  have h1 := hid.const_mul (32/25:ℝ)
  have h2 := (hp 2).const_mul (44/25:ℝ)
  have h3 := (hp 3).const_mul (16/5:ℝ)
  have h01 : Integrable (fun u : ℝ => 4/25+(32/25)*u) (betaMeasure (3/2) (1/2)) :=
    (integrable_const (4/25:ℝ)).add h1
  have h012 : Integrable (fun u : ℝ => 4/25+(32/25)*u+(44/25)*u^2)
      (betaMeasure (3/2) (1/2)) := h01.add h2
  have h0123 : Integrable (fun u : ℝ => 4/25+(32/25)*u+(44/25)*u^2-(16/5)*u^3)
      (betaMeasure (3/2) (1/2)) := h012.sub h3
  rw [heq, integral_add h0123 (hp 4), integral_sub h012 h3,
    integral_add h01 h2, integral_add (integrable_const (4/25:ℝ)) h1]
  have hlin : (∫ u : ℝ, (32/25:ℝ)*u ∂betaMeasure (3/2) (1/2)) =
      (32/25:ℝ)*(∫ u : ℝ, u ∂betaMeasure (3/2) (1/2)) :=
    integral_const_mul (32/25:ℝ) (fun u : ℝ => u)
  rw [hlin]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
    integral_const_mul, _root_.GD.N0053.d005114.1, _root_.GD.N0053.d005114.2.1,
    _root_.GD.N0053.d005114.2.2.1, _root_.GD.N0053.d005114.2.2.2]
  norm_num

theorem d005116 :
    (∫ u in Ioo (0:ℝ) 1, (_root_.GD.N0053.d005109 u)^2) = 143/150 := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
  have heq : (fun u => (_root_.GD.N0053.d005109 u)^2) =
      (fun u : ℝ => 1+(6/5)*u-(41/25)*u^2-(6/5)*u^3+u^4) := by
    funext u
    unfold _root_.GD.N0053.d005109
    ring
  rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_sub, intervalIntegral.integral_add]
  · have hlin : (∫ u : ℝ in 0..1, (6/5:ℝ)*u) = (6/5:ℝ)*(∫ u : ℝ in 0..1, u) :=
      intervalIntegral.integral_const_mul (6/5:ℝ) (fun u : ℝ => u)
    rw [hlin]
    norm_num [intervalIntegral.integral_const_mul, integral_pow, integral_id]
  all_goals apply Continuous.intervalIntegrable; fun_prop

end
end GD.N0053

#print axioms _root_.GD.N0053.d005112
#print axioms _root_.GD.N0053.d005115
#print axioms _root_.GD.N0053.d005116
