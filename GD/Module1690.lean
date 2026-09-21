import GD.Module1654
import GD.Module1689




set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace GD.N0101.N0394
noncomputable section

open _root_.GD.N0213
open _root_.GD.N0213.N0510 _root_.GD.N0213.N0508 _root_.GD.N0213.N0516
open _root_.GD.N0213.N0526 _root_.GD.N0213.N0505
open _root_.GD.N0101.N0397
open _root_.GD.N0101.N0396
open _root_.GD.N0101.N0389

abbrev d028502 := Fin 2 → ℝ

def d028503 (t : _root_.GD.N0101.N0394.d028502) : ℝ := t 1 / (t 0 + t 1)

def d028504 (a : ℝ) (t β : _root_.GD.N0101.N0394.d028502) : _root_.GD.N0101.N0394.d028502 :=
  _root_.GD.N0101.N0397.d028118.symm (_root_.GD.N0213.N0526.d028101 (a * t 0) (a * t 1) (_root_.GD.N0101.N0397.d028118 β))

def d028505 (a : ℝ) (h : _root_.GD.N0101.N0394.d028502 → ℝ) (β t : _root_.GD.N0101.N0394.d028502) : ℝ≥0∞ :=
  ENNReal.ofReal ((β 0)⁻¹ * _root_.GD.N0101.N0394.d028503 t * (h β - h (_root_.GD.N0101.N0394.d028504 a t β)) ^ 2)

def d028506 (a : ℝ) (h : _root_.GD.N0101.N0394.d028502 → ℝ) (t : _root_.GD.N0101.N0394.d028502) : ℝ≥0∞ :=
  ENNReal.ofReal (_root_.GD.N0213.N0505.d007548
    (_root_.GD.N0101.N0396.d028143 a (a * t 0) (a * t 1) 0)
    (_root_.GD.N0101.N0396.d028143 a (a * t 0) (a * t 1) 1)) *
    ∫⁻ z, ENNReal.ofReal ((h (_root_.GD.N0101.N0397.d028118.symm z) -
      h (_root_.GD.N0101.N0397.d028118.symm (_root_.GD.N0213.N0526.d028101 (a * t 0) (a * t 1) z))) ^ 2)
      ∂_root_.GD.N0101.N0396.d028146 a (a * t 0) (a * t 1) 0



theorem d028507 {a r₁ r₂ : ℝ}
    (ha : 0 < a) (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    _root_.GD.N0213.N0505.d007548 (_root_.GD.N0101.N0396.d028143 a r₁ r₂ 0) (_root_.GD.N0101.N0396.d028143 a r₁ r₂ 1) =
      _root_.GD.N0101.N0396.d028143 a r₁ r₂ 0 * (r₂ / (r₁ + r₂)) := by
  have hm₀ := _root_.GD.N0101.N0396.d028147 ha h₁ h₂ 0
  have hm₁ := _root_.GD.N0101.N0396.d028147 ha h₁ h₂ 1
  unfold _root_.GD.N0213.N0505.d007548
  apply (div_eq_iff (add_pos hm₀ hm₁).ne').2
  rw [_root_.GD.N0101.N0396.d028148 ha h₁ h₂]
  field_simp [h₂.ne', (add_pos h₁ h₂).ne']

theorem d028508
    (a : ℝ) (ha : 0 < a) (t : _root_.GD.N0101.N0394.d028502) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0213.N0505.d007548 (_root_.GD.N0101.N0396.d028143 a (a * t 0) (a * t 1) 0)
        (_root_.GD.N0101.N0396.d028143 a (a * t 0) (a * t 1) 1) =
      _root_.GD.N0101.N0396.d028143 a (a * t 0) (a * t 1) 0 * _root_.GD.N0101.N0394.d028503 t := by
  rw [_root_.GD.N0101.N0394.d028507 ha
    (mul_pos ha (ht 0)) (mul_pos ha (ht 1))]
  unfold _root_.GD.N0101.N0394.d028503
  rw [← mul_add, mul_div_mul_left _ _ ha.ne']



theorem d028509 {a r₁ r₂ : ℝ}
    (ha : 0 < a) (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (G : (ℝ × ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ENNReal.ofReal (_root_.GD.N0213.N0505.d007548
        (_root_.GD.N0101.N0396.d028143 a r₁ r₂ 0) (_root_.GD.N0101.N0396.d028143 a r₁ r₂ 1)) *
        (∫⁻ z, G z ∂_root_.GD.N0101.N0396.d028146 a r₁ r₂ 0) =
      ∫⁻ z, ENNReal.ofReal (_root_.GD.N0101.N0396.d028144 0 z * (r₂ / (r₁ + r₂))) * G z
        ∂_root_.GD.N0101.N0397.d028125 a r₁ r₂ := by
  have hm₀ := _root_.GD.N0101.N0396.d028147 ha h₁ h₂ 0
  have hcoeff := _root_.GD.N0101.N0394.d028507 ha h₁ h₂
  have hcoeff_nonneg : 0 ≤ _root_.GD.N0213.N0505.d007548
      (_root_.GD.N0101.N0396.d028143 a r₁ r₂ 0) (_root_.GD.N0101.N0396.d028143 a r₁ r₂ 1) := by
    rw [hcoeff]
    exact (mul_pos hm₀ (div_pos h₂ (add_pos h₁ h₂))).le
  unfold _root_.GD.N0101.N0396.d028146
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hG]
  rw [← lintegral_const_mul _ (by fun_prop)]
  apply lintegral_congr
  intro z
  have hc : _root_.GD.N0213.N0505.d007548 (_root_.GD.N0101.N0396.d028143 a r₁ r₂ 0) (_root_.GD.N0101.N0396.d028143 a r₁ r₂ 1) *
      (_root_.GD.N0101.N0396.d028144 0 z / _root_.GD.N0101.N0396.d028143 a r₁ r₂ 0) =
        _root_.GD.N0101.N0396.d028144 0 z * (r₂ / (r₁ + r₂)) := by
    rw [hcoeff]
    field_simp [hm₀.ne']
  simp only [Pi.mul_apply]
  rw [← mul_assoc, ← ENNReal.ofReal_mul hcoeff_nonneg, hc]

@[fun_prop] theorem d028510 (a : ℝ) :
    Measurable (fun z : _root_.GD.N0101.N0394.d028502 × _root_.GD.N0101.N0394.d028502 => _root_.GD.N0101.N0394.d028504 a z.2 z.1) := by
  unfold _root_.GD.N0101.N0394.d028504 _root_.GD.N0213.N0526.d028101
  fun_prop

@[fun_prop] theorem d028511
    (a : ℝ) (h : _root_.GD.N0101.N0394.d028502 → ℝ) (hh : Measurable h) :
    Measurable (fun z : _root_.GD.N0101.N0394.d028502 × _root_.GD.N0101.N0394.d028502 => _root_.GD.N0101.N0394.d028505 a h z.1 z.2) := by
  unfold _root_.GD.N0101.N0394.d028505 _root_.GD.N0101.N0394.d028503
  fun_prop



theorem d028512
    (a : ℝ) (ha : 0 < a) (h : _root_.GD.N0101.N0394.d028502 → ℝ) (hh : Measurable h)
    (t : _root_.GD.N0101.N0394.d028502) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0101.N0394.d028506 a h t =
      ∫⁻ β, _root_.GD.N0101.N0394.d028505 a h β t
        ∂_root_.GD.N0213.N0510.d023126 (fun _ : Fin 2 => a) (fun i => a * t i) := by
  have h₁ := mul_pos ha (ht 0)
  have h₂ := mul_pos ha (ht 1)
  have hrates : (![a * t 0, a * t 1] : _root_.GD.N0101.N0394.d028502) = (fun i => a * t i) := by
    funext i
    fin_cases i <;> rfl
  unfold _root_.GD.N0101.N0394.d028506
  rw [_root_.GD.N0101.N0394.d028509 ha h₁ h₂ _ (by fun_prop)]
  unfold _root_.GD.N0101.N0397.d028125
  rw [lintegral_map (by fun_prop) _root_.GD.N0101.N0397.d028118.measurable, hrates]
  apply lintegral_congr
  intro β
  simp only [_root_.GD.N0101.N0396.d028144, MeasurableEquiv.symm_apply_apply]
  rw [← ENNReal.ofReal_mul' (sq_nonneg _)]
  unfold _root_.GD.N0101.N0394.d028505 _root_.GD.N0101.N0394.d028503 _root_.GD.N0101.N0394.d028504
  rw [← mul_add, mul_div_mul_left _ _ ha.ne']



theorem d028513
    (a : ℝ) (ha : 0 < a) (h : _root_.GD.N0101.N0394.d028502 → ℝ) (hh : Measurable h) :
    (∫⁻ t, ENNReal.ofReal (_root_.GD.N0213.N0510.d023124 (fun _ : Fin 2 => a) (fun i => a * t i)) *
      _root_.GD.N0101.N0394.d028506 a h t ∂_root_.GD.N0213.N0516.d028413 (fun _ : Fin 2 => a) 0) =
      ∫⁻ β, ∫⁻ t, _root_.GD.N0101.N0394.d028505 a h β t
        ∂_root_.GD.N0213.N0516.d028411 (fun _ : Fin 2 => a) β ∂_root_.GD.N0213.N0508.d028429 (fun _ : Fin 2 => a) := by
  rw [_root_.GD.N0101.N0389.d028500 _ (fun _ => ha) _
    (_root_.GD.N0101.N0394.d028511 a h hh)]
  apply lintegral_congr_ae
  filter_upwards [_root_.GD.N0213.N0494.d028485 (fun _ : Fin 2 => a) 0]
    with t ht
  rw [_root_.GD.N0101.N0394.d028512 a ha h hh t ht]

end
end GD.N0101.N0394

#print axioms _root_.GD.N0101.N0394.d028507
#print axioms _root_.GD.N0101.N0394.d028508
#print axioms _root_.GD.N0101.N0394.d028509
#print axioms _root_.GD.N0101.N0394.d028510
#print axioms _root_.GD.N0101.N0394.d028511
#print axioms _root_.GD.N0101.N0394.d028512
#print axioms _root_.GD.N0101.N0394.d028513
