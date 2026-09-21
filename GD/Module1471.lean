import GD.Module1325
import GD.Module0035

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace GD.N0213.N0523
noncomputable section
open _root_.GD.N0230.N0665
open _root_.GD.N0023.N0257

def d023144 (a ρ : ℝ) : ℝ := a * (1 - ρ) + 1

def d023145 (a ρ t : ℝ) : ℝ :=
  a ^ a / Real.Gamma a * t ^ (a - 1) *
    (Real.Gamma (_root_.GD.N0213.N0523.d023144 a ρ) / (a * t) ^ _root_.GD.N0213.N0523.d023144 a ρ)

theorem d023146 {a ρ : ℝ} (ha : 0 < a) (hρ : ρ < 1) :
    1 < _root_.GD.N0213.N0523.d023144 a ρ := by
  have := mul_pos ha (sub_pos.mpr hρ)
  unfold _root_.GD.N0213.N0523.d023144
  linarith

theorem d023147
    {a ρ t β : ℝ} (ha : 0 < a) (hρ : ρ < 1) (ht : 0 < t) (hβ : 0 < β) :
    gammaPDFReal a (a * β) t * β ^ (-ρ * a) =
      _root_.GD.N0213.N0523.d023145 a ρ t * gammaPDFReal (_root_.GD.N0213.N0523.d023144 a ρ) (a * t) β := by
  have hb : 0 < _root_.GD.N0213.N0523.d023144 a ρ := lt_trans zero_lt_one (_root_.GD.N0213.N0523.d023146 ha hρ)
  have hpow : β ^ a * β ^ (-ρ * a) = β ^ (_root_.GD.N0213.N0523.d023144 a ρ - 1) := by
    rw [← Real.rpow_add hβ]
    congr 1
    unfold _root_.GD.N0213.N0523.d023144
    ring
  simp only [gammaPDFReal, if_pos ht.le, if_pos hβ.le, _root_.GD.N0213.N0523.d023145,
    Real.mul_rpow ha.le hβ.le]
  have hG := (Real.Gamma_pos_of_pos hb).ne'
  have hrate := (Real.rpow_pos_of_pos (mul_pos ha ht) (_root_.GD.N0213.N0523.d023144 a ρ)).ne'
  rw [show -(a * β * t) = -(a * t * β) by ring]
  field_simp
  rw [← hpow]
  ring

theorem d023148
    {a ρ t : ℝ} (ha : 0 < a) (hρ : ρ < 1) (ht : 0 < t) :
    (∫ β, β⁻¹ ∂gammaMeasure (_root_.GD.N0213.N0523.d023144 a ρ) (a * t)) = t / (1 - ρ) := by
  rw [_root_.GD.N0023.N0257.d021615 (_root_.GD.N0213.N0523.d023146 ha hρ) (mul_pos ha ht)]
  unfold _root_.GD.N0213.N0523.d023144
  field_simp [ha.ne', (sub_pos.mpr hρ).ne']
  ring

variable {k : ℕ}

def d023149 (a t : Fin k → ℝ) (ρ : ℝ) (i : Fin k) : ℝ :=
  ∫ β, β⁻¹ ∂gammaMeasure (_root_.GD.N0213.N0523.d023144 (a i) ρ) (a i * t i)

theorem d023150 (a t : Fin k → ℝ) (ρ : ℝ)
    (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 < t i) (hρ : ρ < 1) :
    _root_.GD.N0213.N0523.d023149 a t ρ = fun i => (1 - ρ)⁻¹ * t i := by
  funext i
  rw [_root_.GD.N0213.N0523.d023149, _root_.GD.N0213.N0523.d023148 (ha i) hρ (ht i)]
  ring

theorem d023151 [NeZero k]
    (a t : Fin k → ℝ) (ρ : ℝ)
    (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 < t i) (hρ : ρ < 1) :
    _root_.GD.N0230.N0665.d000407 (_root_.GD.N0213.N0523.d023149 a t ρ) = _root_.GD.N0230.N0665.d000407 t := by
  rw [_root_.GD.N0213.N0523.d023150 a t ρ ha ht hρ]
  exact _root_.GD.N0230.N0665.d000417 ht (inv_pos.mpr (sub_pos.mpr hρ))

theorem d023152 [NeZero k]
    (a t w : Fin k → ℝ) (ρ : ℝ)
    (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 < t i) (hρ : ρ < 1)
    (hw : ∑ i, w i = 1) :
    (∑ i, _root_.GD.N0213.N0523.d023149 a t ρ i * w i ^ 2) =
      (_root_.GD.N0230.N0665.d000406 (_root_.GD.N0213.N0523.d023149 a t ρ))⁻¹ +
        ∑ i, _root_.GD.N0213.N0523.d023149 a t ρ i * (w i - _root_.GD.N0230.N0665.d000407 t i) ^ 2 := by
  have hp : ∀ i, 0 < _root_.GD.N0213.N0523.d023149 a t ρ i := by
    rw [_root_.GD.N0213.N0523.d023150 a t ρ ha ht hρ]
    exact fun i => mul_pos (inv_pos.mpr (sub_pos.mpr hρ)) (ht i)
  simpa only [_root_.GD.N0213.N0523.d023151 a t ρ ha ht hρ] using
    _root_.GD.N0230.N0665.d000412 hp hw

theorem d023153 [NeZero k]
    (a t w : Fin k → ℝ) (ρ : ℝ)
    (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 < t i) (hρ : ρ < 1)
    (hw : ∑ i, w i = 1) :
    (∑ i, _root_.GD.N0213.N0523.d023149 a t ρ i * w i ^ 2) =
      (_root_.GD.N0230.N0665.d000406 (_root_.GD.N0213.N0523.d023149 a t ρ))⁻¹ ↔ w = _root_.GD.N0230.N0665.d000407 t := by
  have hp : ∀ i, 0 < _root_.GD.N0213.N0523.d023149 a t ρ i := by
    rw [_root_.GD.N0213.N0523.d023150 a t ρ ha ht hρ]
    exact fun i => mul_pos (inv_pos.mpr (sub_pos.mpr hρ)) (ht i)
  simpa only [_root_.GD.N0213.N0523.d023151 a t ρ ha ht hρ] using
    _root_.GD.N0230.N0665.d000416 hp hw

def d023154 (a : Fin k → ℝ) : ℝ := ((k : ℝ) - 1) / ∑ i, a i

def d023155 (a : Fin k → ℝ) (i : Fin k) : ℝ := 1 - _root_.GD.N0213.N0523.d023154 a * a i

theorem d023156 (a : Fin k → ℝ) (hA : (∑ i, a i) ≠ 0) :
    (∑ i, _root_.GD.N0213.N0523.d023155 a i) = 1 := by
  simp only [_root_.GD.N0213.N0523.d023155, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    _root_.GD.N0213.N0523.d023154]
  field_simp
  ring

theorem d023157 [NeZero k]
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) :
    (_root_.GD.N0213.N0523.d023154 a < 1 ∧ ∀ i, 0 < _root_.GD.N0213.N0523.d023155 a i) ↔
      ((k : ℝ) - 1 < ∑ i, a i) ∧
        ∀ i, ((k : ℝ) - 1) * a i < ∑ j, a j := by
  have hA : 0 < ∑ i, a i := Finset.sum_pos (fun i _ => ha i) Finset.univ_nonempty
  simp only [_root_.GD.N0213.N0523.d023154, _root_.GD.N0213.N0523.d023155, sub_pos, div_lt_one hA]
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨h, fun i => ?_⟩
    have hi := hh i
    rwa [div_mul_eq_mul_div, div_lt_one hA] at hi
  · rintro ⟨h, hh⟩
    refine ⟨h, fun i => ?_⟩
    rw [div_mul_eq_mul_div, div_lt_one hA]
    exact hh i

end
end GD.N0213.N0523

#print axioms _root_.GD.N0213.N0523.d023147
#print axioms _root_.GD.N0213.N0523.d023148
#print axioms _root_.GD.N0213.N0523.d023151
#print axioms _root_.GD.N0213.N0523.d023152
#print axioms _root_.GD.N0213.N0523.d023153
#print axioms _root_.GD.N0213.N0523.d023156
#print axioms _root_.GD.N0213.N0523.d023157
