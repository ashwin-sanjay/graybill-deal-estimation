import GD.Module1469
import GD.Module0035

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace GD.N0213.N0510
noncomputable section
open _root_.GD.N0213.N0509
open _root_.GD.N0230.N0665

variable {k : ℕ}

def d023122 (a r : Fin k → ℝ) : Measure (Fin k → ℝ) :=
  Measure.pi fun i => gammaMeasure (a i + 1) (r i)

def d023123 (a r : Fin k → ℝ) : ℝ :=
  ∫ β, _root_.GD.N0213.N0509.d023108 a β ∂_root_.GD.N0213.N0510.d023122 a r

def d023124 (a r : Fin k → ℝ) : ℝ :=
  ∫ β, _root_.GD.N0213.N0509.d023108 a β ^ 2 ∂_root_.GD.N0213.N0510.d023122 a r

def d023125 (a r β : Fin k → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (_root_.GD.N0213.N0509.d023108 a β ^ 2 / _root_.GD.N0213.N0510.d023124 a r)

def d023126 (a r : Fin k → ℝ) : Measure (Fin k → ℝ) :=
  (_root_.GD.N0213.N0510.d023122 a r).withDensity (_root_.GD.N0213.N0510.d023125 a r)

@[fun_prop] theorem d023127 (a r : Fin k → ℝ) :
    Measurable (_root_.GD.N0213.N0510.d023125 a r) := by
  unfold _root_.GD.N0213.N0510.d023125
  fun_prop

theorem d023128 (a r : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) :
    0 < _root_.GD.N0213.N0510.d023123 a r ∧ 0 < _root_.GD.N0213.N0510.d023124 a r :=
  _root_.GD.N0213.N0509.d023118 a r ha hr

theorem d023129 (a r β : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) :
    (_root_.GD.N0213.N0510.d023125 a r β).toReal = _root_.GD.N0213.N0509.d023108 a β ^ 2 / _root_.GD.N0213.N0510.d023124 a r := by
  unfold _root_.GD.N0213.N0510.d023125
  exact ENNReal.toReal_ofReal (div_nonneg (sq_nonneg _) (_root_.GD.N0213.N0510.d023128 a r ha hr).2.le)

theorem d023130 (a r : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) :
    IsProbabilityMeasure (_root_.GD.N0213.N0510.d023126 a r) := by
  have hZ := (_root_.GD.N0213.N0510.d023128 a r ha hr).2
  have hi : Integrable (fun β => _root_.GD.N0213.N0509.d023108 a β ^ 2 / _root_.GD.N0213.N0510.d023124 a r)
      (_root_.GD.N0213.N0510.d023122 a r) :=
    (_root_.GD.N0213.N0509.d023115 a r ha hr).div_const _
  have hn : ∀ᵐ β ∂_root_.GD.N0213.N0510.d023122 a r, 0 ≤ _root_.GD.N0213.N0509.d023108 a β ^ 2 / _root_.GD.N0213.N0510.d023124 a r :=
    ae_of_all _ (fun β => div_nonneg (sq_nonneg _) hZ.le)
  refine ⟨?_⟩
  change (_root_.GD.N0213.N0510.d023122 a r).withDensity (_root_.GD.N0213.N0510.d023125 a r) univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change (∫⁻ β, ENNReal.ofReal (_root_.GD.N0213.N0509.d023108 a β ^ 2 / _root_.GD.N0213.N0510.d023124 a r)
    ∂_root_.GD.N0213.N0510.d023122 a r) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, integral_div]
  change ENNReal.ofReal (_root_.GD.N0213.N0510.d023124 a r / _root_.GD.N0213.N0510.d023124 a r) = 1
  rw [div_self hZ.ne', ENNReal.ofReal_one]



theorem d023131 (a r : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) (f : (Fin k → ℝ) → ℝ) :
    (∫ β, f β ∂_root_.GD.N0213.N0510.d023126 a r) =
      (∫ β, _root_.GD.N0213.N0509.d023108 a β ^ 2 * f β ∂_root_.GD.N0213.N0510.d023122 a r) / _root_.GD.N0213.N0510.d023124 a r := by
  unfold _root_.GD.N0213.N0510.d023126
  rw [integral_withDensity_eq_integral_toReal_smul
    (_root_.GD.N0213.N0510.d023127 a r)
    (ae_of_all _ (fun β => ENNReal.ofReal_lt_top))]
  simp_rw [_root_.GD.N0213.N0510.d023129 a r _ ha hr, smul_eq_mul]
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards with β
  ring

theorem d023132 (a r : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) (i : Fin k) :
    Integrable (fun β : Fin k → ℝ => (β i)⁻¹) (_root_.GD.N0213.N0510.d023126 a r) := by
  unfold _root_.GD.N0213.N0510.d023126
  apply (integrable_withDensity_iff_integrable_smul'
    (_root_.GD.N0213.N0510.d023127 a r)
    (ae_of_all _ (fun β => ENNReal.ofReal_lt_top))).mpr
  have hi : Integrable
      (fun β : Fin k → ℝ => ((β i)⁻¹ * _root_.GD.N0213.N0509.d023108 a β ^ 2) / _root_.GD.N0213.N0510.d023124 a r)
      (_root_.GD.N0213.N0510.d023122 a r) :=
    (_root_.GD.N0213.N0509.d023116 a r ha hr i).div_const _
  apply hi.congr
  filter_upwards with β
  rw [_root_.GD.N0213.N0510.d023129 a r β ha hr, smul_eq_mul]
  ring

theorem d023133 (a r : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) (i : Fin k) :
    (∫ β : Fin k → ℝ, (β i)⁻¹ ∂_root_.GD.N0213.N0510.d023126 a r) =
      (r i / a i) * _root_.GD.N0213.N0510.d023123 a r / _root_.GD.N0213.N0510.d023124 a r := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [_root_.GD.N0213.N0510.d023131 a r ha hr]
    have hi :
        (∫ β, _root_.GD.N0213.N0509.d023108 a β ^ 2 * (β i)⁻¹ ∂_root_.GD.N0213.N0510.d023122 a r) =
          (r i / a i) * _root_.GD.N0213.N0510.d023123 a r := by
      calc
        _ = ∫ β, (β i)⁻¹ * _root_.GD.N0213.N0509.d023108 a β ^ 2 ∂_root_.GD.N0213.N0510.d023122 a r := by
          apply integral_congr_ae
          exact ae_of_all _ (fun β => mul_comm _ _)
        _ = _ := _root_.GD.N0213.N0509.d023121 a r ha hr i
    rw [hi]

def d023134 (a r : Fin k → ℝ) (i : Fin k) : ℝ :=
  ∫ β : Fin k → ℝ, (β i)⁻¹ ∂_root_.GD.N0213.N0510.d023126 a r

def d023135 (a r w : Fin k → ℝ) : ℝ :=
  ∑ i, _root_.GD.N0213.N0510.d023134 a r i * w i ^ 2

theorem d023136 (a r w : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) :
    _root_.GD.N0213.N0510.d023135 a r w =
      ∫ β : Fin k → ℝ, ∑ i, (β i)⁻¹ * w i ^ 2 ∂_root_.GD.N0213.N0510.d023126 a r := by
  rw [integral_finsetSum _
    (fun i _ => (_root_.GD.N0213.N0510.d023132 a r ha hr i).mul_const _)]
  simp only [integral_mul_const, _root_.GD.N0213.N0510.d023135, _root_.GD.N0213.N0510.d023134]

def d023137 (a t : Fin k → ℝ) : ℝ :=
  _root_.GD.N0213.N0510.d023123 a (fun i => a i * t i) / _root_.GD.N0213.N0510.d023124 a (fun i => a i * t i)

theorem d023138 (a t : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 < t i) :
    0 < _root_.GD.N0213.N0510.d023137 a t := by
  have hm := _root_.GD.N0213.N0510.d023128 a (fun i => a i * t i) ha (fun i => mul_pos (ha i) (ht i))
  exact div_pos hm.1 hm.2

theorem d023139 (a t : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0213.N0510.d023134 a (fun i => a i * t i) =
      fun i => _root_.GD.N0213.N0510.d023137 a t * t i := by
  funext i
  unfold _root_.GD.N0213.N0510.d023134
  rw [_root_.GD.N0213.N0510.d023133 a (fun i => a i * t i) ha
    (fun i => mul_pos (ha i) (ht i))]
  have hc : a i * t i / a i = t i := by
    field_simp [(ha i).ne']
  rw [hc]
  unfold _root_.GD.N0213.N0510.d023137
  ring

theorem d023140 (a t w : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 < t i) :
    _root_.GD.N0213.N0510.d023135 a (fun i => a i * t i) w =
      _root_.GD.N0213.N0510.d023137 a t * ∑ i, t i * w i ^ 2 := by
  unfold _root_.GD.N0213.N0510.d023135
  rw [_root_.GD.N0213.N0510.d023139 a t ha ht, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring



theorem d023141 [NeZero k] (a t w : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 < t i) (hw : ∑ i, w i = 1) :
    _root_.GD.N0213.N0510.d023135 a (fun i => a i * t i) w =
      _root_.GD.N0213.N0510.d023135 a (fun i => a i * t i) (_root_.GD.N0230.N0665.d000407 t) +
        _root_.GD.N0213.N0510.d023137 a t * ∑ i, t i * (w i - _root_.GD.N0230.N0665.d000407 t i) ^ 2 := by
  rw [_root_.GD.N0213.N0510.d023140 a t w ha ht,
    _root_.GD.N0213.N0510.d023140 a t (_root_.GD.N0230.N0665.d000407 t) ha ht,
    _root_.GD.N0230.N0665.d000412 ht hw, _root_.GD.N0230.N0665.d000411 ht]
  ring

theorem d023142 [NeZero k] (a t w : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 < t i) (hw : ∑ i, w i = 1) :
    _root_.GD.N0213.N0510.d023135 a (fun i => a i * t i) (_root_.GD.N0230.N0665.d000407 t) ≤
      _root_.GD.N0213.N0510.d023135 a (fun i => a i * t i) w := by
  rw [_root_.GD.N0213.N0510.d023140 a t w ha ht,
    _root_.GD.N0213.N0510.d023140 a t (_root_.GD.N0230.N0665.d000407 t) ha ht,
    _root_.GD.N0230.N0665.d000411 ht]
  exact mul_le_mul_of_nonneg_left (_root_.GD.N0230.N0665.d000415 ht hw)
    (_root_.GD.N0213.N0510.d023138 a t ha ht).le

theorem d023143 [NeZero k] (a t w : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (ht : ∀ i, 0 < t i) (hw : ∑ i, w i = 1) :
    (_root_.GD.N0213.N0510.d023135 a (fun i => a i * t i) w =
      _root_.GD.N0213.N0510.d023135 a (fun i => a i * t i) (_root_.GD.N0230.N0665.d000407 t)) ↔
        w = _root_.GD.N0230.N0665.d000407 t := by
  constructor
  · intro h
    rw [_root_.GD.N0213.N0510.d023140 a t w ha ht,
      _root_.GD.N0213.N0510.d023140 a t (_root_.GD.N0230.N0665.d000407 t) ha ht] at h
    have heq := mul_left_cancel₀ (_root_.GD.N0213.N0510.d023138 a t ha ht).ne' h
    rw [_root_.GD.N0230.N0665.d000411 ht] at heq
    exact _root_.GD.N0230.N0665.d000414 ht hw heq
  · rintro rfl
    rfl

end
end GD.N0213.N0510

#print axioms _root_.GD.N0213.N0510.d023130
#print axioms _root_.GD.N0213.N0510.d023132
#print axioms _root_.GD.N0213.N0510.d023133
#print axioms _root_.GD.N0213.N0510.d023141
#print axioms _root_.GD.N0213.N0510.d023143
