import GD.Module1652
import GD.Module0490





set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace GD.N0101.N0396
noncomputable section

open _root_.GD.N0213
open _root_.GD.N0213.N0510 _root_.GD.N0213.N0526 _root_.GD.N0213.N0505
open _root_.GD.N0101.N0397

abbrev d028143 (a r₁ r₂ : ℝ) (i : Fin 2) : ℝ :=
  _root_.GD.N0213.N0510.d023134 (fun _ : Fin 2 => a) ![r₁, r₂] i

def d028144 (i : Fin 2) (z : ℝ × ℝ) : ℝ :=
  (_root_.GD.N0101.N0397.d028118.symm z i)⁻¹

@[fun_prop] theorem d028145 (i : Fin 2) :
    Measurable (_root_.GD.N0101.N0396.d028144 i) := by
  unfold _root_.GD.N0101.N0396.d028144
  fun_prop


def d028146 (a r₁ r₂ : ℝ) (i : Fin 2) : Measure (ℝ × ℝ) :=
  (_root_.GD.N0101.N0397.d028125 a r₁ r₂).withDensity
    (fun z => ENNReal.ofReal (_root_.GD.N0101.N0396.d028144 i z / _root_.GD.N0101.N0396.d028143 a r₁ r₂ i))

theorem d028147 {a r₁ r₂ : ℝ}
    (ha : 0 < a) (h₁ : 0 < r₁) (h₂ : 0 < r₂) (i : Fin 2) :
    0 < _root_.GD.N0101.N0396.d028143 a r₁ r₂ i := by
  have hr : ∀ i : Fin 2, 0 < (![r₁, r₂] i) := Fin.forall_fin_two.mpr ⟨h₁, h₂⟩
  have hm := _root_.GD.N0213.N0510.d023128 (fun _ : Fin 2 => a) ![r₁, r₂] (fun _ => ha) hr
  rw [_root_.GD.N0101.N0396.d028143, _root_.GD.N0213.N0510.d023134, _root_.GD.N0213.N0510.d023133 _ _ (fun _ => ha) hr]
  exact div_pos (mul_pos (div_pos (hr i) ha) hm.1) hm.2

theorem d028148 {a r₁ r₂ : ℝ}
    (ha : 0 < a) (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    _root_.GD.N0101.N0396.d028143 a r₁ r₂ 0 = (r₁ / r₂) * _root_.GD.N0101.N0396.d028143 a r₁ r₂ 1 := by
  have hr : ∀ i : Fin 2, 0 < (![r₁, r₂] i) := Fin.forall_fin_two.mpr ⟨h₁, h₂⟩
  simp only [_root_.GD.N0101.N0396.d028143, _root_.GD.N0213.N0510.d023134,
    _root_.GD.N0213.N0510.d023133 _ _ (fun _ => ha) hr, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  field_simp [h₂.ne']

theorem d028149 {a r₁ r₂ : ℝ}
    (ha : 0 < a) (h₁ : 0 < r₁) (h₂ : 0 < r₂) (i : Fin 2) :
    Integrable (_root_.GD.N0101.N0396.d028144 i) (_root_.GD.N0101.N0397.d028125 a r₁ r₂) := by
  have hr : ∀ i : Fin 2, 0 < (![r₁, r₂] i) := Fin.forall_fin_two.mpr ⟨h₁, h₂⟩
  apply _root_.GD.N0101.N0397.d028118.measurableEmbedding.integrable_map_iff.mpr
  change Integrable (fun β => (_root_.GD.N0101.N0397.d028118.symm (_root_.GD.N0101.N0397.d028118 β) i)⁻¹) _
  simpa only [MeasurableEquiv.symm_apply_apply]
    using _root_.GD.N0213.N0510.d023132 (fun _ : Fin 2 => a) ![r₁, r₂] (fun _ => ha) hr i

theorem d028150 (a r₁ r₂ : ℝ) (i : Fin 2) :
    (∫ z, _root_.GD.N0101.N0396.d028144 i z ∂_root_.GD.N0101.N0397.d028125 a r₁ r₂) =
      _root_.GD.N0101.N0396.d028143 a r₁ r₂ i := by
  unfold _root_.GD.N0101.N0397.d028125
  rw [integral_map_of_stronglyMeasurable _root_.GD.N0101.N0397.d028118.measurable
    (_root_.GD.N0101.N0396.d028145 i).stronglyMeasurable]
  simp only [_root_.GD.N0101.N0396.d028144, MeasurableEquiv.symm_apply_apply]
  rfl

theorem d028151 {a r₁ r₂ : ℝ}
    (ha : 0 < a) (h₁ : 0 < r₁) (h₂ : 0 < r₂) (i : Fin 2) :
    ∀ᵐ z ∂_root_.GD.N0101.N0397.d028125 a r₁ r₂, 0 ≤ _root_.GD.N0101.N0396.d028144 i z := by
  have hr : ∀ i : Fin 2, 0 < (![r₁, r₂] i) := Fin.forall_fin_two.mpr ⟨h₁, h₂⟩
  have hpos := _root_.GD.N0232.N0719.N0910.d010287
    (shape := fun _ : Fin 2 => a + 1) (rate := ![r₁, r₂])
    (fun _ => by linarith) hr
  have hp : ∀ᵐ β ∂_root_.GD.N0213.N0510.d023126 (fun _ : Fin 2 => a) ![r₁, r₂], ∀ i, 0 < β i :=
    (withDensity_absolutelyContinuous _ _).ae_le hpos
  apply (ae_map_iff _root_.GD.N0101.N0397.d028118.measurable.aemeasurable
    (measurableSet_le measurable_const (_root_.GD.N0101.N0396.d028145 i))).mpr
  filter_upwards [hp] with β hβ
  simp only [_root_.GD.N0101.N0396.d028144, MeasurableEquiv.symm_apply_apply]
  exact inv_nonneg.mpr (hβ i).le


theorem d028152 {a r₁ r₂ : ℝ}
    (ha : 0 < a) (h₁ : 0 < r₁) (h₂ : 0 < r₂) (i : Fin 2) :
    IsProbabilityMeasure (_root_.GD.N0101.N0396.d028146 a r₁ r₂ i) := by
  have hm := _root_.GD.N0101.N0396.d028147 ha h₁ h₂ i
  have hi := (_root_.GD.N0101.N0396.d028149 ha h₁ h₂ i).div_const (_root_.GD.N0101.N0396.d028143 a r₁ r₂ i)
  have hn : ∀ᵐ z ∂_root_.GD.N0101.N0397.d028125 a r₁ r₂,
      0 ≤ _root_.GD.N0101.N0396.d028144 i z / _root_.GD.N0101.N0396.d028143 a r₁ r₂ i := by
    filter_upwards [_root_.GD.N0101.N0396.d028151 ha h₁ h₂ i] with z hz
    exact div_nonneg hz hm.le
  refine ⟨?_⟩
  unfold _root_.GD.N0101.N0396.d028146
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hn, integral_div,
    _root_.GD.N0101.N0396.d028150, div_self hm.ne', ENNReal.ofReal_one]


theorem d028153 {a r₁ r₂ : ℝ}
    (ha : 0 < a) (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    MeasurePreserving (_root_.GD.N0213.N0526.d028101 r₁ r₂)
      (_root_.GD.N0101.N0396.d028146 a r₁ r₂ 0) (_root_.GD.N0101.N0396.d028146 a r₁ r₂ 1) := by
  have hm := _root_.GD.N0101.N0396.d028148 ha h₁ h₂
  have hd : (fun z : ℝ × ℝ => ENNReal.ofReal
      (_root_.GD.N0101.N0396.d028144 0 z / _root_.GD.N0101.N0396.d028143 a r₁ r₂ 0)) =
      fun z => ENNReal.ofReal
        (_root_.GD.N0101.N0396.d028144 1 (_root_.GD.N0213.N0526.d028101 r₁ r₂ z) / _root_.GD.N0101.N0396.d028143 a r₁ r₂ 1) := by
    funext z
    congr 1
    change z.1⁻¹ / _root_.GD.N0101.N0396.d028143 a r₁ r₂ 0 =
      ((r₁ / r₂) * z.1)⁻¹ / _root_.GD.N0101.N0396.d028143 a r₁ r₂ 1
    rw [hm]
    simp only [mul_inv_rev, div_eq_mul_inv]
    ring
  refine ⟨_root_.GD.N0213.N0526.d028102 r₁ r₂, ?_⟩
  unfold _root_.GD.N0101.N0396.d028146
  rw [hd]
  exact _root_.GD.N0101.N0397.d028119 _ _ _ (_root_.GD.N0101.N0397.d028126 ha h₁ h₂)
    (fun z => ENNReal.ofReal
      (_root_.GD.N0101.N0396.d028144 1 z / _root_.GD.N0101.N0396.d028143 a r₁ r₂ 1)) (by fun_prop)


theorem d028154 {a r₁ r₂ : ℝ}
    (ha : 0 < a) (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (h : (ℝ × ℝ) → ℝ) (w : ℝ)
    (hh₁ : MemLp h 2 (_root_.GD.N0101.N0396.d028146 a r₁ r₂ 0))
    (hh₂ : MemLp (fun z => h (_root_.GD.N0213.N0526.d028101 r₁ r₂ z)) 2
      (_root_.GD.N0101.N0396.d028146 a r₁ r₂ 0)) :
    _root_.GD.N0213.N0505.d007549 (_root_.GD.N0101.N0396.d028143 a r₁ r₂ 0) (_root_.GD.N0101.N0396.d028143 a r₁ r₂ 1)
      (∫ z, h z ^ 2 ∂_root_.GD.N0101.N0396.d028146 a r₁ r₂ 0)
      (∫ z, h z ^ 2 ∂_root_.GD.N0101.N0396.d028146 a r₁ r₂ 1) w ≤
    _root_.GD.N0213.N0505.d007548 (_root_.GD.N0101.N0396.d028143 a r₁ r₂ 0) (_root_.GD.N0101.N0396.d028143 a r₁ r₂ 1) *
      ∫ z, (h z - h (_root_.GD.N0213.N0526.d028101 r₁ r₂ z)) ^ 2 ∂_root_.GD.N0101.N0396.d028146 a r₁ r₂ 0 := by
  have htransport := (_root_.GD.N0101.N0396.d028153 ha h₁ h₂).integral_comp
    (_root_.GD.N0213.N0526.d028106 r₁ r₂ h₁.ne' h₂.ne').measurableEmbedding (fun z => h z ^ 2)
  have hbound := _root_.GD.N0213.N0505.d007553 (_root_.GD.N0101.N0396.d028146 a r₁ r₂ 0)
    h (fun z => h (_root_.GD.N0213.N0526.d028101 r₁ r₂ z))
    (_root_.GD.N0101.N0396.d028143 a r₁ r₂ 0) (_root_.GD.N0101.N0396.d028143 a r₁ r₂ 1) w
    (_root_.GD.N0101.N0396.d028147 ha h₁ h₂ 0) (_root_.GD.N0101.N0396.d028147 ha h₁ h₂ 1) hh₁ hh₂
  rw [htransport] at hbound
  exact hbound

end
end GD.N0101.N0396

#print axioms _root_.GD.N0101.N0396.d028147
#print axioms _root_.GD.N0101.N0396.d028148
#print axioms _root_.GD.N0101.N0396.d028149
#print axioms _root_.GD.N0101.N0396.d028150
#print axioms _root_.GD.N0101.N0396.d028151
#print axioms _root_.GD.N0101.N0396.d028152
#print axioms _root_.GD.N0101.N0396.d028153
#print axioms _root_.GD.N0101.N0396.d028154
