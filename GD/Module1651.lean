import GD.Module0640
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GD.N0213.N0526
noncomputable section
open _root_.GD.N0232.N0719.N0954

def d028101 (r₁ r₂ : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  ((r₂ / r₁) * z.2, (r₁ / r₂) * z.1)

@[fun_prop] theorem d028102 (r₁ r₂ : ℝ) :
    Measurable (_root_.GD.N0213.N0526.d028101 r₁ r₂) := by
  unfold _root_.GD.N0213.N0526.d028101
  fun_prop

theorem d028103 {r₁ r₂ : ℝ} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) :
    Function.Involutive (_root_.GD.N0213.N0526.d028101 r₁ r₂) := by
  intro z
  apply Prod.ext <;> dsimp only [_root_.GD.N0213.N0526.d028101] <;> field_simp [h₁, h₂]

theorem d028104 {r₁ r₂ : ℝ} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0)
    (z : ℝ × ℝ) :
    (_root_.GD.N0213.N0526.d028101 r₁ r₂ z).1 * (_root_.GD.N0213.N0526.d028101 r₁ r₂ z).2 = z.1 * z.2 := by
  dsimp only [_root_.GD.N0213.N0526.d028101]
  field_simp [h₁, h₂]

theorem d028105 {r₁ r₂ : ℝ} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0)
    (z : ℝ × ℝ) :
    r₁ * (_root_.GD.N0213.N0526.d028101 r₁ r₂ z).1 = r₂ * z.2 ∧
      r₂ * (_root_.GD.N0213.N0526.d028101 r₁ r₂ z).2 = r₁ * z.1 := by
  constructor <;> dsimp only [_root_.GD.N0213.N0526.d028101] <;> field_simp [h₁, h₂]

def d028106 (r₁ r₂ : ℝ) (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) :
    (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun := _root_.GD.N0213.N0526.d028101 r₁ r₂
  invFun := _root_.GD.N0213.N0526.d028101 r₁ r₂
  left_inv := _root_.GD.N0213.N0526.d028103 h₁ h₂
  right_inv := _root_.GD.N0213.N0526.d028103 h₁ h₂
  measurable_toFun := _root_.GD.N0213.N0526.d028102 r₁ r₂
  measurable_invFun := _root_.GD.N0213.N0526.d028102 r₁ r₂

def d028107 (s r₁ r₂ : ℝ) : Measure (ℝ × ℝ) :=
  (gammaMeasure s r₁).prod (gammaMeasure s r₂)

theorem d028108 {s r₁ r₂ : ℝ}
    (hs : 0 < s) (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    (_root_.GD.N0213.N0526.d028107 s r₁ r₂).map (_root_.GD.N0213.N0526.d028101 r₁ r₂) = _root_.GD.N0213.N0526.d028107 s r₁ r₂ := by
  letI := isProbabilityMeasure_gammaMeasure hs h₁
  letI := isProbabilityMeasure_gammaMeasure hs h₂
  have hm₁ : (gammaMeasure s r₂).map (fun x => (r₂ / r₁) * x) =
      gammaMeasure s r₁ := by
    rw [_root_.GD.N0232.N0719.N0954.d009354 hs h₂ (div_pos h₂ h₁)]
    congr 1
    field_simp [h₁.ne', h₂.ne']
  have hm₂ : (gammaMeasure s r₁).map (fun x => (r₁ / r₂) * x) =
      gammaMeasure s r₂ := by
    rw [_root_.GD.N0232.N0719.N0954.d009354 hs h₁ (div_pos h₁ h₂)]
    congr 1
    field_simp [h₁.ne', h₂.ne']
  have hcomp : _root_.GD.N0213.N0526.d028101 r₁ r₂ =
      (Prod.map (fun x : ℝ => (r₂ / r₁) * x)
        (fun y : ℝ => (r₁ / r₂) * y)) ∘ Prod.swap := rfl
  unfold _root_.GD.N0213.N0526.d028107
  rw [hcomp, ← Measure.map_map (by fun_prop) measurable_swap, Measure.prod_swap,
    ← Measure.map_prod_map (gammaMeasure s r₂) (gammaMeasure s r₁)
      (by fun_prop) (by fun_prop), hm₁, hm₂]

theorem d028109 {s r₁ r₂ : ℝ}
    (hs : 0 < s) (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    MeasurePreserving (_root_.GD.N0213.N0526.d028101 r₁ r₂)
      (_root_.GD.N0213.N0526.d028107 s r₁ r₂) (_root_.GD.N0213.N0526.d028107 s r₁ r₂) :=
  ⟨_root_.GD.N0213.N0526.d028102 r₁ r₂, _root_.GD.N0213.N0526.d028108 hs h₁ h₂⟩



theorem d028110 (μ : Measure (ℝ × ℝ))
    (T : (ℝ × ℝ) → (ℝ × ℝ)) (hT : MeasurePreserving T μ μ)
    (D : (ℝ × ℝ) → ℝ≥0∞) (hD : Measurable D) (hfix : ∀ z, D (T z) = D z) :
    (μ.withDensity D).map T = μ.withDensity D := by
  ext E hE
  rw [Measure.map_apply hT.measurable hE,
    withDensity_apply _ (hT.measurable hE), withDensity_apply _ hE,
    ← lintegral_indicator (hT.measurable hE), ← lintegral_indicator hE]
  calc
    (∫⁻ z, (T ⁻¹' E).indicator D z ∂μ) = ∫⁻ z, E.indicator D (T z) ∂μ := by
      apply lintegral_congr
      intro z
      by_cases hz : T z ∈ E
      · simp only [mem_preimage, hz, indicator_of_mem, hfix]
      · simp only [mem_preimage, hz, not_false_eq_true, indicator_of_notMem]
    _ = _ := hT.lintegral_comp (hD.indicator hE)

def d028111 (s r₁ r₂ : ℝ) (H : ℝ → ℝ≥0∞) : Measure (ℝ × ℝ) :=
  (_root_.GD.N0213.N0526.d028107 s r₁ r₂).withDensity (fun z => H (z.1 * z.2))

theorem d028112 {s r₁ r₂ : ℝ}
    (hs : 0 < s) (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (_root_.GD.N0213.N0526.d028111 s r₁ r₂ H).map (_root_.GD.N0213.N0526.d028101 r₁ r₂) = _root_.GD.N0213.N0526.d028111 s r₁ r₂ H := by
  apply _root_.GD.N0213.N0526.d028110 (_root_.GD.N0213.N0526.d028107 s r₁ r₂) (_root_.GD.N0213.N0526.d028101 r₁ r₂)
    (_root_.GD.N0213.N0526.d028109 hs h₁ h₂) (fun z => H (z.1 * z.2))
    (hH.comp (measurable_fst.mul measurable_snd))
  intro z
  rw [_root_.GD.N0213.N0526.d028104 h₁.ne' h₂.ne']

theorem d028113 {s r₁ r₂ : ℝ}
    (hs : 0 < s) (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    MeasurePreserving (_root_.GD.N0213.N0526.d028101 r₁ r₂)
      (_root_.GD.N0213.N0526.d028111 s r₁ r₂ H) (_root_.GD.N0213.N0526.d028111 s r₁ r₂ H) :=
  ⟨_root_.GD.N0213.N0526.d028102 r₁ r₂, _root_.GD.N0213.N0526.d028112 hs h₁ h₂ H hH⟩

theorem d028114 {s r₁ r₂ : ℝ}
    (hs : 0 < s) (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (H : ℝ → ℝ≥0∞) (hH : Measurable H) (f : (ℝ × ℝ) → ℝ) :
    (∫ z, f (_root_.GD.N0213.N0526.d028101 r₁ r₂ z) ∂_root_.GD.N0213.N0526.d028111 s r₁ r₂ H) =
      ∫ z, f z ∂_root_.GD.N0213.N0526.d028111 s r₁ r₂ H := by
  exact (_root_.GD.N0213.N0526.d028113 hs h₁ h₂ H hH).integral_comp
    (_root_.GD.N0213.N0526.d028106 r₁ r₂ h₁.ne' h₂.ne').measurableEmbedding f

theorem d028115 (r₁ r₂ : ℝ) (z : ℝ × ℝ) :
    (_root_.GD.N0213.N0526.d028101 r₁ r₂ z).1⁻¹ = (r₁ / r₂) * z.2⁻¹ := by
  simp only [_root_.GD.N0213.N0526.d028101, mul_inv_rev, inv_div]
  ring


theorem d028116 {s r₁ r₂ : ℝ}
    (hs : 0 < s) (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    Integrable (fun z : ℝ × ℝ => z.1⁻¹) (_root_.GD.N0213.N0526.d028111 s r₁ r₂ H) ↔
      Integrable (fun z : ℝ × ℝ => z.2⁻¹) (_root_.GD.N0213.N0526.d028111 s r₁ r₂ H) := by
  have h := (_root_.GD.N0213.N0526.d028113 hs h₁ h₂ H hH).integrable_comp_emb
    (_root_.GD.N0213.N0526.d028106 r₁ r₂ h₁.ne' h₂.ne').measurableEmbedding
    (g := fun z : ℝ × ℝ => z.1⁻¹)
  have heq : (fun z : ℝ × ℝ => z.1⁻¹) ∘ _root_.GD.N0213.N0526.d028101 r₁ r₂ =
      fun z => (r₁ / r₂) * z.2⁻¹ := by
    funext z
    exact _root_.GD.N0213.N0526.d028115 r₁ r₂ z
  rw [heq, integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (div_ne_zero h₁.ne' h₂.ne'))] at h
  exact h.symm



theorem d028117 {s r₁ r₂ : ℝ}
    (hs : 0 < s) (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫ z : ℝ × ℝ, z.1⁻¹ ∂_root_.GD.N0213.N0526.d028111 s r₁ r₂ H) =
      (r₁ / r₂) * (∫ z : ℝ × ℝ, z.2⁻¹ ∂_root_.GD.N0213.N0526.d028111 s r₁ r₂ H) := by
  have h := _root_.GD.N0213.N0526.d028114 hs h₁ h₂ H hH (fun z => z.1⁻¹)
  simp_rw [_root_.GD.N0213.N0526.d028115] at h
  rw [integral_const_mul] at h
  exact h.symm

end
end GD.N0213.N0526

#print axioms _root_.GD.N0213.N0526.d028103
#print axioms _root_.GD.N0213.N0526.d028108
#print axioms _root_.GD.N0213.N0526.d028112
#print axioms _root_.GD.N0213.N0526.d028116
#print axioms _root_.GD.N0213.N0526.d028117
