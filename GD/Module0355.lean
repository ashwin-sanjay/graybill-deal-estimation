import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace GD.N0018.N0253

variable {Ω Θ : Type*} [MeasurableSpace Ω]

def d005248 (T : Ω → Ω) (a b : ℝ) (f : Ω → ℝ) (z : Ω) : ℝ :=
  f (T z) - a * f z - b

def d005249 (T₂ T₃ : Ω → Ω) (f : Ω → ℝ) (z : Ω) : ℝ :=
  _root_.GD.N0018.N0253.d005248 T₂ 2 0 f z ^ 2 + _root_.GD.N0018.N0253.d005248 T₃ 3 1 f z ^ 2

def d005250 (ν : Measure Ω) (T₂ T₃ : Ω → Ω) (f : Ω → ℝ) : ℝ :=
  ∫ z, _root_.GD.N0018.N0253.d005249 T₂ T₃ f z ∂ν

def d005251 (ν : Measure Ω) (T₂ T₃ : Ω → Ω) (f : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (_root_.GD.N0018.N0253.d005249 T₂ T₃ f z) ∂ν

theorem d005252 (a b : ℝ) :
    a ^ 2 + b ^ 2 = 0 ↔ a = 0 ∧ b = 0 := by
  simpa only [pow_two] using (mul_self_add_mul_self_eq_zero (a := a) (b := b))

omit [MeasurableSpace Ω] in
theorem d005253 (T₂ T₃ : Ω → Ω) (f : Ω → ℝ) (z : Ω) :
    0 ≤ _root_.GD.N0018.N0253.d005249 T₂ T₃ f z :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

omit [MeasurableSpace Ω] in
theorem d005254 (T₂ T₃ : Ω → Ω) (f : Ω → ℝ) (z : Ω) :
    _root_.GD.N0018.N0253.d005249 T₂ T₃ f z = 0 ↔
      f (T₂ z) = 2 * f z ∧ f (T₃ z) = 3 * f z + 1 := by
  rw [_root_.GD.N0018.N0253.d005249, _root_.GD.N0018.N0253.d005252]
  simp only [_root_.GD.N0018.N0253.d005248, sub_zero, sub_eq_zero]
  constructor <;> rintro ⟨h₂, h₃⟩ <;> constructor <;> linarith

theorem d005255 {T₂ T₃ : Ω → Ω} {f : Ω → ℝ}
    (h₂ : Measurable T₂) (h₃ : Measurable T₃) (hf : Measurable f) :
    Measurable (_root_.GD.N0018.N0253.d005249 T₂ T₃ f) := by
  exact (((hf.comp h₂).sub (hf.const_mul 2)).sub measurable_const).pow_const 2 |>.add
    ((((hf.comp h₃).sub (hf.const_mul 3)).sub measurable_const).pow_const 2)

theorem d005256 (ν : Measure Ω) (T₂ T₃ : Ω → Ω) (f : Ω → ℝ) :
    0 ≤ _root_.GD.N0018.N0253.d005250 ν T₂ T₃ f :=
  integral_nonneg (_root_.GD.N0018.N0253.d005253 T₂ T₃ f)

theorem d005257 {ν : Measure Ω} {T₂ T₃ : Ω → Ω} {f : Ω → ℝ}
    (hint : Integrable (_root_.GD.N0018.N0253.d005249 T₂ T₃ f) ν) :
    _root_.GD.N0018.N0253.d005250 ν T₂ T₃ f = 0 ↔
      (∀ᵐ z ∂ν, f (T₂ z) = 2 * f z) ∧
      (∀ᵐ z ∂ν, f (T₃ z) = 3 * f z + 1) := by
  rw [_root_.GD.N0018.N0253.d005250, integral_eq_zero_iff_of_nonneg (_root_.GD.N0018.N0253.d005253 T₂ T₃ f) hint]
  change (∀ᵐ z ∂ν, _root_.GD.N0018.N0253.d005249 T₂ T₃ f z = 0) ↔ _
  simp only [_root_.GD.N0018.N0253.d005254, Filter.eventually_and]

theorem d005258 {ν : Measure Ω} {T₂ T₃ : Ω → Ω}
    {f : Ω → ℝ} (h : ¬ Integrable (_root_.GD.N0018.N0253.d005249 T₂ T₃ f) ν) :
    _root_.GD.N0018.N0253.d005250 ν T₂ T₃ f = 0 :=
  integral_undef h

theorem d005259 {ν : Measure Ω} {T₂ T₃ : Ω → Ω} {f : Ω → ℝ}
    (h₂ : Measurable T₂) (h₃ : Measurable T₃) (hf : Measurable f) :
    _root_.GD.N0018.N0253.d005251 ν T₂ T₃ f = 0 ↔
      (∀ᵐ z ∂ν, f (T₂ z) = 2 * f z) ∧
      (∀ᵐ z ∂ν, f (T₃ z) = 3 * f z + 1) := by
  have hm : AEMeasurable (fun z => ENNReal.ofReal (_root_.GD.N0018.N0253.d005249 T₂ T₃ f z)) ν :=
    (ENNReal.measurable_ofReal.comp (_root_.GD.N0018.N0253.d005255 h₂ h₃ hf)).aemeasurable
  rw [_root_.GD.N0018.N0253.d005251, lintegral_eq_zero_iff' hm]
  change (∀ᵐ z ∂ν, ENNReal.ofReal (_root_.GD.N0018.N0253.d005249 T₂ T₃ f z) = 0) ↔ _
  simp only [ENNReal.ofReal_eq_zero]
  have hzero : (∀ᵐ z ∂ν, _root_.GD.N0018.N0253.d005249 T₂ T₃ f z ≤ 0) ↔
      (∀ᵐ z ∂ν, _root_.GD.N0018.N0253.d005249 T₂ T₃ f z = 0) := by
    constructor
    · exact fun h => h.mono fun z hz => le_antisymm hz (_root_.GD.N0018.N0253.d005253 T₂ T₃ f z)
    · exact fun h => h.mono fun z hz => hz.le
  rw [hzero]
  simp only [_root_.GD.N0018.N0253.d005254, Filter.eventually_and]

theorem d005260 {ν : Measure Ω} {T₂ T₃ : Ω → Ω} {f : Ω → ℝ}
    (h₂ : Measurable T₂) (h₃ : Measurable T₃) (hf : Measurable f) :
    0 < _root_.GD.N0018.N0253.d005251 ν T₂ T₃ f ↔
      0 < ν {z | ¬ (f (T₂ z) = 2 * f z ∧ f (T₃ z) = 3 * f z + 1)} := by
  rw [pos_iff_ne_zero, pos_iff_ne_zero]
  exact not_congr ((_root_.GD.N0018.N0253.d005259 h₂ h₃ hf).trans
    (Filter.eventually_and.symm.trans ae_iff))

theorem d005261 {α : Type*} (K : α → Prop) (E : α → ℝ)
    (hE : ∀ f, K f → 0 ≤ E f) :
    (¬ ∀ f, K f → E f = 0) ↔ ∃ f, K f ∧ 0 < E f := by
  classical
  simp only [not_forall]
  constructor
  · rintro ⟨f, hf, hne⟩
    exact ⟨f, hf, lt_of_le_of_ne (hE f hf) (Ne.symm hne)⟩
  · rintro ⟨f, hf, hpos⟩
    exact ⟨f, hf, ne_of_gt hpos⟩

theorem d005262 {α : Type*} (K : α → Prop) (E : α → ℝ≥0∞) :
    (¬ ∀ f, K f → E f = 0) ↔ ∃ f, K f ∧ 0 < E f := by
  classical
  simp only [not_forall, exists_prop, pos_iff_ne_zero]

def d005263 (R : Θ → (Ω → ℝ) → ℝ) (β τ : Θ → ℝ) (V : ℝ) (f : Ω → ℝ) : Prop :=
  Measurable f ∧ ∀ θ, R θ f ≤ min (β θ) (V * τ θ)

def d005264 (ν : Measure Ω) (T₂ T₃ : Ω → Ω)
    (R : Θ → (Ω → ℝ) → ℝ) (β τ : Θ → ℝ) (V : ℝ) : Prop :=
  ∀ f, _root_.GD.N0018.N0253.d005263 R β τ V f → _root_.GD.N0018.N0253.d005250 ν T₂ T₃ f = 0

theorem d005265 (ν : Measure Ω) (T₂ T₃ : Ω → Ω)
    (R : Θ → (Ω → ℝ) → ℝ) (β τ : Θ → ℝ) (V : ℝ) :
    (¬ _root_.GD.N0018.N0253.d005264 ν T₂ T₃ R β τ V) ↔
      ∃ f : Ω → ℝ, Measurable f ∧
        (∀ θ, R θ f ≤ min (β θ) (V * τ θ)) ∧ 0 < _root_.GD.N0018.N0253.d005250 ν T₂ T₃ f := by
  rw [_root_.GD.N0018.N0253.d005264, _root_.GD.N0018.N0253.d005261 (_root_.GD.N0018.N0253.d005263 R β τ V)
    (_root_.GD.N0018.N0253.d005250 ν T₂ T₃) (fun f _ => _root_.GD.N0018.N0253.d005256 ν T₂ T₃ f)]
  simp only [_root_.GD.N0018.N0253.d005263, and_assoc]

theorem d005266 (ν : Measure Ω) (T₂ T₃ : Ω → Ω)
    (R : Θ → (Ω → ℝ) → ℝ) (β τ : Θ → ℝ) (V : ℝ) :
    (¬ ∀ f, _root_.GD.N0018.N0253.d005263 R β τ V f → _root_.GD.N0018.N0253.d005251 ν T₂ T₃ f = 0) ↔
      ∃ f : Ω → ℝ, Measurable f ∧
        (∀ θ, R θ f ≤ min (β θ) (V * τ θ)) ∧ 0 < _root_.GD.N0018.N0253.d005251 ν T₂ T₃ f := by
  rw [_root_.GD.N0018.N0253.d005262 (_root_.GD.N0018.N0253.d005263 R β τ V) (_root_.GD.N0018.N0253.d005251 ν T₂ T₃)]
  simp only [_root_.GD.N0018.N0253.d005263, and_assoc]

theorem d005267 (R : Θ → (Ω → ℝ) → ℝ) (β τ : Θ → ℝ)
    (V : ℝ) (f : Ω → ℝ) :
    _root_.GD.N0018.N0253.d005263 R β τ V f ↔ Measurable f ∧
      (∀ θ, R θ f ≤ β θ) ∧ (∀ θ, R θ f ≤ V * τ θ) := by
  simp only [_root_.GD.N0018.N0253.d005263, le_min_iff, forall_and]

end GD.N0018.N0253

#print axioms _root_.GD.N0018.N0253.d005265
#print axioms _root_.GD.N0018.N0253.d005257
#print axioms _root_.GD.N0018.N0253.d005259
