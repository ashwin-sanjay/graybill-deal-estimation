import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0079.N0318

noncomputable section

variable {X Y Θ : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def d005273 (μ : Measure X) (c : ℝ) (d : X → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((d x - c) ^ 2) ∂μ

def d005274 (μ : Θ → Measure X) (c : Θ → ℝ) (d : X → ℝ) : Prop :=
  ∀ e : X → ℝ, Measurable e →
    (∀ θ, _root_.GD.N0079.N0318.d005273 (μ θ) (c θ) e ≤ _root_.GD.N0079.N0318.d005273 (μ θ) (c θ) d) →
    ∀ θ, e =ᵐ[μ θ] d


def d005275 (μ : Θ → Measure X) (T : X → Y) (e : X → ℝ) : Prop :=
  ∃ f : Y → ℝ, Measurable f ∧ ∀ θ, e =ᵐ[μ θ] f ∘ T



def d005276 (μ : Θ → Measure X) (c : Θ → ℝ)
    (T : X → Y) (b : Y → ℝ) : Prop :=
  ∀ e : X → ℝ, Measurable e →
    (∀ θ, _root_.GD.N0079.N0318.d005273 (μ θ) (c θ) e ≤ _root_.GD.N0079.N0318.d005273 (μ θ) (c θ) (b ∘ T)) →
    _root_.GD.N0079.N0318.d005275 μ T e

theorem d005277 (μ : Measure X) (c : ℝ) (d e : X → ℝ)
    (h : d =ᵐ[μ] e) : _root_.GD.N0079.N0318.d005273 μ c d = _root_.GD.N0079.N0318.d005273 μ c e := by
  apply lintegral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

theorem d005278 (μ : Measure X) (ν : Measure Y) (T : X → Y)
    (hT : Measurable T) (hmap : μ.map T = ν) (c : ℝ)
    (d : Y → ℝ) (hd : Measurable d) :
    _root_.GD.N0079.N0318.d005273 μ c (d ∘ T) = _root_.GD.N0079.N0318.d005273 ν c d := by
  rw [← hmap]
  exact (lintegral_map
    ((hd.sub (measurable_const (a := c))).pow_const 2).ennreal_ofReal hT).symm

theorem d005279 (μ : Measure X) (ν : Measure Y) (T : X → Y)
    (hT : Measurable T) (hmap : μ.map T = ν)
    (d e : Y → ℝ) (hd : Measurable d) (he : Measurable e) :
    d ∘ T =ᵐ[μ] e ∘ T ↔ d =ᵐ[ν] e := by
  rw [← hmap]
  exact (ae_map_iff hT.aemeasurable (measurableSet_eq_fun hd he)).symm



theorem d005280 (μ : Θ → Measure X) (ν : Θ → Measure Y)
    (c : Θ → ℝ) (T : X → Y) (hT : Measurable T)
    (hmap : ∀ θ, (μ θ).map T = ν θ) (b : Y → ℝ) (hb : Measurable b) :
    _root_.GD.N0079.N0318.d005274 μ c (b ∘ T) ↔ _root_.GD.N0079.N0318.d005274 ν c b ∧ _root_.GD.N0079.N0318.d005276 μ c T b := by
  constructor
  · intro h
    constructor
    · intro f hf hdom θ
      have hlift : ∀ η, _root_.GD.N0079.N0318.d005273 (μ η) (c η) (f ∘ T) ≤ _root_.GD.N0079.N0318.d005273 (μ η) (c η) (b ∘ T) := by
        intro η
        rw [_root_.GD.N0079.N0318.d005278 _ _ T hT (hmap η) _ f hf,
          _root_.GD.N0079.N0318.d005278 _ _ T hT (hmap η) _ b hb]
        exact hdom η
      exact (_root_.GD.N0079.N0318.d005279 (μ θ) (ν θ) T hT (hmap θ) f b hf hb).mp
        (h (f ∘ T) (hf.comp hT) hlift θ)
    · intro e he hdom
      exact ⟨b, hb, h e he hdom⟩
  · rintro ⟨hsmall, hdescend⟩ e he hdom
    obtain ⟨f, hf, hef⟩ := hdescend e he hdom
    have hsmallDom : ∀ θ, _root_.GD.N0079.N0318.d005273 (ν θ) (c θ) f ≤ _root_.GD.N0079.N0318.d005273 (ν θ) (c θ) b := by
      intro θ
      rw [← _root_.GD.N0079.N0318.d005278 (μ θ) (ν θ) T hT (hmap θ) _ f hf,
        ← _root_.GD.N0079.N0318.d005278 (μ θ) (ν θ) T hT (hmap θ) _ b hb,
        ← _root_.GD.N0079.N0318.d005277 (μ θ) (c θ) e (f ∘ T) (hef θ)]
      exact hdom θ
    intro θ
    exact (hef θ).trans
      ((_root_.GD.N0079.N0318.d005279 (μ θ) (ν θ) T hT (hmap θ) f b hf hb).mpr
        (hsmall f hf hsmallDom θ))



theorem d005281 (μ : Θ → Measure X) (c : Θ → ℝ)
    (T : X → Y) (b : Y → ℝ) (hb : Measurable b)
    (e : X → ℝ) (he : Measurable e)
    (hdom : ∀ θ, _root_.GD.N0079.N0318.d005273 (μ θ) (c θ) e ≤ _root_.GD.N0079.N0318.d005273 (μ θ) (c θ) (b ∘ T))
    (hnf : ¬ _root_.GD.N0079.N0318.d005275 μ T e) : ¬ _root_.GD.N0079.N0318.d005274 μ c (b ∘ T) := by
  intro hterminal
  exact hnf ⟨b, hb, hterminal e he hdom⟩



theorem d005282 (μ : Θ → Measure X) (ν : Θ → Measure Y)
    (c : Θ → ℝ) (T : X → Y) (hT : Measurable T)
    (hmap : ∀ θ, (μ θ).map T = ν θ) (b : Y → ℝ) (hb : Measurable b)
    (hsmall : _root_.GD.N0079.N0318.d005274 ν c b) :
    _root_.GD.N0079.N0318.d005274 μ c (b ∘ T) ↔ _root_.GD.N0079.N0318.d005276 μ c T b := by
  rw [_root_.GD.N0079.N0318.d005280 μ ν c T hT hmap b hb]
  exact and_iff_right hsmall

#print axioms _root_.GD.N0079.N0318.d005277
#print axioms _root_.GD.N0079.N0318.d005278
#print axioms _root_.GD.N0079.N0318.d005279
#print axioms _root_.GD.N0079.N0318.d005280
#print axioms _root_.GD.N0079.N0318.d005281
#print axioms _root_.GD.N0079.N0318.d005282

end
end GD.N0079.N0318
