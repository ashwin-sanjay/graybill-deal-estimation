import GD.Module0640
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace GD.N0216
noncomputable section

open _root_.GD.N0232.N0719.N0954
open _root_.GD.N0232.N0719.N0933

variable {k : ℕ}


def d023266 : Set (Fin k → ℝ) := {t | ∀ i, 0 < t i}

theorem d023267 : IsOpen (_root_.GD.N0216.d023266 (k := k)) := by
  simp only [_root_.GD.N0216.d023266, setOf_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)

theorem d023268 : MeasurableSet (_root_.GD.N0216.d023266 (k := k)) :=
  _root_.GD.N0216.d023267.measurableSet

private theorem d023269 (shape rate : Fin k → ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0954.d009343 shape rate) := by
  unfold _root_.GD.N0232.N0719.N0954.d009343
  exact Finset.measurable_prod _ fun i _ =>
    (measurable_gammaPDFReal (shape i) (rate i)).comp (measurable_pi_apply i)

theorem d023270 (shape rate : Fin k → ℝ)
    (hshape : ∀ i, 0 < shape i) (hrate : ∀ i, 0 < rate i)
    {t : Fin k → ℝ} (ht : t ∈ _root_.GD.N0216.d023266) :
    0 < _root_.GD.N0232.N0719.N0954.d009343 shape rate t := by
  exact Finset.prod_pos fun i _ => gammaPDFReal_pos (hshape i) (hrate i) (ht i)



theorem d023271 (shape rate : Fin k → ℝ)
    (hshape : ∀ i, 0 < shape i) (hrate : ∀ i, 0 < rate i)
    {P : (Fin k → ℝ) → Prop} (hP : ∀ᵐ t ∂_root_.GD.N0232.N0719.N0954.d009342 shape rate, P t) :
    ∀ᵐ t ∂(volume.restrict _root_.GD.N0216.d023266 : Measure (Fin k → ℝ)), P t := by
  rw [_root_.GD.N0232.N0719.N0954.d009363 hshape hrate,
    ae_withDensity_iff (_root_.GD.N0216.d023269 shape rate).ennreal_ofReal] at hP
  apply (ae_restrict_iff' _root_.GD.N0216.d023268).mpr
  filter_upwards [hP] with t ht
  intro horthant
  exact ht (ne_of_gt (ENNReal.ofReal_pos.mpr
    (_root_.GD.N0216.d023270 shape rate hshape hrate horthant)))


theorem d023272 {Y : Type*}
    (shape rate : Fin k → ℝ)
    (hshape : ∀ i, 0 < shape i) (hrate : ∀ i, 0 < rate i)
    {f g : (Fin k → ℝ) → Y} (hae : f =ᵐ[_root_.GD.N0232.N0719.N0954.d009342 shape rate] g) :
    f =ᵐ[(volume.restrict _root_.GD.N0216.d023266 : Measure (Fin k → ℝ))] g :=
  _root_.GD.N0216.d023271 shape rate hshape hrate hae



theorem d023273 {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (shape rate : Fin k → ℝ)
    (hshape : ∀ i, 0 < shape i) (hrate : ∀ i, 0 < rate i)
    {f g : (Fin k → ℝ) → Y} (hae : f =ᵐ[_root_.GD.N0232.N0719.N0954.d009342 shape rate] g)
    (hf : ContinuousOn f _root_.GD.N0216.d023266) (hg : ContinuousOn g _root_.GD.N0216.d023266) :
    EqOn f g _root_.GD.N0216.d023266 :=
  Measure.eqOn_open_of_ae_eq (μ := volume)
    (_root_.GD.N0216.d023272 shape rate hshape hrate hae)
    _root_.GD.N0216.d023267 hf hg



theorem d023274 {Y : Type*}
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i)
    {f g : (Fin k → ℝ) → Y} (hae : f =ᵐ[_root_.GD.N0232.N0719.N0933.d009301 k sizes scales] g) :
    f =ᵐ[(volume.restrict _root_.GD.N0216.d023266 : Measure (Fin k → ℝ))] g := by
  rw [_root_.GD.N0232.N0719.N0954.d009362 sizes hn scales hscales] at hae
  exact _root_.GD.N0216.d023272
    (_root_.GD.N0232.N0719.N0954.d009355 sizes) (_root_.GD.N0232.N0719.N0954.d009357 sizes scales)
    (_root_.GD.N0232.N0719.N0954.d009358 hn) (_root_.GD.N0232.N0719.N0954.d009360 hn hscales) hae



theorem d023275 {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i)
    {f g : (Fin k → ℝ) → Y} (hae : f =ᵐ[_root_.GD.N0232.N0719.N0933.d009301 k sizes scales] g)
    (hf : ContinuousOn f _root_.GD.N0216.d023266) (hg : ContinuousOn g _root_.GD.N0216.d023266) :
    EqOn f g _root_.GD.N0216.d023266 :=
  Measure.eqOn_open_of_ae_eq (μ := volume)
    (_root_.GD.N0216.d023274 sizes hn scales hscales hae)
    _root_.GD.N0216.d023267 hf hg

end
end GD.N0216

#print axioms _root_.GD.N0216.d023267
#print axioms _root_.GD.N0216.d023268
#print axioms _root_.GD.N0216.d023270
#print axioms _root_.GD.N0216.d023271
#print axioms _root_.GD.N0216.d023272
#print axioms _root_.GD.N0216.d023273
#print axioms _root_.GD.N0216.d023274
#print axioms _root_.GD.N0216.d023275
