import GD.Module1494
import GD.Module0658

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD.N0215
noncomputable section
open _root_.GD.N0223 _root_.GD.N0072
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0933

variable {k : ℕ}

theorem d023403
    (μ ν : Measure (Fin k → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (c : ℝ) (hc : _root_.GD.N0223.d023384 μ ν =ᵐ[ν] fun _ => c) : μ = ν := by
  letI : μ.HaveLebesgueDecomposition ν :=
    Measure.haveLebesgueDecomposition_of_finiteMeasure (μ := μ) (ν := ν)
  have hrn : μ.rnDeriv ν =ᵐ[ν] fun _ => ENNReal.ofReal c := by
    filter_upwards [Measure.rnDeriv_ne_top μ ν, hc] with t ht heq
    exact (ENNReal.ofReal_toReal ht).symm.trans (congrArg ENNReal.ofReal heq)
  have hmeasure : μ = ENNReal.ofReal c • ν := by
    rw [← Measure.withDensity_rnDeriv_eq μ ν hμν,
      withDensity_congr_ae hrn, withDensity_const]
  have hc1 : ENNReal.ofReal c = 1 := by
    have h := congrArg (fun ξ : Measure (Fin k → ℝ) => ξ Set.univ) hmeasure
    simpa only [measure_univ, Measure.smul_apply, smul_eq_mul, mul_one] using h.symm
  simpa only [hc1, one_smul] using hmeasure

theorem d023404 [NeZero k]
    (μ ν : Measure (Fin k → ℝ)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hne : μ ≠ ν)
    (v₀ v₁ : Fin k → ℝ) (hv₀ : ∀ i, 0 < v₀ i) (hv₁ : ∀ i, 0 ≤ v₁ i)
    (i j : Fin k) (hdet : v₀ i * v₁ j - v₀ j * v₁ i ≠ 0) :
    ¬ ∃ p : Fin k → ℝ, _root_.GD.N0223.d023386 μ ν v₀ v₁ =ᵐ[ν] fun _ => p := by
  rintro ⟨p, hp⟩
  obtain ⟨u, hu⟩ := hp.exists
  have hc : _root_.GD.N0223.d023384 μ ν =ᵐ[ν] fun _ => _root_.GD.N0223.d023384 μ ν u := by
    filter_upwards [hp] with t ht
    apply (_root_.GD.N0223.d023387 μ ν v₀ v₁ hv₀ hv₁ i j hdet t u).mp
    exact ht.trans hu.symm
  exact hne (_root_.GD.N0215.d023403 μ ν hμν _ hc)

theorem d023405 (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    (∫ t, t i ∂_root_.GD.N0232.N0719.N0933.d009301 k sizes θ.scale) = _root_.GD.N0223.d023393 sizes θ i := by
  have hshape (j : Fin k) : 0 < _root_.GD.N0232.N0719.N0954.d009355 sizes j :=
    _root_.GD.N0232.N0719.N0954.d009358 hn j
  have hrate (j : Fin k) : 0 < _root_.GD.N0232.N0719.N0954.d009357 sizes θ.scale j :=
    _root_.GD.N0232.N0719.N0954.d009360 hn θ.scale_pos j
  letI (j : Fin k) := isProbabilityMeasure_gammaMeasure (hshape j) (hrate j)
  rw [_root_.GD.N0232.N0719.N0954.d009362 sizes hn
    θ.scale θ.scale_pos]
  change (∫ t, t i ∂Measure.pi (fun j => gammaMeasure
    (_root_.GD.N0232.N0719.N0954.d009355 sizes j)
    (_root_.GD.N0232.N0719.N0954.d009357 sizes θ.scale j))) = _
  have hmap := (measurePreserving_eval
    (fun j => gammaMeasure (_root_.GD.N0232.N0719.N0954.d009355 sizes j)
      (_root_.GD.N0232.N0719.N0954.d009357 sizes θ.scale j)) i).map_eq
  have hint := integral_map
    (μ := Measure.pi (fun j => gammaMeasure (_root_.GD.N0232.N0719.N0954.d009355 sizes j)
      (_root_.GD.N0232.N0719.N0954.d009357 sizes θ.scale j)))
    (f := fun x : ℝ => x) (measurable_pi_apply i).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x)
      ((Measure.pi (fun j => gammaMeasure (_root_.GD.N0232.N0719.N0954.d009355 sizes j)
        (_root_.GD.N0232.N0719.N0954.d009357 sizes θ.scale j))).map (Function.eval i)))
  rw [hmap] at hint
  rw [← hint]
  rw [_root_.GD.N0232.N0719.N0960.d009682 (hshape i) (hrate i)]
  unfold _root_.GD.N0232.N0719.N0954.d009357
    _root_.GD.N0232.N0719.N0954.d009356 _root_.GD.N0223.d023393
  field_simp [(hshape i).ne']

theorem d023406 (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (θ₀ θ₁ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (heq : _root_.GD.N0232.N0719.N0933.d009301 k sizes θ₁.scale = _root_.GD.N0232.N0719.N0933.d009301 k sizes θ₀.scale) :
    _root_.GD.N0223.d023393 sizes θ₁ = _root_.GD.N0223.d023393 sizes θ₀ := by
  funext i
  rw [← _root_.GD.N0215.d023405 sizes hn θ₁ i, heq,
    _root_.GD.N0215.d023405 sizes hn θ₀ i]

theorem d023407 [NeZero k]
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) (θ₀ θ₁ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (i j : Fin k)
    (hdet : _root_.GD.N0223.d023393 sizes θ₀ i * _root_.GD.N0223.d023393 sizes θ₁ j -
      _root_.GD.N0223.d023393 sizes θ₀ j * _root_.GD.N0223.d023393 sizes θ₁ i ≠ 0) :
    ¬ ∃ p : Fin k → ℝ, _root_.GD.N0223.d023395 sizes θ₀ θ₁
      =ᵐ[_root_.GD.N0232.N0719.N0933.d009301 k sizes θ₀.scale] fun _ => p := by
  letI := _root_.GD.N0232.N0719.N0910.d010289 sizes hn θ₀.scale
  letI := _root_.GD.N0232.N0719.N0910.d010289 sizes hn θ₁.scale
  apply _root_.GD.N0215.d023404 _ _
    (_root_.GD.N0002.d023309 sizes hn θ₁ θ₀)
    _ _ _ (_root_.GD.N0223.d023394 sizes hn θ₀)
    (fun l => (_root_.GD.N0223.d023394 sizes hn θ₁ l).le) i j hdet
  intro heq
  have hv := _root_.GD.N0215.d023406 sizes hn θ₀ θ₁ heq
  apply hdet
  rw [hv]
  ring

def d023408 [NeZero k] (sizes : Fin k → ℕ) (θ₀ θ₁ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (s : Fin k → ℝ) : Fin k → ℝ :=
  _root_.GD.N0223.d023395 sizes θ₀ θ₁ (fun i => s i / (sizes i : ℝ))

@[fun_prop] theorem d023409 [NeZero k]
    (sizes : Fin k → ℕ) (θ₀ θ₁ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    Measurable (_root_.GD.N0215.d023408 sizes θ₀ θ₁) := by
  unfold _root_.GD.N0215.d023408
  fun_prop

theorem d023410 [NeZero k] (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (θ₀ θ₁ : _root_.GD.N0232.N0719.N0859.d010809 k) (s : Fin k → ℝ) :
    ∑ i, _root_.GD.N0215.d023408 sizes θ₀ θ₁ s i = 1 :=
  _root_.GD.N0223.d023397 sizes hn θ₀ θ₁ _

theorem d023411 [NeZero k] (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (θ₀ θ₁ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0072.d023292 sizes (_root_.GD.N0215.d023408 sizes θ₀ θ₁) =
      _root_.GD.N0072.d023291 sizes (_root_.GD.N0223.d023395 sizes θ₀ θ₁) := by
  have hn₀ : ∀ i, 0 < sizes i := fun i => lt_of_lt_of_le (by decide : 0 < 2) (hn i)
  rw [_root_.GD.N0072.d023294 sizes hn₀]
  congr 1
  funext t
  unfold _root_.GD.N0215.d023408
  congr 1
  funext i
  field_simp [Nat.cast_ne_zero.mpr (hn₀ i).ne']

theorem d023412 [NeZero k]
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i) (θ₀ θ₁ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    ¬ ∃ w : (Fin k → ℝ) → Fin k → ℝ, Measurable w ∧
      (∀ t, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
          (_root_.GD.N0072.d023292 sizes (_root_.GD.N0215.d023408 sizes θ₀ θ₁))) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes w) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
          (_root_.GD.N0072.d023292 sizes (_root_.GD.N0215.d023408 sizes θ₀ θ₁)) := by
  rintro ⟨w, hw, hunit, hdom, θ, hstrict⟩
  have hn₀ : ∀ i, 0 < sizes i := fun i => lt_of_lt_of_le (by decide : 0 < 2) (hn i)
  simp_rw [_root_.GD.N0215.d023411 sizes hn θ₀ θ₁,
    _root_.GD.N0072.d023294 sizes hn₀ w] at hdom hstrict
  apply _root_.GD.N0223.d023402 sizes hn θ₀ θ₁
  refine ⟨fun t => w (fun i => (sizes i : ℝ) * t i), ?_, fun t => hunit _, hdom, θ, hstrict⟩
  fun_prop

theorem d023413 [NeZero k]
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (i j : Fin k) (hij : i ≠ j) :
    ∃ w : (Fin k → ℝ) → Fin k → ℝ,
      Measurable w ∧ (∀ t, ∑ l, w t l = 1) ∧ (∀ t l, 0 < w t l) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≠ ⊤) ∧
      (∃ θ : _root_.GD.N0232.N0719.N0859.d010809 k, ¬ ∃ p : Fin k → ℝ,
        w =ᵐ[_root_.GD.N0232.N0719.N0933.d009301 k sizes θ.scale] fun _ => p) ∧
      ¬ ∃ u : (Fin k → ℝ) → Fin k → ℝ, Measurable u ∧
        (∀ t, ∑ l, u t l = 1) ∧
        (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes u) ≤
          _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w)) ∧
        ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes u) <
          _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) := by
  let p₀ : Fin k → ℝ := fun _ => 1
  let p₁ : Fin k → ℝ := fun l => if l = i then 1 / 2 else 1
  have hp₀ : ∀ l, 0 < p₀ l := fun _ => zero_lt_one
  have hp₁ : ∀ l, 0 < p₁ l := by
    intro l
    dsimp only [p₁]
    split_ifs <;> norm_num
  let θ₀ := _root_.GD.N0002.d023306 sizes hn p₀ hp₀
  let θ₁ := _root_.GD.N0002.d023306 sizes hn p₁ hp₁
  have hv₀ (l : Fin k) : _root_.GD.N0223.d023393 sizes θ₀ l = 1 := by
    rw [_root_.GD.N0223.d023393, _root_.GD.N0002.d023307]
    norm_num [p₀]
  have hv₁ (l : Fin k) : _root_.GD.N0223.d023393 sizes θ₁ l = (p₁ l)⁻¹ :=
    _root_.GD.N0002.d023307 sizes hn p₁ hp₁ l
  have hdet : _root_.GD.N0223.d023393 sizes θ₀ i * _root_.GD.N0223.d023393 sizes θ₁ j -
      _root_.GD.N0223.d023393 sizes θ₀ j * _root_.GD.N0223.d023393 sizes θ₁ i ≠ 0 := by
    rw [hv₀ i, hv₀ j, hv₁ i, hv₁ j]
    norm_num [p₁, hij.symm]
  refine ⟨_root_.GD.N0223.d023395 sizes θ₀ θ₁,
    _root_.GD.N0223.d023396 sizes θ₀ θ₁,
    _root_.GD.N0223.d023397 sizes hn θ₀ θ₁,
    _root_.GD.N0223.d023398 sizes hn θ₀ θ₁,
    _root_.GD.N0223.d023399 sizes hn θ₀ θ₁,
    ⟨θ₀, _root_.GD.N0215.d023407 sizes hn θ₀ θ₁ i j hdet⟩,
    _root_.GD.N0223.d023402 sizes hn θ₀ θ₁⟩

#print axioms _root_.GD.N0215.d023403
#print axioms _root_.GD.N0215.d023404
#print axioms _root_.GD.N0215.d023405
#print axioms _root_.GD.N0215.d023406
#print axioms _root_.GD.N0215.d023407
#print axioms _root_.GD.N0215.d023411
#print axioms _root_.GD.N0215.d023412
#print axioms _root_.GD.N0215.d023413

end
end GD.N0215
