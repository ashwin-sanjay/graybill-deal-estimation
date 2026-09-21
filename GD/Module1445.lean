import GD.Module1444
import GD.Module0777
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace GD.N0074

variable {X : Type*} {m m₀ : MeasurableSpace X} {μ ν : Measure X}

theorem d022927 (hm : m ≤ m₀)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {w f : X → ℝ} (hw : StronglyMeasurable[m] w) (hw0 : ∀ x, 0 ≤ w x)
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (w x)))
    (hf : Integrable f μ) (hfν : Integrable f ν)
    (hpν : Integrable (μ[f | m]) ν) :
    μ[f | m] =ᵐ[ν] ν[f | m] := by
  have hwambient : Measurable w := (hw.mono hm).measurable
  have hwi : Integrable (fun x ↦ w x * f x) μ := by
    have := (integrable_withDensity_iff_integrable_smul'
      hwambient.ennreal_ofReal (Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)).mp
      (hν ▸ hfν)
    simpa only [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul] using this
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hfν
    (fun s _ _ ↦ hpν.integrableOn) ?_ stronglyMeasurable_condExp.aestronglyMeasurable
  intro s hs _
  rw [hν, setIntegral_withDensity_eq_setIntegral_toReal_smul
      hwambient.ennreal_ofReal (Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)
      _ (hm s hs),
    setIntegral_withDensity_eq_setIntegral_toReal_smul
      hwambient.ennreal_ofReal (Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)
      _ (hm s hs)]
  simp only [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul]
  calc
    (∫ x in s, w x * μ[f | m] x ∂μ) =
        ∫ x in s, μ[(fun y ↦ w y * f y) | m] x ∂μ := by
      exact integral_congr_ae ((condExp_mul_of_stronglyMeasurable_left hw hwi hf).symm.restrict)
    _ = ∫ x in s, w x * f x ∂μ := setIntegral_condExp hm hwi hs

theorem d022928 {Y : Type*} {mY mY₀ : MeasurableSpace Y}
    (hmY : mY ≤ mY₀) [IsFiniteMeasure μ]
    (e : X → Y) (he : Measurable e) {f : Y → ℝ}
    (hf : Integrable f (μ.map e)) :
    (fun x ↦ (μ.map e)[f | mY] (e x)) =ᵐ[μ]
      μ[(f ∘ e) | mY.comap e] := by
  have hm : mY.comap e ≤ m₀ := (MeasurableSpace.comap_mono hmY).trans he.comap_le
  have hp : Integrable (fun x ↦ (μ.map e)[f | mY] (e x)) μ :=
    integrable_condExp.comp_measurable he
  refine ae_eq_condExp_of_forall_setIntegral_eq hm (hf.comp_measurable he)
    (fun s _ _ ↦ hp.integrableOn) ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩ _
    simp only [Function.comp_apply]
    rw [← setIntegral_map (hmY s hs) (stronglyMeasurable_condExp.mono hmY).aestronglyMeasurable
      he.aemeasurable, ← setIntegral_map (hmY s hs) hf.aestronglyMeasurable he.aemeasurable,
      setIntegral_condExp hmY hf hs]
  · exact (stronglyMeasurable_condExp.comp_measurable
      (measurable_iff_comap_le.mpr le_rfl)).aestronglyMeasurable

theorem d022929 {e e' : X → X}
    (he : Measurable[m, m] e) (he' : Measurable[m, m] e')
    (hinv : ∀ x, e' (e x) = x) : m.comap e = m := by
  apply le_antisymm he.comap_le
  intro s hs
  refine ⟨e' ⁻¹' s, he' hs, ?_⟩
  ext x
  simp only [Set.mem_preimage, hinv]

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N1012
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0842
open _root_.GD.N0232.N0719.N0805

theorem d022930
    (k : ℕ) (sizes : Fin k → ℕ) (hsizes : ∀ i, 0 < sizes i)
    (b a : ℝ) :
    Measurable[_root_.GD.N0232.N0719.N1012.d011397 k sizes, _root_.GD.N0232.N0719.N1012.d011397 k sizes]
      (_root_.GD.N0232.N0719.N0900.d009095 k sizes b a) := by
  intro s hs
  rcases hs with ⟨t, ht, rfl⟩
  have hA : Measurable (_root_.GD.N0232.N0719.N0900.d009101 b a : _root_.GD.N0232.N0719.N0900.d009096 k → _root_.GD.N0232.N0719.N0900.d009096 k) := by
    rw [measurable_comap_iff]
    change Measurable (fun s : _root_.GD.N0232.N0719.N0900.d009096 k ↦
      ((fun i ↦ b + a * s.mean i), fun i ↦ a ^ 2 * s.meanVariance i))
    fun_prop
  refine ⟨_root_.GD.N0232.N0719.N0900.d009101 b a ⁻¹' t, hA ht, ?_⟩
  ext x
  simp only [Set.mem_preimage, _root_.GD.N0232.N0719.N0900.d009139 hsizes]

theorem d022931
    (k : ℕ) (sizes : Fin k → ℕ) (hsizes : ∀ i, 0 < sizes i)
    (b a : ℝ) (ha : a ≠ 0) :
    (_root_.GD.N0232.N0719.N1012.d011397 k sizes).comap (_root_.GD.N0232.N0719.N0842.d010907 k sizes b a) =
      _root_.GD.N0232.N0719.N1012.d011397 k sizes := by
  exact _root_.GD.N0074.d022929
    (_root_.GD.N0074.d022930 k sizes hsizes (_root_.GD.N0232.N0719.N0842.d010906 b a) a⁻¹)
    (_root_.GD.N0074.d022930 k sizes hsizes b a)
    (_root_.GD.N0232.N0719.N0842.d010910 k sizes b a ha)


theorem d022932
    (k : ℕ) (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (b a : ℝ) (ha : 0 < a) (d : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)
    (hd : Integrable d (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hdν : Integrable d (_root_.GD.N0232.N0719.N0805.d011790 k sizes b a))
    (hpdν : Integrable
      ((_root_.GD.N0232.N0719.N0859.d010813 k sizes)[d | _root_.GD.N0232.N0719.N1012.d011397 k sizes])
      (_root_.GD.N0232.N0719.N0805.d011790 k sizes b a)) :
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes)[_root_.GD.N0232.N0719.N0842.d010911 k sizes b a d |
        _root_.GD.N0232.N0719.N1012.d011397 k sizes] =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
      _root_.GD.N0232.N0719.N0842.d010911 k sizes b a
        ((_root_.GD.N0232.N0719.N0859.d010813 k sizes)[d | _root_.GD.N0232.N0719.N1012.d011397 k sizes]) := by
  let μ := _root_.GD.N0232.N0719.N0859.d010813 k sizes
  let ν := _root_.GD.N0232.N0719.N0805.d011790 k sizes b a
  let e := _root_.GD.N0232.N0719.N0842.d010907 k sizes b a
  let theta := _root_.GD.N0232.N0719.N0805.d011791 k b a ha
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, _root_.GD.N0232.N0719.N0859.d010813]
    infer_instance
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    rw [_root_.GD.N0232.N0719.N0805.d011792 k sizes b a ha]
    unfold _root_.GD.N0232.N0719.N0859.d010812
    infer_instance
  have hm := _root_.GD.N0232.N0719.N1012.d011398 k sizes
  have hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal
      (_root_.GD.N0232.N0719.N0865.d011217 k sizes theta x)) := by
    rw [show ν = _root_.GD.N0232.N0719.N0859.d010812 k sizes theta from _root_.GD.N0232.N0719.N0805.d011792 k sizes b a ha]
    exact _root_.GD.N0232.N0719.N0865.d011220 k sizes theta
  have hdensity : μ[d | (_root_.GD.N0232.N0719.N1012.d011397 k sizes)] =ᵐ[ν] ν[d | (_root_.GD.N0232.N0719.N1012.d011397 k sizes)] :=
    _root_.GD.N0074.d022927 hm
      (_root_.GD.N0232.N0719.N1011.d011294
        k sizes hsizes theta).stronglyMeasurable
      (_root_.GD.N0232.N0719.N0865.d011219 k sizes theta)
      hν hd hdν hpdν
  have hcomp := (_root_.GD.N0232.N0719.N0805.d011793 k sizes b a).quasiMeasurePreserving.ae_eq_comp hdensity
  have hmap := _root_.GD.N0074.d022928 (μ := μ) hm e
    (_root_.GD.N0232.N0719.N0842.d010908 k sizes b a) hdν
  rw [_root_.GD.N0074.d022931 k sizes
    (fun i ↦ lt_of_lt_of_le (by norm_num) (hsizes i)) b a ha.ne'] at hmap
  have hce : (fun x ↦ μ[d | (_root_.GD.N0232.N0719.N1012.d011397 k sizes)] (e x)) =ᵐ[μ] μ[(d ∘ e) | (_root_.GD.N0232.N0719.N1012.d011397 k sizes)] := hcomp.trans hmap
  have hde : Integrable (d ∘ e) μ := hdν.comp_measurable
    (_root_.GD.N0232.N0719.N0842.d010908 k sizes b a)
  have haff := (condExp_add (integrable_const b) (hde.smul a) (_root_.GD.N0232.N0719.N1012.d011397 k sizes)).trans
    ((EventuallyEq.refl _ _).add (condExp_smul a (d ∘ e) (_root_.GD.N0232.N0719.N1012.d011397 k sizes)))
  have hfun : (fun _ : _root_.GD.N0232.N0719.N0900.d009094 k sizes ↦ b) + a • (d ∘ e) =
      (fun y ↦ b + a * d (e y)) := by
    funext y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
  rw [hfun] at haff
  simp only [condExp_const hm] at haff
  filter_upwards [haff, hce] with x hx hcx
  change μ[(fun y ↦ b + a * d (e y)) | (_root_.GD.N0232.N0719.N1012.d011397 k sizes)] x = b + a * μ[d | (_root_.GD.N0232.N0719.N1012.d011397 k sizes)] (e x)
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, hcx] using hx


theorem d022933
    (k : ℕ) (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (b a : ℝ) (ha : 0 < a)
    (d dT : _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hd : ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
      MemLp (d : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta))
    (hdT : (dT : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
      _root_.GD.N0232.N0719.N0842.d010911 k sizes b a (d : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ)) :
    (fun x ↦ _root_.GD.N0232.N0719.N1012.d011399 k sizes dT x) =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes]
      _root_.GD.N0232.N0719.N0842.d010911 k sizes b a (fun x ↦ _root_.GD.N0232.N0719.N1012.d011399 k sizes d x) := by
  let μ := _root_.GD.N0232.N0719.N0859.d010813 k sizes
  let ν := _root_.GD.N0232.N0719.N0805.d011790 k sizes b a
  let theta := _root_.GD.N0232.N0719.N0805.d011791 k b a ha
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, _root_.GD.N0232.N0719.N0859.d010813]
    infer_instance
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
    unfold _root_.GD.N0232.N0719.N0859.d010812
    infer_instance
  have hν : ν = _root_.GD.N0232.N0719.N0859.d010812 k sizes theta := _root_.GD.N0232.N0719.N0805.d011792 k sizes b a ha
  have hproj : (fun x ↦ _root_.GD.N0232.N0719.N1012.d011399 k sizes d x) =ᵐ[ν]
      μ[(d : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) | (_root_.GD.N0232.N0719.N1012.d011397 k sizes)] := by
    rw [hν]
    exact (_root_.GD.N0232.N0719.N0859.d010814 k sizes theta).ae_le
      (_root_.GD.N0074.d022922 k sizes d)
  have hpdν : Integrable (μ[(d : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) | (_root_.GD.N0232.N0719.N1012.d011397 k sizes)]) ν := by
    have hp : Integrable (fun x ↦ _root_.GD.N0232.N0719.N1012.d011399 k sizes d x) ν := by
      rw [hν]
      exact (_root_.GD.N0074.d022924 k sizes hsizes theta d (hd theta)).integrable (by norm_num)
    exact hp.congr hproj
  have hdν : Integrable (d : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) ν := by
    rw [hν]
    exact (hd theta).integrable (by norm_num)
  have hce := _root_.GD.N0074.d022932 k sizes hsizes b a ha
    (d : _root_.GD.N0232.N0719.N0900.d009094 k sizes → ℝ) ((Lp.memLp d).integrable (by norm_num)) hdν hpdν
  have hprojcomp := (_root_.GD.N0232.N0719.N0805.d011793 k sizes b a).quasiMeasurePreserving.ae_eq_comp hproj
  have hresult := (_root_.GD.N0074.d022922 k sizes dT).trans
    ((condExp_congr_ae hdT).trans hce)
  filter_upwards [hresult, hprojcomp] with x hx hpx
  simp only [Function.comp_apply] at hpx
  exact hx.trans (by dsimp [_root_.GD.N0232.N0719.N0842.d010911]; rw [hpx])

end GD.N0074

#print axioms _root_.GD.N0074.d022927
#print axioms _root_.GD.N0074.d022928
#print axioms _root_.GD.N0074.d022929
#print axioms _root_.GD.N0074.d022930
#print axioms _root_.GD.N0074.d022931
#print axioms _root_.GD.N0074.d022932
#print axioms _root_.GD.N0074.d022933
