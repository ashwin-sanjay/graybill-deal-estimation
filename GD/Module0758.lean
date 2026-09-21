import GD.Module0102
import GD.Module0752
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2





















open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N1012

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0865
open _root_.GD.N0232.N0719.N1011
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0591
open _root_.GD.N0230.N0716

variable (k : ℕ) (sizes : Fin k → ℕ)



@[reducible] def d011397 :
    MeasurableSpace (_root_.GD.N0232.N0719.d009173 k sizes) :=
  (_root_.GD.N0232.N0719.N0900.d009098 k).comap (_root_.GD.N0232.N0719.N0900.d009104 k sizes)



theorem d011398 :
    _root_.GD.N0232.N0719.N1012.d011397 k sizes ≤
      (inferInstance : MeasurableSpace (_root_.GD.N0232.N0719.d009173 k sizes)) := by
  exact (_root_.GD.N0232.N0719.N0900.d009115 k sizes).comap_le



noncomputable def d011399 :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) →L[ℝ]
      _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
  (lpMeas ℝ ℝ (_root_.GD.N0232.N0719.N1012.d011397 k sizes) 2
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)).subtypeL.comp
    (condExpL2 ℝ ℝ (_root_.GD.N0232.N0719.N1012.d011398 k sizes))

theorem d011400
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    _root_.GD.N0232.N0719.N1012.d011399 k sizes d =
      (condExpL2 ℝ ℝ (_root_.GD.N0232.N0719.N1012.d011398 k sizes) d :
        _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) := rfl



theorem d011401
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    AEStronglyMeasurable[_root_.GD.N0232.N0719.N1012.d011397 k sizes]
      (fun omega ↦ _root_.GD.N0232.N0719.N1012.d011399 k sizes d omega)
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  simpa only [_root_.GD.N0232.N0719.N1012.d011400] using
    (aestronglyMeasurable_condExpL2
      (_root_.GD.N0232.N0719.N1012.d011398 k sizes) d)



theorem d011402
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    ‖d‖ ^ 2 =
      ‖_root_.GD.N0232.N0719.N1012.d011399 k sizes d‖ ^ 2 +
        ‖d - _root_.GD.N0232.N0719.N1012.d011399 k sizes d‖ ^ 2 := by
  let S := lpMeas ℝ ℝ (_root_.GD.N0232.N0719.N1012.d011397 k sizes) 2
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
  letI : Fact (_root_.GD.N0232.N0719.N1012.d011397 k sizes ≤
      (inferInstance : MeasurableSpace (_root_.GD.N0232.N0719.d009173 k sizes))) :=
    ⟨_root_.GD.N0232.N0719.N1012.d011398 k sizes⟩
  have h := S.norm_sq_eq_add_norm_sq_starProjection d
  simpa [S, _root_.GD.N0232.N0719.N1012.d011399, condExpL2] using h




theorem d011403
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) d =
      _root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) (_root_.GD.N0232.N0719.N1012.d011399 k sizes d) +
        ENNReal.ofReal (‖d - _root_.GD.N0232.N0719.N1012.d011399 k sizes d‖ ^ 2) := by
  rw [_root_.GD.N0232.N0719.N0859.d010829 k sizes d,
    _root_.GD.N0232.N0719.N0859.d010829 k sizes (_root_.GD.N0232.N0719.N1012.d011399 k sizes d)]
  simp only [zero_sub, norm_neg]
  rw [_root_.GD.N0232.N0719.N1012.d011402 k sizes d]
  exact ENNReal.ofReal_add
    (sq_nonneg ‖_root_.GD.N0232.N0719.N1012.d011399 k sizes d‖)
    (sq_nonneg ‖d - _root_.GD.N0232.N0719.N1012.d011399 k sizes d‖)



theorem d011404
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    ‖d - _root_.GD.N0232.N0719.N1012.d011399 k sizes d‖ ^ 2 = 0 ↔
      AEStronglyMeasurable[_root_.GD.N0232.N0719.N1012.d011397 k sizes]
        (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
          (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  let S := lpMeas ℝ ℝ (_root_.GD.N0232.N0719.N1012.d011397 k sizes) 2
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
  letI : Fact (_root_.GD.N0232.N0719.N1012.d011397 k sizes ≤
      (inferInstance : MeasurableSpace (_root_.GD.N0232.N0719.d009173 k sizes))) :=
    ⟨_root_.GD.N0232.N0719.N1012.d011398 k sizes⟩
  constructor
  · intro hzero
    have hnorm : ‖d - _root_.GD.N0232.N0719.N1012.d011399 k sizes d‖ = 0 := by
      nlinarith [norm_nonneg (d - _root_.GD.N0232.N0719.N1012.d011399 k sizes d)]
    have heq : d = _root_.GD.N0232.N0719.N1012.d011399 k sizes d := by
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    rw [heq]
    exact _root_.GD.N0232.N0719.N1012.d011401 k sizes d
  · intro hmeas
    have hmem : d ∈ S :=
      mem_lpMeas_iff_aestronglyMeasurable.mpr hmeas
    have hproj : _root_.GD.N0232.N0719.N1012.d011399 k sizes d = d := by
      simpa [S, _root_.GD.N0232.N0719.N1012.d011399, condExpL2] using
        (S.starProjection_eq_self_iff.mpr hmem)
    simp [hproj]



theorem d011405
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    _root_.GD.N0232.N0719.N1012.d011399 k sizes d = d ↔
      AEStronglyMeasurable[_root_.GD.N0232.N0719.N1012.d011397 k sizes]
        (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
          (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  constructor
  · intro h
    rw [← h]
    exact _root_.GD.N0232.N0719.N1012.d011401 k sizes d
  · intro h
    have hzero := (_root_.GD.N0232.N0719.N1012.d011404 k sizes d).2 h
    have hnorm : ‖d - _root_.GD.N0232.N0719.N1012.d011399 k sizes d‖ = 0 := by
      nlinarith [norm_nonneg (d - _root_.GD.N0232.N0719.N1012.d011399 k sizes d)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm



theorem d011406
    (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes theta d =
      ∫⁻ omega,
        ENNReal.ofReal
          (_root_.GD.N0232.N0719.N0865.d011217 k sizes theta omega *
            (d omega - theta.location) ^ 2)
        ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes := by
  simpa [_root_.GD.N0232.N0719.N0859.d010821, _root_.GD.N0230.N0591.d000126] using
    (_root_.GD.N0230.N0591.d000130
      (_root_.GD.N0232.N0719.N0865.d011217 k sizes theta) theta.location d
      (_root_.GD.N0232.N0719.N0865.d011220 k sizes theta)
      (_root_.GD.N0232.N0719.N0865.d011218 k sizes theta)
      (_root_.GD.N0232.N0719.N0865.d011219 k sizes theta))




theorem d011407
    (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes theta (_root_.GD.N0232.N0719.N1012.d011399 k sizes d) ≤
      _root_.GD.N0232.N0719.N0859.d010821 k sizes theta d := by
  letI : IsProbabilityMeasure
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
    unfold _root_.GD.N0232.N0719.N0859.d010813
    infer_instance
  rw [_root_.GD.N0232.N0719.N1012.d011406 k sizes hsizes theta
      (_root_.GD.N0232.N0719.N1012.d011399 k sizes d),
    _root_.GD.N0232.N0719.N1012.d011406 k sizes hsizes theta d]
  let m := _root_.GD.N0232.N0719.N1012.d011397 k sizes
  let mu := _root_.GD.N0232.N0719.N0859.d010813 k sizes
  let w := _root_.GD.N0232.N0719.N0865.d011217 k sizes theta
  have hw : StronglyMeasurable[m] w := by
    exact (_root_.GD.N0232.N0719.N1011.d011294
      k sizes hsizes theta).stronglyMeasurable
  have hw0 : 0 ≤ᵐ[mu] w :=
    Filter.Eventually.of_forall
      (_root_.GD.N0232.N0719.N0865.d011219 k sizes theta)
  have hcond := _root_.GD.N0230.N0716.d001319
    (μ := mu) (_root_.GD.N0232.N0719.N1012.d011398 k sizes)
    theta.location (Lp.memLp d) hw hw0
  have hprojection :
      (fun omega ↦ _root_.GD.N0232.N0719.N1012.d011399 k sizes d omega) =ᵐ[mu]
        mu[(d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) | m] := by
    simpa only [m, mu, _root_.GD.N0232.N0719.N1012.d011400, Lp.toLp_coeFn] using
      (Lp.memLp d).condExpL2_ae_eq_condExp
        (_root_.GD.N0232.N0719.N1012.d011398 k sizes)
  calc
    (∫⁻ omega,
        ENNReal.ofReal
          (w omega *
            (_root_.GD.N0232.N0719.N1012.d011399 k sizes d omega - theta.location) ^ 2)
        ∂mu) =
        ∫⁻ omega,
          ENNReal.ofReal
            (w omega *
              (mu[(d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) | m] omega -
                theta.location) ^ 2)
          ∂mu := by
      apply lintegral_congr_ae
      filter_upwards [hprojection] with omega homega
      rw [homega]
    _ ≤ ∫⁻ omega,
          ENNReal.ofReal
            (w omega * (d omega - theta.location) ^ 2)
          ∂mu := hcond




theorem d011408
    (hsizes : ∀ i, 2 ≤ sizes i)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) d) :
    _root_.GD.N0232.N0719.N1012.d011399 k sizes d = d := by
  apply hterminal
  intro theta
  exact _root_.GD.N0232.N0719.N1012.d011407 k sizes hsizes theta d




theorem d011409
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N1012.d011399 k sizes
        (_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes) =
      _root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes := by
  exact _root_.GD.N0232.N0719.N1012.d011408 k sizes hsizes
    (_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0858.d010865
      k sizes hk hsizes)


theorem d011410
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    ‖_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes -
        _root_.GD.N0232.N0719.N1012.d011399 k sizes
          (_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes)‖ ^ 2 = 0 := by
  rw [_root_.GD.N0232.N0719.N1012.d011409
    k sizes hk hsizes]
  simp


theorem d011411
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    AEStronglyMeasurable[_root_.GD.N0232.N0719.N1012.d011397 k sizes]
      (_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes :
        _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  exact (_root_.GD.N0232.N0719.N1012.d011404 k sizes
    (_root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes)).mp
      (_root_.GD.N0232.N0719.N1012.d011410
        k sizes hk hsizes)



theorem d011412
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    ∃ g : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ,
      Measurable g ∧
      ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
        (fun omega ↦
          _root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes omega) =ᵐ[
            _root_.GD.N0232.N0719.N0859.d010812 k sizes theta]
          g ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes := by
  let p : _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
    fun omega ↦ _root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes omega
  have hp : AEStronglyMeasurable[_root_.GD.N0232.N0719.N1012.d011397 k sizes]
      p (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
    _root_.GD.N0232.N0719.N1012.d011411
      k sizes hk hsizes
  let p' : _root_.GD.N0232.N0719.d009173 k sizes → ℝ := hp.mk p
  have hp'_strong : StronglyMeasurable[_root_.GD.N0232.N0719.N1012.d011397 k sizes] p' :=
    hp.stronglyMeasurable_mk
  obtain ⟨g, hgstrong, hfactor⟩ :=
    hp'_strong.exists_eq_measurable_comp
  refine ⟨g, hgstrong.measurable, ?_⟩
  intro theta
  have href : p =ᵐ[_root_.GD.N0232.N0719.N0859.d010813 k sizes] p' :=
    hp.ae_eq_mk
  have hlive : p =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta] p' :=
    (_root_.GD.N0232.N0719.N0859.d010814 k sizes theta).ae_le href
  filter_upwards [hlive] with omega homega
  calc
    _root_.GD.N0232.N0719.N0858.d010863 k sizes hk hsizes omega = p' omega := by
      simpa [p] using homega
    _ = (g ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes) omega := congrFun hfactor omega

end

end N1012
end N0719
end N0232
end GD
