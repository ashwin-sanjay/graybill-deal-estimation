import GD.Module0102
import GD.Module0752
import GD.Module0821
import GD.Module0955
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2






















open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1501

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0137
open _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0591
open _root_.GD.N0230.N0716
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N1011

variable (m n : ℕ)



@[reducible] def d016287 :
    MeasurableSpace (_root_.GD.N0232.N0720.N1080.d014170 m n) :=
  (_root_.GD.N0232.N0719.N0900.d009098 2).comap
    (_root_.GD.N0232.N0720.N1467.d012542 m n)

@[fun_prop]
theorem d016288 :
    Measurable (_root_.GD.N0232.N0720.N1467.d012541 m n) := by
  change Measurable ((_root_.GD.N0232.N0720.N1467.d012540 m n).symm :
    (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) →
      _root_.GD.N0232.N0719.N0900.d009094 2
        (_root_.GD.N0232.N0720.N1467.d012537 m n))
  exact (_root_.GD.N0232.N0720.N1467.d012540 m n).symm.measurable

@[fun_prop]
theorem d016289 :
    Measurable (_root_.GD.N0232.N0720.N1467.d012542 m n) := by
  unfold _root_.GD.N0232.N0720.N1467.d012542
  exact (_root_.GD.N0232.N0719.N0900.d009115
    2 (_root_.GD.N0232.N0720.N1467.d012537 m n)).comp (_root_.GD.N0232.N0720.N1501.d016288 m n)



theorem d016290 :
    _root_.GD.N0232.N0720.N1501.d016287 m n ≤
      (inferInstance : MeasurableSpace
        (_root_.GD.N0232.N0720.N1080.d014170 m n)) := by
  exact (_root_.GD.N0232.N0720.N1501.d016289 m n).comap_le


noncomputable def d016291 :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) →L[ℝ]
      _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  (lpMeas ℝ ℝ (_root_.GD.N0232.N0720.N1501.d016287 m n) 2
      (_root_.GD.N0232.N0720.N1080.d014172 m n)).subtypeL.comp
    (condExpL2 ℝ ℝ (_root_.GD.N0232.N0720.N1501.d016290 m n))

theorem d016292
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1501.d016291 m n d =
      (condExpL2 ℝ ℝ (_root_.GD.N0232.N0720.N1501.d016290 m n) d :
        _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) := rfl



theorem d016293
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    AEStronglyMeasurable[_root_.GD.N0232.N0720.N1501.d016287 m n]
      (fun omega ↦ _root_.GD.N0232.N0720.N1501.d016291 m n d omega)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  simpa only [_root_.GD.N0232.N0720.N1501.d016292] using
    (aestronglyMeasurable_condExpL2
      (_root_.GD.N0232.N0720.N1501.d016290 m n) d)



def d016294 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ :=
  _root_.GD.N0232.N0719.N1011.d011288 2 (_root_.GD.N0232.N0720.N1467.d012537 m n) theta.location
    ![theta.scale₁, theta.scale₂]

@[fun_prop]
theorem d016295 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    Measurable (_root_.GD.N0232.N0720.N1501.d016294 m n theta) := by
  exact _root_.GD.N0232.N0719.N1011.d011289 2 (_root_.GD.N0232.N0720.N1467.d012537 m n)
    theta.location ![theta.scale₁, theta.scale₂]



theorem d016296
    (hm : 2 ≤ m) (hn : 2 ≤ n) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1499.d015001 m n theta =
      _root_.GD.N0232.N0720.N1501.d016294 m n theta ∘
        _root_.GD.N0232.N0720.N1467.d012542 m n := by
  funext omega
  unfold _root_.GD.N0232.N0720.N1499.d015001 _root_.GD.N0232.N0720.N1501.d016294
    _root_.GD.N0232.N0719.N1011.d011288
  simp only [Function.comp_apply]
  rw [Fin.prod_univ_two]
  rw [_root_.GD.N0232.N0719.N1011.d011287
      hm theta.location theta.scale₁ theta.scale₁_pos.ne' omega.1,
    _root_.GD.N0232.N0719.N1011.d011287
      hn theta.location theta.scale₂ theta.scale₂_pos.ne' omega.2]
  simp only [Function.comp_apply, _root_.GD.N0232.N0720.N1467.d012538, _root_.GD.N0232.N0720.N1467.d012539,
    _root_.GD.N0232.N0720.N1467.d012545, _root_.GD.N0232.N0720.N1467.d012546,
    _root_.GD.N0232.N0720.N1467.d012547,
    _root_.GD.N0232.N0720.N1467.d012548, Matrix.cons_val_zero,
    Matrix.cons_val_one]



theorem d016297
    (hm : 2 ≤ m) (hn : 2 ≤ n) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    Measurable[_root_.GD.N0232.N0720.N1501.d016287 m n]
      (_root_.GD.N0232.N0720.N1499.d015001 m n theta) := by
  rw [_root_.GD.N0232.N0720.N1501.d016296 m n hm hn theta]
  exact (_root_.GD.N0232.N0720.N1501.d016295 m n theta).comp
    (comap_measurable (_root_.GD.N0232.N0720.N1467.d012542 m n))



theorem d016298
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1080.d014182 m n theta d =
      ∫⁻ omega,
        ENNReal.ofReal
          (_root_.GD.N0232.N0720.N1499.d015001 m n theta omega *
            (d omega - theta.location) ^ 2)
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  simpa [_root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0230.N0591.d000126] using
    (_root_.GD.N0230.N0591.d000130
      (_root_.GD.N0232.N0720.N1499.d015001 m n theta) theta.location d
      (_root_.GD.N0232.N0720.N1499.d015006 m n theta)
      (_root_.GD.N0232.N0720.N1499.d015002 m n theta)
      (_root_.GD.N0232.N0720.N1499.d015003 m n theta))




theorem d016299
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1501.d016291 m n d) ≤ _root_.GD.N0232.N0720.N1080.d014182 m n theta d := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  rw [_root_.GD.N0232.N0720.N1501.d016298 m n hm hn theta
      (_root_.GD.N0232.N0720.N1501.d016291 m n d),
    _root_.GD.N0232.N0720.N1501.d016298 m n hm hn theta d]
  let s := _root_.GD.N0232.N0720.N1501.d016287 m n
  let mu := _root_.GD.N0232.N0720.N1080.d014172 m n
  let w := _root_.GD.N0232.N0720.N1499.d015001 m n theta
  have hw : StronglyMeasurable[s] w := by
    exact (_root_.GD.N0232.N0720.N1501.d016297
      m n hm hn theta).stronglyMeasurable
  have hw0 : 0 ≤ᵐ[mu] w :=
    Filter.Eventually.of_forall
      (_root_.GD.N0232.N0720.N1499.d015003 m n theta)
  have hcond := _root_.GD.N0230.N0716.d001319
    (μ := mu) (_root_.GD.N0232.N0720.N1501.d016290 m n)
    theta.location (Lp.memLp d) hw hw0
  have hprojection :
      (fun omega ↦ _root_.GD.N0232.N0720.N1501.d016291 m n d omega) =ᵐ[mu]
        mu[(d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) | s] := by
    simpa only [s, mu, _root_.GD.N0232.N0720.N1501.d016292, Lp.toLp_coeFn] using
      (Lp.memLp d).condExpL2_ae_eq_condExp
        (_root_.GD.N0232.N0720.N1501.d016290 m n)
  calc
    (∫⁻ omega,
        ENNReal.ofReal
          (w omega *
            (_root_.GD.N0232.N0720.N1501.d016291 m n d omega - theta.location) ^ 2)
        ∂mu) =
        ∫⁻ omega,
          ENNReal.ofReal
            (w omega *
              (mu[(d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) | s] omega -
                theta.location) ^ 2)
          ∂mu := by
      apply lintegral_congr_ae
      filter_upwards [hprojection] with omega homega
      rw [homega]
    _ ≤ ∫⁻ omega,
          ENNReal.ofReal
            (w omega * (d omega - theta.location) ^ 2)
          ∂mu := hcond

set_option maxHeartbeats 800000 in





theorem d016300
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hrisk : Integrable (fun omega ↦ (d omega - theta.location) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014171 m n theta)) :
    Integrable (fun omega ↦ _root_.GD.N0232.N0720.N1499.d015001 m n theta omega *
      (d omega - _root_.GD.N0232.N0720.N1501.d016291 m n d omega) ^ 2)
        (_root_.GD.N0232.N0720.N1080.d014172 m n) ∧
      (∫ omega, (d omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) =
        (∫ omega,
          (_root_.GD.N0232.N0720.N1501.d016291 m n d omega - theta.location) ^ 2
            ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) +
          ∫ omega, _root_.GD.N0232.N0720.N1499.d015001 m n theta omega *
            (d omega - _root_.GD.N0232.N0720.N1501.d016291 m n d omega) ^ 2
            ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  let mu := _root_.GD.N0232.N0720.N1080.d014172 m n
  let w := _root_.GD.N0232.N0720.N1499.d015001 m n theta
  let rho : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ≥0∞ :=
    fun omega ↦ ENNReal.ofReal (w omega)
  have hw : StronglyMeasurable[_root_.GD.N0232.N0720.N1501.d016287 m n] w :=
    (_root_.GD.N0232.N0720.N1501.d016297
      m n hm hn theta).stronglyMeasurable
  have hw0 : 0 ≤ᵐ[mu] w :=
    Filter.Eventually.of_forall
      (_root_.GD.N0232.N0720.N1499.d015003 m n theta)
  have hrhoMeas : Measurable rho := by
    simpa only [rho, w] using
      (_root_.GD.N0232.N0720.N1499.d015002 m n theta).ennreal_ofReal
  have hrhoFinite : ∀ᵐ omega ∂mu, rho omega < ∞ := by
    filter_upwards with omega
    exact ENNReal.ofReal_lt_top
  have hrawWeighted : Integrable
      (fun omega ↦ w omega * (d omega - theta.location) ^ 2) mu := by
    have hphysical : Integrable
        (fun omega ↦ (d omega - theta.location) ^ 2)
        (mu.withDensity rho) := by
      rw [← _root_.GD.N0232.N0720.N1499.d015006 m n theta]
      exact hrisk
    have hweighted : Integrable
        (fun omega ↦
          (d omega - theta.location) ^ 2 * (rho omega).toReal) mu :=
      (integrable_withDensity_iff (μ := mu) hrhoMeas hrhoFinite).1
        hphysical
    refine hweighted.congr ?_
    filter_upwards with omega
    rw [ENNReal.toReal_ofReal
      (_root_.GD.N0232.N0720.N1499.d015003 m n theta omega)]
    ring
  have hprojection :
      (fun omega ↦ _root_.GD.N0232.N0720.N1501.d016291 m n d omega) =ᵐ[mu]
        mu[(d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) |
          _root_.GD.N0232.N0720.N1501.d016287 m n] := by
    simpa only [mu, _root_.GD.N0232.N0720.N1501.d016292, Lp.toLp_coeFn] using
      (Lp.memLp d).condExpL2_ae_eq_condExp
        (_root_.GD.N0232.N0720.N1501.d016290 m n)
  have hPyth :=
    _root_.GD.N0230.N0716.d001322
    (_root_.GD.N0232.N0720.N1501.d016290 m n) theta.location (Lp.memLp d) hw hw0
    hrawWeighted
  have hcenterEq :
      (∫ omega, w omega *
          (mu[(d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) |
              _root_.GD.N0232.N0720.N1501.d016287 m n] omega -
            theta.location) ^ 2 ∂mu) =
        ∫ omega, w omega *
          (_root_.GD.N0232.N0720.N1501.d016291 m n d omega - theta.location) ^ 2 ∂mu := by
    apply integral_congr_ae
    filter_upwards [hprojection] with omega homega
    rw [← homega]
  have hresidualEq :
      (∫ omega, w omega *
          (d omega -
            mu[(d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) |
              _root_.GD.N0232.N0720.N1501.d016287 m n] omega) ^ 2
          ∂mu) =
        ∫ omega, w omega *
          (d omega - _root_.GD.N0232.N0720.N1501.d016291 m n d omega) ^ 2 ∂mu := by
    apply integral_congr_ae
    filter_upwards [hprojection] with omega homega
    rw [← homega]
  have hresidualInt : Integrable
      (fun omega ↦ w omega *
        (d omega - _root_.GD.N0232.N0720.N1501.d016291 m n d omega) ^ 2) mu := by
    refine hPyth.1.congr ?_
    filter_upwards [hprojection] with omega homega
    rw [← homega]
  have hweightedPyth :
      (∫ omega, w omega * (d omega - theta.location) ^ 2 ∂mu) =
        (∫ omega, w omega *
          (_root_.GD.N0232.N0720.N1501.d016291 m n d omega - theta.location) ^ 2 ∂mu) +
          ∫ omega, w omega *
            (d omega - _root_.GD.N0232.N0720.N1501.d016291 m n d omega) ^ 2 ∂mu := by
    rw [← hcenterEq, ← hresidualEq]
    simpa only [mu] using hPyth.2
  have hrawIntegral :
      (∫ omega, (d omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) =
        ∫ omega, w omega * (d omega - theta.location) ^ 2 ∂mu := by
    rw [_root_.GD.N0232.N0720.N1499.d015006 m n theta]
    change
      (∫ omega, (d omega - theta.location) ^ 2 ∂mu.withDensity rho) =
        ∫ omega, w omega * (d omega - theta.location) ^ 2 ∂mu
    have hdensityIntegral :=
      integral_withDensity_eq_integral_toReal_smul
        (μ := mu) hrhoMeas hrhoFinite
        (fun omega ↦ (d omega - theta.location) ^ 2)
    rw [hdensityIntegral]
    apply integral_congr_ae
    filter_upwards with omega
    rw [ENNReal.toReal_ofReal
      (_root_.GD.N0232.N0720.N1499.d015003 m n theta omega)]
    simp only [rho, w, mu, smul_eq_mul]
  have hprojectedIntegral :
      (∫ omega,
        (_root_.GD.N0232.N0720.N1501.d016291 m n d omega - theta.location) ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) =
        ∫ omega, w omega *
          (_root_.GD.N0232.N0720.N1501.d016291 m n d omega - theta.location) ^ 2 ∂mu := by
    rw [_root_.GD.N0232.N0720.N1499.d015006 m n theta]
    change
      (∫ omega, (_root_.GD.N0232.N0720.N1501.d016291 m n d omega - theta.location) ^ 2
        ∂mu.withDensity rho) =
        ∫ omega, w omega *
          (_root_.GD.N0232.N0720.N1501.d016291 m n d omega - theta.location) ^ 2 ∂mu
    have hdensityIntegral :=
      integral_withDensity_eq_integral_toReal_smul
        (μ := mu) hrhoMeas hrhoFinite
        (fun omega ↦
          (_root_.GD.N0232.N0720.N1501.d016291 m n d omega - theta.location) ^ 2)
    rw [hdensityIntegral]
    apply integral_congr_ae
    filter_upwards with omega
    rw [ENNReal.toReal_ofReal
      (_root_.GD.N0232.N0720.N1499.d015003 m n theta omega)]
    simp only [rho, w, mu, smul_eq_mul]
  refine ⟨?_, ?_⟩
  · simpa only [w, mu] using hresidualInt
  · rw [hrawIntegral, hprojectedIntegral]
    simpa only [w, mu] using hweightedPyth



theorem d016301
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hrisk : Integrable (fun omega ↦ (d omega - theta.location) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014171 m n theta)) :
    (∫ omega, (d omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) =
      (∫ omega,
        (_root_.GD.N0232.N0720.N1501.d016291 m n d omega - theta.location) ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) +
        ∫ omega, _root_.GD.N0232.N0720.N1499.d015001 m n theta omega *
          (d omega - _root_.GD.N0232.N0720.N1501.d016291 m n d omega) ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n :=
  (_root_.GD.N0232.N0720.N1501.d016300
    m n hm hn theta d hrisk).2



theorem d016302
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hrisk : Integrable (fun omega ↦ (d omega - theta.location) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014171 m n theta)) :
    (∫ omega, _root_.GD.N0232.N0720.N1499.d015001 m n theta omega *
        (d omega - _root_.GD.N0232.N0720.N1501.d016291 m n d omega) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
      (∫ omega, (d omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) -
        ∫ omega,
          (_root_.GD.N0232.N0720.N1501.d016291 m n d omega - theta.location) ^ 2
            ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta := by
  have hdecomp := _root_.GD.N0232.N0720.N1501.d016301
    m n hm hn theta d hrisk
  linarith



theorem d016303
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hrisk : Integrable (fun omega ↦ (d omega - theta.location) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014171 m n theta)) :
    (∫ omega, _root_.GD.N0232.N0720.N1499.d015001 m n theta omega *
        (d omega - _root_.GD.N0232.N0720.N1501.d016291 m n d omega) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n) ∈
      Set.Icc 0
        (∫ omega, (d omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  constructor
  · exact integral_nonneg fun omega ↦ mul_nonneg
      (_root_.GD.N0232.N0720.N1499.d015003 m n theta omega) (sq_nonneg _)
  · rw [_root_.GD.N0232.N0720.N1501.d016302
      m n hm hn theta d hrisk]
    have hprojectedNonneg : 0 ≤
        ∫ omega,
          (_root_.GD.N0232.N0720.N1501.d016291 m n d omega - theta.location) ^ 2
            ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta :=
      integral_nonneg fun _ ↦ sq_nonneg _
    linarith




theorem d016304
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hrisk : Integrable (fun omega ↦ (d omega - theta.location) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014171 m n theta)) :
    (∫ omega, _root_.GD.N0232.N0720.N1499.d015001 m n theta omega *
        (d omega - _root_.GD.N0232.N0720.N1501.d016291 m n d omega) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n) = 0 ↔
      d = _root_.GD.N0232.N0720.N1501.d016291 m n d := by
  have hresidualInt :=
    (_root_.GD.N0232.N0720.N1501.d016300
      m n hm hn theta d hrisk).1
  constructor
  · intro hzero
    have hweightedZero :
        (fun omega ↦ _root_.GD.N0232.N0720.N1499.d015001 m n theta omega *
          (d omega - _root_.GD.N0232.N0720.N1501.d016291 m n d omega) ^ 2) =ᵐ[
            _root_.GD.N0232.N0720.N1080.d014172 m n] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun omega ↦ mul_nonneg
          (_root_.GD.N0232.N0720.N1499.d015003 m n theta omega) (sq_nonneg _))
        hresidualInt).1 hzero
    apply Lp.ext
    filter_upwards [hweightedZero] with omega homega
    have hsquare :
        (d omega - _root_.GD.N0232.N0720.N1501.d016291 m n d omega) ^ 2 = 0 :=
      (mul_eq_zero.mp homega).resolve_left
        (_root_.GD.N0232.N0720.N1499.d015005 m n theta omega).ne'
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · intro hfixed
    have hpointwise :
        (fun omega ↦ d omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
          fun omega ↦ _root_.GD.N0232.N0720.N1501.d016291 m n d omega := by
      filter_upwards with omega
      exact congrArg
        (fun p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) ↦ p omega) hfixed
    apply integral_eq_zero_of_ae
    filter_upwards [hpointwise] with omega homega
    simp only [homega, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero, Pi.zero_apply]




theorem d016305
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hrisk : Integrable (fun omega ↦ (d omega - theta.location) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014171 m n theta)) :
    (∫ omega, (d omega - theta.location) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) =
        ∫ omega,
          (_root_.GD.N0232.N0720.N1501.d016291 m n d omega - theta.location) ^ 2
            ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta ↔
      d = _root_.GD.N0232.N0720.N1501.d016291 m n d := by
  rw [← _root_.GD.N0232.N0720.N1501.d016304
    m n hm hn theta d hrisk]
  have hdecomp := _root_.GD.N0232.N0720.N1501.d016301
    m n hm hn theta d hrisk
  constructor <;> intro h <;> linarith



theorem d016306
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ∃ g : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ,
      Measurable g ∧
        (fun omega ↦ _root_.GD.N0232.N0720.N1501.d016291 m n d omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
          g ∘ _root_.GD.N0232.N0720.N1467.d012542 m n := by
  let p : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
    fun omega ↦ _root_.GD.N0232.N0720.N1501.d016291 m n d omega
  have hp : AEStronglyMeasurable[_root_.GD.N0232.N0720.N1501.d016287 m n]
      p (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1501.d016293 m n d
  let p' : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ := hp.mk p
  have hp'_strong : StronglyMeasurable[_root_.GD.N0232.N0720.N1501.d016287 m n] p' :=
    hp.stronglyMeasurable_mk
  obtain ⟨g, hgstrong, hfactor⟩ :=
    hp'_strong.exists_eq_measurable_comp
  refine ⟨g, hgstrong.measurable, ?_⟩
  have href : p =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] p' := hp.ae_eq_mk
  filter_upwards [href] with omega homega
  calc
    _root_.GD.N0232.N0720.N1501.d016291 m n d omega = p' omega := by
      simpa [p] using homega
    _ = (g ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) omega := congrFun hfactor omega




theorem d016307
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ∃ (g : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ)
        (hmem : MemLp (g ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) 2
          (_root_.GD.N0232.N0720.N1080.d014172 m n)),
      Measurable g ∧
        (fun omega ↦ _root_.GD.N0232.N0720.N1501.d016291 m n d omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
          g ∘ _root_.GD.N0232.N0720.N1467.d012542 m n ∧
        MemLp.toLp (g ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) hmem =
          _root_.GD.N0232.N0720.N1501.d016291 m n d := by
  obtain ⟨g, hg, hae⟩ :=
    _root_.GD.N0232.N0720.N1501.d016306 m n d
  let projected := _root_.GD.N0232.N0720.N1501.d016291 m n d
  have hmem : MemLp (g ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) 2
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    (Lp.memLp projected).ae_eq (by simpa only [projected] using hae)
  refine ⟨g, hmem, hg, hae, ?_⟩
  calc
    MemLp.toLp (g ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) hmem =
        MemLp.toLp (fun omega ↦ projected omega) (Lp.memLp projected) :=
      MemLp.toLp_congr hmem (Lp.memLp projected)
        (by simpa only [projected] using hae.symm)
    _ = projected := Lp.toLp_coeFn projected (Lp.memLp projected)
    _ = _root_.GD.N0232.N0720.N1501.d016291 m n d := rfl

end

end N1501
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1501.d016296
#print axioms _root_.GD.N0232.N0720.N1501.d016299
#print axioms _root_.GD.N0232.N0720.N1501.d016300
#print axioms _root_.GD.N0232.N0720.N1501.d016301
#print axioms _root_.GD.N0232.N0720.N1501.d016304
#print axioms _root_.GD.N0232.N0720.N1501.d016305
#print axioms _root_.GD.N0232.N0720.N1501.d016306
#print axioms _root_.GD.N0232.N0720.N1501.d016307
