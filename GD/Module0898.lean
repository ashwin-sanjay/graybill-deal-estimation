import GD.Module0837
import GD.Module0716
import GD.Module0711
import GD.Module0688










open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1504

noncomputable section

open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0232.N0719

private abbrev d013956 : 0 < 2 := by norm_num



def d013957 (alpha beta : ℝ) : Fin 2 → ℝ :=
  ![beta, alpha]

def d013958 : Fin 2 → ℝ := ![(1 : ℝ), 1]


def d013959 (q : ℝ × ℝ) : Fin 2 → ℝ :=
  ![q.2, q.1]

@[fun_prop]
theorem d013960 : Measurable _root_.GD.N0232.N0720.N1504.d013959 := by
  unfold _root_.GD.N0232.N0720.N1504.d013959
  fun_prop


def d013961 (v : Fin 2 → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0953.d003307
    (_root_.GD.N0232.N0719.N0954.d009347 _root_.GD.N0232.N0720.N1504.d013956 v) 0

@[fun_prop]
theorem d013962 : Measurable _root_.GD.N0232.N0720.N1504.d013961 := by
  unfold _root_.GD.N0232.N0720.N1504.d013961 _root_.GD.N0232.N0719.N0954.d009347
    _root_.GD.N0232.N0719.N0954.d009346
    _root_.GD.N0232.N0719.N0953.d003307
    _root_.GD.N0232.N0719.N0953.d003314
    _root_.GD.N0232.N0719.N0953.d003313
    _root_.GD.N0232.N0719.N0953.d003312
  fun_prop



theorem d013963
    {q : ℝ × ℝ} (hx : 0 < q.1) (hy : 0 < q.2) :
    _root_.GD.N0232.N0720.N1504.d013961 (_root_.GD.N0232.N0720.N1504.d013959 q) = _root_.GD.N0232.N0720.N1091.d012757 q := by
  unfold _root_.GD.N0232.N0720.N1504.d013961 _root_.GD.N0232.N0720.N1504.d013959 _root_.GD.N0232.N0720.N1091.d012757
    _root_.GD.N0232.N0719.N0954.d009347
    _root_.GD.N0232.N0719.N0953.d003307
    _root_.GD.N0232.N0719.N0953.d003314
    _root_.GD.N0232.N0719.N0953.d003313
    _root_.GD.N0232.N0719.N0953.d003312
  simp [_root_.GD.N0232.N0719.N0956.d010060,
    _root_.GD.N0232.N0719.N0954.d009344]
  change (q.2⁻¹ + q.1⁻¹)⁻¹ / q.2 = q.1 / (q.1 + q.2)
  field_simp [hx.ne', hy.ne', (add_pos hx hy).ne']



def d013964
    (alpha beta u : ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0954.d009508
    (_root_.GD.N0232.N0720.N1504.d013957 alpha beta) _root_.GD.N0232.N0720.N1504.d013958
    (_root_.GD.N0232.N0719.N0853.d009567 _root_.GD.N0232.N0720.N1504.d013956
      (_root_.GD.N0232.N0719.N0925.d010557 u))

theorem d013965
    {alpha beta u : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1504.d013964 alpha beta u =
      betaPDFReal alpha beta u := by
  have hu0 : 0 < u := hu.1
  have hu1 : 0 < 1 - u := sub_pos.mpr hu.2
  have hzero :
      (finSumFinEquiv : (Fin 1 ⊕ Fin 1) ≃ Fin 2).symm (0 : Fin 2) =
        Sum.inl (0 : Fin 1) := rfl
  have hone :
      (finSumFinEquiv : (Fin 1 ⊕ Fin 1) ≃ Fin 2).symm (1 : Fin 2) =
        Sum.inr (0 : Fin 1) := rfl
  rw [betaPDFReal, if_pos ⟨hu.1, hu.2⟩]
  unfold _root_.GD.N0232.N0720.N1504.d013964
    _root_.GD.N0232.N0719.N0954.d009508
    _root_.GD.N0232.N0719.N0954.d009507
    _root_.GD.N0232.N0719.N0954.d009503
    _root_.GD.N0232.N0719.N0951.d003587
    _root_.GD.N0232.N0720.N1504.d013957 _root_.GD.N0232.N0720.N1504.d013958
  simp [_root_.GD.N0232.N0719.N0853.d009567,
    _root_.GD.N0232.N0719.N0925.d010557,
    _root_.GD.N0232.N0719.N0954.d009344,
    Fin.sum_univ_succ, hzero, hone]
  change
    (Real.Gamma alpha)⁻¹ * (Real.Gamma beta)⁻¹ *
          Real.Gamma (beta + alpha) *
        (u⁻¹ + (1 - u)⁻¹) ^ (-alpha + -beta) *
      (u ^ (-1 + -beta) * (1 - u) ^ (-1 + -alpha)) =
    (ProbabilityTheory.beta alpha beta)⁻¹ *
      u ^ (alpha - 1) * (1 - u) ^ (beta - 1)
  have hsum : u⁻¹ + (1 - u)⁻¹ = (u * (1 - u))⁻¹ := by
    field_simp [hu0.ne', hu1.ne']
    ring
  have hprod : 0 < u * (1 - u) := mul_pos hu0 hu1
  have hpower :
      (u⁻¹ + (1 - u)⁻¹) ^ (-alpha + -beta) *
          (u ^ (-1 + -beta) * (1 - u) ^ (-1 + -alpha)) =
        u ^ (alpha - 1) * (1 - u) ^ (beta - 1) := by
    rw [hsum, Real.inv_rpow hprod.le]
    rw [← Real.rpow_neg hprod.le]
    rw [show -(-alpha + -beta) = alpha + beta by ring]
    rw [Real.mul_rpow hu0.le hu1.le]
    rw [show
        u ^ (alpha + beta) * (1 - u) ^ (alpha + beta) *
              (u ^ (-1 + -beta) * (1 - u) ^ (-1 + -alpha)) =
            (u ^ (alpha + beta) * u ^ (-1 + -beta)) *
              ((1 - u) ^ (alpha + beta) * (1 - u) ^ (-1 + -alpha)) by
      ring]
    rw [← Real.rpow_add hu0, ← Real.rpow_add hu1]
    congr 1 <;> ring
  have hnorm :
      (Real.Gamma alpha)⁻¹ * (Real.Gamma beta)⁻¹ *
          Real.Gamma (beta + alpha) =
        (ProbabilityTheory.beta alpha beta)⁻¹ := by
    unfold ProbabilityTheory.beta
    field_simp [
      (Real.Gamma_pos_of_pos halpha).ne',
      (Real.Gamma_pos_of_pos hbeta).ne',
      (Real.Gamma_pos_of_pos (add_pos halpha hbeta)).ne']
    ring
  rw [hnorm]
  calc
    (ProbabilityTheory.beta alpha beta)⁻¹ *
          (u⁻¹ + (1 - u)⁻¹) ^ (-alpha + -beta) *
          (u ^ (-1 + -beta) * (1 - u) ^ (-1 + -alpha)) =
        (ProbabilityTheory.beta alpha beta)⁻¹ *
          ((u⁻¹ + (1 - u)⁻¹) ^ (-alpha + -beta) *
            (u ^ (-1 + -beta) * (1 - u) ^ (-1 + -alpha))) := by
      ring
    _ = (ProbabilityTheory.beta alpha beta)⁻¹ *
          (u ^ (alpha - 1) * (1 - u) ^ (beta - 1)) := by
      rw [hpower]
    _ = (ProbabilityTheory.beta alpha beta)⁻¹ *
          u ^ (alpha - 1) * (1 - u) ^ (beta - 1) := by
      ring

theorem d013966
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    ∀ i, 0 < _root_.GD.N0232.N0720.N1504.d013957 alpha beta i := by
  intro i
  fin_cases i
  · exact hbeta
  · exact halpha

theorem d013967 : ∀ i, 0 < _root_.GD.N0232.N0720.N1504.d013958 i := by
  intro i
  fin_cases i <;> norm_num [_root_.GD.N0232.N0720.N1504.d013958]



theorem d013968
    {alpha beta : ℝ} (_halpha : 0 < alpha) (_hbeta : 0 < beta) :
    (_root_.GD.N0232.N0720.N1091.d012755 alpha beta).map _root_.GD.N0232.N0720.N1504.d013959 =
      _root_.GD.N0232.N0719.N0954.d009342
        (_root_.GD.N0232.N0720.N1504.d013957 alpha beta) _root_.GD.N0232.N0720.N1504.d013958 := by
  let mu : Fin 2 → Measure ℝ :=
    ![gammaMeasure beta 1, gammaMeasure alpha 1]
  letI : IsProbabilityMeasure (gammaMeasure beta 1) :=
    isProbabilityMeasure_gammaMeasure _hbeta (by norm_num)
  letI : IsProbabilityMeasure (gammaMeasure alpha 1) :=
    isProbabilityMeasure_gammaMeasure _halpha (by norm_num)
  letI : ∀ i, SigmaFinite (mu i) := by
    intro i
    fin_cases i <;> simp [mu] <;> infer_instance
  have hswap :
      MeasurePreserving Prod.swap
        ((gammaMeasure alpha 1).prod (gammaMeasure beta 1))
        ((gammaMeasure beta 1).prod (gammaMeasure alpha 1)) := by
    simpa using
      (Measure.measurePreserving_swap :
        MeasurePreserving Prod.swap
          ((gammaMeasure alpha 1).prod (gammaMeasure beta 1))
          ((gammaMeasure beta 1).prod (gammaMeasure alpha 1)))
  have hfin :
      MeasurePreserving
        (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ)).symm
        ((gammaMeasure beta 1).prod (gammaMeasure alpha 1))
        (Measure.pi mu) := by
    exact MeasurePreserving.symm
      (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ))
      (measurePreserving_finTwoArrow_vec
        (gammaMeasure beta 1) (gammaMeasure alpha 1))
  have hcomp := hfin.comp hswap
  have hfun :
      ((MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ (ℝ × ℝ)).symm ∘
          Prod.swap) = _root_.GD.N0232.N0720.N1504.d013959 := by
    funext q i
    fin_cases i <;> rfl
  rw [hfun] at hcomp
  calc
    (_root_.GD.N0232.N0720.N1091.d012755 alpha beta).map _root_.GD.N0232.N0720.N1504.d013959 = Measure.pi mu := by
      simpa [_root_.GD.N0232.N0720.N1091.d012755] using hcomp.map_eq
    _ = _root_.GD.N0232.N0719.N0954.d009342
          (_root_.GD.N0232.N0720.N1504.d013957 alpha beta) _root_.GD.N0232.N0720.N1504.d013958 := by
      unfold _root_.GD.N0232.N0719.N0954.d009342
      congr 1
      funext i
      fin_cases i <;> simp [mu, _root_.GD.N0232.N0720.N1504.d013957, _root_.GD.N0232.N0720.N1504.d013958]



def d013969 (phi : ℝ → ℝ)
    (x : _root_.GD.N0232.N0719.N0953.d003306 1) : ℝ :=
  phi (_root_.GD.N0232.N0719.N0953.d003307 x 0)

theorem d013970
    {phi : ℝ → ℝ} (hphi : Measurable phi) :
    Measurable (_root_.GD.N0232.N0720.N1504.d013969 phi) := by
  unfold _root_.GD.N0232.N0720.N1504.d013969
  apply hphi.comp
  unfold _root_.GD.N0232.N0719.N0953.d003307
  fun_prop

@[simp]
theorem d013971
    (phi : ℝ → ℝ)
    (q : _root_.GD.N0232.N0719.N0857.d009377 2)
    (omega : ℝ) :
    _root_.GD.N0232.N0720.N1504.d013969 phi
        (_root_.GD.N0232.N0719.N0955.d009612 q omega) =
      phi (q 0) := by
  simp [_root_.GD.N0232.N0720.N1504.d013969]

theorem d013972
    (phi : ℝ → ℝ) (v : Fin 2 → ℝ) :
    _root_.GD.N0232.N0720.N1504.d013969 phi
        (_root_.GD.N0232.N0719.N0954.d009347 _root_.GD.N0232.N0720.N1504.d013956 v) =
      phi (_root_.GD.N0232.N0720.N1504.d013961 v) := by
  rfl



theorem d013973
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (phi : ℝ → ℝ)
    {q : _root_.GD.N0232.N0719.N0857.d009377 2}
    (hq : q ∈ _root_.GD.N0232.N0719.N0955.d009607 2) :
    (∫ omega in Set.Ioi 0,
        _root_.GD.N0232.N0720.N1504.d013969 phi
            (_root_.GD.N0232.N0719.N0955.d009612 q omega) *
          _root_.GD.N0232.N0719.N0954.d009483
            (_root_.GD.N0232.N0719.N0954.d009350 _root_.GD.N0232.N0720.N1504.d013956
              (_root_.GD.N0232.N0720.N1504.d013957 alpha beta))
            (_root_.GD.N0232.N0719.N0954.d009350 _root_.GD.N0232.N0720.N1504.d013956
              _root_.GD.N0232.N0720.N1504.d013958)
            (_root_.GD.N0232.N0719.N0955.d009612 q omega)) =
      _root_.GD.N0232.N0719.N0954.d009508
          (_root_.GD.N0232.N0720.N1504.d013957 alpha beta) _root_.GD.N0232.N0720.N1504.d013958
          (_root_.GD.N0232.N0719.N0853.d009567 _root_.GD.N0232.N0720.N1504.d013956 q) *
        phi (q 0) := by
  have hshape := _root_.GD.N0232.N0720.N1504.d013966 halpha hbeta
  have hrate := _root_.GD.N0232.N0720.N1504.d013967
  have hweightPos :
      ∀ i, 0 <
        _root_.GD.N0232.N0719.N0853.d009567 _root_.GD.N0232.N0720.N1504.d013956 q i := by
    intro i
    cases hi :
        (_root_.GD.N0232.N0719.N0954.d009344 2 _root_.GD.N0232.N0720.N1504.d013956).symm i with
    | inl j =>
        have hj := hq.1 j
        simpa [_root_.GD.N0232.N0719.N0853.d009567, hi]
          using hj
    | inr j =>
        fin_cases j
        simpa [_root_.GD.N0232.N0719.N0853.d009567, hi]
          using hq.2
  have hprojectiveRate :
      0 < _root_.GD.N0232.N0719.N0951.d003587 _root_.GD.N0232.N0720.N1504.d013958
        (_root_.GD.N0232.N0719.N0853.d009567 _root_.GD.N0232.N0720.N1504.d013956 q) := by
    unfold _root_.GD.N0232.N0719.N0951.d003587
    exact Finset.sum_pos
      (fun i _ => div_pos (hrate i) (hweightPos i))
      ⟨0, Finset.mem_univ 0⟩
  letI :
      IsProbabilityMeasure
        (gammaMeasure
          (_root_.GD.N0232.N0719.N0954.d009503
            (_root_.GD.N0232.N0720.N1504.d013957 alpha beta))
          (_root_.GD.N0232.N0719.N0951.d003587 _root_.GD.N0232.N0720.N1504.d013958
            (_root_.GD.N0232.N0719.N0853.d009567 _root_.GD.N0232.N0720.N1504.d013956 q))) :=
    isProbabilityMeasure_gammaMeasure
      (_root_.GD.N0232.N0719.N0954.d009504 _root_.GD.N0232.N0720.N1504.d013956 hshape)
      hprojectiveRate
  have hradial :=
    _root_.GD.N0232.N0719.N0955.d009625
      _root_.GD.N0232.N0720.N1504.d013956 hshape hrate hq (fun _ => phi (q 0))
  calc
    (∫ omega in Set.Ioi 0,
        _root_.GD.N0232.N0720.N1504.d013969 phi
            (_root_.GD.N0232.N0719.N0955.d009612 q omega) *
          _root_.GD.N0232.N0719.N0954.d009483
            (_root_.GD.N0232.N0719.N0954.d009350 _root_.GD.N0232.N0720.N1504.d013956
              (_root_.GD.N0232.N0720.N1504.d013957 alpha beta))
            (_root_.GD.N0232.N0719.N0954.d009350 _root_.GD.N0232.N0720.N1504.d013956
              _root_.GD.N0232.N0720.N1504.d013958)
            (_root_.GD.N0232.N0719.N0955.d009612 q omega)) =
        ∫ omega in Set.Ioi 0,
          _root_.GD.N0232.N0719.N0954.d009483
              (_root_.GD.N0232.N0719.N0954.d009350 _root_.GD.N0232.N0720.N1504.d013956
                (_root_.GD.N0232.N0720.N1504.d013957 alpha beta))
              (_root_.GD.N0232.N0719.N0954.d009350 _root_.GD.N0232.N0720.N1504.d013956
                _root_.GD.N0232.N0720.N1504.d013958)
              (_root_.GD.N0232.N0719.N0955.d009612 q omega) *
            phi (q 0) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro omega _
      dsimp only
      rw [_root_.GD.N0232.N0720.N1504.d013971]
      ring
    _ = _root_.GD.N0232.N0719.N0954.d009508
          (_root_.GD.N0232.N0720.N1504.d013957 alpha beta) _root_.GD.N0232.N0720.N1504.d013958
          (_root_.GD.N0232.N0719.N0853.d009567 _root_.GD.N0232.N0720.N1504.d013956 q) *
        phi (q 0) := by
      simpa using hradial



theorem d013974
    {alpha beta C : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (phi : ℝ → ℝ) (hphi : Measurable phi)
    (hbound : ∀ u, |phi u| ≤ C) :
    (∫ v, phi (_root_.GD.N0232.N0720.N1504.d013961 v)
        ∂_root_.GD.N0232.N0719.N0954.d009342
          (_root_.GD.N0232.N0720.N1504.d013957 alpha beta) _root_.GD.N0232.N0720.N1504.d013958) =
      ∫ q in _root_.GD.N0232.N0719.N0955.d009607 2,
        _root_.GD.N0232.N0719.N0954.d009508
            (_root_.GD.N0232.N0720.N1504.d013957 alpha beta) _root_.GD.N0232.N0720.N1504.d013958
            (_root_.GD.N0232.N0719.N0853.d009567 _root_.GD.N0232.N0720.N1504.d013956 q) *
          phi (q 0) := by
  have hC : 0 ≤ C :=
    (abs_nonneg (phi 0)).trans (hbound 0)
  have hchartBound :
      ∀ x ∈ _root_.GD.N0232.N0719.N0953.d003311 1,
        ‖_root_.GD.N0232.N0720.N1504.d013969 phi x‖ ≤ C := by
    intro x _
    simpa [Real.norm_eq_abs, _root_.GD.N0232.N0720.N1504.d013969] using
      hbound (_root_.GD.N0232.N0719.N0953.d003307 x 0)
  have hchartInt :=
    _root_.GD.N0232.N0719.N0913.d010639
      _root_.GD.N0232.N0720.N1504.d013956 (_root_.GD.N0232.N0720.N1504.d013966 halpha hbeta) _root_.GD.N0232.N0720.N1504.d013967
      (_root_.GD.N0232.N0720.N1504.d013969 phi)
      (_root_.GD.N0232.N0720.N1504.d013970 hphi).aestronglyMeasurable
      hC hchartBound
  change
    (∫ v, _root_.GD.N0232.N0720.N1504.d013969 phi
        (_root_.GD.N0232.N0719.N0954.d009347 _root_.GD.N0232.N0720.N1504.d013956 v)
        ∂_root_.GD.N0232.N0719.N0954.d009342
          (_root_.GD.N0232.N0720.N1504.d013957 alpha beta) _root_.GD.N0232.N0720.N1504.d013958) = _
  rw [_root_.GD.N0232.N0719.N0955.d009630
    _root_.GD.N0232.N0720.N1504.d013956 (_root_.GD.N0232.N0720.N1504.d013966 halpha hbeta) _root_.GD.N0232.N0720.N1504.d013967 _ hchartInt]
  apply setIntegral_congr_fun
    (_root_.GD.N0232.N0719.N0955.d009608 2)
  intro q hq
  exact _root_.GD.N0232.N0720.N1504.d013973 halpha hbeta phi hq



theorem d013975
    {alpha beta C : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (phi : ℝ → ℝ) (hphi : Measurable phi)
    (hbound : ∀ u, |phi u| ≤ C) :
    (∫ v, phi (_root_.GD.N0232.N0720.N1504.d013961 v)
        ∂_root_.GD.N0232.N0719.N0954.d009342
          (_root_.GD.N0232.N0720.N1504.d013957 alpha beta) _root_.GD.N0232.N0720.N1504.d013958) =
      ∫ u, phi u ∂betaMeasure alpha beta := by
  rw [_root_.GD.N0232.N0720.N1504.d013974
    halpha hbeta phi hphi hbound]
  rw [_root_.GD.N0232.N0719.N0925.d010560]
  calc
    (∫ u in Set.Ioo (0 : ℝ) 1,
        _root_.GD.N0232.N0719.N0954.d009508
            (_root_.GD.N0232.N0720.N1504.d013957 alpha beta) _root_.GD.N0232.N0720.N1504.d013958
            (_root_.GD.N0232.N0719.N0853.d009567 _root_.GD.N0232.N0720.N1504.d013956
              (_root_.GD.N0232.N0719.N0925.d010557 u)) *
          phi
            (_root_.GD.N0232.N0719.N0925.d010557 u 0)) =
        ∫ u in Set.Ioo (0 : ℝ) 1,
          betaPDFReal alpha beta u * phi u := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      dsimp only
      change _root_.GD.N0232.N0720.N1504.d013964 alpha beta u * phi u = _
      rw [_root_.GD.N0232.N0720.N1504.d013965
        halpha hbeta hu]
    _ = ∫ u, betaPDFReal alpha beta u * phi u := by
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      filter_upwards with u hu
      have houtside : ¬(0 < u ∧ u < 1) := by
        simpa only [Set.mem_Ioo] using hu
      simp [betaPDFReal, houtside]
    _ = ∫ u, phi u ∂betaMeasure alpha beta := by
      symm
      exact _root_.GD.N0235.d004041
        halpha hbeta phi



theorem d013976
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    (_root_.GD.N0232.N0719.N0954.d009342
        (_root_.GD.N0232.N0720.N1504.d013957 alpha beta) _root_.GD.N0232.N0720.N1504.d013958).map _root_.GD.N0232.N0720.N1504.d013961 =
      betaMeasure alpha beta := by
  letI :
      ∀ i, IsProbabilityMeasure
        (gammaMeasure (_root_.GD.N0232.N0720.N1504.d013957 alpha beta i) (_root_.GD.N0232.N0720.N1504.d013958 i)) :=
    fun i => isProbabilityMeasure_gammaMeasure
      (_root_.GD.N0232.N0720.N1504.d013966 halpha hbeta i) (_root_.GD.N0232.N0720.N1504.d013967 i)
  letI :
      IsProbabilityMeasure
        (_root_.GD.N0232.N0719.N0954.d009342
          (_root_.GD.N0232.N0720.N1504.d013957 alpha beta) _root_.GD.N0232.N0720.N1504.d013958) := by
    unfold _root_.GD.N0232.N0719.N0954.d009342
    infer_instance
  letI : IsProbabilityMeasure (betaMeasure alpha beta) :=
    isProbabilityMeasureBeta halpha hbeta
  apply Measure.ext
  intro s hs
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _) (measure_ne_top _ _)).mp
  rw [← measureReal_def, ← measureReal_def,
    ← integral_indicator_one hs, ← integral_indicator_one hs]
  let phi : ℝ → ℝ := s.indicator (fun _ => (1 : ℝ))
  have hphi : Measurable phi :=
    Measurable.indicator measurable_const hs
  have hbound : ∀ u, |phi u| ≤ (1 : ℝ) := by
    intro u
    by_cases hu : u ∈ s <;> simp [phi, hu]
  change (∫ u, phi u
      ∂Measure.map _root_.GD.N0232.N0720.N1504.d013961
        (_root_.GD.N0232.N0719.N0954.d009342
          (_root_.GD.N0232.N0720.N1504.d013957 alpha beta) _root_.GD.N0232.N0720.N1504.d013958)) =
    ∫ u, phi u ∂betaMeasure alpha beta
  rw [integral_map _root_.GD.N0232.N0720.N1504.d013962.aemeasurable
    hphi.aestronglyMeasurable]
  exact _root_.GD.N0232.N0720.N1504.d013975
    halpha hbeta phi hphi hbound

theorem d013977
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    ∀ᵐ q ∂_root_.GD.N0232.N0720.N1091.d012755 alpha beta, 0 < q.1 ∧ 0 < q.2 := by
  unfold _root_.GD.N0232.N0720.N1091.d012755
  apply (Measure.ae_prod_iff_ae_ae
    ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd))).2
  filter_upwards [_root_.GD.N0232.N0720.N1091.d012773 halpha (by norm_num)] with x hx
  filter_upwards [_root_.GD.N0232.N0720.N1091.d012773 hbeta (by norm_num)] with y hy
  exact ⟨hx, hy⟩


theorem d013978
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    _root_.GD.N0232.N0720.N1091.d012758 alpha beta := by
  unfold _root_.GD.N0232.N0720.N1091.d012758
  calc
    (_root_.GD.N0232.N0720.N1091.d012755 alpha beta).map _root_.GD.N0232.N0720.N1091.d012757 =
        (_root_.GD.N0232.N0720.N1091.d012755 alpha beta).map
          (_root_.GD.N0232.N0720.N1504.d013961 ∘ _root_.GD.N0232.N0720.N1504.d013959) := by
      apply Measure.map_congr
      filter_upwards [_root_.GD.N0232.N0720.N1504.d013977 halpha hbeta]
        with q hq
      exact (_root_.GD.N0232.N0720.N1504.d013963 hq.1 hq.2).symm
    _ = ((_root_.GD.N0232.N0720.N1091.d012755 alpha beta).map _root_.GD.N0232.N0720.N1504.d013959).map
          _root_.GD.N0232.N0720.N1504.d013961 := by
      rw [Measure.map_map _root_.GD.N0232.N0720.N1504.d013962
        _root_.GD.N0232.N0720.N1504.d013960]
    _ = (_root_.GD.N0232.N0719.N0954.d009342
          (_root_.GD.N0232.N0720.N1504.d013957 alpha beta) _root_.GD.N0232.N0720.N1504.d013958).map _root_.GD.N0232.N0720.N1504.d013961 := by
      rw [_root_.GD.N0232.N0720.N1504.d013968 halpha hbeta]
    _ = betaMeasure alpha beta :=
      _root_.GD.N0232.N0720.N1504.d013976 halpha hbeta



theorem d013979
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    _root_.GD.N0232.N0720.N1091.d012761 alpha beta :=
  _root_.GD.N0232.N0720.N1091.d012793
    halpha hbeta (_root_.GD.N0232.N0720.N1504.d013978 halpha hbeta)

end

end N1504
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1504.d013965
#print axioms _root_.GD.N0232.N0720.N1504.d013968
#print axioms _root_.GD.N0232.N0720.N1504.d013975
#print axioms _root_.GD.N0232.N0720.N1504.d013976
#print axioms _root_.GD.N0232.N0720.N1504.d013978
#print axioms _root_.GD.N0232.N0720.N1504.d013979
