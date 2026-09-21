import GD.Module1038























open Filter MeasureTheory
open scoped BigOperators ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1212

noncomputable section

open _root_.GD.N0230.N0591
open _root_.GD.N0230.N0617
open _root_.GD.N0230.N0618
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0720.N1078
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1132
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0232.N0720.N1499

set_option linter.unusedSectionVars false



variable {Omega : Type*} [MeasurableSpace Omega]




def d016733 (mu : Measure Omega) (likelihood : Omega → ℝ)
    (K : ℝ) : ℝ :=
  ∫ omega in {omega | K < likelihood omega}, likelihood omega ∂mu





theorem d016734
    (mu : Measure Omega) (f g likelihood : Omega → ℝ) (B K : ℝ)
    (hsq : Integrable (fun omega ↦ (f omega - g omega) ^ 2) mu)
    (hlikelihoodInt : Integrable likelihood mu)
    (hlikelihoodMeas : Measurable likelihood)
    (hlikelihood : ∀ omega, 0 ≤ likelihood omega)
    (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hf : ∀ omega, |f omega| ≤ B)
    (hg : ∀ omega, |g omega| ≤ B) :
    ∫ omega, likelihood omega * (f omega - g omega) ^ 2 ∂mu ≤
      K * ∫ omega, (f omega - g omega) ^ 2 ∂mu +
        4 * B ^ 2 * _root_.GD.N0232.N0720.N1212.d016733 mu likelihood K := by
  let high : Set Omega := {omega | K < likelihood omega}
  have hhigh : MeasurableSet high := by
    exact measurableSet_lt measurable_const hlikelihoodMeas
  have hsqBound : ∀ᵐ omega ∂mu,
      ‖(f omega - g omega) ^ 2‖ ≤ 4 * B ^ 2 := by
    filter_upwards with omega
    have hdiff : |f omega - g omega| ≤ 2 * B := by
      calc
        |f omega - g omega| ≤ |f omega| + |g omega| := abs_sub _ _
        _ ≤ B + B := add_le_add (hf omega) (hg omega)
        _ = 2 * B := by ring
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hsquare : (f omega - g omega) ^ 2 ≤ (2 * B) ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) hB)).2 hdiff
    nlinarith
  have hleft : Integrable
      (fun omega ↦ likelihood omega * (f omega - g omega) ^ 2) mu :=
    hlikelihoodInt.mul_bdd hsq.aestronglyMeasurable hsqBound
  have htail : Integrable (high.indicator likelihood) mu :=
    hlikelihoodInt.integrableOn.integrable_indicator hhigh
  have hfirst : Integrable
      (fun omega ↦ K * (f omega - g omega) ^ 2) mu :=
    hsq.const_mul K
  have hsecond : Integrable
      (fun omega ↦ 4 * B ^ 2 * high.indicator likelihood omega) mu :=
    htail.const_mul (4 * B ^ 2)
  have hright : Integrable (fun omega ↦
      K * (f omega - g omega) ^ 2 +
        4 * B ^ 2 * high.indicator likelihood omega) mu :=
    hfirst.add hsecond
  calc
    ∫ omega, likelihood omega * (f omega - g omega) ^ 2 ∂mu ≤
        ∫ omega,
          (K * (f omega - g omega) ^ 2 +
            4 * B ^ 2 * high.indicator likelihood omega) ∂mu := by
      apply integral_mono hleft hright
      intro omega
      change likelihood omega * (f omega - g omega) ^ 2 ≤
        K * (f omega - g omega) ^ 2 +
          4 * B ^ 2 * high.indicator likelihood omega
      by_cases homega : omega ∈ high
      · have hsqPoint : (f omega - g omega) ^ 2 ≤ 4 * B ^ 2 := by
          have hdiff : |f omega - g omega| ≤ 2 * B := by
            calc
              |f omega - g omega| ≤ |f omega| + |g omega| := abs_sub _ _
              _ ≤ B + B := add_le_add (hf omega) (hg omega)
              _ = 2 * B := by ring
          have hsquare : (f omega - g omega) ^ 2 ≤ (2 * B) ^ 2 := by
            rw [← sq_abs]
            exact (sq_le_sq₀ (abs_nonneg _)
              (mul_nonneg (by norm_num) hB)).2 hdiff
          nlinarith
        rw [Set.indicator_of_mem homega]
        have hmul := mul_le_mul_of_nonneg_left hsqPoint
          (hlikelihood omega)
        have hnonneg : 0 ≤ K * (f omega - g omega) ^ 2 :=
          mul_nonneg hK (sq_nonneg _)
        nlinarith
      · rw [Set.indicator_of_notMem homega, mul_zero, add_zero]
        have hle : likelihood omega ≤ K := le_of_not_gt homega
        exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
    _ = K * ∫ omega, (f omega - g omega) ^ 2 ∂mu +
        4 * B ^ 2 * _root_.GD.N0232.N0720.N1212.d016733 mu likelihood K := by
      rw [integral_add hfirst hsecond, integral_const_mul,
        integral_const_mul]
      unfold _root_.GD.N0232.N0720.N1212.d016733 high
      rw [integral_indicator hhigh]




theorem d016735
    (mu : Measure Omega) (likelihood : Omega → ℝ)
    (hlikelihoodInt : Integrable likelihood mu)
    (hlikelihoodMeas : Measurable likelihood) :
    Tendsto (fun N : ℕ ↦ _root_.GD.N0232.N0720.N1212.d016733 mu likelihood (N : ℝ))
      atTop (nhds 0) := by
  let high : ℕ → Set Omega := fun N ↦
    {omega | (N : ℝ) < likelihood omega}
  have hhigh : ∀ N, MeasurableSet (high N) := by
    intro N
    exact measurableSet_lt measurable_const hlikelihoodMeas
  have hanti : Antitone high := by
    intro N M hNM omega homega
    change (M : ℝ) < likelihood omega at homega
    exact lt_of_le_of_lt (by exact_mod_cast hNM) homega
  have hinter : ⋂ N, high N = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro omega homega
    obtain ⟨N, hN⟩ := exists_nat_gt (likelihood omega)
    have hhighN : (N : ℝ) < likelihood omega :=
      Set.mem_iInter.1 homega N
    exact lt_asymm hN hhighN
  have htendsto := hanti.tendsto_setIntegral hhigh
    hlikelihoodInt.integrableOn
  simpa [_root_.GD.N0232.N0720.N1212.d016733, high, hinter] using htendsto



variable (m n : ℕ) [NeZero m] [NeZero n]
variable {I : Type*} [Fintype I] [DecidableEq I]

private noncomputable local instance d016736 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance


def d016737 (theta : _root_.GD.N0232.N0720.N1080.d014168) (K : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1212.d016733 (_root_.GD.N0232.N0720.N1080.d014172 m n)
    (_root_.GD.N0232.N0720.N1499.d015001 m n theta) K



theorem d016738 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    Tendsto (fun N : ℕ ↦ _root_.GD.N0232.N0720.N1212.d016737 m n theta (N : ℝ))
      atTop (nhds 0) := by
  exact _root_.GD.N0232.N0720.N1212.d016735
    (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1499.d015001 m n theta)
      (_root_.GD.N0232.N0720.N1484.d015103 m n theta)
      (_root_.GD.N0232.N0720.N1499.d015002 m n theta)




theorem d016739
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (packet : I → _root_.GD.N0232.N0720.N1080.d014168)
    (weight weight' : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hweight' : ∀ i, 0 ≤ weight' i) (K : ℝ) (hK : 0 ≤ K) :
    ∫ omega,
        (_root_.GD.N0232.N0720.N1126.d016416 packet weight omega -
          _root_.GD.N0232.N0720.N1126.d016416 packet weight' omega) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta ≤
      K * ∫ omega,
        (_root_.GD.N0232.N0720.N1126.d016416 packet weight omega -
          _root_.GD.N0232.N0720.N1126.d016416 packet weight' omega) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n +
      4 * _root_.GD.N0232.N0720.N1126.d016418 packet ^ 2 *
        _root_.GD.N0232.N0720.N1212.d016737 m n theta K := by
  let f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
    _root_.GD.N0232.N0720.N1126.d016416 packet weight
  let g : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
    _root_.GD.N0232.N0720.N1126.d016416 packet weight'
  let likelihood : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
    _root_.GD.N0232.N0720.N1499.d015001 m n theta
  have hsq : Integrable (fun omega ↦ (f omega - g omega) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    ((_root_.GD.N0232.N0720.N1126.d016425 packet weight hweight).sub
      (_root_.GD.N0232.N0720.N1126.d016425 packet weight' hweight')).integrable_sq
  have hweighted := _root_.GD.N0232.N0720.N1212.d016734
    (_root_.GD.N0232.N0720.N1080.d014172 m n) f g likelihood (_root_.GD.N0232.N0720.N1126.d016418 packet) K
    hsq (_root_.GD.N0232.N0720.N1484.d015103 m n theta)
    (_root_.GD.N0232.N0720.N1499.d015002 m n theta)
    (_root_.GD.N0232.N0720.N1499.d015003 m n theta)
    (Real.sqrt_nonneg _) hK
    (_root_.GD.N0232.N0720.N1126.d016424 packet weight hweight)
    (_root_.GD.N0232.N0720.N1126.d016424 packet weight' hweight')
  have hphysical :
      (∫ omega, (f omega - g omega) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) =
        ∫ omega, likelihood omega * (f omega - g omega) ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    simpa [_root_.GD.N0230.N0591.d000133, likelihood] using
      (_root_.GD.N0230.N0591.d000135
        (_root_.GD.N0232.N0720.N1499.d015001 m n theta)
        (fun omega ↦ (f omega - g omega) ^ 2)
        (_root_.GD.N0232.N0720.N1499.d015006 m n theta)
        (_root_.GD.N0232.N0720.N1499.d015002 m n theta)
        (_root_.GD.N0232.N0720.N1499.d015003 m n theta))
  simpa [f, g, likelihood, _root_.GD.N0232.N0720.N1212.d016737] using
    (hphysical.symm ▸ hweighted)





theorem d016740
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (packet : I → _root_.GD.N0232.N0720.N1080.d014168)
    (weight weight' : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hweight' : ∀ i, 0 ≤ weight' i) (K : ℝ) (hK : 0 ≤ K) :
    ∫ omega,
        (_root_.GD.N0232.N0720.N1126.d016416 packet weight omega -
          _root_.GD.N0232.N0720.N1126.d016416 packet weight' omega) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta ≤
      4 * _root_.GD.N0232.N0720.N1126.d016418 packet ^ 2 *
        (K * ∑ i, |weight i - weight' i| +
          _root_.GD.N0232.N0720.N1212.d016737 m n theta K) := by
  have hthreshold :=
    _root_.GD.N0232.N0720.N1212.d016739
      m n theta packet weight weight' hweight hweight' K hK
  have href := _root_.GD.N0232.N0720.N1132.d016562
    m n packet weight weight' hweight hweight'
  have hscale := mul_le_mul_of_nonneg_left href hK
  calc
    ∫ omega,
        (_root_.GD.N0232.N0720.N1126.d016416 packet weight omega -
          _root_.GD.N0232.N0720.N1126.d016416 packet weight' omega) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta ≤
      K * ∫ omega,
        (_root_.GD.N0232.N0720.N1126.d016416 packet weight omega -
          _root_.GD.N0232.N0720.N1126.d016416 packet weight' omega) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n +
      4 * _root_.GD.N0232.N0720.N1126.d016418 packet ^ 2 *
        _root_.GD.N0232.N0720.N1212.d016737 m n theta K := hthreshold
    _ ≤ K * (4 * _root_.GD.N0232.N0720.N1126.d016418 packet ^ 2 *
          ∑ i, |weight i - weight' i|) +
        4 * _root_.GD.N0232.N0720.N1126.d016418 packet ^ 2 *
          _root_.GD.N0232.N0720.N1212.d016737 m n theta K :=
      add_le_add hscale (le_refl _)
    _ = 4 * _root_.GD.N0232.N0720.N1126.d016418 packet ^ 2 *
        (K * ∑ i, |weight i - weight' i| +
          _root_.GD.N0232.N0720.N1212.d016737 m n theta K) := by ring

end

end N1212
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1212.d016734
#print axioms _root_.GD.N0232.N0720.N1212.d016738
#print axioms _root_.GD.N0232.N0720.N1212.d016740
