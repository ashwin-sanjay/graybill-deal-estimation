import GD.Module0850
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
















open MeasureTheory ProbabilityTheory Filter Set

namespace GD
namespace N0232
namespace N0720
namespace N1093

noncomputable section

open _root_.GD.N0232.N0720.N1091 _root_.GD.N0232.N0720.N1092



theorem d013046
    {alpha beta u : ℝ}
    (_halpha : 0 < alpha) (_hbeta : 0 < beta)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    betaPDFReal alpha beta u * _root_.GD.N0232.N0720.N1092.d013024 u =
      (1 / ProbabilityTheory.beta alpha beta) *
        u ^ (alpha - 3) * (1 - u) ^ (beta + 1) := by
  have h1u : 0 < 1 - u := sub_pos.mpr hu.2
  have hu' : 0 < u ∧ u < 1 := hu
  rw [betaPDFReal, if_pos hu']
  unfold _root_.GD.N0232.N0720.N1092.d013024
  have hleft : alpha - 1 + (-2 : ℝ) = alpha - 3 := by ring
  have hright : beta - 1 + (2 : ℝ) = beta + 1 := by ring
  calc
    1 / ProbabilityTheory.beta alpha beta * u ^ (alpha - 1) *
          (1 - u) ^ (beta - 1) *
          (u ^ (-2 : ℝ) * (1 - u) ^ 2) =
        1 / ProbabilityTheory.beta alpha beta *
          (u ^ (alpha - 1) * u ^ (-2 : ℝ)) *
          ((1 - u) ^ (beta - 1) * (1 - u) ^ (2 : ℝ)) := by
      rw [Real.rpow_two]
      ring
    _ = (1 / ProbabilityTheory.beta alpha beta) *
        u ^ (alpha - 3) * (1 - u) ^ (beta + 1) := by
      rw [← Real.rpow_add hu.1, ← Real.rpow_add h1u, hleft, hright]



def d013047 (alpha beta : ℝ) : ℝ :=
  (1 / ProbabilityTheory.beta alpha beta) * (1 / 2 : ℝ) ^ (beta + 1)

theorem d013048
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    0 < _root_.GD.N0232.N0720.N1093.d013047 alpha beta := by
  unfold _root_.GD.N0232.N0720.N1093.d013047
  exact mul_pos (one_div_pos.mpr (ProbabilityTheory.beta_pos halpha hbeta))
    (Real.rpow_pos_of_pos (by norm_num) _)



theorem d013049
    {alpha beta u : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hu : u ∈ Ioo (0 : ℝ) (1 / 2)) :
    _root_.GD.N0232.N0720.N1093.d013047 alpha beta * u ^ (alpha - 3) ≤
      betaPDFReal alpha beta u * _root_.GD.N0232.N0720.N1092.d013024 u := by
  have huOne : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans (by norm_num)⟩
  rw [_root_.GD.N0232.N0720.N1093.d013046 halpha hbeta huOne]
  unfold _root_.GD.N0232.N0720.N1093.d013047
  have hbase : (1 / 2 : ℝ) ≤ 1 - u := by
    norm_num at hu ⊢
    linarith
  have hexp : 0 ≤ beta + 1 := by linarith
  have hpow : (1 / 2 : ℝ) ^ (beta + 1) ≤ (1 - u) ^ (beta + 1) :=
    Real.rpow_le_rpow (by norm_num) hbase hexp
  have hnorm : 0 ≤ 1 / ProbabilityTheory.beta alpha beta :=
    (one_div_pos.mpr (ProbabilityTheory.beta_pos halpha hbeta)).le
  have hupow : 0 ≤ u ^ (alpha - 3) := Real.rpow_nonneg hu.1.le _
  nlinarith [mul_le_mul_of_nonneg_left hpow (mul_nonneg hnorm hupow)]



theorem d013050
    {alpha beta : ℝ} (halpha : 2 < alpha) (hbeta : 0 < beta) :
    ProbabilityTheory.beta (alpha - 2) (beta + 2) /
        ProbabilityTheory.beta alpha beta =
      beta * (beta + 1) / ((alpha - 1) * (alpha - 2)) := by
  have ha2 : 0 < alpha - 2 := sub_pos.mpr halpha
  have ha1 : 0 < alpha - 1 := by linarith
  have hb1 : 0 < beta + 1 := by linarith
  have hL1 : ProbabilityTheory.beta (alpha - 1) beta =
      (alpha - 2) / (alpha - 2 + beta) *
        ProbabilityTheory.beta (alpha - 2) beta := by
    convert _root_.GD.N0235.d004038 ha2 hbeta using 1 <;> ring
  have hL2 : ProbabilityTheory.beta alpha beta =
      (alpha - 1) / (alpha - 1 + beta) *
        ProbabilityTheory.beta (alpha - 1) beta := by
    convert _root_.GD.N0235.d004038 ha1 hbeta using 1 <;> ring
  have hR1 : ProbabilityTheory.beta (alpha - 2) (beta + 1) =
      beta / (alpha - 2 + beta) *
        ProbabilityTheory.beta (alpha - 2) beta := by
    exact _root_.GD.N0235.d004039 ha2 hbeta
  have hR2 : ProbabilityTheory.beta (alpha - 2) (beta + 2) =
      (beta + 1) / (alpha - 2 + (beta + 1)) *
        ProbabilityTheory.beta (alpha - 2) (beta + 1) := by
    convert _root_.GD.N0235.d004039 ha2 hb1 using 1 <;> ring
  rw [hR2, hR1, hL2, hL1]
  field_simp [ne_of_gt ha2, ne_of_gt ha1, ne_of_gt hbeta,
    ne_of_gt (ProbabilityTheory.beta_pos ha2 hbeta),
    ne_of_gt (add_pos ha2 hbeta),
    ne_of_gt (add_pos ha1 hbeta)]
  <;> ring



theorem d013051
    {alpha beta : ℝ} (halpha : 2 < alpha) (hbeta : 0 < beta) :
    (∫ u, (_root_.GD.N0232.N0720.N1092.d013035 alpha beta u) ^ 2
      ∂betaMeasure alpha beta) =
      alpha ^ 2 * (beta + 1) /
        (beta * (alpha - 1) * (alpha - 2)) := by
  rw [_root_.GD.N0232.N0720.N1092.d013040 halpha hbeta,
    _root_.GD.N0232.N0720.N1093.d013050 halpha hbeta]
  field_simp [hbeta.ne', (sub_pos.mpr halpha).ne',
    (by linarith : alpha - 1 ≠ 0)]


theorem d013052
    {alpha beta : ℝ} (halpha : 0 < alpha) (halphaTwo : alpha ≤ 2)
    (hbeta : 0 < beta) :
    ¬ Integrable _root_.GD.N0232.N0720.N1092.d013024 (betaMeasure alpha beta) := by
  intro hint
  have hweighted : Integrable
      (fun u => _root_.GD.N0232.N0720.N1092.d013024 u * betaPDFReal alpha beta u) := by
    change Integrable _root_.GD.N0232.N0720.N1092.d013024
      (volume.withDensity (fun u => ENNReal.ofReal (betaPDFReal alpha beta u))) at hint
    rw [integrable_withDensity_iff
      ((measurable_betaPDFReal alpha beta).ennreal_ofReal) (by simp)] at hint
    apply hint.congr
    filter_upwards with u
    rw [ENNReal.toReal_ofReal
      (_root_.GD.N0235.d004040 halpha hbeta u)]
  have hweightedHalf : IntegrableOn
      (fun u => betaPDFReal alpha beta u * _root_.GD.N0232.N0720.N1092.d013024 u)
      (Ioo (0 : ℝ) (1 / 2)) := by
    exact (hweighted.congr (Eventually.of_forall fun u => by ring)).integrableOn
  let c := _root_.GD.N0232.N0720.N1093.d013047 alpha beta
  have hc : 0 < c := _root_.GD.N0232.N0720.N1093.d013048 halpha hbeta
  have hcriticalScaled : IntegrableOn
      (fun u => c * u ^ (alpha - 3)) (Ioo (0 : ℝ) (1 / 2)) := by
    apply hweightedHalf.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hc.le (Real.rpow_nonneg hu.1.le _))]
    exact _root_.GD.N0232.N0720.N1093.d013049 halpha hbeta hu
  have hcritical : IntegrableOn
      (fun u => u ^ (alpha - 3)) (Ioo (0 : ℝ) (1 / 2)) := by
    have hscaled := hcriticalScaled.const_mul c⁻¹
    apply IntegrableOn.congr_fun hscaled _ measurableSet_Ioo
    intro u hu
    field_simp [hc.ne']
  have hpower := (intervalIntegral.integrableOn_Ioo_rpow_iff
    (by norm_num : (0 : ℝ) < 1 / 2)).1 hcritical
  linarith



theorem d013053
    {alpha beta : ℝ} (halpha : 0 < alpha) (halphaTwo : alpha ≤ 2)
    (hbeta : 0 < beta) :
    ¬ Integrable (fun u => (_root_.GD.N0232.N0720.N1092.d013035 alpha beta u) ^ 2)
      (betaMeasure alpha beta) := by
  intro hint
  have hscale : 0 < (alpha / beta) ^ 2 := sq_pos_of_pos (div_pos halpha hbeta)
  have hscaled : Integrable
      (fun u => (alpha / beta) ^ 2 * _root_.GD.N0232.N0720.N1092.d013024 u)
      (betaMeasure alpha beta) := by
    apply hint.congr
    filter_upwards [_root_.GD.N0232.N0720.N1092.d013031 alpha beta] with u hu
    exact _root_.GD.N0232.N0720.N1092.d013038 hbeta.ne' hu
  have hinverse := hscaled.const_mul (((alpha / beta) ^ 2)⁻¹)
  have : Integrable _root_.GD.N0232.N0720.N1092.d013024 (betaMeasure alpha beta) := by
    apply hinverse.congr
    filter_upwards with u
    field_simp [hscale.ne']
  exact _root_.GD.N0232.N0720.N1093.d013052 halpha halphaTwo hbeta this


theorem d013054
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    Integrable _root_.GD.N0232.N0720.N1092.d013024 (betaMeasure alpha beta) ↔ 2 < alpha := by
  constructor
  · intro hint
    exact lt_of_not_ge fun h => _root_.GD.N0232.N0720.N1093.d013052 halpha h hbeta hint
  · intro h
    exact _root_.GD.N0232.N0720.N1092.d013029 h hbeta


theorem d013055
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    Integrable (fun u => (_root_.GD.N0232.N0720.N1092.d013035 alpha beta u) ^ 2)
      (betaMeasure alpha beta) ↔ 2 < alpha := by
  constructor
  · intro hint
    exact lt_of_not_ge fun h =>
      _root_.GD.N0232.N0720.N1093.d013053 halpha h hbeta hint
  · intro h
    exact _root_.GD.N0232.N0720.N1092.d013039 h hbeta



theorem d013056
    {n : ℕ} (hn : 2 ≤ n) {beta : ℝ} (hbeta : 0 < beta) :
    Integrable _root_.GD.N0232.N0720.N1092.d013024
      (betaMeasure (((n - 1 : ℕ) : ℝ) / 2) beta) ↔ 6 ≤ n := by
  have hshape : 0 < (((n - 1 : ℕ) : ℝ) / 2) := by
    have hnsub : 1 ≤ n - 1 := by omega
    have hnsubReal : (1 : ℝ) ≤ (n - 1 : ℕ) := by exact_mod_cast hnsub
    linarith
  exact (_root_.GD.N0232.N0720.N1093.d013054 hshape hbeta).trans
    _root_.GD.N0232.N0720.N1092.d013044



theorem d013057
    {n : ℕ} (hn : 2 ≤ n) {beta : ℝ} (hbeta : 0 < beta) :
    Integrable
      (fun u =>
        (_root_.GD.N0232.N0720.N1092.d013035 (((n - 1 : ℕ) : ℝ) / 2) beta u) ^ 2)
      (betaMeasure (((n - 1 : ℕ) : ℝ) / 2) beta) ↔ 6 ≤ n := by
  have hshape : 0 < (((n - 1 : ℕ) : ℝ) / 2) := by
    have hnsub : 1 ≤ n - 1 := by omega
    have hnsubReal : (1 : ℝ) ≤ (n - 1 : ℕ) := by exact_mod_cast hnsub
    linarith
  exact (_root_.GD.N0232.N0720.N1093.d013055 hshape hbeta).trans
    _root_.GD.N0232.N0720.N1092.d013044

end

end N1093
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1093.d013052
#print axioms _root_.GD.N0232.N0720.N1093.d013053
#print axioms _root_.GD.N0232.N0720.N1093.d013051
#print axioms _root_.GD.N0232.N0720.N1093.d013054
#print axioms _root_.GD.N0232.N0720.N1093.d013055
#print axioms _root_.GD.N0232.N0720.N1093.d013057
