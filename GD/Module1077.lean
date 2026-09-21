import GD.Module1076
import GD.Module1030





























open MeasureTheory
open scoped ENNReal BigOperators RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1125

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0617
open _root_.GD.N0232.N0720.N1055
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1159

variable {m n : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

private noncomputable local instance d017248 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance





def d017249
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ :=
  ‖q‖ ^ 2 +
    ∑ i, weight i * (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal


def d017250
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) : ℝ :=
  (∑ i, weight i * (packet i).location ^ 2) -
    ∫ omega, _root_.GD.N0230.N0617.d000167 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
      (_root_.GD.N0232.N0720.N1126.d016414 packet) omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n



theorem d017251
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0232.N0720.N1125.d017250 (m := m) (n := n) packet weight =
      ∫ omega,
        _root_.GD.N0230.N0617.d000165 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
            (_root_.GD.N0232.N0720.N1126.d016414 packet) omega -
          _root_.GD.N0230.N0617.d000167 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
            (_root_.GD.N0232.N0720.N1126.d016414 packet) omega
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  have hsecond := _root_.GD.N0230.N0617.d000182
    (_root_.GD.N0232.N0720.N1080.d014172 m n) weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
      (_root_.GD.N0232.N0720.N1126.d016414 packet) (_root_.GD.N0232.N0720.N1126.d016421 packet)
  have hcorrection := _root_.GD.N0230.N0617.d000183
    (_root_.GD.N0232.N0720.N1080.d014172 m n) weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
      (_root_.GD.N0232.N0720.N1126.d016414 packet) hweight (_root_.GD.N0232.N0720.N1126.d016419 packet)
      (_root_.GD.N0232.N0720.N1126.d016420 packet)
      (_root_.GD.N0232.N0720.N1126.d016421 packet)
  have hsecondIntegral :
      (∫ omega, _root_.GD.N0230.N0617.d000165 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
          (_root_.GD.N0232.N0720.N1126.d016414 packet) omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
        ∑ i, weight i * (packet i).location ^ 2 := by
    unfold _root_.GD.N0230.N0617.d000165
    rw [integral_finsetSum Finset.univ (fun i _ ↦ by
      convert (_root_.GD.N0232.N0720.N1126.d016421 (m := m) (n := n) packet i).const_mul
        (weight i * _root_.GD.N0232.N0720.N1126.d016414 packet i ^ 2) using 1
      funext omega
      ring)]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      (∫ omega, weight i * _root_.GD.N0232.N0720.N1126.d016413 packet i omega *
          _root_.GD.N0232.N0720.N1126.d016414 packet i ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
          weight i * _root_.GD.N0232.N0720.N1126.d016414 packet i ^ 2 *
            ∫ omega, _root_.GD.N0232.N0720.N1126.d016413 packet i omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with omega
        ring
      _ = weight i * (packet i).location ^ 2 := by
        rw [_root_.GD.N0232.N0720.N1126.d016422]
        simp [_root_.GD.N0232.N0720.N1126.d016414]
  unfold _root_.GD.N0232.N0720.N1125.d017250
  rw [integral_sub hsecond hcorrection, hsecondIntegral]









theorem d017252
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (i : ι) (event : Set (_root_.GD.N0232.N0720.N1080.d014170 m n))
    (hevent : MeasurableSet event) (lower : ℝ) (hlower : 0 ≤ lower)
    (hmass : ∀ omega ∈ event,
      lower ≤ weight i * _root_.GD.N0232.N0720.N1126.d016413 packet i omega) :
    (lower / (1 + lower) * (packet i).location ^ 2) *
        (_root_.GD.N0232.N0720.N1080.d014172 m n event).toReal ≤
      _root_.GD.N0232.N0720.N1125.d017250 (m := m) (n := n) packet weight := by
  let density : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ := fun omega ↦
    _root_.GD.N0230.N0617.d000165 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
        (_root_.GD.N0232.N0720.N1126.d016414 packet) omega -
      _root_.GD.N0230.N0617.d000167 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
        (_root_.GD.N0232.N0720.N1126.d016414 packet) omega
  let tax : ℝ := lower / (1 + lower) * (packet i).location ^ 2
  have hlowerDen : 0 < 1 + lower := by linarith
  have hdensityInt : Integrable density (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    exact (_root_.GD.N0230.N0617.d000182
      (_root_.GD.N0232.N0720.N1080.d014172 m n) weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
        (_root_.GD.N0232.N0720.N1126.d016414 packet) (_root_.GD.N0232.N0720.N1126.d016421 packet)).sub
      (_root_.GD.N0230.N0617.d000183
        (_root_.GD.N0232.N0720.N1080.d014172 m n) weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
          (_root_.GD.N0232.N0720.N1126.d016414 packet) hweight (_root_.GD.N0232.N0720.N1126.d016419 packet)
          (_root_.GD.N0232.N0720.N1126.d016420 packet)
          (_root_.GD.N0232.N0720.N1126.d016421 packet))
  have hdensityNonneg : ∀ omega, 0 ≤ density omega := by
    intro omega
    have hsingle := _root_.GD.N0230.N0617.d000174
      weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet)
        hweight (_root_.GD.N0232.N0720.N1126.d016419 packet) i omega
    have hatomMass : 0 ≤ weight i * _root_.GD.N0232.N0720.N1126.d016413 packet i omega :=
      mul_nonneg (hweight i) (_root_.GD.N0232.N0720.N1126.d016419 packet i omega)
    have hcoeff :
        0 ≤ (weight i * _root_.GD.N0232.N0720.N1126.d016413 packet i omega) /
          (1 + weight i * _root_.GD.N0232.N0720.N1126.d016413 packet i omega) :=
      div_nonneg hatomMass (by linarith)
    exact (mul_nonneg hcoeff (sq_nonneg _)).trans hsingle
  have heventLower : ∀ omega ∈ event, tax ≤ density omega := by
    intro omega homega
    let a : ℝ := weight i * _root_.GD.N0232.N0720.N1126.d016413 packet i omega
    have ha : 0 ≤ a :=
      mul_nonneg (hweight i) (_root_.GD.N0232.N0720.N1126.d016419 packet i omega)
    have haDen : 0 < 1 + a := by linarith
    have hcoefficient : lower / (1 + lower) ≤ a / (1 + a) := by
      rw [div_le_div_iff₀ hlowerDen haDen]
      dsimp only [a]
      nlinarith [hmass omega homega]
    have htax : tax ≤
        a / (1 + a) * (packet i).location ^ 2 := by
      exact mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg _)
    exact htax.trans <| by
      simpa only [density, a, _root_.GD.N0232.N0720.N1126.d016414] using
        (_root_.GD.N0230.N0617.d000174
          weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet)
            hweight (_root_.GD.N0232.N0720.N1126.d016419 packet) i omega)
  have heventFinite : _root_.GD.N0232.N0720.N1080.d014172 m n event ≠ ∞ :=
    (measure_lt_top (_root_.GD.N0232.N0720.N1080.d014172 m n) event).ne
  have hconstInt : IntegrableOn (fun _omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ tax)
      event (_root_.GD.N0232.N0720.N1080.d014172 m n) := integrableOn_const heventFinite
  have hsetLower :
      tax * (_root_.GD.N0232.N0720.N1080.d014172 m n event).toReal ≤
        ∫ omega in event, density omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    have hmono := setIntegral_mono_on hconstInt hdensityInt.integrableOn
      hevent heventLower
    rw [setIntegral_const, smul_eq_mul] at hmono
    simpa only [Measure.real, mul_comm] using hmono
  have hsetUpper :
      (∫ omega in event, density omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n) ≤
        ∫ omega, density omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n :=
    setIntegral_le_integral hdensityInt
      (Filter.Eventually.of_forall hdensityNonneg)
  rw [_root_.GD.N0232.N0720.N1125.d017251
    packet weight hweight]
  exact hsetLower.trans hsetUpper


theorem d017253
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ‖q‖ ^ 2 = ∫ omega, (q omega) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  rw [← real_inner_self_eq_norm_sq q, L2.inner_def]
  apply integral_congr_ae
  filter_upwards with omega
  simp only [RCLike.inner_apply, conj_trivial, pow_two]



theorem d017254
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ‖q - _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight‖ ^ 2 =
      ∫ omega,
        (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  rw [← real_inner_self_eq_norm_sq
    (q - _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub q
      (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight),
    _root_.GD.N0232.N0720.N1126.d016427 packet weight hweight] with
      omega hsub hcompletion
  rw [hsub, Pi.sub_apply, hcompletion]
  simp only [RCLike.inner_apply, conj_trivial, pow_two]




theorem d017255
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hqFinite : ∀ i, _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q ≠ ⊤) :
    _root_.GD.N0232.N0720.N1125.d017249 (m := m) (n := n) packet weight q =
      (∫ omega, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
          (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
            ∂_root_.GD.N0232.N0720.N1080.d014172 m n) +
        _root_.GD.N0232.N0720.N1125.d017250 (m := m) (n := n) packet weight := by
  have hexact := _root_.GD.N0230.N0617.d000187
    (_root_.GD.N0232.N0720.N1080.d014172 m n) weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
      (_root_.GD.N0232.N0720.N1126.d016414 packet) (fun omega ↦ q omega)
      hweight (_root_.GD.N0232.N0720.N1126.d016419 packet)
      (_root_.GD.N0232.N0720.N1126.d016420 packet)
      (_root_.GD.N0232.N0720.N1126.d016421 packet)
      (Lp.memLp q).integrable_sq
      (fun i ↦ _root_.GD.N0232.N0720.N1126.d016429
        (packet i) q (hqFinite i))
  rw [← _root_.GD.N0232.N0720.N1125.d017253 q] at hexact
  have hriskEq (i : ι) :
      (∫ omega, _root_.GD.N0232.N0720.N1126.d016413 packet i omega *
          (q omega - _root_.GD.N0232.N0720.N1126.d016414 packet i) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
        (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal :=
    (_root_.GD.N0232.N0720.N1126.d016430
      (packet i) q (hqFinite i)).symm
  simp_rw [hriskEq] at hexact
  simp_rw [_root_.GD.N0232.N0720.N1126.d016422] at hexact
  simp only [_root_.GD.N0232.N0720.N1125.d017249, _root_.GD.N0232.N0720.N1125.d017250,
    _root_.GD.N0232.N0720.N1126.d016415, _root_.GD.N0232.N0720.N1126.d016416, _root_.GD.N0232.N0720.N1126.d016414,
    mul_one] at hexact ⊢
  linarith


theorem d017256
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    (∫ omega, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
        (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight omega -
          _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n) = 0 := by
  calc
    (∫ omega, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
        (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight omega -
          _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
        ∫ _omega, (0 : ℝ) ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
      apply integral_congr_ae
      filter_upwards [_root_.GD.N0232.N0720.N1126.d016427
          packet weight hweight] with omega hcompletion
      simp only [hcompletion, sub_self, pow_two, mul_zero]
    _ = 0 := by simp


theorem d017257
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0232.N0720.N1125.d017249 (m := m) (n := n) packet weight
        (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
          packet weight hweight) =
      _root_.GD.N0232.N0720.N1125.d017250 (m := m) (n := n) packet weight := by
  rw [_root_.GD.N0232.N0720.N1125.d017255
      (m := m) (n := n) packet weight hweight
      (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
        packet weight hweight)
      (fun i ↦ _root_.GD.N0232.N0720.N1126.d016428
        (m := m) (n := n) packet weight hweight (packet i)),
    _root_.GD.N0232.N0720.N1125.d017256
      (m := m) (n := n),
    zero_add]


theorem d017258
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hqFinite : ∀ i, _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q ≠ ⊤) :
    _root_.GD.N0232.N0720.N1125.d017249 (m := m) (n := n) packet weight q -
        _root_.GD.N0232.N0720.N1125.d017249 (m := m) (n := n) packet weight
          (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
            packet weight hweight) =
      ∫ omega, _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
        (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  rw [_root_.GD.N0232.N0720.N1125.d017255
      (m := m) (n := n) packet weight hweight q hqFinite,
    _root_.GD.N0232.N0720.N1125.d017257
      (m := m) (n := n)]
  ring




theorem d017259
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hqFinite : ∀ i, _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q ≠ ⊤) :
    ‖q - _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
        packet weight hweight‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1125.d017249 (m := m) (n := n) packet weight q -
        _root_.GD.N0232.N0720.N1125.d017249 (m := m) (n := n) packet weight
          (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
            packet weight hweight) := by
  rw [_root_.GD.N0232.N0720.N1125.d017258
      (m := m) (n := n) packet weight hweight q hqFinite,
    _root_.GD.N0232.N0720.N1125.d017254
      (m := m) (n := n)]
  have hplain : Integrable (fun omega ↦
      (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    have hsub :=
      (Lp.memLp (q - _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight)).integrable_sq
    refine hsub.congr ?_
    filter_upwards [Lp.coeFn_sub q
        (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight),
      _root_.GD.N0232.N0720.N1126.d016427 packet weight hweight] with
        omega hsubCoe hcompletion
    rw [hsubCoe, Pi.sub_apply, hcompletion]
  have hweighted := _root_.GD.N0230.N0617.d000185
    (_root_.GD.N0232.N0720.N1080.d014172 m n) weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
      (_root_.GD.N0232.N0720.N1126.d016414 packet) (fun omega ↦ q omega)
      hweight (_root_.GD.N0232.N0720.N1126.d016419 packet)
      (_root_.GD.N0232.N0720.N1126.d016420 packet)
      (_root_.GD.N0232.N0720.N1126.d016421 packet)
      (Lp.memLp q).integrable_sq
      (fun i ↦ _root_.GD.N0232.N0720.N1126.d016429
        (packet i) q (hqFinite i))
  apply integral_mono hplain hweighted
  intro omega
  have hmass := _root_.GD.N0230.N0617.d000168 weight (_root_.GD.N0232.N0720.N1126.d016413 packet)
    hweight (_root_.GD.N0232.N0720.N1126.d016419 packet) omega
  change (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2 ≤
    _root_.GD.N0232.N0720.N1126.d016415 packet weight omega *
      (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega) ^ 2
  exact le_mul_of_one_le_left
    (sq_nonneg (q omega - _root_.GD.N0232.N0720.N1126.d016416 packet weight omega))
    hmass




theorem d017260
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (href : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 q ≤
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169
        (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight))
    (hatomRisk : ∀ i, _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q ≤
      _root_.GD.N0232.N0720.N1080.d014182 m n (packet i)
        (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight)) :
    _root_.GD.N0232.N0720.N1125.d017249 (m := m) (n := n) packet weight q ≤
      _root_.GD.N0232.N0720.N1125.d017249 (m := m) (n := n) packet weight
        (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
          packet weight hweight) := by
  have huFinite := _root_.GD.N0232.N0720.N1126.d016428
    (m := m) (n := n) packet weight hweight
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
  simp only [zero_sub, norm_neg] at href
  have hrefReal : ‖q‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp href
  have hatom : ∀ i,
      (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q).toReal ≤
        (_root_.GD.N0232.N0720.N1080.d014182 m n (packet i)
          (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight)).toReal := by
    intro i
    exact ENNReal.toReal_mono (huFinite (packet i)) (hatomRisk i)
  unfold _root_.GD.N0232.N0720.N1125.d017249
  exact add_le_add hrefReal <|
    Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_left (hatom i) (hweight i)



theorem d017261
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 m n) q
      (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight)) :
    _root_.GD.N0232.N0720.N1125.d017249 (m := m) (n := n) packet weight q ≤
      _root_.GD.N0232.N0720.N1125.d017249 (m := m) (n := n) packet weight
        (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
          packet weight hweight) := by
  exact _root_.GD.N0232.N0720.N1125.d017260
    (m := m) (n := n) packet weight hweight q
      (hq _root_.GD.N0232.N0720.N1080.d014169) (fun i ↦ hq (packet i))




theorem d017262
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (href : _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 q ≤
      _root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169
        (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight))
    (hatomRisk : ∀ i, _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q ≤
      _root_.GD.N0232.N0720.N1080.d014182 m n (packet i)
        (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight)) :
    q = _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
      packet weight hweight := by
  have huFinite := _root_.GD.N0232.N0720.N1126.d016428
    (m := m) (n := n) packet weight hweight
  have hqFinite : ∀ i, _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q ≠ ⊤ := by
    intro i
    exact ne_top_of_le_ne_top (huFinite (packet i)) (hatomRisk i)
  have hdist := _root_.GD.N0232.N0720.N1125.d017259
    (m := m) (n := n) packet weight hweight q hqFinite
  have hobj := _root_.GD.N0232.N0720.N1125.d017260
    (m := m) (n := n) packet weight hweight q href hatomRisk
  have hnorm : ‖q - _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight‖ = 0 := by
    nlinarith [norm_nonneg
      (q - _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)




theorem d017263
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight) := by
  intro q hq
  have huFinite := _root_.GD.N0232.N0720.N1126.d016428
    (m := m) (n := n) packet weight hweight
  have hqFinite : ∀ i, _root_.GD.N0232.N0720.N1080.d014182 m n (packet i) q ≠ ⊤ := by
    intro i
    exact ne_top_of_le_ne_top (huFinite (packet i)) (hq (packet i))
  have hdist := _root_.GD.N0232.N0720.N1125.d017259
    packet weight hweight q hqFinite
  have hobj := _root_.GD.N0232.N0720.N1125.d017261
    packet weight hweight q hq
  have hnorm : ‖q - _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight‖ = 0 := by
    nlinarith [norm_nonneg
      (q - _root_.GD.N0232.N0720.N1126.d016426 packet weight hweight)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)



theorem d017264
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight) ∧
      ¬ _root_.GD.N0232.N0720.N1159.d014638 m n
        (_root_.GD.N0232.N0720.N1126.d016426 packet weight hweight) := by
  exact ⟨_root_.GD.N0232.N0720.N1125.d017263
      packet weight hweight,
    _root_.GD.N0232.N0720.N1055.d017240
      packet weight hweight⟩

end

end N1125
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1125.d017255
#print axioms _root_.GD.N0232.N0720.N1125.d017252
#print axioms _root_.GD.N0232.N0720.N1125.d017258
#print axioms _root_.GD.N0232.N0720.N1125.d017259
#print axioms _root_.GD.N0232.N0720.N1125.d017263
#print axioms _root_.GD.N0232.N0720.N1125.d017264
