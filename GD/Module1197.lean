import GD.Module1191
import GD.Module1145
import GD.Module1166
import GD.Module0988































open Filter MeasureTheory Topology

namespace GD
namespace N0232
namespace N0720
namespace N1451

noncomputable section

open _root_.GD.N0230.N0617
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1054
open _root_.GD.N0232.N0720.N1055
open _root_.GD.N0232.N0720.N1068
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1096
open _root_.GD.N0232.N0720.N1097
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1121
open _root_.GD.N0232.N0720.N1131
open _root_.GD.N0232.N0720.N1109
open _root_.GD.N0232.N0720.N1110
open _root_.GD.N0232.N0720.N1135
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1102
open _root_.GD.N0232.N0720.N1298
open _root_.GD.N0232.N0720.N1288
open _root_.GD.N0232.N0720.N1412

variable {m n : ℕ}





theorem d019336
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    |_root_.GD.N0232.N0720.N1126.d016416
        candidate.packet candidate.weight omega| ≤
      _root_.GD.N0232.N0720.N1298.d018713 candidate := by
  let a : Fin candidate.width → ℝ := fun i ↦
    candidate.weight i * _root_.GD.N0232.N0720.N1126.d016413 candidate.packet i omega
  let M : ℝ := _root_.GD.N0232.N0720.N1298.d018713 candidate
  have ha : ∀ i, 0 ≤ a i := fun i ↦
    mul_nonneg (candidate.weight_nonneg i)
      (_root_.GD.N0232.N0720.N1126.d016419 candidate.packet i omega)
  have hM : 0 ≤ M := _root_.GD.N0232.N0720.N1298.d018714 candidate
  have hlocation : ∀ i, |(candidate.packet i).location| ≤ M :=
    fun i ↦ _root_.GD.N0232.N0720.N1298.d018715 candidate i
  have hsum : 0 ≤ ∑ i, a i :=
    Finset.sum_nonneg fun i _ ↦ ha i
  have hmoment :
      |∑ i, a i * (candidate.packet i).location| ≤ M * ∑ i, a i := by
    calc
      |∑ i, a i * (candidate.packet i).location| ≤
          ∑ i, |a i * (candidate.packet i).location| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, a i * |(candidate.packet i).location| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_nonneg (ha i)]
      _ ≤ ∑ i, a i * M := by
        exact Finset.sum_le_sum fun i hi ↦
          mul_le_mul_of_nonneg_left (hlocation i) (ha i)
      _ = M * ∑ i, a i := by
        rw [← Finset.sum_mul, mul_comm]
  have hmass : 0 < 1 + ∑ i, a i := by linarith
  unfold _root_.GD.N0232.N0720.N1126.d016416 _root_.GD.N0230.N0617.d000166 _root_.GD.N0230.N0617.d000164
    _root_.GD.N0230.N0617.d000163 _root_.GD.N0232.N0720.N1126.d016414
  change |(∑ i, a i * (candidate.packet i).location) /
      (1 + ∑ i, a i)| ≤ M
  rw [abs_div, abs_of_pos hmass]
  apply (div_le_iff₀ hmass).2
  calc
    |∑ i, a i * (candidate.packet i).location| ≤ M * ∑ i, a i :=
      hmoment
    _ ≤ M * (1 + ∑ i, a i) := by
      exact mul_le_mul_of_nonneg_left (by linarith) hM


theorem d019337
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) :
    ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 m n,
      |_root_.GD.N0232.N0720.N1130.d017075 m n candidate omega| ≤
        _root_.GD.N0232.N0720.N1298.d018713 candidate := by
  filter_upwards [_root_.GD.N0232.N0720.N1126.d016427
      candidate.packet candidate.weight candidate.weight_nonneg] with
      omega hcompletion
  rw [show _root_.GD.N0232.N0720.N1130.d017075 m n candidate omega =
      _root_.GD.N0232.N0720.N1126.d016416 candidate.packet candidate.weight omega by
        exact hcompletion]
  exact
    _root_.GD.N0232.N0720.N1451.d019336
      candidate omega





theorem d019338
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hconv : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (candidate j))
      atTop (nhds p))
    (hcharacter : _root_.GD.N0232.N0720.N1159.d014638 m n p) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1298.d018713 (candidate j))
      atTop atTop := by
  refine tendsto_atTop.2 (fun B ↦ ?_)
  have hstrict : ∀ᶠ j in atTop,
      B < _root_.GD.N0232.N0720.N1298.d018713 (candidate j) := by
    by_contra hnot
    have hfrequent : ∃ᶠ j in atTop,
        _root_.GD.N0232.N0720.N1298.d018713 (candidate j) ≤ B := by
      simpa only [not_lt] using (not_eventually.mp hnot)
    obtain ⟨extraction, hextraction, hbound⟩ :=
      extraction_of_frequently_atTop hfrequent
    have hconvSub : Tendsto
        (fun k ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (candidate (extraction k)))
        atTop (nhds p) :=
      hconv.comp hextraction.tendsto_atTop
    obtain ⟨k, hk⟩ :=
      _root_.GD.N0232.N0720.N1055.d017246
        (fun r ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (candidate (extraction r)))
        p hconvSub hcharacter B
    apply hk
    filter_upwards [
      _root_.GD.N0232.N0720.N1451.d019337
        (m := m) (n := n) (candidate (extraction k))] with omega homega
    exact homega.trans (hbound k)
  exact hstrict.mono fun _ hj ↦ hj.le



theorem d019339
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hconv : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (candidate j))
      atTop (nhds p))
    (hrep : _root_.GD.N0232.N0720.N1159.d014652 m n p) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1298.d018713 (candidate j))
      atTop atTop := by
  refine tendsto_atTop.2 (fun B ↦ ?_)
  have hstrict : ∀ᶠ j in atTop,
      B < _root_.GD.N0232.N0720.N1298.d018713 (candidate j) := by
    by_contra hnot
    have hfrequent : ∃ᶠ j in atTop,
        _root_.GD.N0232.N0720.N1298.d018713 (candidate j) ≤ B := by
      simpa only [not_lt] using (not_eventually.mp hnot)
    obtain ⟨extraction, hextraction, hbound⟩ :=
      extraction_of_frequently_atTop hfrequent
    have hconvSub : Tendsto
        (fun k ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (candidate (extraction k)))
        atTop (nhds p) :=
      hconv.comp hextraction.tendsto_atTop
    obtain ⟨k, hk⟩ :=
      _root_.GD.N0232.N0720.N1054.d016448
        (fun r ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (candidate (extraction r)))
        p hconvSub hrep B
    apply hk
    filter_upwards [
      _root_.GD.N0232.N0720.N1451.d019337
        (m := m) (n := n) (candidate (extraction k))] with omega homega
    exact homega.trans (hbound k)
  exact hstrict.mono fun _ hj ↦ hj.le






theorem d019340
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hcalibration : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1131.d017154
        m n (candidate j) s.value) atTop (nhds 0)) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1298.d018713 (candidate j))
      atTop atTop := by
  exact
    _root_.GD.N0232.N0720.N1451.d019338
      candidate s.value
      (_root_.GD.N0232.N0720.N1135.d018336
        s candidate hcalibration)
      s.riskCharacter


theorem d019341
    (c : _root_.GD.N0232.N0720.N1097.d019167 m n)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hcalibration : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1131.d017154
        m n (candidate k) (c.seed k).value) atTop (nhds 0)) :
    Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (candidate k))
      atTop (nhds c.d019178) := by
  have hgap : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (c.seed k))
      atTop (nhds 0) :=
    _root_.GD.N0232.N0720.N1096.d019220 c candidate hcalibration
  have hseedProjection : Tendsto
      (fun k ↦ ‖(c.seed k).value - c.d019172 k‖)
      atTop (nhds 0) := by
    simpa only [_root_.GD.N0232.N0720.N1097.d019167.d019172] using
      _root_.GD.N0232.N0720.N1412.d015646 c.seed hgap
  have hprojectionLimit : Tendsto
      (fun k ↦ ‖c.d019172 k - c.d019178‖) atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp c.d019186
  have hseedLimit : Tendsto (fun k ↦ (c.seed k).value)
      atTop (nhds c.d019178) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    apply squeeze_zero
      (fun k ↦ norm_nonneg ((c.seed k).value - c.d019178))
      (fun k ↦ norm_sub_le_norm_sub_add_norm_sub
        (c.seed k).value (c.d019172 k) c.d019178)
    simpa only [zero_add] using hseedProjection.add hprojectionLimit
  have hcandidateSeedSq : Tendsto
      (fun k ↦ ‖_root_.GD.N0232.N0720.N1130.d017075 m n (candidate k) -
        (c.seed k).value‖ ^ 2) atTop (nhds 0) := by
    exact squeeze_zero
      (fun k ↦ sq_nonneg
        ‖_root_.GD.N0232.N0720.N1130.d017075 m n (candidate k) - (c.seed k).value‖)
      (fun k ↦
        _root_.GD.N0232.N0720.N1121.d018304
          m n (candidate k) (c.seed k).value (c.seed k).finiteRisk)
      hcalibration
  have hcandidateSeed : Tendsto
      (fun k ↦ ‖_root_.GD.N0232.N0720.N1130.d017075 m n (candidate k) -
        (c.seed k).value‖) atTop (nhds 0) := by
    have hsqrt := hcandidateSeedSq.sqrt
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt
  have hseedLimitNorm : Tendsto
      (fun k ↦ ‖(c.seed k).value - c.d019178‖) atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hseedLimit
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero
    (fun k ↦ norm_nonneg
      (_root_.GD.N0232.N0720.N1130.d017075 m n (candidate k) - c.d019178))
    (fun k ↦ norm_sub_le_norm_sub_add_norm_sub
      (_root_.GD.N0232.N0720.N1130.d017075 m n (candidate k)) (c.seed k).value c.d019178)
  simpa only [zero_add] using hcandidateSeed.add hseedLimitNorm





theorem d019342
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1097.d019167 m n)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hcalibration : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1131.d017154
        m n (candidate k) (c.seed k).value) atTop (nhds 0)) :
    Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1298.d018713 (candidate k))
      atTop atTop := by
  have hgap : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (c.seed k))
      atTop (nhds 0) :=
    _root_.GD.N0232.N0720.N1096.d019220 c candidate hcalibration
  have hseedProjection : Tendsto
      (fun k ↦ ‖(c.seed k).value - c.d019172 k‖)
      atTop (nhds 0) := by
    simpa only [_root_.GD.N0232.N0720.N1097.d019167.d019172] using
      _root_.GD.N0232.N0720.N1412.d015646 c.seed hgap
  have hprojectionLimit : Tendsto
      (fun k ↦ ‖c.d019172 k - c.d019178‖) atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp c.d019186
  have hseedLimit : Tendsto (fun k ↦ (c.seed k).value)
      atTop (nhds c.d019178) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    apply squeeze_zero
      (fun k ↦ norm_nonneg ((c.seed k).value - c.d019178))
      (fun k ↦ norm_sub_le_norm_sub_add_norm_sub
        (c.seed k).value (c.d019172 k) c.d019178)
    simpa only [zero_add] using hseedProjection.add hprojectionLimit
  have hrep : _root_.GD.N0232.N0720.N1159.d014652 m n c.d019178 :=
    _root_.GD.N0232.N0720.N1412.d015651
      hm hn c.seed c.d019178 hseedLimit hgap c.d019181
  exact _root_.GD.N0232.N0720.N1451.d019339
    candidate c.d019178
      (_root_.GD.N0232.N0720.N1451.d019341
        c candidate hcalibration)
      hrep










theorem d019343
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hd : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value d) :
    ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate - d‖ ^ 2 ≤
      9 * _root_.GD.N0232.N0720.N1131.d017154
        m n candidate s.value := by
  let P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  let T : ℝ := _root_.GD.N0232.N0720.N1131.d017154 m n candidate s.value
  have hcompletionSeed :
      ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate - s.value‖ ^ 2 ≤ T := by
    exact
      _root_.GD.N0232.N0720.N1121.d018304
        m n candidate s.value s.finiteRisk
  have hgap : _root_.GD.N0232.N0720.N1201.d015333 m n s ≤ T :=
    _root_.GD.N0232.N0720.N1135.d018316 s candidate
  have hseedProjection : ‖s.value - P‖ ^ 2 ≤ T := by
    exact (_root_.GD.N0232.N0720.N1288.d015626 m n s).trans hgap
  have hdescendantProjection : ‖d - P‖ ^ 2 ≤ T := by
    exact
      (_root_.GD.N0232.N0720.N1102.d015429
        m n s d hd).trans hgap
  have htri :
      ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate - d‖ ≤
        ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate - s.value‖ +
          ‖s.value - P‖ + ‖P - d‖ := by
    have hsplit : _root_.GD.N0232.N0720.N1130.d017075 m n candidate - d =
        (_root_.GD.N0232.N0720.N1130.d017075 m n candidate - s.value) +
          (s.value - P) + (P - d) := by
      abel
    rw [hsplit]
    exact norm_add₃_le
  have hprojectionDescendant : ‖P - d‖ ^ 2 ≤ T := by
    simpa only [norm_sub_rev] using hdescendantProjection
  have hsumSq :
      (‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate - s.value‖ +
          ‖s.value - P‖ + ‖P - d‖) ^ 2 ≤ 9 * T := by
    nlinarith [
      sq_nonneg
        (‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate - s.value‖ -
          ‖s.value - P‖),
      sq_nonneg
        (‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate - s.value‖ - ‖P - d‖),
      sq_nonneg (‖s.value - P‖ - ‖P - d‖)]
  nlinarith [norm_nonneg (_root_.GD.N0232.N0720.N1130.d017075 m n candidate - d),
    norm_nonneg (_root_.GD.N0232.N0720.N1130.d017075 m n candidate - s.value),
    norm_nonneg (s.value - P), norm_nonneg (P - d)]



theorem d019344
    {I : Type*}
    (seed : I → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hbelow : ∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d)
    (index : ℕ → I)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hcalibration : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1131.d017154
        m n (candidate k) (seed (index k)).value)
      atTop (nhds 0)) :
    Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (candidate k))
      atTop (nhds d) := by
  have hsq : Tendsto
      (fun k ↦ ‖_root_.GD.N0232.N0720.N1130.d017075 m n (candidate k) - d‖ ^ 2)
      atTop (nhds 0) := by
    have hupper := hcalibration.const_mul 9
    rw [mul_zero] at hupper
    exact squeeze_zero
      (fun k ↦ sq_nonneg ‖_root_.GD.N0232.N0720.N1130.d017075 m n (candidate k) - d‖)
      (fun k ↦
        _root_.GD.N0232.N0720.N1451.d019343
          (seed (index k)) (candidate k) d (hbelow (index k)))
      hupper
  have hnorm : Tendsto
      (fun k ↦ ‖_root_.GD.N0232.N0720.N1130.d017075 m n (candidate k) - d‖)
      atTop (nhds 0) := by
    have hsqrt := hsq.sqrt
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt
  exact tendsto_iff_norm_sub_tendsto_zero.2 hnorm







theorem d019345
    {I : Type*}
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : I → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hbelow : ∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d)
    (hsmall : _root_.GD.N0232.N0720.N1109.d018402 seed)
    (B : ℝ) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ (i : I) (candidate : _root_.GD.N0232.N0720.N1130.d017074),
        _root_.GD.N0232.N0720.N1298.d018713 candidate ≤ B →
          epsilon ≤ _root_.GD.N0232.N0720.N1131.d017154
            m n candidate (seed i).value := by
  have hgapSmall : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ i, _root_.GD.N0232.N0720.N1201.d015333 m n (seed i) < epsilon := by
    intro epsilon hepsilon
    obtain ⟨i, candidate, htax⟩ := hsmall epsilon hepsilon
    exact ⟨i, lt_of_le_of_lt
      (_root_.GD.N0232.N0720.N1135.d018316
        (seed i) candidate) htax⟩
  have hrep : _root_.GD.N0232.N0720.N1159.d014652 m n d :=
    (_root_.GD.N0232.N0720.N1102.d015432
      m n hm hn seed d hgapSmall hbelow).2
  by_contra hfloor
  push Not at hfloor
  have hchoose : ∀ k : ℕ,
      ∃ (i : I) (candidate : _root_.GD.N0232.N0720.N1130.d017074),
        _root_.GD.N0232.N0720.N1298.d018713 candidate ≤ B ∧
          _root_.GD.N0232.N0720.N1131.d017154
            m n candidate (seed i).value < 1 / ((k : ℝ) + 1) := by
    intro k
    exact hfloor (1 / ((k : ℝ) + 1)) (by positivity)
  choose index candidate hbound htax using hchoose
  have hcalibration : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1131.d017154
        m n (candidate k) (seed (index k)).value)
      atTop (nhds 0) := by
    exact squeeze_zero
      (fun k ↦ _root_.GD.N0232.N0720.N1131.d017156
        m n (candidate k) (seed (index k)).value)
      (fun k ↦ (htax k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hconv : Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (candidate k))
      atTop (nhds d) :=
    _root_.GD.N0232.N0720.N1451.d019344
      seed d hbelow index candidate hcalibration
  have hescape :=
    _root_.GD.N0232.N0720.N1451.d019339
      candidate d hconv hrep
  have heventual : ∀ᶠ k in atTop,
      B + 1 ≤ _root_.GD.N0232.N0720.N1298.d018713 (candidate k) :=
    (tendsto_atTop.1 hescape) (B + 1)
  obtain ⟨k, hk⟩ := heventual.exists
  linarith [hbound k]



theorem d019346
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hfinite : _root_.GD.N0232.N0720.N1110.d015460 m n seed)
    (hsmall : _root_.GD.N0232.N0720.N1109.d018402 seed)
    (B : ℝ) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ (i : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074),
        _root_.GD.N0232.N0720.N1298.d018713 candidate ≤ B →
          epsilon ≤ _root_.GD.N0232.N0720.N1131.d017154
            m n candidate (seed i).value := by
  obtain ⟨d, hbelow⟩ :=
    _root_.GD.N0232.N0720.N1110.d015462
      m n seed hfinite
  exact
    _root_.GD.N0232.N0720.N1451.d019345
      hm hn seed d hbelow hsmall B




theorem d019347
    {I : Type*}
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : I → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hbelow : ∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d)
    (hsmall : _root_.GD.N0232.N0720.N1109.d018402 seed)
    (B epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ (i : I) (candidate : _root_.GD.N0232.N0720.N1130.d017074),
      B < _root_.GD.N0232.N0720.N1298.d018713 candidate ∧
        _root_.GD.N0232.N0720.N1131.d017154
          m n candidate (seed i).value < epsilon := by
  obtain ⟨eta, heta, hfloor⟩ :=
    _root_.GD.N0232.N0720.N1451.d019345
      hm hn seed d hbelow hsmall B
  let delta : ℝ := min epsilon eta
  have hdelta : 0 < delta := by
    exact lt_min hepsilon heta
  obtain ⟨i, candidate, htax⟩ := hsmall delta hdelta
  refine ⟨i, candidate, ?_, htax.trans_le (min_le_left epsilon eta)⟩
  by_contra hnot
  have hbounded : _root_.GD.N0232.N0720.N1298.d018713 candidate ≤ B :=
    le_of_not_gt hnot
  have hlower := hfloor i candidate hbounded
  have hdeltaEta : delta ≤ eta := min_le_right epsilon eta
  linarith






theorem d019348
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1097.d019167 m n)
    (hsmall : _root_.GD.N0232.N0720.N1096.d019226 c)
    (B : ℝ) :
    ∃ (_k : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074),
      B < _root_.GD.N0232.N0720.N1298.d018713 candidate := by
  have hfamily : _root_.GD.N0232.N0720.N1109.d018402 c.seed := by
    exact hsmall
  have hbelow : ∀ k, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (c.seed k).value c.d019178 := by
    intro k
    exact c.d019180 k
  obtain ⟨epsilon, hepsilon, hfloor⟩ :=
    _root_.GD.N0232.N0720.N1451.d019345
      hm hn c.seed c.d019178 hbelow hfamily B
  obtain ⟨k, candidate, htax⟩ := hsmall epsilon hepsilon
  refine ⟨k, candidate, ?_⟩
  by_contra hnot
  exact (not_lt_of_ge (hfloor k candidate (le_of_not_gt hnot))) htax


theorem d019349
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (c : _root_.GD.N0232.N0720.N1097.d019167 m n)
    (hsmall : _root_.GD.N0232.N0720.N1096.d019226 c)
    (B epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ (k : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074),
      B < _root_.GD.N0232.N0720.N1298.d018713 candidate ∧
        _root_.GD.N0232.N0720.N1131.d017154
          m n candidate (c.seed k).value < epsilon := by
  exact
    _root_.GD.N0232.N0720.N1451.d019347
      hm hn c.seed c.d019178 (fun k ↦ c.d019180 k) hsmall
      B epsilon hepsilon

end

end N1451
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1451.d019336
#print axioms _root_.GD.N0232.N0720.N1451.d019340
#print axioms _root_.GD.N0232.N0720.N1451.d019341
#print axioms _root_.GD.N0232.N0720.N1451.d019342
#print axioms _root_.GD.N0232.N0720.N1451.d019343
#print axioms _root_.GD.N0232.N0720.N1451.d019346
#print axioms _root_.GD.N0232.N0720.N1451.d019348
#print axioms _root_.GD.N0232.N0720.N1451.d019349
