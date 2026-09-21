import GD.Module1065








































open Filter MeasureTheory
open scoped ENNReal BigOperators InnerProductSpace RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1131

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0617
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159




def d017153
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ :=
  ∑ i, candidate.weight i *
    ((_root_.GD.N0232.N0720.N1080.d014182 m n (candidate.packet i) s.value).toReal -
      (_root_.GD.N0232.N0720.N1080.d014182 m n (candidate.packet i) q).toReal)




def d017154
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ :=
  ∫ omega, _root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega *
    (q omega -
      _root_.GD.N0232.N0720.N1126.d016416 candidate.packet candidate.weight omega) ^ 2
      ∂_root_.GD.N0232.N0720.N1080.d014172 m n

theorem d017155
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    0 ≤ _root_.GD.N0232.N0720.N1131.d017153 m n s candidate q := by
  unfold _root_.GD.N0232.N0720.N1131.d017153
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg (candidate.weight_nonneg i)
  apply sub_nonneg.mpr
  exact ENNReal.toReal_mono (s.finiteRisk (candidate.packet i))
    (hq (candidate.packet i))

theorem d017156
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    0 ≤ _root_.GD.N0232.N0720.N1131.d017154 m n candidate q := by
  unfold _root_.GD.N0232.N0720.N1131.d017154
  apply integral_nonneg
  intro omega
  exact mul_nonneg
    (le_trans zero_le_one
      (_root_.GD.N0230.N0617.d000168 candidate.weight
        (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet) candidate.weight_nonneg
        (_root_.GD.N0232.N0720.N1126.d016419 candidate.packet) omega))
    (sq_nonneg _)




theorem d017157
    (m n : ℕ) (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate - q‖ ^ 2 =
      ∫ omega,
        (q omega -
          _root_.GD.N0232.N0720.N1126.d016416
            candidate.packet candidate.weight omega) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  unfold _root_.GD.N0232.N0720.N1130.d017075
  rw [norm_sub_rev]
  rw [← real_inner_self_eq_norm_sq
    (q - _root_.GD.N0232.N0720.N1126.d016426
      candidate.packet candidate.weight candidate.weight_nonneg), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    Lp.coeFn_sub q (_root_.GD.N0232.N0720.N1126.d016426
      candidate.packet candidate.weight candidate.weight_nonneg),
    _root_.GD.N0232.N0720.N1126.d016427
      candidate.packet candidate.weight candidate.weight_nonneg] with
      omega hsub hcompletion
  rw [hsub, Pi.sub_apply, hcompletion]
  simp only [RCLike.inner_apply, conj_trivial, pow_two]





theorem d017158
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate - q‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1131.d017154 m n candidate q := by
  have hqFinite : _root_.GD.N0232.N0720.N1159.d014637 m n q :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s q hq
  have hweighted : Integrable
      (fun omega ↦
        _root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega *
          (q omega - _root_.GD.N0232.N0720.N1126.d016416
            candidate.packet candidate.weight omega) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    exact _root_.GD.N0230.N0617.d000185
      (_root_.GD.N0232.N0720.N1080.d014172 m n) candidate.weight
      (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet) (_root_.GD.N0232.N0720.N1126.d016414 candidate.packet)
      (fun omega ↦ q omega) candidate.weight_nonneg
      (_root_.GD.N0232.N0720.N1126.d016419 candidate.packet)
      (_root_.GD.N0232.N0720.N1126.d016420 candidate.packet)
      (_root_.GD.N0232.N0720.N1126.d016421 candidate.packet)
      (Lp.memLp q).integrable_sq
      (fun i ↦ _root_.GD.N0232.N0720.N1126.d016429
        (candidate.packet i) q (hqFinite (candidate.packet i)))
  have hplain : Integrable
      (fun omega ↦
        (q omega - _root_.GD.N0232.N0720.N1126.d016416
          candidate.packet candidate.weight omega) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    apply Integrable.mono' hweighted
    · exact ((Lp.aestronglyMeasurable q).aemeasurable.sub
        (_root_.GD.N0232.N0720.N1126.d016423
          candidate.packet candidate.weight).aemeasurable).pow_const 2
          |>.aestronglyMeasurable
    · filter_upwards with omega
      have hsq : 0 ≤
          (q omega - _root_.GD.N0232.N0720.N1126.d016416
            candidate.packet candidate.weight omega) ^ 2 := sq_nonneg _
      have hmass := _root_.GD.N0230.N0617.d000168 candidate.weight
        (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet) candidate.weight_nonneg
        (_root_.GD.N0232.N0720.N1126.d016419 candidate.packet) omega
      rw [Real.norm_eq_abs, abs_of_nonneg hsq]
      simpa only [one_mul, _root_.GD.N0232.N0720.N1126.d016415] using
        (mul_le_mul_of_nonneg_right hmass hsq)
  have hmono :
      (∫ omega,
        (q omega - _root_.GD.N0232.N0720.N1126.d016416
          candidate.packet candidate.weight omega) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n) ≤
      ∫ omega,
        _root_.GD.N0232.N0720.N1126.d016415 candidate.packet candidate.weight omega *
          (q omega - _root_.GD.N0232.N0720.N1126.d016416
            candidate.packet candidate.weight omega) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    apply integral_mono hplain hweighted
    intro omega
    have hsq : 0 ≤
        (q omega - _root_.GD.N0232.N0720.N1126.d016416
          candidate.packet candidate.weight omega) ^ 2 := sq_nonneg _
    have hmass := _root_.GD.N0230.N0617.d000168 candidate.weight
      (_root_.GD.N0232.N0720.N1126.d016413 candidate.packet) candidate.weight_nonneg
      (_root_.GD.N0232.N0720.N1126.d016419 candidate.packet) omega
    simpa only [one_mul, _root_.GD.N0232.N0720.N1126.d016415] using
      (mul_le_mul_of_nonneg_right hmass hsq)
  rw [_root_.GD.N0232.N0720.N1131.d017157]
  simpa only [_root_.GD.N0232.N0720.N1131.d017154] using hmono





theorem d017159
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    ‖q‖ ^ 2 - _root_.GD.N0232.N0720.N1126.d016432 s candidate.packet candidate.weight =
      _root_.GD.N0232.N0720.N1131.d017154 m n candidate q +
        _root_.GD.N0232.N0720.N1131.d017153 m n s candidate q := by
  have hexact :=
    _root_.GD.N0232.N0720.N1126.d016435
      s candidate.packet candidate.weight candidate.weight_nonneg q hq
  unfold _root_.GD.N0232.N0720.N1131.d017154
    _root_.GD.N0232.N0720.N1131.d017153
  linarith


theorem d017160
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s candidate.packet candidate.weight =
      (‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate‖ ^ 2 - ‖q‖ ^ 2) +
        _root_.GD.N0232.N0720.N1131.d017154 m n candidate q +
          _root_.GD.N0232.N0720.N1131.d017153 m n s candidate q := by
  have hexact := _root_.GD.N0232.N0720.N1131.d017159
    m n s candidate q hq
  linarith



theorem d017161
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    ‖q‖ ≤ ‖s.value‖ := by
  have href := hq _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
  simp only [zero_sub, norm_neg] at href
  have hsq : ‖q‖ ^ 2 ≤ ‖s.value‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖s.value‖)).mp href
  nlinarith [norm_nonneg q, norm_nonneg s.value]



theorem d017162
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    |‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate‖ ^ 2 - ‖q‖ ^ 2| ≤
      ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate - q‖ *
        (2 * ‖s.value‖ + ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate - q‖) := by
  let r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1130.d017075 m n candidate
  let d : ℝ := ‖r - q‖
  have hqnorm : ‖q‖ ≤ ‖s.value‖ :=
    _root_.GD.N0232.N0720.N1131.d017161 m n s q hq
  have hrnorm : ‖r‖ ≤ ‖q‖ + d := by
    calc
      ‖r‖ = ‖q + (r - q)‖ := by congr 1; abel
      _ ≤ ‖q‖ + ‖r - q‖ := norm_add_le _ _
      _ = ‖q‖ + d := rfl
  have hsum : ‖r‖ + ‖q‖ ≤ 2 * ‖s.value‖ + d := by
    linarith
  have hdiff : |‖r‖ - ‖q‖| ≤ d := by
    simpa only [d] using abs_norm_sub_norm_le r q
  calc
    |‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate‖ ^ 2 - ‖q‖ ^ 2| =
        |‖r‖ - ‖q‖| * (‖r‖ + ‖q‖) := by
          change |‖r‖ ^ 2 - ‖q‖ ^ 2| = _
          rw [show ‖r‖ ^ 2 - ‖q‖ ^ 2 =
            (‖r‖ - ‖q‖) * (‖r‖ + ‖q‖) by ring,
            abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg r) (norm_nonneg q))]
    _ ≤ d * (‖r‖ + ‖q‖) :=
      mul_le_mul_of_nonneg_right hdiff
        (add_nonneg (norm_nonneg r) (norm_nonneg q))
    _ ≤ d * (2 * ‖s.value‖ + d) :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg (r - q))
    _ = ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate - q‖ *
        (2 * ‖s.value‖ + ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate - q‖) := rfl













def d017163
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ :=
  _root_.GD.N0232.N0720.N1131.d017154 m n candidate q +
    _root_.GD.N0232.N0720.N1131.d017153 m n s candidate q +
    _root_.GD.N0232.N0720.N1130.d017078 m n candidate +
    _root_.GD.N0232.N0720.N1130.d017079 m n candidate



def d017164
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ :=
  ‖_root_.GD.N0232.N0720.N1130.d017075 m n candidate - q‖ +
    _root_.GD.N0232.N0720.N1131.d017163 m n s candidate q

theorem d017165
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0232.N0720.N1131.d017163 m n s candidate q ≤
      _root_.GD.N0232.N0720.N1131.d017164
        m n s candidate q := by
  unfold _root_.GD.N0232.N0720.N1131.d017164
  linarith [norm_nonneg (_root_.GD.N0232.N0720.N1130.d017075 m n candidate - q)]

theorem d017166
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value) :
    0 ≤ _root_.GD.N0232.N0720.N1131.d017163 m n s candidate q := by
  unfold _root_.GD.N0232.N0720.N1131.d017163
  linarith [_root_.GD.N0232.N0720.N1131.d017156 m n candidate q,
    _root_.GD.N0232.N0720.N1131.d017155 m n s candidate q hq,
    _root_.GD.N0232.N0720.N1130.d017083 m n candidate,
    _root_.GD.N0232.N0720.N1130.d017084 m n candidate]




theorem d017167
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (q : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : ∀ j, q j ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (hdefect : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1131.d017163
        m n s (candidate j) (q j)) atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  let d : ℕ → ℝ := fun j ↦
    ‖_root_.GD.N0232.N0720.N1130.d017075 m n (candidate j) - q j‖
  let weighted : ℕ → ℝ := fun j ↦
    _root_.GD.N0232.N0720.N1131.d017154 m n (candidate j) (q j)
  let complementarity : ℕ → ℝ := fun j ↦
    _root_.GD.N0232.N0720.N1131.d017153 m n s (candidate j) (q j)
  have hweighted : Tendsto weighted atTop (nhds 0) := by
    apply squeeze_zero
      (fun j ↦ _root_.GD.N0232.N0720.N1131.d017156
        m n (candidate j) (q j))
      (fun j ↦ ?_) hdefect
    unfold _root_.GD.N0232.N0720.N1131.d017163
    linarith [_root_.GD.N0232.N0720.N1131.d017155
        m n s (candidate j) (q j) (hq j),
      _root_.GD.N0232.N0720.N1130.d017083 m n (candidate j),
      _root_.GD.N0232.N0720.N1130.d017084 m n (candidate j)]
  have hdSq : Tendsto (fun j ↦ (d j) ^ 2) atTop (nhds 0) := by
    apply squeeze_zero (fun j ↦ sq_nonneg (d j))
      (fun j ↦ ?_) hweighted
    simpa only [d, weighted] using
      _root_.GD.N0232.N0720.N1131.d017158
        m n s (candidate j) (q j) (hq j)
  have hd : Tendsto d atTop (nhds 0) := by
    have hsqrt := hdSq.sqrt
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero, d] using hsqrt
  have hcomplementarity : Tendsto complementarity atTop (nhds 0) := by
    apply squeeze_zero
      (fun j ↦ _root_.GD.N0232.N0720.N1131.d017155
        m n s (candidate j) (q j) (hq j))
      (fun j ↦ ?_) hdefect
    unfold _root_.GD.N0232.N0720.N1131.d017163
    linarith [_root_.GD.N0232.N0720.N1131.d017156
        m n (candidate j) (q j),
      _root_.GD.N0232.N0720.N1130.d017083 m n (candidate j),
      _root_.GD.N0232.N0720.N1130.d017084 m n (candidate j)]
  have htwo : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017078 m n (candidate j))
      atTop (nhds 0) := by
    apply squeeze_zero
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017083 m n (candidate j))
      (fun j ↦ ?_) hdefect
    unfold _root_.GD.N0232.N0720.N1131.d017163
    linarith [_root_.GD.N0232.N0720.N1131.d017156
        m n (candidate j) (q j),
      _root_.GD.N0232.N0720.N1131.d017155
        m n s (candidate j) (q j) (hq j),
      _root_.GD.N0232.N0720.N1130.d017084 m n (candidate j)]
  have hthree : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017079 m n (candidate j))
      atTop (nhds 0) := by
    apply squeeze_zero
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017084 m n (candidate j))
      (fun j ↦ ?_) hdefect
    unfold _root_.GD.N0232.N0720.N1131.d017163
    linarith [_root_.GD.N0232.N0720.N1131.d017156
        m n (candidate j) (q j),
      _root_.GD.N0232.N0720.N1131.d017155
        m n s (candidate j) (q j) (hq j),
      _root_.GD.N0232.N0720.N1130.d017083 m n (candidate j)]
  have houter : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017076 m n s (candidate j))
      atTop (nhds 0) := by
    apply squeeze_zero
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017081 m n s (candidate j))
      (fun j ↦ ?_) hd
    simpa only [_root_.GD.N0232.N0720.N1130.d017076, _root_.GD.N0232.N0720.N1130.d017075, d,
      dist_eq_norm] using
      (Metric.infDist_le_dist_of_mem (hq j))
  have hnormGapAbs : Tendsto
      (fun j ↦
        |‖_root_.GD.N0232.N0720.N1130.d017075 m n (candidate j)‖ ^ 2 - ‖q j‖ ^ 2|)
      atTop (nhds 0) := by
    have hgeom : Tendsto
        (fun j ↦ d j * (2 * ‖s.value‖ + d j))
        atTop (nhds 0) := by
      have hright : Tendsto (fun j ↦ 2 * ‖s.value‖ + d j)
          atTop (nhds (2 * ‖s.value‖)) := by
        simpa only [add_zero] using
          (tendsto_const_nhds.add hd)
      have hproduct := hd.mul hright
      simpa only [zero_mul] using hproduct
    apply squeeze_zero (fun j ↦ abs_nonneg _)
      (fun j ↦ ?_) hgeom
    simpa only [d] using
      _root_.GD.N0232.N0720.N1131.d017162
        m n s (candidate j) (q j) (hq j)
  have hnormGap : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1130.d017075 m n (candidate j)‖ ^ 2 - ‖q j‖ ^ 2)
      atTop (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 hnormGapAbs
  have hradial : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017077 m n s (candidate j))
      atTop (nhds 0) := by
    have hgap : Tendsto
        (fun j ↦
          (‖_root_.GD.N0232.N0720.N1130.d017075 m n (candidate j)‖ ^ 2 - ‖q j‖ ^ 2) +
            weighted j + complementarity j)
        atTop (nhds 0) := by
      simpa only [zero_add, add_zero] using
        ((hnormGap.add hweighted).add hcomplementarity)
    have hgap' : Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1130.d017075 m n (candidate j)‖ ^ 2 -
            _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight)
        atTop (nhds 0) := by
      apply hgap.congr'
      filter_upwards with j
      exact (_root_.GD.N0232.N0720.N1131.d017160
        m n s (candidate j) (q j) (hq j)).symm
    have hpositive : Tendsto
        (fun j ↦ max
          (‖_root_.GD.N0232.N0720.N1130.d017075 m n (candidate j)‖ ^ 2 -
            _root_.GD.N0232.N0720.N1126.d016432 s (candidate j).packet (candidate j).weight)
          0) atTop (nhds 0) := by
      have hzero : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds
      simpa only [max_self] using hgap'.max hzero
    simpa only [_root_.GD.N0232.N0720.N1130.d017077] using hpositive
  have hcandidateDefect : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017080 m n s (candidate j))
      atTop (nhds 0) := by
    simpa only [_root_.GD.N0232.N0720.N1130.d017080, zero_add, add_zero] using
      (((houter.add hradial).add htwo).add hthree)
  exact
    _root_.GD.N0232.N0720.N1130.d017090
      m n hm hn s hstrict candidate hcandidateDefect






def d017168
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ (candidate : _root_.GD.N0232.N0720.N1130.d017074)
      (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)),
      q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value ∧
        _root_.GD.N0232.N0720.N1131.d017163
          m n s candidate q < epsilon



theorem d017169
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hsmall : _root_.GD.N0232.N0720.N1131.d017168 m n s) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  have hchoose : ∀ j : ℕ,
      ∃ (candidate : _root_.GD.N0232.N0720.N1130.d017074)
        (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)),
        q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value ∧
          _root_.GD.N0232.N0720.N1131.d017163 m n s candidate q <
            1 / ((j : ℝ) + 1) := by
    intro j
    exact hsmall (1 / ((j : ℝ) + 1)) (by positivity)
  choose candidate q hq hbound using hchoose
  have hdefect : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1131.d017163
        m n s (candidate j) (q j)) atTop (nhds 0) := by
    exact squeeze_zero
      (fun j ↦ _root_.GD.N0232.N0720.N1131.d017166
        m n s (candidate j) (q j) (hq j))
      (fun j ↦ (hbound j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  exact _root_.GD.N0232.N0720.N1131.d017167
    m n hm hn s hstrict candidate q hq hdefect





theorem d017170
    (m n : ℕ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    ¬ _root_.GD.N0232.N0720.N1131.d017168 m n s ↔
      ∃ eta : ℝ, 0 < eta ∧
        ∀ (candidate : _root_.GD.N0232.N0720.N1130.d017074)
          (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)),
          q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value →
            eta ≤ _root_.GD.N0232.N0720.N1131.d017163
              m n s candidate q := by
  classical
  constructor
  · intro hnot
    by_contra hfloor
    apply hnot
    intro epsilon hepsilon
    by_contra hsmall
    apply hfloor
    refine ⟨epsilon, hepsilon, ?_⟩
    intro candidate q hq
    exact le_of_not_gt fun hlt ↦ hsmall ⟨candidate, q, hq, hlt⟩
  · rintro ⟨eta, heta, hfloor⟩ hsmall
    obtain ⟨candidate, q, hq, hlt⟩ := hsmall eta heta
    exact (not_lt_of_ge (hfloor candidate q hq)) hlt




theorem d017171
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hno : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ (candidate : _root_.GD.N0232.N0720.N1130.d017074)
        (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)),
        q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value →
          eta ≤ _root_.GD.N0232.N0720.N1131.d017163
            m n s candidate q := by
  apply (_root_.GD.N0232.N0720.N1131.d017170
    m n s).1
  intro hsmall
  exact hno
    (_root_.GD.N0232.N0720.N1131.d017169
      m n hm hn s hstrict hsmall)

end
end N1131
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1131.d017159
#print axioms _root_.GD.N0232.N0720.N1131.d017160
#print axioms _root_.GD.N0232.N0720.N1131.d017167
#print axioms _root_.GD.N0232.N0720.N1131.d017169
#print axioms _root_.GD.N0232.N0720.N1131.d017170
#print axioms _root_.GD.N0232.N0720.N1131.d017171
