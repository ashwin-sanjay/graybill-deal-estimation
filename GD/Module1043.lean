import GD.Module1037
import GD.Module0965
import GD.Module1042



































open Filter MeasureTheory
open scoped BigOperators ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1163

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0617
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1127
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1162
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0232.N0720.N1499

abbrev d016630 :=
  _root_.GD.N0232.N0719.N0946.d009229

variable {m n : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

private noncomputable local instance d016631 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance





theorem d016632
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ i, 0 ≤ _root_.GD.N0232.N0720.N1162.d016619 t weight i := by
  intro i
  exact mul_nonneg ht (hweight i)




theorem d016633
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hpositive : ∃ i, 0 < weight i)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    0 < _root_.GD.N0232.N0720.N1162.d016620 packet weight omega := by
  unfold _root_.GD.N0232.N0720.N1162.d016620
  apply Finset.sum_pos'
  · intro i hi
    exact mul_nonneg (hweight i)
      (_root_.GD.N0232.N0720.N1126.d016419 packet i omega)
  · obtain ⟨i, hi⟩ := hpositive
    exact ⟨i, Finset.mem_univ i,
      mul_pos hi (_root_.GD.N0232.N0720.N1499.d015005 m n (packet i) omega)⟩




def d016634
    (g : _root_.GD.N0232.N0720.N1163.d016630) (j : ℕ)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) :
    _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  fun omega ↦
    _root_.GD.N0232.N0720.N1126.d016416
        (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))
        (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight) omega -
      _root_.GD.N0232.N0720.N1214.d014261 m n g
        (_root_.GD.N0232.N0720.N1126.d016416 packet
          (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)) omega

theorem d016635
    (g : _root_.GD.N0232.N0720.N1163.d016630) (j : ℕ)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1163.d016634
      (m := m) (n := n) g j packet weight) := by
  unfold _root_.GD.N0232.N0720.N1163.d016634
  exact
    (_root_.GD.N0232.N0720.N1126.d016423
      (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))
      (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)).sub
    (_root_.GD.N0232.N0720.N1214.d014262 m n g
      (_root_.GD.N0232.N0720.N1126.d016416 packet
        (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight))
      (_root_.GD.N0232.N0720.N1126.d016423 packet
        (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)))



theorem d016636
    (g : _root_.GD.N0232.N0720.N1163.d016630) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hpositive : ∃ i, 0 < weight i)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    Tendsto
      (fun j : ℕ ↦ _root_.GD.N0232.N0720.N1163.d016634
        (m := m) (n := n) g j packet weight omega)
      atTop (nhds 0) := by
  have hmass : 0 < _root_.GD.N0232.N0720.N1162.d016620 packet weight
      (_root_.GD.N0232.N0720.N1484.d015094 m n g omega) :=
    _root_.GD.N0232.N0720.N1163.d016633
      packet weight hweight hpositive _
  have hpoint :=
    _root_.GD.N0232.N0720.N1162.d016629
      g packet weight (_root_.GD.N0232.N0720.N1484.d015094 m n g omega) hmass
  have hnat := hpoint.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards with j
  simp only [Function.comp_apply, _root_.GD.N0232.N0720.N1163.d016634, _root_.GD.N0232.N0720.N1484.d015094,
    _root_.GD.N0232.N0720.N1214.d014261, smul_inv_smul]





def d016637
    (g : _root_.GD.N0232.N0720.N1163.d016630) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  _root_.GD.N0232.N0720.N1126.d016418 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)) +
    |g.shift| + g.d009239 * _root_.GD.N0232.N0720.N1126.d016418 packet

theorem d016638
    (g : _root_.GD.N0232.N0720.N1163.d016630) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) :
    0 ≤ _root_.GD.N0232.N0720.N1163.d016637 g packet := by
  unfold _root_.GD.N0232.N0720.N1163.d016637
  exact add_nonneg
    (add_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    (mul_nonneg g.d009240.le (Real.sqrt_nonneg _))


theorem d016639
    (g : _root_.GD.N0232.N0720.N1163.d016630) (j : ℕ)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    |_root_.GD.N0232.N0720.N1163.d016634
        (m := m) (n := n) g j packet weight omega| ≤
      _root_.GD.N0232.N0720.N1163.d016637 g packet := by
  have hscaled : ∀ i, 0 ≤ _root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight i :=
    _root_.GD.N0232.N0720.N1163.d016632 weight hweight (Nat.cast_nonneg j)
  have hleft := _root_.GD.N0232.N0720.N1126.d016424
    (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))
    (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight) hscaled omega
  have horiginal := _root_.GD.N0232.N0720.N1126.d016424
    packet (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight) hscaled
      (_root_.GD.N0232.N0720.N1484.d015094 m n g omega)
  have htransport :
      |_root_.GD.N0232.N0720.N1214.d014261 m n g
          (_root_.GD.N0232.N0720.N1126.d016416 packet
            (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)) omega| ≤
        |g.shift| + g.d009239 * _root_.GD.N0232.N0720.N1126.d016418 packet := by
    unfold _root_.GD.N0232.N0720.N1214.d014261
    rw [_root_.GD.N0232.N0719.N0946.d009229.d009244]
    calc
      |g.shift + g.d009239 *
          _root_.GD.N0232.N0720.N1126.d016416 packet
            (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
            (g⁻¹ • omega)| ≤
          |g.shift| +
            |g.d009239 *
              _root_.GD.N0232.N0720.N1126.d016416 packet
                (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
                (g⁻¹ • omega)| := abs_add_le _ _
      _ = |g.shift| + g.d009239 *
            |_root_.GD.N0232.N0720.N1126.d016416 packet
              (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
              (g⁻¹ • omega)| := by
          rw [abs_mul, abs_of_pos g.d009240]
      _ ≤ |g.shift| + g.d009239 * _root_.GD.N0232.N0720.N1126.d016418 packet := by
          exact add_le_add_right
            (mul_le_mul_of_nonneg_left horiginal g.d009240.le)
            |g.shift|
  unfold _root_.GD.N0232.N0720.N1163.d016634 _root_.GD.N0232.N0720.N1163.d016637
  calc
    |_ - _| ≤ _ + _ := abs_sub _ _
    _ ≤ _root_.GD.N0232.N0720.N1126.d016418 (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i)) +
          (|g.shift| + g.d009239 * _root_.GD.N0232.N0720.N1126.d016418 packet) :=
      add_le_add hleft htransport
    _ = _ := by ring



theorem d016640
    (g : _root_.GD.N0232.N0720.N1163.d016630) (j : ℕ)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    MemLp (_root_.GD.N0232.N0720.N1163.d016634
      (m := m) (n := n) g j packet weight) 2
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  let B := _root_.GD.N0232.N0720.N1163.d016637 g packet
  apply memLp_of_bounded (a := -B) (b := B)
  · filter_upwards with omega
    exact abs_le.mp
      (_root_.GD.N0232.N0720.N1163.d016639
        g j packet weight hweight omega)
  · exact (_root_.GD.N0232.N0720.N1163.d016635
      g j packet weight).aestronglyMeasurable



def d016641
    (g : _root_.GD.N0232.N0720.N1163.d016630) (j : ℕ)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  MemLp.toLp
    (_root_.GD.N0232.N0720.N1163.d016634
      (m := m) (n := n) g j packet weight)
    (_root_.GD.N0232.N0720.N1163.d016640
      g j packet weight hweight)





theorem d016642
    (g : _root_.GD.N0232.N0720.N1163.d016630) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hpositive : ∃ i, 0 < weight i) :
    Tendsto
      (fun j : ℕ ↦
        ∫ omega,
          _root_.GD.N0232.N0720.N1163.d016634
            (m := m) (n := n) g j packet weight omega ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n)
      atTop (nhds 0) := by
  let B := _root_.GD.N0232.N0720.N1163.d016637 g packet
  have hB : 0 ≤ B := _root_.GD.N0232.N0720.N1163.d016638 g packet
  have hlim : Tendsto
      (fun j : ℕ ↦
        ∫ omega,
          _root_.GD.N0232.N0720.N1163.d016634
            (m := m) (n := n) g j packet weight omega ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n)
      atTop
      (nhds (∫ _omega, (0 : ℝ) ∂_root_.GD.N0232.N0720.N1080.d014172 m n)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun _omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ B ^ 2)
    · exact Filter.Eventually.of_forall fun j ↦
        ((_root_.GD.N0232.N0720.N1163.d016635
          g j packet weight).pow_const 2).aestronglyMeasurable
    · filter_upwards with j
      filter_upwards with omega
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have habs := _root_.GD.N0232.N0720.N1163.d016639
        g j packet weight hweight omega
      simpa only [sq_abs] using
        ((sq_le_sq₀ (abs_nonneg _) hB).2 habs)
    · exact integrable_const (B ^ 2)
    · filter_upwards with omega
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
        (_root_.GD.N0232.N0720.N1163.d016636
          g packet weight hweight hpositive omega).pow 2
  simpa using hlim




theorem d016643
    (g : _root_.GD.N0232.N0720.N1163.d016630) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hpositive : ∃ i, 0 < weight i) :
    Tendsto
      (fun j : ℕ ↦
        ‖_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n) g j packet weight hweight‖)
      atTop (nhds 0) := by
  have hintegral :=
    _root_.GD.N0232.N0720.N1163.d016642
      (m := m) (n := n) g packet weight hweight hpositive
  have hsq : Tendsto
      (fun j : ℕ ↦
        ‖_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n) g j packet weight hweight‖ ^ 2)
      atTop (nhds 0) := by
    apply hintegral.congr'
    filter_upwards with j
    unfold _root_.GD.N0232.N0720.N1163.d016641
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [
      (_root_.GD.N0232.N0720.N1163.d016640
        g j packet weight hweight).coeFn_toLp] with omega homega
    rw [homega]
    simp only [RCLike.inner_apply, conj_trivial, pow_two]
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  change Tendsto
    (fun j : ℕ ↦
      Real.sqrt
        (‖_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n) g j packet weight hweight‖ ^ 2))
    atTop (nhds (Real.sqrt 0)) at hsqrt
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using hsqrt






theorem d016644
    (g : _root_.GD.N0232.N0720.N1163.d016630)
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g)
    (j : ℕ) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0232.N0720.N1163.d016641
        (m := m) (n := n) g j packet weight hweight =
      _root_.GD.N0232.N0720.N1126.d016426
          (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))
          (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
          (_root_.GD.N0232.N0720.N1163.d016632 weight hweight (Nat.cast_nonneg j)) -
        _root_.GD.N0232.N0720.N1146.d015212 m n certificate
          (_root_.GD.N0232.N0720.N1126.d016426 packet
            (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
            (_root_.GD.N0232.N0720.N1163.d016632 weight hweight
              (Nat.cast_nonneg j))) := by
  let scaledNonneg : ∀ i, 0 ≤ _root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight i :=
    _root_.GD.N0232.N0720.N1163.d016632 weight hweight (Nat.cast_nonneg j)
  let p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1126.d016426 packet
      (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight) scaledNonneg
  have hpRaw : _root_.GD.N0232.N0720.N1214.d014265 m n p =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
      _root_.GD.N0232.N0720.N1126.d016416 packet
        (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight) :=
    (_root_.GD.N0232.N0720.N1214.d014267 m n p).trans
      (_root_.GD.N0232.N0720.N1126.d016427
        packet (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight) scaledNonneg)
  have htransportRaw :=
    _root_.GD.N0232.N0720.N1081.d014625
      m n g hpRaw
  unfold _root_.GD.N0232.N0720.N1163.d016641
  apply Lp.ext
  filter_upwards [
    (_root_.GD.N0232.N0720.N1163.d016640
      g j packet weight hweight).coeFn_toLp,
    Lp.coeFn_sub
      (_root_.GD.N0232.N0720.N1126.d016426
        (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))
        (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight) scaledNonneg)
      (_root_.GD.N0232.N0720.N1146.d015212 m n certificate p),
    _root_.GD.N0232.N0720.N1126.d016427
      (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))
      (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight) scaledNonneg,
    (_root_.GD.N0232.N0720.N1146.d015211 m n certificate p).coeFn_toLp,
    htransportRaw] with omega hdef hsub hleft htransport hraw
  rw [hdef, hsub, Pi.sub_apply, hleft]
  change _root_.GD.N0232.N0720.N1163.d016634 g j packet weight omega =
    _root_.GD.N0232.N0720.N1126.d016416
        (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))
        (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight) omega -
      MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p))
        (_root_.GD.N0232.N0720.N1146.d015211 m n certificate p) omega
  rw [htransport, hraw]
  rfl





theorem d016645
    (g : _root_.GD.N0232.N0720.N1163.d016630)
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g)
    (j : ℕ) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate
          (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n) packet
            (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
            (_root_.GD.N0232.N0720.N1163.d016632 weight hweight
              (Nat.cast_nonneg j))) -
        _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n) packet
          (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
          (_root_.GD.N0232.N0720.N1163.d016632 weight hweight
            (Nat.cast_nonneg j))‖ ≤
      ‖_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n) g j packet weight hweight‖ +
        ‖_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
            (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))
            (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
            (_root_.GD.N0232.N0720.N1163.d016632 weight hweight
              (Nat.cast_nonneg j)) -
          _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n) packet
            (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
            (_root_.GD.N0232.N0720.N1163.d016632 weight hweight
              (Nat.cast_nonneg j))‖ := by
  let scaledNonneg : ∀ i, 0 ≤ _root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight i :=
    _root_.GD.N0232.N0720.N1163.d016632 weight hweight (Nat.cast_nonneg j)
  let p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1126.d016426 packet
      (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight) scaledNonneg
  let pg : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1126.d016426
      (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))
      (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight) scaledNonneg
  have hcov : _root_.GD.N0232.N0720.N1163.d016641
      (m := m) (n := n) g j packet weight hweight =
      pg - _root_.GD.N0232.N0720.N1146.d015212 m n certificate p := by
    simpa only [p, pg] using
      (_root_.GD.N0232.N0720.N1163.d016644
        (m := m) (n := n) g certificate j packet weight hweight)
  have hdecomp :
      _root_.GD.N0232.N0720.N1146.d015212 m n certificate p - p =
        (_root_.GD.N0232.N0720.N1146.d015212 m n certificate p - pg) +
          (pg - p) := by abel
  have hfirst :
      ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate p - pg‖ =
        ‖_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n) g j packet weight hweight‖ := by
    rw [norm_sub_rev]
    exact congrArg norm hcov.symm
  change
    ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate p - p‖ ≤
      ‖_root_.GD.N0232.N0720.N1163.d016641
        (m := m) (n := n) g j packet weight hweight‖ + ‖pg - p‖
  rw [hdecomp]
  calc
    ‖(_root_.GD.N0232.N0720.N1146.d015212 m n certificate p - pg) +
        (pg - p)‖ ≤
        ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate p - pg‖ +
          ‖pg - p‖ := norm_add_le _ _
    _ = _ := by rw [hfirst]




theorem d016646
    (g : _root_.GD.N0232.N0720.N1163.d016630)
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g)
    (packet : ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ι → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hpositive : ∃ i, 0 < weight i)
    (hdrift : Tendsto
      (fun j : ℕ ↦
        ‖_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
            (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))
            (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
            (_root_.GD.N0232.N0720.N1163.d016632 weight hweight
              (Nat.cast_nonneg j)) -
          _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n) packet
            (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
            (_root_.GD.N0232.N0720.N1163.d016632 weight hweight
              (Nat.cast_nonneg j))‖)
      atTop (nhds 0)) :
    Tendsto
      (fun j : ℕ ↦
        ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate
            (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n) packet
              (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
              (_root_.GD.N0232.N0720.N1163.d016632 weight hweight
                (Nat.cast_nonneg j))) -
          _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n) packet
            (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
            (_root_.GD.N0232.N0720.N1163.d016632 weight hweight
              (Nat.cast_nonneg j))‖)
      atTop (nhds 0) := by
  have hcovariance := _root_.GD.N0232.N0720.N1163.d016643
    (m := m) (n := n) g packet weight hweight hpositive
  have hupper : ∀ j : ℕ,
      ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate
            (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n) packet
              (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
              (_root_.GD.N0232.N0720.N1163.d016632 weight hweight
                (Nat.cast_nonneg j))) -
          _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n) packet
            (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
            (_root_.GD.N0232.N0720.N1163.d016632 weight hweight
              (Nat.cast_nonneg j))‖ ≤
        ‖_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n) g j packet weight hweight‖ +
        ‖_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
            (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))
            (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
            (_root_.GD.N0232.N0720.N1163.d016632 weight hweight
              (Nat.cast_nonneg j)) -
          _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n) packet
            (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
            (_root_.GD.N0232.N0720.N1163.d016632 weight hweight
              (Nat.cast_nonneg j))‖ := by
    intro j
    exact _root_.GD.N0232.N0720.N1163.d016645
      g certificate j packet weight hweight
  have hmajor : Tendsto
      (fun j : ℕ ↦
        ‖_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n) g j packet weight hweight‖ +
        ‖_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
            (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet i))
            (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
            (_root_.GD.N0232.N0720.N1163.d016632 weight hweight
              (Nat.cast_nonneg j)) -
          _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n) packet
            (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
            (_root_.GD.N0232.N0720.N1163.d016632 weight hweight
              (Nat.cast_nonneg j))‖)
      atTop (nhds 0) := by
    simpa only [zero_add] using hcovariance.add hdrift
  exact squeeze_zero
    (fun j ↦ norm_nonneg
      (_root_.GD.N0232.N0720.N1146.d015212 m n certificate
          (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n) packet
            (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
            (_root_.GD.N0232.N0720.N1163.d016632 weight hweight
              (Nat.cast_nonneg j))) -
        _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n) packet
          (_root_.GD.N0232.N0720.N1162.d016619 (j : ℝ) weight)
          (_root_.GD.N0232.N0720.N1163.d016632 weight hweight
            (Nat.cast_nonneg j))))
    hupper hmajor







theorem d016647
    (packet : ℕ → ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ℕ → ι → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (hpositive : ∀ j, ∃ i, 0 < weight j i) :
    ∃ scale : ℕ → ℕ,
      Tendsto scale atTop atTop ∧
      Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1163.d016641
            (m := m) (n := n)
              _root_.GD.N0232.N0720.N1482.d015130 (scale j)
              (packet j) (weight j) (hweight j)‖)
        atTop (nhds 0) ∧
      Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1163.d016641
            (m := m) (n := n)
              _root_.GD.N0232.N0720.N1482.d015131
              (scale j)
              (packet j) (weight j) (hweight j)‖)
        atTop (nhds 0) := by
  have hchoice : ∀ j : ℕ, ∃ N : ℕ,
      j ≤ N ∧
      ‖_root_.GD.N0232.N0720.N1163.d016641
        (m := m) (n := n)
          _root_.GD.N0232.N0720.N1482.d015130 N
          (packet j) (weight j) (hweight j)‖ < 1 / ((j : ℝ) + 1) ∧
      ‖_root_.GD.N0232.N0720.N1163.d016641
        (m := m) (n := n)
          _root_.GD.N0232.N0720.N1482.d015131 N
          (packet j) (weight j) (hweight j)‖ < 1 / ((j : ℝ) + 1) := by
    intro j
    let epsilon : ℝ := 1 / ((j : ℝ) + 1)
    have hepsilon : 0 < epsilon := by
      unfold epsilon
      positivity
    have htwo := _root_.GD.N0232.N0720.N1163.d016643
      (m := m) (n := n)
      _root_.GD.N0232.N0720.N1482.d015130
      (packet j) (weight j) (hweight j) (hpositive j)
    have hthree := _root_.GD.N0232.N0720.N1163.d016643
      (m := m) (n := n)
      _root_.GD.N0232.N0720.N1482.d015131
      (packet j) (weight j) (hweight j) (hpositive j)
    rw [Metric.tendsto_atTop] at htwo hthree
    obtain ⟨N₂, hN₂⟩ := htwo epsilon hepsilon
    obtain ⟨N₃, hN₃⟩ := hthree epsilon hepsilon
    let N := max j (max N₂ N₃)
    have hjN : j ≤ N := le_max_left _ _
    have hN₂N : N₂ ≤ N :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hN₃N : N₃ ≤ N :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have htwoN := hN₂ N hN₂N
    have hthreeN := hN₃ N hN₃N
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (norm_nonneg _)] at htwoN hthreeN
    exact ⟨N, hjN, htwoN, hthreeN⟩
  choose scale hscale htwo hthree using hchoice
  have hscaleTendsto : Tendsto scale atTop atTop := by
    exact tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall hscale) tendsto_id
  have hboundTendsto : Tendsto
      (fun j : ℕ ↦ 1 / ((j : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨scale, hscaleTendsto, ?_, ?_⟩
  · exact squeeze_zero
      (fun j ↦ norm_nonneg
        (_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n)
            _root_.GD.N0232.N0720.N1482.d015130 (scale j)
            (packet j) (weight j) (hweight j)))
      (fun j ↦ (htwo j).le) hboundTendsto
  · exact squeeze_zero
      (fun j ↦ norm_nonneg
        (_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n)
            _root_.GD.N0232.N0720.N1482.d015131
            (scale j)
            (packet j) (weight j) (hweight j)))
      (fun j ↦ (hthree j).le) hboundTendsto





theorem d016648
    (packet : ℕ → ι → _root_.GD.N0232.N0720.N1080.d014168) (weight : ℕ → ι → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (hpositive : ∀ j, ∃ i, 0 < weight j i) :
    ∃ scale : ℕ → ℕ,
      Tendsto scale atTop atTop ∧
      Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1126.d016426
                (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272
                  _root_.GD.N0232.N0720.N1482.d015130
                  (packet j i))
                (_root_.GD.N0232.N0720.N1162.d016619 (scale j : ℝ) (weight j))
                (_root_.GD.N0232.N0720.N1163.d016632 (weight j) (hweight j)
                  (Nat.cast_nonneg (scale j))) -
            _root_.GD.N0232.N0720.N1146.d015212 m n
              (_root_.GD.N0232.N0720.N1146.d015221 m n)
              (_root_.GD.N0232.N0720.N1126.d016426 (packet j)
                (_root_.GD.N0232.N0720.N1162.d016619 (scale j : ℝ) (weight j))
                (_root_.GD.N0232.N0720.N1163.d016632 (weight j) (hweight j)
                  (Nat.cast_nonneg (scale j))))‖)
        atTop (nhds 0) ∧
      Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1126.d016426
                (fun i ↦
                  _root_.GD.N0232.N0720.N1215.d014272
                    _root_.GD.N0232.N0720.N1482.d015131
                    (packet j i))
                (_root_.GD.N0232.N0720.N1162.d016619 (scale j : ℝ) (weight j))
                (_root_.GD.N0232.N0720.N1163.d016632 (weight j) (hweight j)
                  (Nat.cast_nonneg (scale j))) -
            _root_.GD.N0232.N0720.N1146.d015212 m n
              (_root_.GD.N0232.N0720.N1146.d015222 m n)
              (_root_.GD.N0232.N0720.N1126.d016426 (packet j)
                (_root_.GD.N0232.N0720.N1162.d016619 (scale j : ℝ) (weight j))
                (_root_.GD.N0232.N0720.N1163.d016632 (weight j) (hweight j)
                  (Nat.cast_nonneg (scale j))))‖)
        atTop (nhds 0) := by
  obtain ⟨scale, hscale, htwo, hthree⟩ :=
    _root_.GD.N0232.N0720.N1163.d016647
      (m := m) (n := n) (ι := ι) packet weight hweight hpositive
  refine ⟨scale, hscale, ?_, ?_⟩
  · apply htwo.congr'
    filter_upwards with j
    rw [_root_.GD.N0232.N0720.N1163.d016644
      (m := m) (n := n)
        _root_.GD.N0232.N0720.N1482.d015130
        (_root_.GD.N0232.N0720.N1146.d015221 m n)]
  · apply hthree.congr'
    filter_upwards with j
    rw [_root_.GD.N0232.N0720.N1163.d016644
      (m := m) (n := n)
        _root_.GD.N0232.N0720.N1482.d015131
        (_root_.GD.N0232.N0720.N1146.d015222 m n)]





theorem d016649
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ) (t : ℝ) :
    _root_.GD.N0232.N0720.N1127.d016545 m n s packet
        (_root_.GD.N0232.N0720.N1162.d016619 t weight) =
      t * _root_.GD.N0232.N0720.N1127.d016545 m n s packet weight := by
  unfold _root_.GD.N0232.N0720.N1127.d016545 _root_.GD.N0232.N0720.N1162.d016619
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring




theorem d016650
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (packet : ι → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ι → ℝ)
    (hpositive :
      0 < _root_.GD.N0232.N0720.N1127.d016545 m n s packet weight) :
    Tendsto
      (fun t : ℝ ↦
        _root_.GD.N0232.N0720.N1127.d016545 m n s packet
          (_root_.GD.N0232.N0720.N1162.d016619 t weight))
      atTop atTop := by
  have hmul : Tendsto
      (fun t : ℝ ↦
        t * _root_.GD.N0232.N0720.N1127.d016545 m n s packet weight)
      atTop atTop :=
    by
      simpa only [mul_comm, id_eq] using
        (tendsto_id.const_mul_atTop hpositive)
  apply hmul.congr'
  filter_upwards with t
  exact (_root_.GD.N0232.N0720.N1163.d016649
    s packet weight t).symm

end

end N1163
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1163.d016643
#print axioms _root_.GD.N0232.N0720.N1163.d016644
#print axioms _root_.GD.N0232.N0720.N1163.d016645
#print axioms _root_.GD.N0232.N0720.N1163.d016646
#print axioms _root_.GD.N0232.N0720.N1163.d016647
#print axioms _root_.GD.N0232.N0720.N1163.d016648
#print axioms _root_.GD.N0232.N0720.N1163.d016649
#print axioms _root_.GD.N0232.N0720.N1163.d016650
