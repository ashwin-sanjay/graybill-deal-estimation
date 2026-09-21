import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Order.Compact
































open Set
open scoped Topology

namespace GD
namespace N0238
namespace N0757

noncomputable section

variable {X : Type*}


def d004846 (weight : ℕ → ℝ) (trace : ℕ → X → ℝ) (x y : X) : ℝ :=
  ∑' n, weight n * (trace n x - trace n y) ^ 2


def d004847 (weight : ℕ → ℝ) (trace : ℕ → X → ℝ)
    (N : ℕ) (x y : X) : ℝ :=
  ∑' k, weight (k + N) * (trace (k + N) x - trace (k + N) y) ^ 2


def d004848 (trace : ℕ → X → ℝ) (x : X) : ℕ → ℝ :=
  fun n ↦ trace n x


def d004849 (weight : ℕ → ℝ) (trace : ℕ → X → ℝ)
    (x : X) : ℕ → ℝ :=
  fun n ↦ Real.sqrt (weight n) * trace n x


def d004850 (trace : ℕ → X → ℝ) (x y : X) : Prop :=
  ∀ n, trace n x = trace n y

theorem d004851 (trace : ℕ → X → ℝ) (x : X) :
    _root_.GD.N0238.N0757.d004850 trace x x :=
  fun _ ↦ rfl

theorem d004852 (trace : ℕ → X → ℝ) {x y : X}
    (h : _root_.GD.N0238.N0757.d004850 trace x y) :
    _root_.GD.N0238.N0757.d004850 trace y x :=
  fun n ↦ (h n).symm

theorem d004853 (trace : ℕ → X → ℝ) {x y z : X}
    (hxy : _root_.GD.N0238.N0757.d004850 trace x y)
    (hyz : _root_.GD.N0238.N0757.d004850 trace y z) :
    _root_.GD.N0238.N0757.d004850 trace x z :=
  fun n ↦ (hxy n).trans (hyz n)



def d004854 (trace : ℕ → X → ℝ) : Setoid X where
  r := _root_.GD.N0238.N0757.d004850 trace
  iseqv := ⟨_root_.GD.N0238.N0757.d004851 trace, _root_.GD.N0238.N0757.d004852 trace,
    _root_.GD.N0238.N0757.d004853 trace⟩

section Bounds

variable (weight : ℕ → ℝ) (trace : ℕ → X → ℝ)

theorem d004855
    (htrace : ∀ n x, |trace n x| ≤ 1)
    (n : ℕ) (x y : X) :
    |trace n x - trace n y| ≤ 2 := by
  calc
    |trace n x - trace n y| ≤ |trace n x| + |trace n y| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (htrace n x) (htrace n y)
    _ = 2 := by norm_num

theorem d004856
    (hweight : ∀ n, 0 ≤ weight n)
    (n : ℕ) (x y : X) :
    0 ≤ weight n * (trace n x - trace n y) ^ 2 :=
  mul_nonneg (hweight n) (sq_nonneg _)

theorem d004857
    (hweight : ∀ n, 0 ≤ weight n)
    (htrace : ∀ n x, |trace n x| ≤ 1)
    (n : ℕ) (x y : X) :
    ‖weight n * (trace n x - trace n y) ^ 2‖ ≤ 4 * weight n := by
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (hweight n)]
  have hd := _root_.GD.N0238.N0757.d004855 trace htrace n x y
  have hsq : |trace n x - trace n y| ^ 2 ≤ 4 := by
    have :=
      (sq_le_sq₀ (abs_nonneg (trace n x - trace n y))
        (by norm_num : (0 : ℝ) ≤ 2)).2 hd
    norm_num at this ⊢
    exact this
  simpa [mul_comm] using mul_le_mul_of_nonneg_left hsq (hweight n)

theorem d004858
    (hweight : ∀ n, 0 ≤ weight n)
    (hsum : Summable weight)
    (htrace : ∀ n x, |trace n x| ≤ 1)
    (x y : X) :
    Summable (fun n ↦ weight n * (trace n x - trace n y) ^ 2) := by
  apply Summable.of_norm_bounded
    (by simpa [mul_comm] using hsum.mul_right 4)
  exact fun n ↦ by
    simpa [mul_comm] using
      _root_.GD.N0238.N0757.d004857 weight trace hweight htrace n x y

theorem d004859
    (hweight : ∀ n, 0 ≤ weight n)
    (x y : X) :
    0 ≤ _root_.GD.N0238.N0757.d004846 weight trace x y := by
  exact tsum_nonneg
    (fun n ↦ _root_.GD.N0238.N0757.d004856 weight trace hweight n x y)

theorem d004860 (x y : X) :
    _root_.GD.N0238.N0757.d004846 weight trace x y = _root_.GD.N0238.N0757.d004846 weight trace y x := by
  apply tsum_congr
  intro n
  ring

@[simp]
theorem d004861 (x : X) :
    _root_.GD.N0238.N0757.d004846 weight trace x x = 0 := by
  simp [_root_.GD.N0238.N0757.d004846]

theorem d004862
    (hweight : ∀ n, 0 ≤ weight n)
    (N : ℕ) (x y : X) :
    0 ≤ _root_.GD.N0238.N0757.d004847 weight trace N x y := by
  unfold _root_.GD.N0238.N0757.d004847
  exact tsum_nonneg
    (fun n ↦ _root_.GD.N0238.N0757.d004856 weight trace hweight (n + N) x y)


theorem d004863
    (hweight : ∀ n, 0 ≤ weight n)
    (hsum : Summable weight)
    (htrace : ∀ n x, |trace n x| ≤ 1)
    (N : ℕ) (x y : X) :
    (∑ n ∈ Finset.range N,
        weight n * (trace n x - trace n y) ^ 2) +
        _root_.GD.N0238.N0757.d004847 weight trace N x y =
      _root_.GD.N0238.N0757.d004846 weight trace x y := by
  simpa [_root_.GD.N0238.N0757.d004846, _root_.GD.N0238.N0757.d004847] using
    (_root_.GD.N0238.N0757.d004858 weight trace hweight hsum htrace x y).sum_add_tsum_nat_add N


theorem d004864
    (hweight : ∀ n, 0 ≤ weight n)
    (hsum : Summable weight)
    (htrace : ∀ n x, |trace n x| ≤ 1)
    (N : ℕ) (x y : X) :
    _root_.GD.N0238.N0757.d004847 weight trace N x y ≤
      4 * ∑' k, weight (k + N) := by
  unfold _root_.GD.N0238.N0757.d004847
  have hpair :=
    (summable_nat_add_iff N).2
      (_root_.GD.N0238.N0757.d004858 weight trace hweight hsum htrace x y)
  have hweights : Summable (fun k ↦ 4 * weight (k + N)) := by
    simpa [mul_comm] using ((summable_nat_add_iff N).2 hsum).mul_left 4
  exact hpair.tsum_le_tsum
    (fun k ↦ by
      have h :=
        _root_.GD.N0238.N0757.d004857 weight trace hweight htrace (k + N) x y
      rw [Real.norm_eq_abs, abs_of_nonneg
        (_root_.GD.N0238.N0757.d004856 weight trace hweight (k + N) x y)] at h
      exact h)
    hweights |>.trans_eq (by rw [tsum_mul_left])




theorem d004865 :
    Filter.Tendsto (fun N ↦ ∑' k, weight (k + N))
      Filter.atTop (𝓝 0) :=
  tendsto_sum_nat_add weight



theorem d004866
    (hweight : ∀ n, 0 ≤ weight n)
    (hsum : Summable weight)
    (htrace : ∀ n x, |trace n x| ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in Filter.atTop,
      ∀ x y, _root_.GD.N0238.N0757.d004847 weight trace N x y < ε := by
  have htend :
      Filter.Tendsto (fun N ↦ 4 * ∑' k, weight (k + N))
        Filter.atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (_root_.GD.N0238.N0757.d004865 weight)
  have hevent :
      ∀ᶠ N in Filter.atTop, 4 * ∑' k, weight (k + N) < ε :=
    (tendsto_order.1 htend).2 ε hε
  filter_upwards [hevent] with N hN
  intro x y
  exact
    (_root_.GD.N0238.N0757.d004864 weight trace hweight hsum htrace N x y).trans_lt hN



theorem d004867
    (hweight : ∀ n, 0 ≤ weight n)
    (hsum : Summable weight)
    (htrace : ∀ n x, |trace n x| ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ x y,
      |_root_.GD.N0238.N0757.d004846 weight trace x y -
        ∑ n ∈ Finset.range N,
          weight n * (trace n x - trace n y) ^ 2| < ε := by
  obtain ⟨N, hN⟩ :=
    (Filter.eventually_atTop.1
      (_root_.GD.N0238.N0757.d004866 weight trace hweight hsum htrace hε))
  refine ⟨N, fun x y ↦ ?_⟩
  have hdecomp :=
    _root_.GD.N0238.N0757.d004863 weight trace hweight hsum htrace N x y
  have hnonneg := _root_.GD.N0238.N0757.d004862 weight trace hweight N x y
  rw [← hdecomp, add_sub_cancel_left, abs_of_nonneg hnonneg]
  exact hN N le_rfl x y


theorem d004868
    (hweight : ∀ n, 0 ≤ weight n)
    (hsum : Summable weight)
    (htrace : ∀ n x, |trace n x| ≤ 1)
    (x : X) :
    Summable (fun n ↦ (_root_.GD.N0238.N0757.d004849 weight trace x n) ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun n ↦ sq_nonneg _)
    (fun n ↦ by
      rw [_root_.GD.N0238.N0757.d004849, mul_pow, Real.sq_sqrt (hweight n)]
      have hsquare : trace n x ^ 2 ≤ 1 := by
        rw [← sq_abs]
        simpa using
          (sq_le_sq₀ (abs_nonneg (trace n x)) (by norm_num : (0 : ℝ) ≤ 1)).2
            (htrace n x)
      exact mul_le_of_le_one_right (hweight n) hsquare)
    hsum

end Bounds

section Continuity

variable [TopologicalSpace X]
variable (weight : ℕ → ℝ) (trace : ℕ → X → ℝ)

theorem d004869
    (htrace_continuous : ∀ n, Continuous (trace n)) :
    Continuous (_root_.GD.N0238.N0757.d004848 trace) := by
  apply continuous_pi
  exact htrace_continuous

theorem d004870
    (htrace_continuous : ∀ n, Continuous (trace n)) :
    Continuous (_root_.GD.N0238.N0757.d004849 weight trace) := by
  apply continuous_pi
  intro n
  exact continuous_const.mul (htrace_continuous n)

theorem d004871
    (hweight : ∀ n, 0 ≤ weight n)
    (hsum : Summable weight)
    (htrace_bound : ∀ n x, |trace n x| ≤ 1)
    (htrace_continuous : ∀ n, Continuous (trace n)) :
    Continuous (fun z : X × X ↦ _root_.GD.N0238.N0757.d004846 weight trace z.1 z.2) := by
  unfold _root_.GD.N0238.N0757.d004846
  apply continuous_tsum
  · intro n
    exact continuous_const.mul
      ((((htrace_continuous n).comp continuous_fst).sub
        ((htrace_continuous n).comp continuous_snd)).pow 2)
  · simpa [mul_comm] using hsum.mul_left 4
  · intro n z
    simpa [mul_comm] using
      _root_.GD.N0238.N0757.d004857 weight trace hweight htrace_bound n z.1 z.2

theorem d004872
    (hweight : ∀ n, 0 ≤ weight n)
    (hsum : Summable weight)
    (htrace_bound : ∀ n x, |trace n x| ≤ 1)
    (htrace_continuous : ∀ n, Continuous (trace n))
    (x : X) :
    Continuous (fun y ↦ _root_.GD.N0238.N0757.d004846 weight trace x y) := by
  exact
    (_root_.GD.N0238.N0757.d004871 weight trace hweight hsum htrace_bound
      htrace_continuous).comp
      (continuous_const.prodMk continuous_id)

theorem d004873
    (hweight : ∀ n, 0 ≤ weight n)
    (hsum : Summable weight)
    (htrace_bound : ∀ n x, |trace n x| ≤ 1)
    (htrace_continuous : ∀ n, Continuous (trace n))
    (x : X) (ε : ℝ) :
    IsOpen {y | _root_.GD.N0238.N0757.d004846 weight trace x y < ε} :=
  isOpen_lt
    (_root_.GD.N0238.N0757.d004872 weight trace hweight hsum htrace_bound
      htrace_continuous x)
    continuous_const

end Continuity

section Separation

variable (weight : ℕ → ℝ) (trace : ℕ → X → ℝ)

theorem d004874
    (hweight : ∀ n, 0 < weight n)
    (hsum : Summable weight)
    (htrace : ∀ n x, |trace n x| ≤ 1)
    (x y : X) :
    _root_.GD.N0238.N0757.d004846 weight trace x y = 0 ↔ _root_.GD.N0238.N0757.d004850 trace x y := by
  constructor
  · intro hzero n
    have hweight_nonneg : ∀ k, 0 ≤ weight k :=
      fun k ↦ (hweight k).le
    have hsummable :=
      _root_.GD.N0238.N0757.d004858 weight trace hweight_nonneg hsum htrace x y
    have hterm_le :
        weight n * (trace n x - trace n y) ^ 2 ≤
          _root_.GD.N0238.N0757.d004846 weight trace x y := by
      exact hsummable.le_tsum n
        (fun k _ ↦ _root_.GD.N0238.N0757.d004856 weight trace hweight_nonneg k x y)
    rw [hzero] at hterm_le
    have hterm_nonneg :=
      _root_.GD.N0238.N0757.d004856 weight trace hweight_nonneg n x y
    have hterm_zero :
        weight n * (trace n x - trace n y) ^ 2 = 0 :=
      le_antisymm hterm_le hterm_nonneg
    rcases mul_eq_zero.mp hterm_zero with hw | hsquare
    · exact (ne_of_gt (hweight n) hw).elim
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · intro heq
    rw [_root_.GD.N0238.N0757.d004846]
    calc
      (∑' n, weight n * (trace n x - trace n y) ^ 2) =
          ∑' _n : ℕ, (0 : ℝ) := by
            apply tsum_congr
            intro n
            rw [heq n, sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
      _ = 0 := tsum_zero

theorem d004875
    (hweight : ∀ n, 0 < weight n)
    (hsum : Summable weight)
    (htrace : ∀ n x, |trace n x| ≤ 1)
    (hseparates :
      ∀ ⦃x y : X⦄, _root_.GD.N0238.N0757.d004850 trace x y → x = y)
    (x y : X) :
    _root_.GD.N0238.N0757.d004846 weight trace x y = 0 ↔ x = y := by
  rw [_root_.GD.N0238.N0757.d004874 weight trace hweight hsum htrace]
  exact ⟨fun h ↦ hseparates h, fun h ↦ h ▸ _root_.GD.N0238.N0757.d004851 trace x⟩

theorem d004876
    (hseparates :
      ∀ ⦃x y : X⦄, _root_.GD.N0238.N0757.d004850 trace x y → x = y) :
    Function.Injective (_root_.GD.N0238.N0757.d004848 trace) := by
  intro x y hxy
  apply hseparates
  intro n
  exact congrFun hxy n

theorem d004877
    (hweight : ∀ n, 0 < weight n)
    (hseparates :
      ∀ ⦃x y : X⦄, _root_.GD.N0238.N0757.d004850 trace x y → x = y) :
    Function.Injective (_root_.GD.N0238.N0757.d004849 weight trace) := by
  intro x y hxy
  apply hseparates
  intro n
  have hsqrt : Real.sqrt (weight n) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (hweight n))
  exact (mul_left_cancel₀ hsqrt (congrFun hxy n))

end Separation

section TopologicalEmbedding

variable [TopologicalSpace X] [CompactSpace X]
variable (weight : ℕ → ℝ) (trace : ℕ → X → ℝ)



theorem d004878
    (htrace_continuous : ∀ n, Continuous (trace n))
    (hseparates :
      ∀ ⦃x y : X⦄, _root_.GD.N0238.N0757.d004850 trace x y → x = y) :
    Topology.IsClosedEmbedding (_root_.GD.N0238.N0757.d004848 trace) := by
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
  · exact _root_.GD.N0238.N0757.d004869 trace htrace_continuous
  · exact _root_.GD.N0238.N0757.d004876 trace hseparates
  · intro s hs
    exact ((hs.isCompact.image
      (_root_.GD.N0238.N0757.d004869 trace htrace_continuous)).isClosed)



theorem d004879
    (hweight : ∀ n, 0 < weight n)
    (htrace_continuous : ∀ n, Continuous (trace n))
    (hseparates :
      ∀ ⦃x y : X⦄, _root_.GD.N0238.N0757.d004850 trace x y → x = y) :
    Topology.IsClosedEmbedding (_root_.GD.N0238.N0757.d004849 weight trace) := by
  apply Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
  · exact _root_.GD.N0238.N0757.d004870 weight trace htrace_continuous
  · exact _root_.GD.N0238.N0757.d004877 weight trace hweight hseparates
  · intro s hs
    exact ((hs.isCompact.image
      (_root_.GD.N0238.N0757.d004870 weight trace htrace_continuous)).isClosed)



theorem d004880
    (hweight : ∀ n, 0 < weight n)
    (hsum : Summable weight)
    (htrace_bound : ∀ n x, |trace n x| ≤ 1)
    (htrace_continuous : ∀ n, Continuous (trace n))
    (hseparates :
      ∀ ⦃x y : X⦄, _root_.GD.N0238.N0757.d004850 trace x y → x = y)
    {x : X} {U : Set X} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ {y | _root_.GD.N0238.N0757.d004846 weight trace x y < ε} ⊆ U := by
  have hweight_nonneg : ∀ n, 0 ≤ weight n :=
    fun n ↦ (hweight n).le
  have hcontinuous :
      Continuous (fun y ↦ _root_.GD.N0238.N0757.d004846 weight trace x y) :=
    _root_.GD.N0238.N0757.d004872 weight trace hweight_nonneg hsum htrace_bound
      htrace_continuous x
  have hcompact : IsCompact Uᶜ :=
    hU.isClosed_compl.isCompact
  have hpositive :
      ∀ y ∈ Uᶜ, 0 < _root_.GD.N0238.N0757.d004846 weight trace x y := by
    intro y hy
    have hxy : x ≠ y := by
      intro h
      subst y
      exact hy hxU
    have hnonneg :=
      _root_.GD.N0238.N0757.d004859 weight trace hweight_nonneg x y
    have hcost_ne : _root_.GD.N0238.N0757.d004846 weight trace x y ≠ 0 :=
      fun hzero ↦ hxy
        ((_root_.GD.N0238.N0757.d004875 weight trace hweight hsum htrace_bound
          hseparates x y).mp hzero)
    exact lt_of_le_of_ne hnonneg hcost_ne.symm
  obtain ⟨ε, hε, hεlower⟩ :=
    hcompact.exists_forall_le' hcontinuous.continuousOn hpositive
  refine ⟨ε, hε, ?_⟩
  intro y hyball
  by_contra hyU
  have hycompl : y ∈ Uᶜ := hyU
  exact (not_lt_of_ge (hεlower y hycompl)) hyball




theorem d004881
    (hweight : ∀ n, 0 < weight n)
    (hsum : Summable weight)
    (htrace_bound : ∀ n x, |trace n x| ≤ 1)
    (htrace_continuous : ∀ n, Continuous (trace n))
    (hseparates :
      ∀ ⦃x y : X⦄, _root_.GD.N0238.N0757.d004850 trace x y → x = y)
    (x : X) :
    Filter.HasBasis (𝓝 x) (fun ε : ℝ ↦ 0 < ε)
      (fun ε ↦ {y | _root_.GD.N0238.N0757.d004846 weight trace x y < ε}) := by
  rw [Filter.hasBasis_iff]
  intro U
  constructor
  · intro hU
    obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hU
    obtain ⟨ε, hε, hball⟩ :=
      _root_.GD.N0238.N0757.d004880 weight trace hweight hsum htrace_bound
        htrace_continuous hseparates hVopen hxV
    exact ⟨ε, hε, hball.trans hVsub⟩
  · rintro ⟨ε, hε, hsub⟩
    apply Filter.mem_of_superset
      ((_root_.GD.N0238.N0757.d004873 weight trace
        (fun n ↦ (hweight n).le) hsum htrace_bound htrace_continuous x ε).mem_nhds
        (by simpa using hε))
      hsub




theorem d004882
    (hweight : ∀ n, 0 < weight n)
    (hsum : Summable weight)
    (htrace_bound : ∀ n x, |trace n x| ≤ 1)
    (htrace_continuous : ∀ n, Continuous (trace n))
    (hseparates :
      ∀ ⦃x y : X⦄, _root_.GD.N0238.N0757.d004850 trace x y → x = y)
    {x : X} {U : Set X} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ N : ℕ, ∃ δ : ℝ, 0 < δ ∧
      {y |
        (∑ n ∈ Finset.range N,
          weight n * (trace n x - trace n y) ^ 2) < δ} ⊆ U := by
  obtain ⟨ε, hε, hcomplete⟩ :=
    _root_.GD.N0238.N0757.d004880 weight trace hweight hsum htrace_bound
      htrace_continuous hseparates hU hxU
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.1
      (_root_.GD.N0238.N0757.d004866 weight trace
        (fun n ↦ (hweight n).le) hsum htrace_bound hhalf)
  refine ⟨N, ε / 2, hhalf, ?_⟩
  intro y hy
  apply hcomplete
  change
    _root_.GD.N0238.N0757.d004846 weight trace x y < ε
  change
    (∑ n ∈ Finset.range N,
      weight n * (trace n x - trace n y) ^ 2) < ε / 2 at hy
  have htail : _root_.GD.N0238.N0757.d004847 weight trace N x y < ε / 2 :=
    hN N le_rfl x y
  rw [← _root_.GD.N0238.N0757.d004863 weight trace
    (fun n ↦ (hweight n).le) hsum htrace_bound N x y]
  linarith

end TopologicalEmbedding

section Quotient

variable (weight : ℕ → ℝ) (trace : ℕ → X → ℝ)

theorem d004883
    {x x' y : X}
    (hxx' : _root_.GD.N0238.N0757.d004850 trace x x') :
    _root_.GD.N0238.N0757.d004846 weight trace x y = _root_.GD.N0238.N0757.d004846 weight trace x' y := by
  apply tsum_congr
  intro n
  rw [hxx' n]

theorem d004884
    {x y y' : X}
    (hyy' : _root_.GD.N0238.N0757.d004850 trace y y') :
    _root_.GD.N0238.N0757.d004846 weight trace x y = _root_.GD.N0238.N0757.d004846 weight trace x y' := by
  apply tsum_congr
  intro n
  rw [hyy' n]


def d004885 :
    Quotient (_root_.GD.N0238.N0757.d004854 trace) → Quotient (_root_.GD.N0238.N0757.d004854 trace) → ℝ :=
  Quotient.lift₂ (_root_.GD.N0238.N0757.d004846 weight trace)
    (fun _ _ _ _ hxx' hyy' ↦
      (_root_.GD.N0238.N0757.d004883 weight trace hxx').trans
        (_root_.GD.N0238.N0757.d004884 weight trace hyy'))

@[simp]
theorem d004886 (x y : X) :
    _root_.GD.N0238.N0757.d004885 weight trace
      (Quotient.mk (_root_.GD.N0238.N0757.d004854 trace) x)
      (Quotient.mk (_root_.GD.N0238.N0757.d004854 trace) y) =
      _root_.GD.N0238.N0757.d004846 weight trace x y :=
  rfl

theorem d004887
    (hweight : ∀ n, 0 < weight n)
    (hsum : Summable weight)
    (htrace : ∀ n x, |trace n x| ≤ 1)
    (u v : Quotient (_root_.GD.N0238.N0757.d004854 trace)) :
    _root_.GD.N0238.N0757.d004885 weight trace u v = 0 ↔ u = v := by
  induction u using Quotient.inductionOn with
  | _ x =>
      induction v using Quotient.inductionOn with
      | _ y =>
          rw [_root_.GD.N0238.N0757.d004886,
            _root_.GD.N0238.N0757.d004874 weight trace hweight hsum htrace]
          change (_root_.GD.N0238.N0757.d004854 trace).r x y ↔
            Quotient.mk (_root_.GD.N0238.N0757.d004854 trace) x =
              Quotient.mk (_root_.GD.N0238.N0757.d004854 trace) y
          exact
            (Quotient.eq (r := _root_.GD.N0238.N0757.d004854 trace) (x := x) (y := y)).symm



theorem d004888
    (gauge : X → X → Prop)
    (hgauge :
      ∀ x y, gauge x y ↔ _root_.GD.N0238.N0757.d004850 trace x y)
    (hweight : ∀ n, 0 < weight n)
    (hsum : Summable weight)
    (htrace : ∀ n x, |trace n x| ≤ 1)
    (x y : X) :
    _root_.GD.N0238.N0757.d004846 weight trace x y = 0 ↔ gauge x y := by
  rw [_root_.GD.N0238.N0757.d004874 weight trace hweight hsum htrace,
    ← hgauge]

end Quotient

end
end N0757
end N0238
end GD
