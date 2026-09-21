import GD.Module0090
import GD.Module0097
import GD.Module1065
import GD.Module1039





















open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace GD
namespace N0232
namespace N0720
namespace N1137

noncomputable section

open _root_.GD.N0230.N0598
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0646
open _root_.GD.N0230.N0708
open _root_.GD.N0230.N0712
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1133
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1461

variable {m n : ℕ}



theorem d017199
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (epsilon : ℕ → ℝ)
    (hradial : ∀ j, ‖r j‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + epsilon j)
    (hepsilon : Tendsto epsilon atTop (nhds 0)) :
    Bornology.IsBounded (Set.range r) := by
  obtain ⟨M, hM⟩ :=
    (Metric.isBounded_range_of_tendsto epsilon hepsilon).exists_norm_le
  have hM_nonneg : 0 ≤ M := by
    exact (norm_nonneg (epsilon 0)).trans (hM (epsilon 0) ⟨0, rfl⟩)
  rw [isBounded_iff_forall_norm_le]
  refine ⟨Real.sqrt
    (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + M), ?_⟩
  intro q hq
  obtain ⟨j, rfl⟩ := hq
  have hepsilon_le : epsilon j ≤ M := by
    have habs : epsilon j ≤ ‖epsilon j‖ := by
      simpa [Real.norm_eq_abs] using le_abs_self (epsilon j)
    exact habs.trans (hM (epsilon j) ⟨j, rfl⟩)
  have hbase_nonneg :
      0 ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + M := by
    positivity
  have hsqrt_sq :
      (Real.sqrt
        (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + M)) ^ 2 =
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + M :=
    Real.sq_sqrt hbase_nonneg
  nlinarith [hradial j, norm_nonneg (r j),
    Real.sqrt_nonneg
      (‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + M)]







theorem d017200
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (capSlack : ℕ → ℝ≥0)
    (epsilon : ℕ → ℝ)
    (hprefix : ∀ j i, i < j →
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1133.d016566 i) (r j) ≤
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1133.d016566 i) s.value + capSlack j)
    (hcapSlack : Tendsto capSlack atTop (nhds 0))
    (hradial : ∀ j, ‖r j‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + epsilon j)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hscaleTwo : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015228 m n (r j) - r j‖)
      atTop (nhds 0))
    (hshiftOneScaleThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n (r j) - r j‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  letI : MeasurableSpace.CountablyGenerated (_root_.GD.N0232.N0720.N1080.d014170 m n) := by
    infer_instance
  letI : SFinite (_root_.GD.N0232.N0720.N1080.d014172 m n) := inferInstance
  letI : IsSeparable (_root_.GD.N0232.N0720.N1080.d014172 m n) := inferInstance
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  letI : SecondCountableTopology
      (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) := inferInstance
  letI : TopologicalSpace.SeparableSpace
      (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  have hrBounded : Bornology.IsBounded (Set.range r) :=
    _root_.GD.N0232.N0720.N1137.d017199 s r epsilon hradial hepsilon
  obtain ⟨k, hk, x, hweak⟩ :=
    _root_.GD.N0230.N0646.d000550
      (E := _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) r hrBounded
  have hweakTop :=
    _root_.GD.N0230.N0570.d001187
      hweak
  have hxSampled :
      x ∈ _root_.GD.N0230.N0598.d000587 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        (fun theta ↦ _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value)
        _root_.GD.N0232.N0720.N1133.d016566 := by
    intro i
    let theta : _root_.GD.N0232.N0720.N1080.d014168 := _root_.GD.N0232.N0720.N1133.d016566 i
    change _root_.GD.N0232.N0720.N1080.d014182 m n theta x ≤ _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value
    refine ENNReal.le_of_forall_pos_le_add ?_
    intro eta heta _hseedFinite
    have hindex : ∀ᶠ j in atTop, i < k j := by
      have hlarge : ∀ᶠ j in atTop, i + 1 ≤ k j :=
        (tendsto_atTop.1 hk) (i + 1)
      exact hlarge.mono fun _ hj ↦ Nat.lt_of_succ_le hj
    have hslack : ∀ᶠ j in atTop, capSlack (k j) < eta :=
      (tendsto_order.1 (hcapSlack.comp hk)).2 eta heta
    have heventually : ∀ᶠ j in atTop,
        _root_.GD.N0230.N0712.d001258 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
            theta.location
            (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (r (k j))) ≤
          _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value + (eta : ENNReal) := by
      filter_upwards [hindex, hslack] with j hj hslackj
      have hrow := hprefix (k j) i hj
      have hcoe :
          ((capSlack (k j) : ℝ≥0) : ENNReal) ≤ (eta : ENNReal) := by
        exact ENNReal.coe_le_coe.mpr hslackj.le
      have hcapBound :
          _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value + (capSlack (k j) : ENNReal) ≤
            _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value + (eta : ENNReal) := by
        simpa only [add_comm] using
          (add_le_add_left hcoe (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value))
      have hbound := hrow.trans hcapBound
      simpa [theta, _root_.GD.N0230.N0712.d001258, _root_.GD.N0232.N0720.N1080.d014182] using hbound
    have hxSublevel :=
      (_root_.GD.N0230.N0712.d001259
        (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
        (_root_.GD.N0232.N0720.N1080.d014173 m n theta)
        theta.location
        (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value + (eta : ENNReal))).mem_of_tendsto
          hweakTop heventually
    simpa [_root_.GD.N0230.N0712.d001258, _root_.GD.N0232.N0720.N1080.d014182] using hxSublevel
  have hxOuter : x ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value := by
    rw [← _root_.GD.N0232.N0720.N1133.d016590 m n s]
    exact hxSampled
  apply _root_.GD.N0232.N0720.N1461.d015688
    m n hm hn s hstrict (fun j ↦ r (k j)) x (fun j ↦ epsilon (k j))
      hweak hxOuter
  · exact fun j ↦ hradial (k j)
  · exact hepsilon.comp hk
  · exact hscaleTwo.comp hk
  · exact hshiftOneScaleThree.comp hk


theorem d017201
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (epsilon : ℕ → ℝ)
    (hprefix : ∀ j i, i < j →
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1133.d016566 i) (r j) ≤
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1133.d016566 i) s.value)
    (hradial : ∀ j, ‖r j‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + epsilon j)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hscaleTwo : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015228 m n (r j) - r j‖)
      atTop (nhds 0))
    (hshiftOneScaleThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n (r j) - r j‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply _root_.GD.N0232.N0720.N1137.d017200
    hm hn s hstrict r (fun _ ↦ 0) epsilon
  · intro j i hij
    simpa using hprefix j i hij
  · exact tendsto_const_nhds
  · exact hradial
  · exact hepsilon
  · exact hscaleTwo
  · exact hshiftOneScaleThree




theorem d017202
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (capSlack : ℕ → ℝ≥0)
    (hprefix : ∀ j i, i < j →
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1133.d016566 i)
          (_root_.GD.N0232.N0720.N1130.d017075 m n (candidate j)) ≤
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1133.d016566 i) s.value + capSlack j)
    (hcapSlack : Tendsto capSlack atTop (nhds 0))
    (hradial : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017077 m n s (candidate j))
      atTop (nhds 0))
    (hscaleTwo : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017078 m n (candidate j))
      atTop (nhds 0))
    (hshiftOneScaleThree : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017079 m n (candidate j))
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply _root_.GD.N0232.N0720.N1137.d017200
    hm hn s hstrict
    (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (candidate j)) capSlack
    (fun j ↦ _root_.GD.N0232.N0720.N1130.d017077 m n s (candidate j))
      hprefix hcapSlack
  · intro j
    have hreserve :=
      _root_.GD.N0232.N0720.N1126.d016437
        s (candidate j).packet (candidate j).weight
          (candidate j).weight_nonneg
    have hdistanceNonneg :
        0 ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value -
          _root_.GD.N0232.N0720.N1130.d017075 m n (candidate j)‖ ^ 2 :=
      sq_nonneg _
    have hgapLe :
        ‖_root_.GD.N0232.N0720.N1130.d017075 m n (candidate j)‖ ^ 2 -
            _root_.GD.N0232.N0720.N1126.d016432 s
              (candidate j).packet (candidate j).weight ≤
      _root_.GD.N0232.N0720.N1130.d017077 m n s (candidate j) := by
      exact le_max_left _ _
    dsimp only [_root_.GD.N0232.N0720.N1130.d017075] at hreserve hdistanceNonneg hgapLe ⊢
    linarith
  · exact hradial
  · simpa [_root_.GD.N0232.N0720.N1130.d017078] using hscaleTwo
  · simpa [_root_.GD.N0232.N0720.N1130.d017079] using hshiftOneScaleThree




def d017203 (N : ℕ) : ℝ :=
  1 / ((N : ℝ) + 1)

theorem d017204 (N : ℕ) :
    0 ≤ _root_.GD.N0232.N0720.N1137.d017203 N := by
  unfold _root_.GD.N0232.N0720.N1137.d017203
  positivity


def d017205 (N : ℕ) : ℝ≥0 :=
  ⟨_root_.GD.N0232.N0720.N1137.d017203 N, _root_.GD.N0232.N0720.N1137.d017204 N⟩

theorem d017206 :
    Tendsto _root_.GD.N0232.N0720.N1137.d017205 atTop (nhds 0) := by
  apply NNReal.tendsto_coe.1
  change Tendsto (fun N : ℕ ↦ 1 / ((N : ℝ) + 1)) atTop (nhds 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat




def d017207
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (N : ℕ)
    (candidate : _root_.GD.N0232.N0720.N1130.d017074) : Prop :=
  (∀ i, i < N →
    _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1133.d016566 i)
        (_root_.GD.N0232.N0720.N1130.d017075 m n candidate) ≤
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1133.d016566 i) s.value +
        _root_.GD.N0232.N0720.N1137.d017205 N) ∧
  _root_.GD.N0232.N0720.N1130.d017077 m n s candidate ≤
      _root_.GD.N0232.N0720.N1137.d017203 N ∧
  _root_.GD.N0232.N0720.N1130.d017078 m n candidate ≤
      _root_.GD.N0232.N0720.N1137.d017203 N ∧
  _root_.GD.N0232.N0720.N1130.d017079 m n candidate ≤
      _root_.GD.N0232.N0720.N1137.d017203 N



def d017208
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ N : ℕ, ∃ candidate : _root_.GD.N0232.N0720.N1130.d017074,
    _root_.GD.N0232.N0720.N1137.d017207 s N candidate



theorem d017209
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hsmall : _root_.GD.N0232.N0720.N1137.d017208 s) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  classical
  choose candidate hcandidate using hsmall
  apply
    _root_.GD.N0232.N0720.N1137.d017202
      hm hn s hstrict candidate _root_.GD.N0232.N0720.N1137.d017205
  · intro j i hij
    exact (hcandidate j).1 i hij
  · exact _root_.GD.N0232.N0720.N1137.d017206
  · apply squeeze_zero
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017082 m n s (candidate j))
      (fun j ↦ (hcandidate j).2.1)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  · apply squeeze_zero
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017083 m n (candidate j))
      (fun j ↦ (hcandidate j).2.2.1)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  · apply squeeze_zero
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017084 m n (candidate j))
      (fun j ↦ (hcandidate j).2.2.2)
    exact tendsto_one_div_add_atTop_nhds_zero_nat




theorem d017210
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    ¬ _root_.GD.N0232.N0720.N1137.d017208 s ↔
      ∃ N : ℕ, ∀ candidate : _root_.GD.N0232.N0720.N1130.d017074,
        ¬ _root_.GD.N0232.N0720.N1137.d017207 s N candidate := by
  classical
  simp only [_root_.GD.N0232.N0720.N1137.d017208, not_forall,
    not_exists]

end

end N1137
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1137.d017200
#print axioms _root_.GD.N0232.N0720.N1137.d017201
#print axioms _root_.GD.N0232.N0720.N1137.d017202
#print axioms _root_.GD.N0232.N0720.N1137.d017209
#print axioms _root_.GD.N0232.N0720.N1137.d017210
