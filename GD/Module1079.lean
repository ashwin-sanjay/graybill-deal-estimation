import GD.Module1075
import GD.Module0994



















open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1141

noncomputable section

open _root_.GD.N0230.N0570
open _root_.GD.N0230.N0598
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0646
open _root_.GD.N0230.N0685
open _root_.GD.N0230.N0712
open _root_.GD.N0230.N0714
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1133
open _root_.GD.N0232.N0720.N1137
open _root_.GD.N0232.N0720.N1139
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1482

variable {m n : ℕ}






theorem d017277
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (N : ℕ) :
    ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value -
          _root_.GD.N0232.N0720.N1139.d017232 s N‖ ^ 2 +
        ‖_root_.GD.N0232.N0720.N1139.d017232 s N‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
  have hterminal : _root_.GD.N0232.N0720.N1159.d014633 m n s.value ∈
      _root_.GD.N0232.N0720.N1139.d017214 s (_root_.GD.N0232.N0720.N1139.d017231 N)
        (_root_.GD.N0232.N0720.N1137.d017205 N) := by
    intro i
    exact ((_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
      (_root_.GD.N0232.N0720.N1139.d017231 N i)).trans (le_add_of_nonneg_right bot_le)
  simpa only [_root_.GD.N0232.N0720.N1139.d017232, sub_zero, norm_neg] using
    (_root_.GD.N0230.N0685.d000512
      (_root_.GD.N0232.N0720.N1139.d017219
        s (_root_.GD.N0232.N0720.N1139.d017231 N) (_root_.GD.N0232.N0720.N1137.d017205 N))
      hterminal)





theorem d017278
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    Tendsto (_root_.GD.N0232.N0720.N1139.d017232 s) atTop
      (nhds (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)) := by
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
  let p : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1139.d017232 s
  let P : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  have hradial : ∀ N, ‖p N‖ ^ 2 ≤ ‖P‖ ^ 2 + (0 : ℝ) := by
    intro N
    have htax := _root_.GD.N0232.N0720.N1141.d017277 s N
    dsimp only [p, P]
    nlinarith [sq_nonneg
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value -
        _root_.GD.N0232.N0720.N1139.d017232 s N‖]
  have hpBounded : Bornology.IsBounded (Set.range p) :=
    _root_.GD.N0232.N0720.N1137.d017199 s p (fun _ ↦ 0)
      hradial tendsto_const_nhds
  apply tendsto_of_subseq_tendsto
  intro k hk
  have hpkBounded : Bornology.IsBounded (Set.range (fun j ↦ p (k j))) :=
    hpBounded.subset (by
      rintro _ ⟨j, rfl⟩
      exact ⟨k j, rfl⟩)
  obtain ⟨l, hl, x, hweak⟩ :=
    _root_.GD.N0230.N0646.d000550
      (E := _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (fun j ↦ p (k j)) hpkBounded
  have hkl : Tendsto (fun j ↦ k (l j)) atTop atTop := hk.comp hl
  have hweakTop := _root_.GD.N0230.N0570.d001187 hweak
  have hxSampled :
      x ∈ _root_.GD.N0230.N0598.d000587 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        (fun theta ↦ _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value)
        _root_.GD.N0232.N0720.N1133.d016566 := by
    intro i
    let theta : _root_.GD.N0232.N0720.N1080.d014168 := _root_.GD.N0232.N0720.N1133.d016566 i
    change _root_.GD.N0232.N0720.N1080.d014182 m n theta x ≤ _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value
    refine ENNReal.le_of_forall_pos_le_add ?_
    intro eta heta _hseedFinite
    have hindex : ∀ᶠ j in atTop, i < k (l j) := by
      have hlarge : ∀ᶠ j in atTop, i + 1 ≤ k (l j) :=
        (tendsto_atTop.1 hkl) (i + 1)
      exact hlarge.mono fun _ hj ↦ Nat.lt_of_succ_le hj
    have hslack : ∀ᶠ j in atTop,
        _root_.GD.N0232.N0720.N1137.d017205 (k (l j)) < eta :=
      (tendsto_order.1
        (_root_.GD.N0232.N0720.N1137.d017206.comp hkl)).2 eta heta
    have heventually : ∀ᶠ j in atTop,
        _root_.GD.N0230.N0712.d001258 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
            theta.location
            (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
              (p (k (l j)))) ≤
          _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value + (eta : ENNReal) := by
      filter_upwards [hindex, hslack] with j hj hslackj
      have hrow :=
        (_root_.GD.N0232.N0720.N1139.d017219
          s (_root_.GD.N0232.N0720.N1139.d017231 (k (l j)))
            (_root_.GD.N0232.N0720.N1137.d017205 (k (l j)))).1
          ⟨i, hj⟩
      have hcoe :
          ((_root_.GD.N0232.N0720.N1137.d017205 (k (l j)) : ℝ≥0) : ENNReal) ≤
            (eta : ENNReal) :=
        ENNReal.coe_le_coe.mpr hslackj.le
      have hcapBound :
          _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value +
              (_root_.GD.N0232.N0720.N1137.d017205 (k (l j)) : ENNReal) ≤
            _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value + (eta : ENNReal) :=
        by
          simpa only [add_comm] using
            (add_le_add_left hcoe (_root_.GD.N0232.N0720.N1080.d014182 m n theta s.value))
      have hbound : _root_.GD.N0232.N0720.N1080.d014182 m n theta (p (k (l j))) ≤
          _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value + (eta : ENNReal) := by
        have hrow' : _root_.GD.N0232.N0720.N1080.d014182 m n theta (p (k (l j))) ≤
            _root_.GD.N0232.N0720.N1080.d014182 m n theta s.value +
              (_root_.GD.N0232.N0720.N1137.d017205 (k (l j)) : ENNReal) := by
          simpa [p, theta, _root_.GD.N0232.N0720.N1139.d017231,
            _root_.GD.N0232.N0720.N1139.d017232] using hrow
        exact hrow'.trans hcapBound
      simpa [_root_.GD.N0230.N0712.d001258, _root_.GD.N0232.N0720.N1080.d014182] using hbound
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
  refine ⟨l, ?_⟩
  have hstrong := _root_.GD.N0230.N0714.d001265
    (_root_.GD.N0232.N0720.N1133.d016601 m n s.value)
    hweak hxOuter (fun j ↦ hradial (k (l j))) tendsto_const_nhds
  simpa only [p, P] using hstrong





theorem d017279
    {E : Type*} [NormedAddCommGroup E]
    (T : E → E) {C : ℝ≥0} (hT : LipschitzWith C T) (x y : E) :
    |‖T x - x‖ - ‖T y - y‖| ≤ ((C : ℝ) + 1) * ‖x - y‖ := by
  calc
    |‖T x - x‖ - ‖T y - y‖| ≤
        ‖(T x - x) - (T y - y)‖ := abs_norm_sub_norm_le _ _
    _ ≤ ‖T x - T y‖ + ‖x - y‖ := by
      have hdecomp : (T x - x) - (T y - y) =
          (T x - T y) + (y - x) := by abel
      rw [hdecomp]
      simpa only [norm_sub_rev] using norm_add_le (T x - T y) (y - x)
    _ ≤ (C : ℝ) * ‖x - y‖ + ‖x - y‖ := by
      gcongr
      simpa [dist_eq_norm] using hT.dist_le_mul x y
    _ = ((C : ℝ) + 1) * ‖x - y‖ := by ring



theorem d017280
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    {g : _root_.GD.N0232.N0720.N1482.d015118}
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g) :
    Tendsto
      (fun N ↦
        ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate
            (_root_.GD.N0232.N0720.N1139.d017232 s N) -
          _root_.GD.N0232.N0720.N1139.d017232 s N‖)
      atTop
      (nhds
        ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate
            (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) -
          _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖) := by
  have hp := _root_.GD.N0232.N0720.N1141.d017278 s
  have hT :=
    (_root_.GD.N0232.N0720.N1146.d015216 m n certificate).continuous
      |>.continuousAt.tendsto.comp hp
  exact (hT.sub hp).norm


def d017281
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (N : ℕ) : ℝ :=
  ‖_root_.GD.N0232.N0720.N1146.d015228 m n
      (_root_.GD.N0232.N0720.N1139.d017232 s N) -
    _root_.GD.N0232.N0720.N1139.d017232 s N‖ ^ 2 +
  ‖_root_.GD.N0232.N0720.N1146.d015229 m n
      (_root_.GD.N0232.N0720.N1139.d017232 s N) -
    _root_.GD.N0232.N0720.N1139.d017232 s N‖ ^ 2



theorem d017282
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    Tendsto (_root_.GD.N0232.N0720.N1141.d017281 s) atTop
      (nhds (_root_.GD.N0232.N0720.N1477.d015749 m n s)) := by
  have htwo :=
    _root_.GD.N0232.N0720.N1141.d017280 s
      (_root_.GD.N0232.N0720.N1146.d015221 m n)
  have hthree :=
    _root_.GD.N0232.N0720.N1141.d017280 s
      (_root_.GD.N0232.N0720.N1146.d015222 m n)
  have hPmem : _root_.GD.N0232.N0720.N1159.d014633 m n s.value ∈
      _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
    (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have hPfinite : _root_.GD.N0232.N0720.N1159.d014637 m n
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hPmem
  have htwoEq :
      _root_.GD.N0232.N0720.N1146.d015212 m n
          (_root_.GD.N0232.N0720.N1146.d015221 m n)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) -
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value =
      _root_.GD.N0232.N0720.N1477.d015744 m n s _root_.GD.N0232.N0720.N1482.d015130 := by
    rw [_root_.GD.N0232.N0720.N1146.d015218
      m n (_root_.GD.N0232.N0720.N1146.d015221 m n)
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hPfinite]
    rfl
  have hthreeEq :
      _root_.GD.N0232.N0720.N1146.d015212 m n
          (_root_.GD.N0232.N0720.N1146.d015222 m n)
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) -
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value =
      _root_.GD.N0232.N0720.N1477.d015744 m n s _root_.GD.N0232.N0720.N1482.d015131 := by
    rw [_root_.GD.N0232.N0720.N1146.d015218
      m n (_root_.GD.N0232.N0720.N1146.d015222 m n)
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) hPfinite]
    rfl
  have hsum := (htwo.pow 2).add (hthree.pow 2)
  change Tendsto
    (fun N ↦
      ‖_root_.GD.N0232.N0720.N1146.d015212 m n
          (_root_.GD.N0232.N0720.N1146.d015221 m n)
          (_root_.GD.N0232.N0720.N1139.d017232 s N) -
        _root_.GD.N0232.N0720.N1139.d017232 s N‖ ^ 2 +
      ‖_root_.GD.N0232.N0720.N1146.d015212 m n
          (_root_.GD.N0232.N0720.N1146.d015222 m n)
          (_root_.GD.N0232.N0720.N1139.d017232 s N) -
        _root_.GD.N0232.N0720.N1139.d017232 s N‖ ^ 2)
    atTop
    (nhds
      (‖_root_.GD.N0232.N0720.N1477.d015744 m n s _root_.GD.N0232.N0720.N1482.d015130‖ ^ 2 +
        ‖_root_.GD.N0232.N0720.N1477.d015744 m n s _root_.GD.N0232.N0720.N1482.d015131‖ ^ 2))
  simpa only [htwoEq, hthreeEq] using hsum





theorem d017283
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    (∃ c : ℝ, 0 < c ∧
      ∀ᶠ N in atTop, c ≤ _root_.GD.N0232.N0720.N1141.d017281 s N) ↔
      0 < _root_.GD.N0232.N0720.N1477.d015749 m n s := by
  let E := _root_.GD.N0232.N0720.N1477.d015749 m n s
  have hlimit : Tendsto (_root_.GD.N0232.N0720.N1141.d017281 s) atTop
      (nhds E) :=
    _root_.GD.N0232.N0720.N1141.d017282 s
  constructor
  · rintro ⟨c, hc, hfloor⟩
    have hcE : c ≤ E := ge_of_tendsto hlimit hfloor
    exact hc.trans_le hcE
  · intro hE
    refine ⟨E / 2, half_pos hE, ?_⟩
    exact ((tendsto_order.1 hlimit).1 (E / 2) (by linarith)).mono
      fun _ h ↦ h.le





theorem d017284
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    (∃ c : ℝ, 0 < c ∧
      ∀ᶠ N in atTop, c ≤ _root_.GD.N0232.N0720.N1141.d017281 s N) ↔
      ¬ (_root_.GD.N0232.N0720.N1159.d014645 m n s _root_.GD.N0232.N0720.N1482.d015130
            (_root_.GD.N0232.N0720.N1159.d014646 m n s) =
          _root_.GD.N0232.N0720.N1159.d014646 m n s ∧
        _root_.GD.N0232.N0720.N1159.d014645 m n s _root_.GD.N0232.N0720.N1482.d015131
            (_root_.GD.N0232.N0720.N1159.d014646 m n s) =
          _root_.GD.N0232.N0720.N1159.d014646 m n s) := by
  rw [_root_.GD.N0232.N0720.N1141.d017283]
  have hnonneg : 0 ≤ _root_.GD.N0232.N0720.N1477.d015749 m n s := by
    unfold _root_.GD.N0232.N0720.N1477.d015749
    positivity
  constructor
  · intro hpos hfixed
    have hzero :=
      (_root_.GD.N0232.N0720.N1477.d015754 m n s).2 hfixed
    linarith
  · intro hnonfixed
    have hne : _root_.GD.N0232.N0720.N1477.d015749 m n s ≠ 0 := by
      intro hzero
      exact hnonfixed
        ((_root_.GD.N0232.N0720.N1477.d015754 m n s).1 hzero)
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)

end

end N1141
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1141.d017278
#print axioms _root_.GD.N0232.N0720.N1141.d017280
#print axioms _root_.GD.N0232.N0720.N1141.d017282
#print axioms _root_.GD.N0232.N0720.N1141.d017284
