import GD.Module1156























open Filter Topology

namespace GD
namespace N0232
namespace N0720
namespace N1064

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1117
open _root_.GD.N0232.N0720.N1122
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1302
open _root_.GD.N0232.N0720.N1448
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1482

variable {m n : ℕ}



def d018552
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (N : ℕ) : ℝ :=
  _root_.GD.N0232.N0720.N1122.d017962 m n
    (_root_.GD.N0232.N0720.N1130.d017075 m n
      ((_root_.GD.N0232.N0720.N1117.d018547 s).candidate N))


theorem d018553
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (N : ℕ) :
    0 ≤ _root_.GD.N0232.N0720.N1064.d018552 s N := by
  unfold _root_.GD.N0232.N0720.N1064.d018552
  exact _root_.GD.N0232.N0720.N1122.d017963 _



theorem d018554
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    Tendsto (_root_.GD.N0232.N0720.N1064.d018552 s) atTop
      (nhds (_root_.GD.N0232.N0720.N1477.d015749 m n s)) := by
  have h :=
    (_root_.GD.N0232.N0720.N1122.d017964
      (m := m) (n := n)).continuousAt.tendsto.comp
        (_root_.GD.N0232.N0720.N1448.d018476 s
          (_root_.GD.N0232.N0720.N1117.d018547 s))
  change Tendsto
    (fun N ↦ _root_.GD.N0232.N0720.N1122.d017962 m n
      (_root_.GD.N0232.N0720.N1130.d017075 m n
        ((_root_.GD.N0232.N0720.N1117.d018547 s).candidate N)))
    atTop (nhds (_root_.GD.N0232.N0720.N1477.d015749 m n s))
  simpa only [Function.comp_def,
    _root_.GD.N0232.N0720.N1122.d017965] using h



def d018555
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ j : ℕ, ∃ N : ℕ, j ≤ N ∧
    _root_.GD.N0232.N0720.N1064.d018552 s N ≤
      1 / ((j : ℝ) + 1)



theorem d018556
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1064.d018555 s ↔
      _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 := by
  constructor
  · intro hcert
    choose pick hpickGe hpickBound using hcert
    have hpickTop : Tendsto pick atTop atTop := by
      refine tendsto_atTop.2 (fun j ↦ ?_)
      filter_upwards [eventually_ge_atTop j] with k hk
      exact hk.trans (hpickGe k)
    have hselectedZero : Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1064.d018552 s (pick j))
        atTop (nhds 0) := by
      exact squeeze_zero
        (fun j ↦ _root_.GD.N0232.N0720.N1064.d018553 s (pick j))
        hpickBound tendsto_one_div_add_atTop_nhds_zero_nat
    have hselectedLimit :=
      (_root_.GD.N0232.N0720.N1064.d018554 s).comp
        hpickTop
    exact tendsto_nhds_unique hselectedLimit hselectedZero
  · intro henergy j
    have hlimit : Tendsto (_root_.GD.N0232.N0720.N1064.d018552 s)
        atTop (nhds 0) := by
      simpa only [henergy] using
        _root_.GD.N0232.N0720.N1064.d018554 s
    have hsmall : ∀ᶠ N in atTop,
        _root_.GD.N0232.N0720.N1064.d018552 s N <
          1 / ((j : ℝ) + 1) :=
      (tendsto_order.1 hlimit).2 _ (by positivity)
    obtain ⟨N, hNsmall, hjN⟩ :=
      (hsmall.and (eventually_ge_atTop j)).exists
    exact ⟨N, hjN, hNsmall.le⟩



theorem d018557
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    (¬ _root_.GD.N0232.N0720.N1064.d018555 s) ↔
      ∃ j : ℕ, ∀ N : ℕ, j ≤ N →
        1 / ((j : ℝ) + 1) <
          _root_.GD.N0232.N0720.N1064.d018552 s N := by
  unfold _root_.GD.N0232.N0720.N1064.d018555
  push Not
  rfl




theorem d018558
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1064.d018555 s := by
  rw [_root_.GD.N0232.N0720.N1482.d015173
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hstrict, hmaster⟩
    refine ⟨s, hstrict, ?_⟩
    apply
      (_root_.GD.N0232.N0720.N1064.d018556
        s).2
    exact
      (_root_.GD.N0232.N0720.N1477.d015755
        (m := m) (n := n) s).1 hmaster
  · rintro ⟨s, hstrict, hcert⟩
    refine ⟨s, hstrict, ?_⟩
    apply
      (_root_.GD.N0232.N0720.N1477.d015755
        (m := m) (n := n) s).2
    exact
      (_root_.GD.N0232.N0720.N1064.d018556
        s).1 hcert



theorem d018559 :
    _root_.GD.N0232.N0720.N1064.d018555
        _root_.GD.N0232.N0720.N1302.d018268 ↔
      _root_.GD.N0232.N0720.N1448.d018480 := by
  rw [_root_.GD.N0232.N0720.N1064.d018556,
    _root_.GD.N0232.N0720.N1448.d018481]

end

end N1064
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1064.d018554
#print axioms _root_.GD.N0232.N0720.N1064.d018556
#print axioms _root_.GD.N0232.N0720.N1064.d018557
#print axioms _root_.GD.N0232.N0720.N1064.d018558
#print axioms _root_.GD.N0232.N0720.N1064.d018559
