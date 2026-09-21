import GD.Module1114
import GD.Module1076
import GD.Module1157
import GD.Module1152





















open Filter MeasureTheory Set Topology

namespace GD
namespace N0232
namespace N0720
namespace N1202

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1033
open _root_.GD.N0232.N0720.N1054
open _root_.GD.N0232.N0720.N1055
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1103
open _root_.GD.N0232.N0720.N1122
open _root_.GD.N0232.N0720.N1117
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1158
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1302
open _root_.GD.N0232.N0720.N1448
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1482

variable {m n : ℕ}








theorem d018573
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (henergy : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0) :
    _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) := by
  let p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  have hpFinite : _root_.GD.N0232.N0720.N1159.d014637 m n p :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s p
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have hreference :
      _root_.GD.N0232.N0720.N1146.d015228 m n p = p ∧
        _root_.GD.N0232.N0720.N1146.d015229 m n p = p := by
    simpa only [p] using
      (_root_.GD.N0232.N0720.N1158.d018490 s).1 henergy
  have hTwo : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hpFinite = p := by
    rw [← _root_.GD.N0232.N0720.N1146.d015218 m n
      (_root_.GD.N0232.N0720.N1146.d015221 m n) p hpFinite]
    exact hreference.1
  have hThree :
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hpFinite = p := by
    rw [← _root_.GD.N0232.N0720.N1146.d015218 m n
      (_root_.GD.N0232.N0720.N1146.d015222 m n) p hpFinite]
    exact hreference.2
  simpa only [p] using
    _root_.GD.N0232.N0720.N1033.d017927
      m n p hpFinite hTwo hThree


theorem d018574
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hmaster : _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0) :
    _root_.GD.N0232.N0720.N1159.d014638 m n (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) := by
  apply _root_.GD.N0232.N0720.N1202.d018573
    s
  exact
    (_root_.GD.N0232.N0720.N1477.d015755
      (m := m) (n := n) s).1
      hmaster






theorem d018575
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hconv : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (candidate j))
      atTop (nhds p))
    (hcharacter : _root_.GD.N0232.N0720.N1159.d014638 m n p)
    (B : ℝ) (N : ℕ) :
    ∃ j : ℕ, N ≤ j ∧
      B < _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet := by
  have hconvTail : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (candidate (k + N)))
      atTop (nhds p) :=
    (tendsto_add_atTop_iff_nat N).2 hconv
  obtain ⟨k, hk⟩ :=
    _root_.GD.N0232.N0720.N1055.d017246
      (fun r ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (candidate (r + N)))
      p hconvTail hcharacter B
  have hnotle :
      ¬ _root_.GD.N0232.N0720.N1126.d016418 (candidate (k + N)).packet ≤ B := by
    intro hle
    apply hk
    filter_upwards [_root_.GD.N0232.N0720.N1054.d016444
        (m := m) (n := n) (candidate (k + N)).packet
          (candidate (k + N)).weight
          (candidate (k + N)).weight_nonneg] with omega homega
    exact homega.trans hle
  exact ⟨k + N, Nat.le_add_left N k, lt_of_not_ge hnotle⟩









theorem d018576
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hconv : Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (candidate j))
      atTop (nhds p))
    (hcharacter : _root_.GD.N0232.N0720.N1159.d014638 m n p) :
    Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet)
      atTop atTop := by
  refine tendsto_atTop.2 (fun B ↦ ?_)
  have hstrict : ∀ᶠ j in atTop,
      B < _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet := by
    by_contra hnot
    have hfrequent : ∃ᶠ j in atTop,
        _root_.GD.N0232.N0720.N1126.d016418 (candidate j).packet ≤ B := by
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
    filter_upwards [_root_.GD.N0232.N0720.N1054.d016444
        (m := m) (n := n) (candidate (extraction k)).packet
          (candidate (extraction k)).weight
          (candidate (extraction k)).weight_nonneg] with omega homega
    exact homega.trans (hbound k)
  exact hstrict.mono fun _ hj ↦ hj.le




def d018577
    {s : _root_.GD.N0232.N0720.N1159.d014639 m n} (row : _root_.GD.N0232.N0720.N1103.d018281 s) : Prop :=
  ∀ B : ℝ, ∀ N : ℕ, ∃ j : ℕ, N ≤ j ∧
    B < _root_.GD.N0232.N0720.N1126.d016418 (row.candidate j).packet




theorem d018578
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (henergy : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0)
    (row : _root_.GD.N0232.N0720.N1103.d018281 s) :
    _root_.GD.N0232.N0720.N1202.d018577 row := by
  intro B N
  exact
    _root_.GD.N0232.N0720.N1202.d018575
      row.candidate (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
      (_root_.GD.N0232.N0720.N1448.d018476 s row)
      (_root_.GD.N0232.N0720.N1202.d018573
        s henergy)
      B N


theorem d018579
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hmaster : _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0)
    (row : _root_.GD.N0232.N0720.N1103.d018281 s) :
    _root_.GD.N0232.N0720.N1202.d018577 row := by
  apply
    _root_.GD.N0232.N0720.N1202.d018578
      s _ row
  exact
    (_root_.GD.N0232.N0720.N1477.d015755
      (m := m) (n := n) s).1
      hmaster




theorem d018580
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (henergy : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0)
    (row : _root_.GD.N0232.N0720.N1103.d018281 s) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016418 (row.candidate j).packet)
      atTop atTop := by
  exact
    _root_.GD.N0232.N0720.N1202.d018576
      row.candidate (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
      (_root_.GD.N0232.N0720.N1448.d018476 s row)
      (_root_.GD.N0232.N0720.N1202.d018573
        s henergy)


theorem d018581
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hmaster : _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0)
    (row : _root_.GD.N0232.N0720.N1103.d018281 s) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016418 (row.candidate j).packet)
      atTop atTop := by
  apply
    _root_.GD.N0232.N0720.N1202.d018580
      s _ row
  exact
    (_root_.GD.N0232.N0720.N1477.d015755
      (m := m) (n := n) s).1
      hmaster










theorem d018582
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hendpoint : _root_.GD.N0232.N0720.N1159.d014661 m n) :
    ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
      _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
        (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
      ∀ row : _root_.GD.N0232.N0720.N1103.d018281 s,
        Tendsto
          (fun j ↦ _root_.GD.N0232.N0720.N1126.d016418 (row.candidate j).packet)
          atTop atTop := by
  obtain ⟨s, hstrict, hmaster⟩ :=
    (_root_.GD.N0232.N0720.N1482.d015173
      (m := m) (n := n) hm hn).mp hendpoint
  refine ⟨s, hstrict, ?_⟩
  intro row
  exact
    _root_.GD.N0232.N0720.N1202.d018581
      s hmaster row






theorem d018583
    (hrecovery : _root_.GD.N0232.N0720.N1448.d018480)
    (row : _root_.GD.N0232.N0720.N1103.d018281
      _root_.GD.N0232.N0720.N1302.d018268) :
    _root_.GD.N0232.N0720.N1202.d018577 row := by
  apply
    _root_.GD.N0232.N0720.N1202.d018578
      _root_.GD.N0232.N0720.N1302.d018268 _ row
  exact
    _root_.GD.N0232.N0720.N1448.d018481.mp
      hrecovery



theorem d018584
    (hrecovery : _root_.GD.N0232.N0720.N1448.d018480) :
    _root_.GD.N0232.N0720.N1202.d018577
      (_root_.GD.N0232.N0720.N1117.d018547
        _root_.GD.N0232.N0720.N1302.d018268) := by
  exact
    _root_.GD.N0232.N0720.N1202.d018583
      hrecovery
      (_root_.GD.N0232.N0720.N1117.d018547
        _root_.GD.N0232.N0720.N1302.d018268)



theorem d018585
    (hrecovery : _root_.GD.N0232.N0720.N1448.d018480)
    (row : _root_.GD.N0232.N0720.N1103.d018281
      _root_.GD.N0232.N0720.N1302.d018268) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016418 (row.candidate j).packet)
      atTop atTop := by
  apply
    _root_.GD.N0232.N0720.N1202.d018580
      _root_.GD.N0232.N0720.N1302.d018268 _ row
  exact
    _root_.GD.N0232.N0720.N1448.d018481.mp
      hrecovery


theorem d018586
    (hrecovery : _root_.GD.N0232.N0720.N1448.d018480) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016418
        ((_root_.GD.N0232.N0720.N1117.d018547
          _root_.GD.N0232.N0720.N1302.d018268).candidate
            j).packet)
      atTop atTop := by
  exact
    _root_.GD.N0232.N0720.N1202.d018585
      hrecovery
      (_root_.GD.N0232.N0720.N1117.d018547
        _root_.GD.N0232.N0720.N1302.d018268)

end

end N1202
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1202.d018573
#print axioms _root_.GD.N0232.N0720.N1202.d018574
#print axioms _root_.GD.N0232.N0720.N1202.d018575
#print axioms _root_.GD.N0232.N0720.N1202.d018576
#print axioms _root_.GD.N0232.N0720.N1202.d018578
#print axioms _root_.GD.N0232.N0720.N1202.d018579
#print axioms _root_.GD.N0232.N0720.N1202.d018580
#print axioms _root_.GD.N0232.N0720.N1202.d018581
#print axioms _root_.GD.N0232.N0720.N1202.d018582
#print axioms _root_.GD.N0232.N0720.N1202.d018583
#print axioms _root_.GD.N0232.N0720.N1202.d018584
#print axioms _root_.GD.N0232.N0720.N1202.d018585
#print axioms _root_.GD.N0232.N0720.N1202.d018586
