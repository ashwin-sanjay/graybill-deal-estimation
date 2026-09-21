import GD.Module1079
import GD.Module1152





































open Filter Topology

namespace GD
namespace N0232
namespace N0720
namespace N1079

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1103
open _root_.GD.N0232.N0720.N1122
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1141
open _root_.GD.N0232.N0720.N1139
open _root_.GD.N0232.N0720.N1158
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1482

variable {m n : ℕ}






def d018506
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  Tendsto (_root_.GD.N0232.N0720.N1141.d017281 s) atTop (nhds 0)





theorem d018507
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1079.d018506 s ↔
      _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 := by
  constructor
  · intro hnull
    exact tendsto_nhds_unique
      (_root_.GD.N0232.N0720.N1141.d017282
        s)
      hnull
  · intro hzero
    simpa only [_root_.GD.N0232.N0720.N1079.d018506, hzero] using
      (_root_.GD.N0232.N0720.N1141.d017282
        s)



theorem d018508
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1079.d018506 s ↔
      _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 := by
  calc
    _root_.GD.N0232.N0720.N1079.d018506 s ↔
        _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 :=
      _root_.GD.N0232.N0720.N1079.d018507 s
    _ ↔ _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 :=
      (_root_.GD.N0232.N0720.N1477.d015755
        m n s).symm





theorem d018509
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1079.d018506 s ↔
      _root_.GD.N0232.N0720.N1158.d018487 s := by
  calc
    _root_.GD.N0232.N0720.N1079.d018506 s ↔
        _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 :=
      _root_.GD.N0232.N0720.N1079.d018507 s
    _ ↔ _root_.GD.N0232.N0720.N1158.d018487 s :=
      (_root_.GD.N0232.N0720.N1158.d018497
        s).symm



theorem d018510
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1079.d018506 s ↔
      ∀ row : _root_.GD.N0232.N0720.N1103.d018281 s,
        Tendsto
          (fun j ↦ _root_.GD.N0232.N0720.N1122.d017962 m n
            (_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j)))
          atTop (nhds 0) := by
  calc
    _root_.GD.N0232.N0720.N1079.d018506 s ↔
        _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 :=
      _root_.GD.N0232.N0720.N1079.d018507 s
    _ ↔ ∀ row : _root_.GD.N0232.N0720.N1103.d018281 s,
          Tendsto
            (fun j ↦ _root_.GD.N0232.N0720.N1122.d017962 m n
              (_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j)))
            atTop (nhds 0) :=
      _root_.GD.N0232.N0720.N1158.d018498 s




theorem d018511
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1079.d018506 s ↔
      _root_.GD.N0232.N0720.N1158.d018488 s := by
  calc
    _root_.GD.N0232.N0720.N1079.d018506 s ↔
        _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 :=
      _root_.GD.N0232.N0720.N1079.d018507 s
    _ ↔ _root_.GD.N0232.N0720.N1158.d018488 s :=
      (_root_.GD.N0232.N0720.N1158.d018499 s).symm




theorem d018512
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1079.d018506 s ↔
      _root_.GD.N0232.N0720.N1158.d018485 s := by
  calc
    _root_.GD.N0232.N0720.N1079.d018506 s ↔
        _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 :=
      _root_.GD.N0232.N0720.N1079.d018507 s
    _ ↔ _root_.GD.N0232.N0720.N1158.d018485 s :=
      (_root_.GD.N0232.N0720.N1158.d018493 s).symm









theorem d018513
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
          _root_.GD.N0232.N0720.N1079.d018506 s := by
  rw [_root_.GD.N0232.N0720.N1482.d015173
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hstrict, hmaster⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0720.N1079.d018508 s).2
        hmaster⟩
  · rintro ⟨s, hstrict, hstatistical⟩
    exact ⟨s, hstrict,
      (_root_.GD.N0232.N0720.N1079.d018508 s).1
        hstatistical⟩

end

end N1079
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1079.d018507
#print axioms _root_.GD.N0232.N0720.N1079.d018508
#print axioms _root_.GD.N0232.N0720.N1079.d018509
#print axioms _root_.GD.N0232.N0720.N1079.d018510
#print axioms _root_.GD.N0232.N0720.N1079.d018511
#print axioms _root_.GD.N0232.N0720.N1079.d018512
#print axioms _root_.GD.N0232.N0720.N1079.d018513
