import GD.Module1151




























open Filter Topology

namespace GD
namespace N0232
namespace N0720
namespace N1158

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1103
open _root_.GD.N0232.N0720.N1122
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1302
open _root_.GD.N0232.N0720.N1363
open _root_.GD.N0232.N0720.N1448
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1482

variable {m n : ℕ}





def d018485 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∃ base scaleTwo shiftOneScaleThree : _root_.GD.N0232.N0720.N1103.d018281 s,
    Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1130.d017075 m n (scaleTwo.candidate j) -
            _root_.GD.N0232.N0720.N1146.d015228 m n
              (_root_.GD.N0232.N0720.N1130.d017075 m n (base.candidate j))‖)
        atTop (nhds 0) ∧
      Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1130.d017075 m n (shiftOneScaleThree.candidate j) -
            _root_.GD.N0232.N0720.N1146.d015229 m n
              (_root_.GD.N0232.N0720.N1130.d017075 m n (base.candidate j))‖)
        atTop (nhds 0)



def d018486 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∃ row : _root_.GD.N0232.N0720.N1103.d018281 s,
    Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j) -
            _root_.GD.N0232.N0720.N1146.d015228 m n
              (_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j))‖)
        atTop (nhds 0) ∧
      Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j) -
            _root_.GD.N0232.N0720.N1146.d015229 m n
              (_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j))‖)
        atTop (nhds 0)



def d018487
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∃ row : _root_.GD.N0232.N0720.N1103.d018281 s,
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1122.d017962 m n
        (_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j)))
      atTop (nhds 0)




def d018488 (s : _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∃ row : _root_.GD.N0232.N0720.N1103.d018289 s,
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1122.d017962 m n
        (_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j)))
      atTop (nhds 0)





theorem d018489
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018281 s) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1122.d017962 m n
        (_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j)))
      atTop (nhds (_root_.GD.N0232.N0720.N1477.d015749 m n s)) := by
  have hlimit :=
    _root_.GD.N0232.N0720.N1122.d017964
      (m := m) (n := n) |>.continuousAt.tendsto.comp
        (_root_.GD.N0232.N0720.N1448.d018476 s row)
  change Tendsto
    (fun j ↦ _root_.GD.N0232.N0720.N1122.d017962 m n
      (_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j)))
    atTop
    (nhds (_root_.GD.N0232.N0720.N1122.d017962 m n
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value))) at hlimit
  simpa only [_root_.GD.N0232.N0720.N1122.d017965]
    using hlimit





theorem d018490
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 ↔
      _root_.GD.N0232.N0720.N1146.d015228 m n
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value ∧
      _root_.GD.N0232.N0720.N1146.d015229 m n
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value := by
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  constructor
  · intro henergy
    have hpResidual : _root_.GD.N0232.N0720.N1122.d017962 m n p = 0 := by
      rw [_root_.GD.N0232.N0720.N1122.d017965]
      exact henergy
    have hscaleNorm :
        ‖_root_.GD.N0232.N0720.N1146.d015228 m n p - p‖ = 0 := by
      unfold _root_.GD.N0232.N0720.N1122.d017962 at hpResidual
      nlinarith [
        sq_nonneg ‖_root_.GD.N0232.N0720.N1146.d015228 m n p - p‖,
        sq_nonneg
          ‖_root_.GD.N0232.N0720.N1146.d015229 m n p - p‖]
    have hshiftNorm :
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n p - p‖ = 0 := by
      unfold _root_.GD.N0232.N0720.N1122.d017962 at hpResidual
      nlinarith [
        sq_nonneg ‖_root_.GD.N0232.N0720.N1146.d015228 m n p - p‖,
        sq_nonneg
          ‖_root_.GD.N0232.N0720.N1146.d015229 m n p - p‖]
    exact ⟨sub_eq_zero.mp (norm_eq_zero.mp hscaleNorm),
      sub_eq_zero.mp (norm_eq_zero.mp hshiftNorm)⟩
  · rintro ⟨hscale, hshift⟩
    rw [← _root_.GD.N0232.N0720.N1122.d017965 s]
    simp only [_root_.GD.N0232.N0720.N1122.d017962, hscale, hshift,
      sub_self, norm_zero]
    norm_num






theorem d018491
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018281 s)
    (henergy : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0) :
    Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j) -
            _root_.GD.N0232.N0720.N1146.d015228 m n
              (_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j))‖)
        atTop (nhds 0) ∧
      Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j) -
            _root_.GD.N0232.N0720.N1146.d015229 m n
              (_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j))‖)
        atTop (nhds 0) := by
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  have hfixed :=
    (_root_.GD.N0232.N0720.N1158.d018490 s).1 henergy
  have hrow : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j))
      atTop (nhds p) :=
    _root_.GD.N0232.N0720.N1448.d018476 s row
  have hscaleTransport : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1146.d015228 m n
        (_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j)))
      atTop (nhds p) := by
    have ht :=
      (_root_.GD.N0232.N0720.N1146.d015216 m n
        (_root_.GD.N0232.N0720.N1146.d015221 m n)).continuous.continuousAt
          |>.tendsto.comp hrow
    change Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1146.d015228 m n
        (_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j)))
      atTop
      (nhds (_root_.GD.N0232.N0720.N1146.d015228 m n p)) at ht
    rw [hfixed.1] at ht
    exact ht
  have hshiftTransport : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1146.d015229 m n
        (_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j)))
      atTop (nhds p) := by
    have ht :=
      (_root_.GD.N0232.N0720.N1146.d015216 m n
        (_root_.GD.N0232.N0720.N1146.d015222 m n)).continuous
          |>.continuousAt.tendsto.comp hrow
    change Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1146.d015229 m n
        (_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j)))
      atTop
      (nhds (_root_.GD.N0232.N0720.N1146.d015229 m n p)) at ht
    rw [hfixed.2] at ht
    exact ht
  constructor
  · simpa only [sub_self, norm_zero] using
      (hrow.sub hscaleTransport).norm
  · simpa only [sub_self, norm_zero] using
      (hrow.sub hshiftTransport).norm




theorem d018492
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (henergy : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0) :
    _root_.GD.N0232.N0720.N1158.d018486 s := by
  let row : _root_.GD.N0232.N0720.N1103.d018281 s :=
    Nonempty.some (_root_.GD.N0232.N0720.N1103.d018282 s)
  exact ⟨row,
    (_root_.GD.N0232.N0720.N1158.d018491
      s row henergy).1,
    (_root_.GD.N0232.N0720.N1158.d018491
      s row henergy).2⟩




theorem d018493
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1158.d018485 s ↔
      _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 := by
  constructor
  · rintro
      ⟨base, scaleTwo, shiftOneScaleThree,
        hscaleTwoCovariance, hshiftOneScaleThreeCovariance⟩
    exact _root_.GD.N0232.N0720.N1448.d018478
      s base scaleTwo shiftOneScaleThree
      hscaleTwoCovariance hshiftOneScaleThreeCovariance
  · intro henergy
    rcases _root_.GD.N0232.N0720.N1158.d018492
        s henergy with ⟨row, hscale, hshift⟩
    exact ⟨row, row, row, hscale, hshift⟩



theorem d018494
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1158.d018485 s ↔
      _root_.GD.N0232.N0720.N1158.d018486 s := by
  constructor
  · intro hthree
    exact _root_.GD.N0232.N0720.N1158.d018492 s
      ((_root_.GD.N0232.N0720.N1158.d018493
        s).1 hthree)
  · rintro ⟨row, hscale, hshift⟩
    exact ⟨row, row, row, hscale, hshift⟩



theorem d018495
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1158.d018486 s ↔
      _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 := by
  rw [← _root_.GD.N0232.N0720.N1158.d018494 s,
    _root_.GD.N0232.N0720.N1158.d018493]




theorem d018496
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 ↔
      ∀ row : _root_.GD.N0232.N0720.N1103.d018281 s,
        Tendsto
            (fun j ↦
              ‖_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j) -
                _root_.GD.N0232.N0720.N1146.d015228 m n
                  (_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j))‖)
            atTop (nhds 0) ∧
          Tendsto
            (fun j ↦
              ‖_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j) -
                _root_.GD.N0232.N0720.N1146.d015229 m n
                  (_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j))‖)
            atTop (nhds 0) := by
  constructor
  · intro henergy row
    exact
      _root_.GD.N0232.N0720.N1158.d018491
        s row henergy
  · intro hall
    let row : _root_.GD.N0232.N0720.N1103.d018281 s :=
      Nonempty.some (_root_.GD.N0232.N0720.N1103.d018282 s)
    apply (_root_.GD.N0232.N0720.N1158.d018495 s).1
    exact ⟨row, (hall row).1, (hall row).2⟩





theorem d018497
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1158.d018487 s ↔
      _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 := by
  constructor
  · rintro ⟨row, hzero⟩
    exact tendsto_nhds_unique
      (_root_.GD.N0232.N0720.N1158.d018489 s row)
      hzero
  · intro henergy
    let row : _root_.GD.N0232.N0720.N1103.d018281 s :=
      Nonempty.some (_root_.GD.N0232.N0720.N1103.d018282 s)
    refine ⟨row, ?_⟩
    simpa only [henergy] using
      (_root_.GD.N0232.N0720.N1158.d018489 s row)



theorem d018498
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 ↔
      ∀ row : _root_.GD.N0232.N0720.N1103.d018281 s,
        Tendsto
          (fun j ↦ _root_.GD.N0232.N0720.N1122.d017962 m n
            (_root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j)))
          atTop (nhds 0) := by
  constructor
  · intro henergy row
    simpa only [henergy] using
      (_root_.GD.N0232.N0720.N1158.d018489 s row)
  · intro hall
    let row : _root_.GD.N0232.N0720.N1103.d018281 s :=
      Nonempty.some (_root_.GD.N0232.N0720.N1103.d018282 s)
    exact tendsto_nhds_unique
      (_root_.GD.N0232.N0720.N1158.d018489 s row)
      (hall row)



theorem d018499
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1158.d018488 s ↔
      _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 := by
  constructor
  · rintro ⟨row, hzero⟩
    exact tendsto_nhds_unique
      (_root_.GD.N0232.N0720.N1363.d018470
        s row)
      hzero
  · intro henergy
    let row : _root_.GD.N0232.N0720.N1103.d018289 s :=
      _root_.GD.N0232.N0720.N1103.d018292 s
    refine ⟨row, ?_⟩
    simpa only [henergy] using
      (_root_.GD.N0232.N0720.N1363.d018470
        s row)



theorem d018500
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1158.d018485 s ↔
      _root_.GD.N0232.N0720.N1158.d018488 s := by
  rw [_root_.GD.N0232.N0720.N1158.d018493,
    _root_.GD.N0232.N0720.N1158.d018499]

theorem d018501
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1158.d018487 s ↔
      _root_.GD.N0232.N0720.N1158.d018488 s := by
  rw [_root_.GD.N0232.N0720.N1158.d018497,
    _root_.GD.N0232.N0720.N1158.d018499]





theorem d018502
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1158.d018485 s ↔
      _root_.GD.N0232.N0720.N1482.d015169 (m := m) (n := n) s = 0 := by
  rw [_root_.GD.N0232.N0720.N1158.d018493,
    _root_.GD.N0232.N0720.N1477.d015755]




theorem d018503
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hrecovery : _root_.GD.N0232.N0720.N1158.d018485 s) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  apply
    (_root_.GD.N0232.N0720.N1482.d015173
      (m := m) (n := n) hm hn).2
  exact ⟨s, hstrict,
    (_root_.GD.N0232.N0720.N1158.d018502 s).1
      hrecovery⟩



theorem d018504 :
    _root_.GD.N0232.N0720.N1448.d018480 ↔
      _root_.GD.N0232.N0720.N1158.d018485
        _root_.GD.N0232.N0720.N1302.d018268 :=
  Iff.rfl

theorem d018505 :
    _root_.GD.N0232.N0720.N1363.d018469 ↔
      _root_.GD.N0232.N0720.N1158.d018488 _root_.GD.N0232.N0720.N1302.d018268 :=
  Iff.rfl

end

end N1158
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1158.d018489
#print axioms _root_.GD.N0232.N0720.N1158.d018490
#print axioms _root_.GD.N0232.N0720.N1158.d018491
#print axioms _root_.GD.N0232.N0720.N1158.d018493
#print axioms _root_.GD.N0232.N0720.N1158.d018494
#print axioms _root_.GD.N0232.N0720.N1158.d018496
#print axioms _root_.GD.N0232.N0720.N1158.d018498
#print axioms _root_.GD.N0232.N0720.N1158.d018499
#print axioms _root_.GD.N0232.N0720.N1158.d018500
#print axioms _root_.GD.N0232.N0720.N1158.d018502
#print axioms _root_.GD.N0232.N0720.N1158.d018503
