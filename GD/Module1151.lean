import GD.Module1136
import GD.Module1131
import GD.Module1150





















open Filter MeasureTheory Set Topology

namespace GD
namespace N0232
namespace N0720
namespace N1448

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
open _root_.GD.N0232.N0720.N1208
open _root_.GD.N0232.N0720.N1302
open _root_.GD.N0232.N0720.N1363
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1482

variable {m n : ℕ}





theorem d018476
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) (row : _root_.GD.N0232.N0720.N1103.d018281 s) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (row.candidate j))
      atTop (nhds (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)) := by
  let width : ℕ → ℕ := fun j ↦ (row.candidate j).width
  let packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168 :=
    fun j ↦ (row.candidate j).packet
  let weight : ∀ j, Fin (width j) → ℝ :=
    fun j ↦ (row.candidate j).weight
  let hweight : ∀ j i, 0 ≤ weight j i :=
    fun j ↦ (row.candidate j).weight_nonneg
  have htight : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0) := by
    simpa only [width, packet, weight, _root_.GD.N0232.N0720.N1103.d018279] using
      row.gap_tendsto_zero
  simpa only [_root_.GD.N0232.N0720.N1130.d017075, width, packet, weight, hweight] using
    _root_.GD.N0232.N0720.N1122.d017966
      s packet weight hweight htight






theorem d018477
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (base scaleTwo shiftOneScaleThree : _root_.GD.N0232.N0720.N1103.d018281 s)
    (hscaleTwoCovariance : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1130.d017075 m n (scaleTwo.candidate j) -
          _root_.GD.N0232.N0720.N1146.d015228 m n
            (_root_.GD.N0232.N0720.N1130.d017075 m n (base.candidate j))‖)
      atTop (nhds 0))
    (hshiftOneScaleThreeCovariance : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1130.d017075 m n (shiftOneScaleThree.candidate j) -
          _root_.GD.N0232.N0720.N1146.d015229 m n
            (_root_.GD.N0232.N0720.N1130.d017075 m n (base.candidate j))‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1146.d015228 m n
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value ∧
      _root_.GD.N0232.N0720.N1146.d015229 m n
          (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value := by
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  have hbase : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (base.candidate j))
      atTop (nhds p) := by
    exact _root_.GD.N0232.N0720.N1448.d018476 s base
  have hscaleTwo : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (scaleTwo.candidate j))
      atTop (nhds p) := by
    exact _root_.GD.N0232.N0720.N1448.d018476 s scaleTwo
  have hshiftOneScaleThree : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (shiftOneScaleThree.candidate j))
      atTop (nhds p) := by
    exact _root_.GD.N0232.N0720.N1448.d018476
      s shiftOneScaleThree
  constructor
  · change _root_.GD.N0232.N0720.N1146.d015212 m n
        (_root_.GD.N0232.N0720.N1146.d015221 m n) p = p
    exact _root_.GD.N0232.N0720.N1208.d018202
      (m := m) (n := n) (_root_.GD.N0232.N0720.N1146.d015221 m n)
      p
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (base.candidate j))
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (scaleTwo.candidate j))
      hbase hscaleTwo hscaleTwoCovariance
  · change _root_.GD.N0232.N0720.N1146.d015212 m n
        (_root_.GD.N0232.N0720.N1146.d015222 m n) p = p
    exact _root_.GD.N0232.N0720.N1208.d018202
      (m := m) (n := n)
      (_root_.GD.N0232.N0720.N1146.d015222 m n)
      p
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 m n (base.candidate j))
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 m n
        (shiftOneScaleThree.candidate j))
      hbase hshiftOneScaleThree hshiftOneScaleThreeCovariance



theorem d018478
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (base scaleTwo shiftOneScaleThree : _root_.GD.N0232.N0720.N1103.d018281 s)
    (hscaleTwoCovariance : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1130.d017075 m n (scaleTwo.candidate j) -
          _root_.GD.N0232.N0720.N1146.d015228 m n
            (_root_.GD.N0232.N0720.N1130.d017075 m n (base.candidate j))‖)
      atTop (nhds 0))
    (hshiftOneScaleThreeCovariance : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1130.d017075 m n (shiftOneScaleThree.candidate j) -
          _root_.GD.N0232.N0720.N1146.d015229 m n
            (_root_.GD.N0232.N0720.N1130.d017075 m n (base.candidate j))‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 := by
  have hfixed :=
    _root_.GD.N0232.N0720.N1448.d018477
      s base scaleTwo shiftOneScaleThree
      hscaleTwoCovariance hshiftOneScaleThreeCovariance
  rw [← _root_.GD.N0232.N0720.N1122.d017965 s]
  unfold _root_.GD.N0232.N0720.N1122.d017962
  rw [hfixed.1, hfixed.2]
  norm_num






theorem d018479
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (base scaleTwo shiftOneScaleThree : _root_.GD.N0232.N0720.N1103.d018281 s)
    (hscaleTwoCovariance : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1130.d017075 m n (scaleTwo.candidate j) -
          _root_.GD.N0232.N0720.N1146.d015228 m n
            (_root_.GD.N0232.N0720.N1130.d017075 m n (base.candidate j))‖)
      atTop (nhds 0))
    (hshiftOneScaleThreeCovariance : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1130.d017075 m n (shiftOneScaleThree.candidate j) -
          _root_.GD.N0232.N0720.N1146.d015229 m n
            (_root_.GD.N0232.N0720.N1130.d017075 m n (base.candidate j))‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  have henergy : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 :=
    _root_.GD.N0232.N0720.N1448.d018478
      s base scaleTwo shiftOneScaleThree
      hscaleTwoCovariance hshiftOneScaleThreeCovariance
  apply
    (_root_.GD.N0232.N0720.N1482.d015173
      (m := m) (n := n) hm hn).2
  exact ⟨s, hstrict,
    (_root_.GD.N0232.N0720.N1477.d015755
      (m := m) (n := n) s).2 henergy⟩





def d018480 : Prop :=
  ∃ base scaleTwo shiftOneScaleThree :
      _root_.GD.N0232.N0720.N1103.d018281 _root_.GD.N0232.N0720.N1302.d018268,
    Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1130.d017075 2 2 (scaleTwo.candidate j) -
            _root_.GD.N0232.N0720.N1146.d015228 2 2
              (_root_.GD.N0232.N0720.N1130.d017075 2 2 (base.candidate j))‖)
        atTop (nhds 0) ∧
      Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1130.d017075 2 2 (shiftOneScaleThree.candidate j) -
            _root_.GD.N0232.N0720.N1146.d015229 2 2
              (_root_.GD.N0232.N0720.N1130.d017075 2 2 (base.candidate j))‖)
        atTop (nhds 0)






theorem d018481 :
    _root_.GD.N0232.N0720.N1448.d018480 ↔
      _root_.GD.N0232.N0720.N1477.d015749 2 2
        _root_.GD.N0232.N0720.N1302.d018268 = 0 := by
  constructor
  · rintro
      ⟨base, scaleTwo, shiftOneScaleThree,
        hscaleTwoCovariance, hshiftOneScaleThreeCovariance⟩
    exact _root_.GD.N0232.N0720.N1448.d018478
      _root_.GD.N0232.N0720.N1302.d018268 base scaleTwo shiftOneScaleThree
      hscaleTwoCovariance hshiftOneScaleThreeCovariance
  · intro henergy
    let row : _root_.GD.N0232.N0720.N1103.d018281 _root_.GD.N0232.N0720.N1302.d018268 :=
      Nonempty.some
        (_root_.GD.N0232.N0720.N1103.d018282 _root_.GD.N0232.N0720.N1302.d018268)
    let p := _root_.GD.N0232.N0720.N1159.d014633 2 2 _root_.GD.N0232.N0720.N1302.d018268.value
    have hpResidual : _root_.GD.N0232.N0720.N1122.d017962 2 2 p = 0 := by
      rw [_root_.GD.N0232.N0720.N1122.d017965]
      exact henergy
    have hscaleFixed : _root_.GD.N0232.N0720.N1146.d015228 2 2 p = p := by
      have hnorm :
          ‖_root_.GD.N0232.N0720.N1146.d015228 2 2 p - p‖ = 0 := by
        unfold _root_.GD.N0232.N0720.N1122.d017962 at hpResidual
        nlinarith [
          sq_nonneg ‖_root_.GD.N0232.N0720.N1146.d015228 2 2 p - p‖,
          sq_nonneg
            ‖_root_.GD.N0232.N0720.N1146.d015229 2 2 p - p‖]
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    have hshiftFixed :
        _root_.GD.N0232.N0720.N1146.d015229 2 2 p = p := by
      have hnorm :
          ‖_root_.GD.N0232.N0720.N1146.d015229 2 2 p - p‖ = 0 := by
        unfold _root_.GD.N0232.N0720.N1122.d017962 at hpResidual
        nlinarith [
          sq_nonneg ‖_root_.GD.N0232.N0720.N1146.d015228 2 2 p - p‖,
          sq_nonneg
            ‖_root_.GD.N0232.N0720.N1146.d015229 2 2 p - p‖]
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    have hrow : Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1130.d017075 2 2 (row.candidate j))
        atTop (nhds p) := by
      exact _root_.GD.N0232.N0720.N1448.d018476
        _root_.GD.N0232.N0720.N1302.d018268 row
    have hscaleTransport : Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1146.d015228 2 2
          (_root_.GD.N0232.N0720.N1130.d017075 2 2 (row.candidate j)))
        atTop (nhds p) := by
      have hcontinuous : Continuous
          (_root_.GD.N0232.N0720.N1146.d015228 2 2) :=
        (_root_.GD.N0232.N0720.N1146.d015216 2 2
          (_root_.GD.N0232.N0720.N1146.d015221 2 2)).continuous
      have ht := hcontinuous.continuousAt.tendsto.comp hrow
      change Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1146.d015228 2 2
          (_root_.GD.N0232.N0720.N1130.d017075 2 2 (row.candidate j)))
        atTop (nhds (_root_.GD.N0232.N0720.N1146.d015228 2 2 p)) at ht
      rw [hscaleFixed] at ht
      exact ht
    have hshiftTransport : Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1146.d015229 2 2
          (_root_.GD.N0232.N0720.N1130.d017075 2 2 (row.candidate j)))
        atTop (nhds p) := by
      have hcontinuous : Continuous
          (_root_.GD.N0232.N0720.N1146.d015229 2 2) :=
        (_root_.GD.N0232.N0720.N1146.d015216 2 2
          (_root_.GD.N0232.N0720.N1146.d015222 2 2)).continuous
      have ht := hcontinuous.continuousAt.tendsto.comp hrow
      change Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1146.d015229 2 2
          (_root_.GD.N0232.N0720.N1130.d017075 2 2 (row.candidate j)))
        atTop
        (nhds (_root_.GD.N0232.N0720.N1146.d015229 2 2 p)) at ht
      rw [hshiftFixed] at ht
      exact ht
    refine ⟨row, row, row, ?_, ?_⟩
    · simpa only [sub_self, norm_zero] using
        (hrow.sub hscaleTransport).norm
    · simpa only [sub_self, norm_zero] using
        (hrow.sub hshiftTransport).norm





theorem d018482 :
    _root_.GD.N0232.N0720.N1448.d018480 ↔
      _root_.GD.N0232.N0720.N1363.d018469 := by
  rw [_root_.GD.N0232.N0720.N1448.d018481,
    _root_.GD.N0232.N0720.N1363.d018471]




theorem d018483
    (base scaleTwo shiftOneScaleThree :
      _root_.GD.N0232.N0720.N1103.d018281 _root_.GD.N0232.N0720.N1302.d018268)
    (hscaleTwoCovariance : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1130.d017075 2 2 (scaleTwo.candidate j) -
          _root_.GD.N0232.N0720.N1146.d015228 2 2
            (_root_.GD.N0232.N0720.N1130.d017075 2 2 (base.candidate j))‖)
      atTop (nhds 0))
    (hshiftOneScaleThreeCovariance : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1130.d017075 2 2 (shiftOneScaleThree.candidate j) -
          _root_.GD.N0232.N0720.N1146.d015229 2 2
            (_root_.GD.N0232.N0720.N1130.d017075 2 2 (base.candidate j))‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  have hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2)
      _root_.GD.N0232.N0720.N1302.d018268.value
      (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by norm_num) (by norm_num)) := by
    simpa only [_root_.GD.N0232.N0720.N1302.d018269] using
      _root_.GD.N0232.N0720.N1302.d018266
  exact _root_.GD.N0232.N0720.N1448.d018479
    (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1302.d018268 hstrict
    base scaleTwo shiftOneScaleThree
    hscaleTwoCovariance hshiftOneScaleThreeCovariance



theorem d018484
    (h : _root_.GD.N0232.N0720.N1448.d018480) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  rcases h with
    ⟨base, scaleTwo, shiftOneScaleThree,
      hscaleTwoCovariance, hshiftOneScaleThreeCovariance⟩
  exact _root_.GD.N0232.N0720.N1448.d018483
    base scaleTwo shiftOneScaleThree
    hscaleTwoCovariance hshiftOneScaleThreeCovariance

end

end N1448
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1448.d018476
#print axioms _root_.GD.N0232.N0720.N1448.d018477
#print axioms _root_.GD.N0232.N0720.N1448.d018478
#print axioms _root_.GD.N0232.N0720.N1448.d018479
#print axioms _root_.GD.N0232.N0720.N1448.d018481
#print axioms _root_.GD.N0232.N0720.N1448.d018482
#print axioms _root_.GD.N0232.N0720.N1448.d018483
#print axioms _root_.GD.N0232.N0720.N1448.d018484
