import GD.Module0970
import GD.Module1117
import GD.Module0965

























open Filter MeasureTheory Set Topology
open scoped ENNReal BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1208

noncomputable section

open _root_.GD.N0232.N0720.N1029
open _root_.GD.N0232.N0720.N1032
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1482

variable {m n : ℕ}










theorem d018202
    {g : _root_.GD.N0232.N0720.N1482.d015118}
    (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (base transported : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hbase : Tendsto base atTop (nhds p))
    (htransported : Tendsto transported atTop (nhds p))
    (hcovariance : Tendsto
      (fun j ↦ ‖transported j -
        _root_.GD.N0232.N0720.N1146.d015212 m n certificate (base j)‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1146.d015212 m n certificate p = p := by
  have hcovariance' : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate (base j) -
        transported j‖) atTop (nhds 0) := by
    simpa only [norm_sub_rev] using hcovariance
  have htransportedSubBase :
      Tendsto (fun j ↦ ‖transported j - base j‖) atTop (nhds 0) := by
    simpa only [sub_self, norm_zero] using (htransported.sub hbase).norm
  have hbaseFixed : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate (base j) - base j‖)
      atTop (nhds 0) := by
    have hmajor : Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate (base j) -
              transported j‖ + ‖transported j - base j‖)
        atTop (nhds 0) := by
      simpa only [zero_add] using
        hcovariance'.add htransportedSubBase
    apply squeeze_zero
      (fun j ↦ norm_nonneg
        (_root_.GD.N0232.N0720.N1146.d015212 m n certificate (base j) - base j))
      (fun j ↦ ?_)
      hmajor
    calc
      ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate (base j) - base j‖ =
          ‖(_root_.GD.N0232.N0720.N1146.d015212 m n certificate (base j) -
              transported j) + (transported j - base j)‖ := by
            congr 1
            abel
      _ ≤
          ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate (base j) -
            transported j‖ + ‖transported j - base j‖ := norm_add_le _ _
  have hpClose : Tendsto (fun j ↦ ‖p - base j‖) atTop (nhds 0) := by
    simpa only [norm_sub_rev] using
      (tendsto_iff_norm_sub_tendsto_zero.mp hbase)
  have hdisplacement : Tendsto
      (fun _ : ℕ ↦ ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate p - p‖)
      atTop (nhds 0) :=
    _root_.GD.N0232.N0720.N1146.d015217 m n certificate
      (fun _ : ℕ ↦ p) base hpClose hbaseFixed
  have hconstant : Tendsto
      (fun _ : ℕ ↦ ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate p - p‖)
      atTop
      (nhds ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate p - p‖) :=
    tendsto_const_nhds
  have hnorm : ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate p - p‖ = 0 :=
    tendsto_nhds_unique hconstant hdisplacement
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)



theorem d018203
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p)
    (base scaleTwo shiftOneScaleThree :
      ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hbase : Tendsto base atTop (nhds p))
    (hscaleTwo : Tendsto scaleTwo atTop (nhds p))
    (hshiftOneScaleThree : Tendsto shiftOneScaleThree atTop (nhds p))
    (hscaleTwoCovariance : Tendsto
      (fun j ↦ ‖scaleTwo j - _root_.GD.N0232.N0720.N1146.d015228 m n (base j)‖)
      atTop (nhds 0))
    (hshiftOneScaleThreeCovariance : Tendsto
      (fun j ↦ ‖shiftOneScaleThree j -
        _root_.GD.N0232.N0720.N1146.d015229 m n (base j)‖)
      atTop (nhds 0)) :
    ∀ g : _root_.GD.N0232.N0720.N1482.d015118, _root_.GD.N0232.N0720.N1159.d014642 m n g p hp = p := by
  have hTwoReference : _root_.GD.N0232.N0720.N1146.d015228 m n p = p :=
    _root_.GD.N0232.N0720.N1208.d018202
      (m := m) (n := n) (_root_.GD.N0232.N0720.N1146.d015221 m n)
      p base scaleTwo hbase hscaleTwo hscaleTwoCovariance
  have hThreeReference :
      _root_.GD.N0232.N0720.N1146.d015229 m n p = p :=
    _root_.GD.N0232.N0720.N1208.d018202
      (m := m) (n := n)
      (_root_.GD.N0232.N0720.N1146.d015222 m n)
      p base shiftOneScaleThree hbase hshiftOneScaleThree
      hshiftOneScaleThreeCovariance
  have hTwo : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp = p := by
    rw [← _root_.GD.N0232.N0720.N1146.d015218
      m n (_root_.GD.N0232.N0720.N1146.d015221 m n) p hp]
    exact hTwoReference
  have hThree :
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp = p := by
    rw [← _root_.GD.N0232.N0720.N1146.d015218
      m n (_root_.GD.N0232.N0720.N1146.d015222 m n) p hp]
    exact hThreeReference
  exact _root_.GD.N0232.N0720.N1482.d015167
    (m := m) (n := n) p hp hTwo hThree







theorem d018204
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (base scaleTwo shiftOneScaleThree :
      ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hbase : Tendsto base atTop
      (nhds (_root_.GD.N0232.N0720.N1159.d014633 m n
        (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value)))
    (hscaleTwo : Tendsto scaleTwo atTop
      (nhds (_root_.GD.N0232.N0720.N1159.d014633 m n
        (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value)))
    (hshiftOneScaleThree : Tendsto shiftOneScaleThree atTop
      (nhds (_root_.GD.N0232.N0720.N1159.d014633 m n
        (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value)))
    (hscaleTwoCovariance : Tendsto
      (fun j ↦ ‖scaleTwo j -
        _root_.GD.N0232.N0720.N1146.d015228 m n (base j)‖)
      atTop (nhds 0))
    (hshiftOneScaleThreeCovariance : Tendsto
      (fun j ↦ ‖shiftOneScaleThree j -
        _root_.GD.N0232.N0720.N1146.d015229 m n (base j)‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014633 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value =
      _root_.GD.N0232.N0720.N1029.d015364 m n hm hn := by
  let s := _root_.GD.N0232.N0720.N1029.d015372 m n hm hn
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  have hpSeed : p ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
    (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have hpFinite : _root_.GD.N0232.N0720.N1159.d014637 m n p :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s p hpSeed
  have hall : ∀ g : _root_.GD.N0232.N0720.N1482.d015118,
      _root_.GD.N0232.N0720.N1159.d014642 m n g p hpFinite = p :=
    _root_.GD.N0232.N0720.N1208.d018203
      (m := m) (n := n) p hpFinite base scaleTwo shiftOneScaleThree
      hbase hscaleTwo hshiftOneScaleThree hscaleTwoCovariance
      hshiftOneScaleThreeCovariance
  have hpLower : p ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn := by
    intro theta
    exact (hpSeed theta).trans
      (_root_.GD.N0232.N0720.N1029.d015366 m n hm hn theta)
  have hnative : ∀ g : _root_.GD.N0232.N0720.N1482.d015118,
      _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g p hpLower = p := by
    intro g
    calc
      _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g p hpLower =
          _root_.GD.N0232.N0720.N1159.d014642 m n g p hpFinite := by
            unfold _root_.GD.N0232.N0720.N1215.d014289 _root_.GD.N0232.N0720.N1159.d014642
            rfl
      _ = p := hall g
  have heq : p = _root_.GD.N0232.N0720.N1029.d015364 m n hm hn :=
    _root_.GD.N0232.N0720.N1029.d015369
      m n hm hn p hpSeed (fun _ g ↦ hnative g)
  simpa only [s, p] using heq



theorem d018205
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (base scaleTwo shiftOneScaleThree :
      ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hbase : Tendsto base atTop
      (nhds (_root_.GD.N0232.N0720.N1159.d014633 m n
        (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value)))
    (hscaleTwo : Tendsto scaleTwo atTop
      (nhds (_root_.GD.N0232.N0720.N1159.d014633 m n
        (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value)))
    (hshiftOneScaleThree : Tendsto shiftOneScaleThree atTop
      (nhds (_root_.GD.N0232.N0720.N1159.d014633 m n
        (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value)))
    (hscaleTwoCovariance : Tendsto
      (fun j ↦ ‖scaleTwo j -
        _root_.GD.N0232.N0720.N1146.d015228 m n (base j)‖)
      atTop (nhds 0))
    (hshiftOneScaleThreeCovariance : Tendsto
      (fun j ↦ ‖shiftOneScaleThree j -
        _root_.GD.N0232.N0720.N1146.d015229 m n (base j)‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  have heq :=
    _root_.GD.N0232.N0720.N1208.d018204
      (m := m) (n := n) hm hn base scaleTwo shiftOneScaleThree
      hbase hscaleTwo hshiftOneScaleThree hscaleTwoCovariance
      hshiftOneScaleThreeCovariance
  apply _root_.GD.N0232.N0720.N1029.d015374
    m n hm hn
  unfold _root_.GD.N0232.N0720.N1201.d015333
  rw [heq]
  change ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ ^ 2 -
    ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ ^ 2 = 0
  exact sub_self _



variable {index : ℕ → Type*}
variable [∀ j, Fintype (index j)] [∀ j, DecidableEq (index j)]











theorem d018206
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (basePacket scaleTwoPacket shiftOneScaleThreePacket :
      ∀ j, index j → _root_.GD.N0232.N0720.N1080.d014168)
    (baseWeight scaleTwoWeight shiftOneScaleThreeWeight :
      ∀ j, index j → ℝ)
    (hbaseWeight : ∀ j i, 0 ≤ baseWeight j i)
    (hscaleTwoWeight : ∀ j i, 0 ≤ scaleTwoWeight j i)
    (hshiftOneScaleThreeWeight :
      ∀ j i, 0 ≤ shiftOneScaleThreeWeight j i)
    (hbaseTight : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value‖ ^ 2 -
          _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn)
            (basePacket j) (baseWeight j))
      atTop (nhds 0))
    (hscaleTwoTight : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value‖ ^ 2 -
          _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn)
            (scaleTwoPacket j) (scaleTwoWeight j))
      atTop (nhds 0))
    (hshiftOneScaleThreeTight : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value‖ ^ 2 -
          _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn)
            (shiftOneScaleThreePacket j) (shiftOneScaleThreeWeight j))
      atTop (nhds 0))
    (hscaleTwoCovariance : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
              (scaleTwoPacket j) (scaleTwoWeight j) (hscaleTwoWeight j) -
          _root_.GD.N0232.N0720.N1146.d015228 m n
            (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
              (basePacket j) (baseWeight j) (hbaseWeight j))‖)
      atTop (nhds 0))
    (hshiftOneScaleThreeCovariance : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
              (shiftOneScaleThreePacket j) (shiftOneScaleThreeWeight j)
              (hshiftOneScaleThreeWeight j) -
          _root_.GD.N0232.N0720.N1146.d015229 m n
            (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
              (basePacket j) (baseWeight j) (hbaseWeight j))‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  let s := _root_.GD.N0232.N0720.N1029.d015372 m n hm hn
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  have hp : p ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
    (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have hbase : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
        (basePacket j) (baseWeight j) (hbaseWeight j))
      atTop (nhds p) :=
    _root_.GD.N0232.N0720.N1032.d017955
      s p hp basePacket baseWeight hbaseWeight hbaseTight
  have htwo : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
        (scaleTwoPacket j) (scaleTwoWeight j) (hscaleTwoWeight j))
      atTop (nhds p) :=
    _root_.GD.N0232.N0720.N1032.d017955
      s p hp scaleTwoPacket scaleTwoWeight hscaleTwoWeight hscaleTwoTight
  have hthree : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
        (shiftOneScaleThreePacket j) (shiftOneScaleThreeWeight j)
          (hshiftOneScaleThreeWeight j))
      atTop (nhds p) :=
    _root_.GD.N0232.N0720.N1032.d017955
      s p hp shiftOneScaleThreePacket shiftOneScaleThreeWeight
        hshiftOneScaleThreeWeight hshiftOneScaleThreeTight
  exact
    _root_.GD.N0232.N0720.N1208.d018205
      (m := m) (n := n) hm hn
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
        (basePacket j) (baseWeight j) (hbaseWeight j))
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
        (scaleTwoPacket j) (scaleTwoWeight j) (hscaleTwoWeight j))
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
        (shiftOneScaleThreePacket j) (shiftOneScaleThreeWeight j)
          (hshiftOneScaleThreeWeight j))
      hbase htwo hthree hscaleTwoCovariance hshiftOneScaleThreeCovariance

end

end N1208
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1208.d018202
#print axioms _root_.GD.N0232.N0720.N1208.d018203
#print axioms _root_.GD.N0232.N0720.N1208.d018204
#print axioms _root_.GD.N0232.N0720.N1208.d018206
