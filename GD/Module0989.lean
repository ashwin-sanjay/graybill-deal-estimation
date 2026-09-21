import GD.Module0098
import GD.Module0975
import GD.Module0965






















open Filter MeasureTheory Set Topology

namespace GD
namespace N0232
namespace N0720
namespace N1461

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0646
open _root_.GD.N0230.N0714
open RealInnerProductSpace
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1100
open _root_.GD.N0232.N0720.N1146

variable (m n : ℕ)




theorem d015683
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hstrong : Tendsto r atTop
      (nhds (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)))
    (hscaleTwo : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015228 m n (r j) - r j‖)
      atTop (nhds 0))
    (hshiftOneScaleThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n (r j) - r j‖)
      atTop (nhds 0)) :
    let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
    let hp : _root_.GD.N0232.N0720.N1159.d014637 m n p :=
      _root_.GD.N0232.N0720.N1159.d014644 m n s p
        (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
    _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp = p ∧
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp = p := by
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  let hp : _root_.GD.N0232.N0720.N1159.d014637 m n p :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s p
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have hclose : Tendsto (fun j ↦ ‖p - r j‖) atTop (nhds 0) := by
    have hpconst : Tendsto (fun _ : ℕ ↦ p) atTop (nhds p) :=
      tendsto_const_nhds
    have hstrong' : Tendsto r atTop (nhds p) := by
      simpa only [p] using hstrong
    have hsub := (hpconst.sub hstrong').norm
    simpa only [sub_self, norm_zero] using hsub
  have hscaleAtP : Tendsto
      (fun _ : ℕ ↦
        ‖_root_.GD.N0232.N0720.N1146.d015212 m n
            (_root_.GD.N0232.N0720.N1146.d015221 m n) p - p‖)
      atTop (nhds 0) := by
    exact _root_.GD.N0232.N0720.N1146.d015217 m n
      (_root_.GD.N0232.N0720.N1146.d015221 m n)
      (fun _ : ℕ ↦ p) r hclose hscaleTwo
  have hthreeAtP : Tendsto
      (fun _ : ℕ ↦
        ‖_root_.GD.N0232.N0720.N1146.d015212 m n
            (_root_.GD.N0232.N0720.N1146.d015222 m n) p - p‖)
      atTop (nhds 0) := by
    exact _root_.GD.N0232.N0720.N1146.d015217 m n
      (_root_.GD.N0232.N0720.N1146.d015222 m n)
      (fun _ : ℕ ↦ p) r hclose hshiftOneScaleThree
  have hscaleNorm :
      ‖_root_.GD.N0232.N0720.N1146.d015212 m n
          (_root_.GD.N0232.N0720.N1146.d015221 m n) p - p‖ = 0 := by
    exact tendsto_nhds_unique tendsto_const_nhds hscaleAtP
  have hthreeNorm :
      ‖_root_.GD.N0232.N0720.N1146.d015212 m n
          (_root_.GD.N0232.N0720.N1146.d015222 m n) p - p‖ = 0 := by
    exact tendsto_nhds_unique tendsto_const_nhds hthreeAtP
  have hscaleRef : _root_.GD.N0232.N0720.N1146.d015212 m n
      (_root_.GD.N0232.N0720.N1146.d015221 m n) p = p := by
    exact sub_eq_zero.mp (norm_eq_zero.mp hscaleNorm)
  have hthreeRef : _root_.GD.N0232.N0720.N1146.d015212 m n
      (_root_.GD.N0232.N0720.N1146.d015222 m n) p = p := by
    exact sub_eq_zero.mp (norm_eq_zero.mp hthreeNorm)
  change _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp = p ∧
    _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp = p
  constructor
  · rw [← _root_.GD.N0232.N0720.N1146.d015218
      m n (_root_.GD.N0232.N0720.N1146.d015221 m n) p hp]
    exact hscaleRef
  · rw [← _root_.GD.N0232.N0720.N1146.d015218
      m n (_root_.GD.N0232.N0720.N1146.d015222 m n) p hp]
    exact hthreeRef




theorem d015684
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (ε : ℕ → ℝ)
    (hprobe : Tendsto (fun j ↦ ⟪r j, x⟫)
      atTop (nhds (‖x‖ ^ 2)))
    (houter : x ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (hradial : ∀ j, ‖r j‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + ε j)
    (hε : Tendsto ε atTop (nhds 0))
    (hscaleTwo : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015228 m n (r j) - r j‖)
      atTop (nhds 0))
    (hshiftOneScaleThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n (r j) - r j‖)
      atTop (nhds 0)) :
    let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
    let hp : _root_.GD.N0232.N0720.N1159.d014637 m n p :=
      _root_.GD.N0232.N0720.N1159.d014644 m n s p
        (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
    _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp = p ∧
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp = p := by
  have hpWitness : _root_.GD.N0230.N0685.d000511
      (_root_.GD.N0232.N0720.N1159.d014630 m n s.value) 0
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) := by
    exact _root_.GD.N0232.N0720.N1100.d015487 m n s.value
  have hstrong : Tendsto r atTop
      (nhds (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)) := by
    exact _root_.GD.N0230.N0714.d001264
      hpWitness hprobe houter hradial hε
  exact _root_.GD.N0232.N0720.N1461.d015683
    m n s r hstrong hscaleTwo hshiftOneScaleThree





theorem d015685
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (ε : ℕ → ℝ)
    (hweak : _root_.GD.N0230.N0646.d000537 r x)
    (houter : x ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (hradial : ∀ j, ‖r j‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + ε j)
    (hε : Tendsto ε atTop (nhds 0))
    (hscaleTwo : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015228 m n (r j) - r j‖)
      atTop (nhds 0))
    (hshiftOneScaleThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n (r j) - r j‖)
      atTop (nhds 0)) :
    let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
    let hp : _root_.GD.N0232.N0720.N1159.d014637 m n p :=
      _root_.GD.N0232.N0720.N1159.d014644 m n s p
        (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
    _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp = p ∧
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp = p := by
  have hpWitness : _root_.GD.N0230.N0685.d000511
      (_root_.GD.N0232.N0720.N1159.d014630 m n s.value) 0
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) := by
    exact _root_.GD.N0232.N0720.N1100.d015487 m n s.value
  have hstrong : Tendsto r atTop
      (nhds (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)) := by
    exact _root_.GD.N0230.N0714.d001265
      hpWitness hweak houter hradial hε
  exact _root_.GD.N0232.N0720.N1461.d015683
    m n s r hstrong hscaleTwo hshiftOneScaleThree



theorem d015686
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (ε : ℕ → ℝ)
    (houter : Tendsto
      (fun j ↦ Metric.infDist (r j) (_root_.GD.N0232.N0720.N1159.d014630 m n s.value))
      atTop (nhds 0))
    (hradial : ∀ j, ‖r j‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + ε j)
    (hε : Tendsto ε atTop (nhds 0))
    (hscaleTwo : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015228 m n (r j) - r j‖)
      atTop (nhds 0))
    (hshiftOneScaleThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n (r j) - r j‖)
      atTop (nhds 0)) :
    let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
    let hp : _root_.GD.N0232.N0720.N1159.d014637 m n p :=
      _root_.GD.N0232.N0720.N1159.d014644 m n s p
        (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
    _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp = p ∧
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp = p := by
  have hpWitness : _root_.GD.N0230.N0685.d000511
      (_root_.GD.N0232.N0720.N1159.d014630 m n s.value) 0
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) := by
    exact _root_.GD.N0232.N0720.N1100.d015487 m n s.value
  have hstrong : Tendsto r atTop
      (nhds (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)) := by
    exact _root_.GD.N0230.N0714.d001267
      hpWitness houter hradial hε
  exact _root_.GD.N0232.N0720.N1461.d015683
    m n s r hstrong hscaleTwo hshiftOneScaleThree




theorem d015687
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hfixed :
      let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
      let hp : _root_.GD.N0232.N0720.N1159.d014637 m n p :=
        _root_.GD.N0232.N0720.N1159.d014644 m n s p
          (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp = p ∧
        _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp = p) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  let hp : _root_.GD.N0232.N0720.N1159.d014637 m n p :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s p
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  change _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp = p ∧
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp = p at hfixed
  have hscalePoint :
      _root_.GD.N0232.N0720.N1159.d014645 m n s _root_.GD.N0232.N0720.N1482.d015130
          (_root_.GD.N0232.N0720.N1159.d014646 m n s) =
        _root_.GD.N0232.N0720.N1159.d014646 m n s := by
    apply Subtype.ext
    change _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp = p
    exact hfixed.1
  have hthreePoint :
      _root_.GD.N0232.N0720.N1159.d014645 m n s _root_.GD.N0232.N0720.N1482.d015131
          (_root_.GD.N0232.N0720.N1159.d014646 m n s) =
        _root_.GD.N0232.N0720.N1159.d014646 m n s := by
    apply Subtype.ext
    change _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp = p
    exact hfixed.2
  apply (_root_.GD.N0232.N0720.N1482.d015172
    (m := m) (n := n) hm hn).2
  exact ⟨s, hstrict,
    (_root_.GD.N0232.N0720.N1159.d014651 m n s _root_.GD.N0232.N0720.N1482.d015130).2 hscalePoint,
    (_root_.GD.N0232.N0720.N1159.d014651
      m n s _root_.GD.N0232.N0720.N1482.d015131).2 hthreePoint⟩







theorem d015688
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (ε : ℕ → ℝ)
    (hweak : _root_.GD.N0230.N0646.d000537 r x)
    (houter : x ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (hradial : ∀ j, ‖r j‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + ε j)
    (hε : Tendsto ε atTop (nhds 0))
    (hscaleTwo : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015228 m n (r j) - r j‖)
      atTop (nhds 0))
    (hshiftOneScaleThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n (r j) - r j‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  have hfixed := _root_.GD.N0232.N0720.N1461.d015685
    m n s r x ε hweak houter hradial hε hscaleTwo hshiftOneScaleThree
  exact _root_.GD.N0232.N0720.N1461.d015687
    m n hm hn s hstrict hfixed




theorem d015689
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (ε : ℕ → ℝ)
    (hprobe : Tendsto (fun j ↦ ⟪r j, x⟫)
      atTop (nhds (‖x‖ ^ 2)))
    (houter : x ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (hradial : ∀ j, ‖r j‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + ε j)
    (hε : Tendsto ε atTop (nhds 0))
    (hscaleTwo : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015228 m n (r j) - r j‖)
      atTop (nhds 0))
    (hshiftOneScaleThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n (r j) - r j‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  have hfixed :=
    _root_.GD.N0232.N0720.N1461.d015684
      m n s r x ε hprobe houter hradial hε hscaleTwo
        hshiftOneScaleThree
  exact _root_.GD.N0232.N0720.N1461.d015687
    m n hm hn s hstrict hfixed




theorem d015690
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (ε : ℕ → ℝ)
    (houter : Tendsto
      (fun j ↦ Metric.infDist (r j) (_root_.GD.N0232.N0720.N1159.d014630 m n s.value))
      atTop (nhds 0))
    (hradial : ∀ j, ‖r j‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + ε j)
    (hε : Tendsto ε atTop (nhds 0))
    (hscaleTwo : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015228 m n (r j) - r j‖)
      atTop (nhds 0))
    (hshiftOneScaleThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n (r j) - r j‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  have hfixed := _root_.GD.N0232.N0720.N1461.d015686
    m n s r ε houter hradial hε hscaleTwo hshiftOneScaleThree
  exact _root_.GD.N0232.N0720.N1461.d015687
    m n hm hn s hstrict hfixed











theorem d015691
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
        (r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
        (x : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (ε : ℕ → ℝ),
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
          (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
        Tendsto (fun j ↦ ⟪r j, x⟫)
          atTop (nhds (‖x‖ ^ 2)) ∧
        x ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value ∧
        (∀ j, ‖r j‖ ^ 2 ≤
          ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + ε j) ∧
        Tendsto ε atTop (nhds 0) ∧
        Tendsto
          (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015228 m n (r j) - r j‖)
          atTop (nhds 0) ∧
        Tendsto
          (fun j ↦
            ‖_root_.GD.N0232.N0720.N1146.d015229 m n (r j) - r j‖)
          atTop (nhds 0) := by
  constructor
  · intro hendpoint
    obtain ⟨s, hstrict, hTwo, hThree⟩ :=
      (_root_.GD.N0232.N0720.N1482.d015172
        (m := m) (n := n) hm hn).1 hendpoint
    let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
    let hp : _root_.GD.N0232.N0720.N1159.d014637 m n p :=
      _root_.GD.N0232.N0720.N1159.d014644 m n s p
        (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
    have hTwoValue : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp = p := by
      have h := congrArg Subtype.val
        ((_root_.GD.N0232.N0720.N1159.d014651 m n s _root_.GD.N0232.N0720.N1482.d015130).1 hTwo)
      exact h
    have hThreeValue :
        _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp = p := by
      have h := congrArg Subtype.val
        ((_root_.GD.N0232.N0720.N1159.d014651
          m n s _root_.GD.N0232.N0720.N1482.d015131).1 hThree)
      exact h
    have hTwoRef : _root_.GD.N0232.N0720.N1146.d015228 m n p = p := by
      change _root_.GD.N0232.N0720.N1146.d015212 m n
        (_root_.GD.N0232.N0720.N1146.d015221 m n) p = p
      rw [_root_.GD.N0232.N0720.N1146.d015218
        m n (_root_.GD.N0232.N0720.N1146.d015221 m n) p hp]
      exact hTwoValue
    have hThreeRef : _root_.GD.N0232.N0720.N1146.d015229 m n p = p := by
      change _root_.GD.N0232.N0720.N1146.d015212 m n
        (_root_.GD.N0232.N0720.N1146.d015222 m n) p = p
      rw [_root_.GD.N0232.N0720.N1146.d015218
        m n (_root_.GD.N0232.N0720.N1146.d015222 m n) p hp]
      exact hThreeValue
    refine ⟨s, fun _ ↦ p, p, fun _ ↦ 0, hstrict, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · exact (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
    · intro j
      simp [p]
    · exact tendsto_const_nhds
    · simp [hTwoRef]
    · simp [hThreeRef]
  · rintro ⟨s, r, x, ε, hstrict, hprobe, houter, hradial, hε,
      hTwo, hThree⟩
    exact _root_.GD.N0232.N0720.N1461.d015689
      m n hm hn s hstrict r x ε hprobe houter hradial hε hTwo hThree




theorem d015692
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
        (r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (ε : ℕ → ℝ),
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
          (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
        Tendsto
          (fun j ↦ Metric.infDist (r j) (_root_.GD.N0232.N0720.N1159.d014630 m n s.value))
          atTop (nhds 0) ∧
        (∀ j, ‖r j‖ ^ 2 ≤
          ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + ε j) ∧
        Tendsto ε atTop (nhds 0) ∧
        Tendsto
          (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015228 m n (r j) - r j‖)
          atTop (nhds 0) ∧
        Tendsto
          (fun j ↦
            ‖_root_.GD.N0232.N0720.N1146.d015229 m n (r j) - r j‖)
          atTop (nhds 0) := by
  constructor
  · intro hendpoint
    obtain ⟨s, hstrict, hTwo, hThree⟩ :=
      (_root_.GD.N0232.N0720.N1482.d015172
        (m := m) (n := n) hm hn).1 hendpoint
    let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
    let hp : _root_.GD.N0232.N0720.N1159.d014637 m n p :=
      _root_.GD.N0232.N0720.N1159.d014644 m n s p
        (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
    have hTwoValue : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp = p := by
      exact congrArg Subtype.val
        ((_root_.GD.N0232.N0720.N1159.d014651 m n s _root_.GD.N0232.N0720.N1482.d015130).1 hTwo)
    have hThreeValue :
        _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp = p := by
      exact congrArg Subtype.val
        ((_root_.GD.N0232.N0720.N1159.d014651
          m n s _root_.GD.N0232.N0720.N1482.d015131).1 hThree)
    have hTwoRef : _root_.GD.N0232.N0720.N1146.d015228 m n p = p := by
      change _root_.GD.N0232.N0720.N1146.d015212 m n
        (_root_.GD.N0232.N0720.N1146.d015221 m n) p = p
      rw [_root_.GD.N0232.N0720.N1146.d015218
        m n (_root_.GD.N0232.N0720.N1146.d015221 m n) p hp]
      exact hTwoValue
    have hThreeRef : _root_.GD.N0232.N0720.N1146.d015229 m n p = p := by
      change _root_.GD.N0232.N0720.N1146.d015212 m n
        (_root_.GD.N0232.N0720.N1146.d015222 m n) p = p
      rw [_root_.GD.N0232.N0720.N1146.d015218
        m n (_root_.GD.N0232.N0720.N1146.d015222 m n) p hp]
      exact hThreeValue
    refine ⟨s, fun _ ↦ p, fun _ ↦ 0, hstrict, ?_, ?_, ?_, ?_, ?_⟩
    · have hpMem : p ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
        (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
      have hzero : Metric.infDist p (_root_.GD.N0232.N0720.N1159.d014630 m n s.value) = 0 :=
        Metric.infDist_zero_of_mem hpMem
      simp [hzero]
    · intro j
      simp [p]
    · exact tendsto_const_nhds
    · simp [hTwoRef]
    · simp [hThreeRef]
  · rintro ⟨s, r, ε, hstrict, houter, hradial, hε, hTwo, hThree⟩
    exact _root_.GD.N0232.N0720.N1461.d015690
      m n hm hn s hstrict r ε houter hradial hε hTwo hThree

end
end N1461
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1461.d015685
#print axioms _root_.GD.N0232.N0720.N1461.d015684
#print axioms _root_.GD.N0232.N0720.N1461.d015688
#print axioms _root_.GD.N0232.N0720.N1461.d015689
#print axioms _root_.GD.N0232.N0720.N1461.d015690
#print axioms _root_.GD.N0232.N0720.N1461.d015691
#print axioms _root_.GD.N0232.N0720.N1461.d015692
