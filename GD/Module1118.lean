import GD.Module0970
import GD.Module1117
import GD.Module1032
import GD.Module1065
import GD.Module0997



















open Filter MeasureTheory Set Topology
open scoped ENNReal BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1122

noncomputable section

open _root_.GD.N0232.N0720.N1029
open _root_.GD.N0232.N0720.N1032
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1099
open _root_.GD.N0232.N0720.N1116
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1200
open _root_.GD.N0232.N0720.N1204
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1461
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1482

variable {m n : ℕ}





noncomputable def d017962
    (m n : ℕ) (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) : ℝ :=
  ‖_root_.GD.N0232.N0720.N1146.d015228 m n q - q‖ ^ 2 +
    ‖_root_.GD.N0232.N0720.N1146.d015229 m n q - q‖ ^ 2

theorem d017963
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    0 ≤ _root_.GD.N0232.N0720.N1122.d017962 m n q := by
  unfold _root_.GD.N0232.N0720.N1122.d017962
  positivity



theorem d017964 :
    Continuous (_root_.GD.N0232.N0720.N1122.d017962 m n) := by
  have htwo : Continuous (_root_.GD.N0232.N0720.N1146.d015228 m n) :=
    (_root_.GD.N0232.N0720.N1146.d015216 m n
      (_root_.GD.N0232.N0720.N1146.d015221 m n)).continuous
  have hthree :
      Continuous (_root_.GD.N0232.N0720.N1146.d015229 m n) :=
    (_root_.GD.N0232.N0720.N1146.d015216 m n
      (_root_.GD.N0232.N0720.N1146.d015222 m n)).continuous
  exact
    ((htwo.sub continuous_id).norm.pow 2).add
      ((hthree.sub continuous_id).norm.pow 2)



theorem d017965
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1122.d017962 m n
        (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
      _root_.GD.N0232.N0720.N1477.d015749 m n s := by
  unfold _root_.GD.N0232.N0720.N1122.d017962
    _root_.GD.N0232.N0720.N1477.d015749 _root_.GD.N0232.N0720.N1146.d015228
    _root_.GD.N0232.N0720.N1146.d015229
  rw [_root_.GD.N0232.N0720.N1204.d015777
      m n (_root_.GD.N0232.N0720.N1146.d015221 m n) s,
    _root_.GD.N0232.N0720.N1204.d015777
      m n (_root_.GD.N0232.N0720.N1146.d015222 m n) s]



variable {width : ℕ → ℕ}



theorem d017966
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ∀ j, Fin (width j) → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (htight : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
        (packet j) (weight j) (hweight j))
      atTop (nhds (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)) := by
  exact _root_.GD.N0232.N0720.N1032.d017955
    s (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
      packet weight hweight htight



theorem d017967
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ∀ j, Fin (width j) → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (htight : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1122.d017962 m n
        (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
          (packet j) (weight j) (hweight j)))
      atTop (nhds (_root_.GD.N0232.N0720.N1477.d015749 m n s)) := by
  have hcompletion :=
    _root_.GD.N0232.N0720.N1122.d017966
      s packet weight hweight htight
  have henergy :=
    _root_.GD.N0232.N0720.N1122.d017964
      (m := m) (n := n) |>.continuousAt.tendsto.comp hcompletion
  change Tendsto
    (fun j ↦ _root_.GD.N0232.N0720.N1122.d017962 m n
      (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
        (packet j) (weight j) (hweight j)))
    atTop
    (nhds (_root_.GD.N0232.N0720.N1122.d017962 m n
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value))) at henergy
  simpa only [_root_.GD.N0232.N0720.N1122.d017965]
    using henergy



theorem d017968
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    ∃ (width : ℕ → ℕ)
        (packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168)
        (weight : ∀ j, Fin (width j) → ℝ)
        (hweight : ∀ j i, 0 ≤ weight j i),
      Tendsto
        (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
          _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
        atTop (nhds 0) ∧
      Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1122.d017962 m n
          (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
            (packet j) (weight j) (hweight j)))
        atTop (nhds (_root_.GD.N0232.N0720.N1477.d015749 m n s)) := by
  obtain ⟨width, packet, weight, hweight, htight⟩ :=
    _root_.GD.N0232.N0720.N1116.d016457 s
  refine ⟨width, packet, weight, hweight, htight, ?_⟩
  simpa only using
    _root_.GD.N0232.N0720.N1122.d017967
      s packet weight hweight htight





theorem d017969
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 ↔
      ∃ (width : ℕ → ℕ)
          (packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168)
          (weight : ∀ j, Fin (width j) → ℝ)
          (hweight : ∀ j i, 0 ≤ weight j i),
        Tendsto
          (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
            _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
          atTop (nhds 0) ∧
        Tendsto
          (fun j ↦ _root_.GD.N0232.N0720.N1122.d017962 m n
            (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
              (packet j) (weight j) (hweight j)))
          atTop (nhds 0) := by
  constructor
  · intro hzero
    obtain ⟨width, packet, weight, hweight, htight⟩ :=
      _root_.GD.N0232.N0720.N1116.d016457 s
    refine ⟨width, packet, weight, hweight, htight, ?_⟩
    simpa only [hzero] using
      _root_.GD.N0232.N0720.N1122.d017967
        s packet weight hweight htight
  · rintro ⟨width, packet, weight, hweight, htight, hresidual⟩
    have hlimit :=
      _root_.GD.N0232.N0720.N1122.d017967
        s packet weight hweight htight
    exact tendsto_nhds_unique hlimit hresidual




theorem d017970
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∃ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
          (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) ∧
        ∃ (width : ℕ → ℕ)
            (packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168)
            (weight : ∀ j, Fin (width j) → ℝ)
            (hweight : ∀ j i, 0 ≤ weight j i),
          Tendsto
            (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
              _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
            atTop (nhds 0) ∧
          Tendsto
            (fun j ↦ _root_.GD.N0232.N0720.N1122.d017962 m n
              (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
                (packet j) (weight j) (hweight j)))
            atTop (nhds 0) := by
  rw [_root_.GD.N0232.N0720.N1482.d015173
    (m := m) (n := n) hm hn]
  constructor
  · rintro ⟨s, hstrict, hmaster⟩
    refine ⟨s, hstrict, ?_⟩
    exact
      (_root_.GD.N0232.N0720.N1122.d017969 s).1
        ((_root_.GD.N0232.N0720.N1477.d015755
          (m := m) (n := n) s).1 hmaster)
  · rintro ⟨s, hstrict, hrow⟩
    refine ⟨s, hstrict, ?_⟩
    exact
      (_root_.GD.N0232.N0720.N1477.d015755
        (m := m) (n := n) s).2
        ((_root_.GD.N0232.N0720.N1122.d017969
          s).2 hrow)






private theorem d017971
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (henergy : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0) :
    ∃ candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074,
      Tendsto
        (fun j ↦ _root_.GD.N0232.N0720.N1130.d017080 m n s (candidate j))
        atTop (nhds 0) := by
  obtain ⟨width, packet, weight, hweight, htight⟩ :=
    _root_.GD.N0232.N0720.N1116.d016457 s
  let candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074 := fun j ↦
    { width := width j
      packet := packet j
      weight := weight j
      weight_nonneg := hweight j }
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  let r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := fun j ↦
    _root_.GD.N0232.N0720.N1130.d017075 m n (candidate j)
  have hp : p ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
    (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have hr : Tendsto r atTop (nhds p) := by
    simpa only [r, candidate, _root_.GD.N0232.N0720.N1130.d017075] using
      _root_.GD.N0232.N0720.N1122.d017966
        s packet weight hweight htight
  have hdistance : Tendsto (fun j ↦ ‖r j - p‖) atTop (nhds 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hr
  have houter : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017076 m n s (candidate j))
      atTop (nhds 0) := by
    apply squeeze_zero
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017081 m n s (candidate j))
      (fun j ↦ ?_) hdistance
    simpa only [_root_.GD.N0232.N0720.N1130.d017076, r, dist_eq_norm] using
      (Metric.infDist_le_dist_of_mem hp)
  have hreserve : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds (‖p‖ ^ 2)) := by
    have hconstant : Tendsto (fun _ : ℕ ↦ ‖p‖ ^ 2)
        atTop (nhds (‖p‖ ^ 2)) := tendsto_const_nhds
    have h := hconstant.sub htight
    simpa only [p, sub_sub_cancel, sub_zero] using h
  have hnormSq : Tendsto (fun j ↦ ‖r j‖ ^ 2)
      atTop (nhds (‖p‖ ^ 2)) := hr.norm.pow 2
  have hradialRaw : Tendsto
      (fun j ↦ ‖r j‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0) := by
    simpa only [sub_self] using hnormSq.sub hreserve
  have hradial : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017077 m n s (candidate j))
      atTop (nhds 0) := by
    apply squeeze_zero
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017082 m n s (candidate j))
      (fun j ↦ ?_)
      ((tendsto_zero_iff_abs_tendsto_zero _).1 hradialRaw)
    change max
        (‖r j‖ ^ 2 - _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j)) 0 ≤
      |‖r j‖ ^ 2 - _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j)|
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hterminalResidual :
      _root_.GD.N0232.N0720.N1122.d017962 m n p = 0 := by
    simpa only [p, _root_.GD.N0232.N0720.N1122.d017965]
      using henergy
  have htwoAtP :
      ‖_root_.GD.N0232.N0720.N1146.d015228 m n p - p‖ = 0 := by
    unfold _root_.GD.N0232.N0720.N1122.d017962 at hterminalResidual
    nlinarith [sq_nonneg
        ‖_root_.GD.N0232.N0720.N1146.d015228 m n p - p‖,
      sq_nonneg
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n p - p‖]
  have hthreeAtP :
      ‖_root_.GD.N0232.N0720.N1146.d015229 m n p - p‖ = 0 := by
    unfold _root_.GD.N0232.N0720.N1122.d017962 at hterminalResidual
    nlinarith [sq_nonneg
        ‖_root_.GD.N0232.N0720.N1146.d015228 m n p - p‖,
      sq_nonneg
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n p - p‖]
  have htwo : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017078 m n (candidate j))
      atTop (nhds 0) := by
    have hcontinuous : Continuous
        (fun q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) ↦
          ‖_root_.GD.N0232.N0720.N1146.d015228 m n q - q‖) :=
      ((_root_.GD.N0232.N0720.N1146.d015216 m n
        (_root_.GD.N0232.N0720.N1146.d015221 m n)).continuous.sub
          continuous_id).norm
    have h := hcontinuous.continuousAt.tendsto.comp hr
    change Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015228 m n (r j) - r j‖)
      atTop
      (nhds ‖_root_.GD.N0232.N0720.N1146.d015228 m n p - p‖) at h
    simpa only [_root_.GD.N0232.N0720.N1130.d017078, r, htwoAtP] using h
  have hthree : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017079 m n (candidate j))
      atTop (nhds 0) := by
    have hcontinuous : Continuous
        (fun q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) ↦
          ‖_root_.GD.N0232.N0720.N1146.d015229 m n q - q‖) :=
      ((_root_.GD.N0232.N0720.N1146.d015216 m n
        (_root_.GD.N0232.N0720.N1146.d015222 m n)).continuous.sub
          continuous_id).norm
    have h := hcontinuous.continuousAt.tendsto.comp hr
    change Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n (r j) - r j‖)
      atTop
      (nhds ‖_root_.GD.N0232.N0720.N1146.d015229 m n p - p‖) at h
    simpa only [_root_.GD.N0232.N0720.N1130.d017079, r, hthreeAtP] using h
  refine ⟨candidate, ?_⟩
  simpa only [_root_.GD.N0232.N0720.N1130.d017080, zero_add, add_zero] using
    ((houter.add hradial).add htwo).add hthree




private theorem d017972
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (candidate : ℕ → _root_.GD.N0232.N0720.N1130.d017074)
    (hdefect : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017080 m n s (candidate j))
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 := by
  let r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := fun j ↦
    _root_.GD.N0232.N0720.N1130.d017075 m n (candidate j)
  let epsilon : ℕ → ℝ := fun j ↦
    _root_.GD.N0232.N0720.N1130.d017077 m n s (candidate j)
  have houter : Tendsto
      (fun j ↦ Metric.infDist (r j) (_root_.GD.N0232.N0720.N1159.d014630 m n s.value))
      atTop (nhds 0) := by
    apply squeeze_zero
      (fun _ ↦ Metric.infDist_nonneg)
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017086 m n s (candidate j))
      hdefect
  have hepsilon : Tendsto epsilon atTop (nhds 0) := by
    exact squeeze_zero
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017082 m n s (candidate j))
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017087 m n s (candidate j))
      hdefect
  have hradial : ∀ j, ‖r j‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + epsilon j := by
    intro j
    have hreserve :=
      _root_.GD.N0232.N0720.N1126.d016437
        s (candidate j).packet (candidate j).weight
          (candidate j).weight_nonneg
    have hdistanceNonneg :
        0 ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value - r j‖ ^ 2 :=
      sq_nonneg _
    have hgapLe :
        ‖r j‖ ^ 2 - _root_.GD.N0232.N0720.N1126.d016432 s
            (candidate j).packet (candidate j).weight ≤ epsilon j := by
      dsimp only [epsilon, _root_.GD.N0232.N0720.N1130.d017077]
      exact le_max_left _ _
    dsimp only [r, _root_.GD.N0232.N0720.N1130.d017075] at hreserve hdistanceNonneg hgapLe ⊢
    linarith
  have htwo : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1146.d015228 m n (r j) - r j‖)
      atTop (nhds 0) := by
    exact squeeze_zero
      (fun _ ↦ norm_nonneg _)
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017088 m n s (candidate j))
      hdefect
  have hthree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015229 m n (r j) - r j‖)
      atTop (nhds 0) := by
    exact squeeze_zero
      (fun _ ↦ norm_nonneg _)
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017089 m n s (candidate j))
      hdefect
  have hfixed :=
    _root_.GD.N0232.N0720.N1461.d015686
      m n s r epsilon houter hradial hepsilon htwo hthree
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  let hp : _root_.GD.N0232.N0720.N1159.d014637 m n p :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s p
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have htwoRef : _root_.GD.N0232.N0720.N1146.d015228 m n p = p := by
    change _root_.GD.N0232.N0720.N1146.d015212 m n
      (_root_.GD.N0232.N0720.N1146.d015221 m n) p = p
    rw [_root_.GD.N0232.N0720.N1146.d015218 m n
      (_root_.GD.N0232.N0720.N1146.d015221 m n) p hp]
    exact hfixed.1
  have hthreeRef : _root_.GD.N0232.N0720.N1146.d015229 m n p = p := by
    change _root_.GD.N0232.N0720.N1146.d015212 m n
      (_root_.GD.N0232.N0720.N1146.d015222 m n) p = p
    rw [_root_.GD.N0232.N0720.N1146.d015218 m n
      (_root_.GD.N0232.N0720.N1146.d015222 m n) p hp]
    exact hfixed.2
  rw [← _root_.GD.N0232.N0720.N1122.d017965
    (m := m) (n := n) s]
  unfold _root_.GD.N0232.N0720.N1122.d017962
  rw [show _root_.GD.N0232.N0720.N1159.d014633 m n s.value = p by rfl,
    htwoRef, hthreeRef, sub_self, norm_zero]
  norm_num




theorem d017973
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1130.d017091 m n s ↔
      _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 := by
  classical
  constructor
  · intro hsmall
    have hchoose : ∀ j : ℕ, ∃ c : _root_.GD.N0232.N0720.N1130.d017074,
        _root_.GD.N0232.N0720.N1130.d017080 m n s c < 1 / ((j : ℝ) + 1) := by
      intro j
      exact hsmall (1 / ((j : ℝ) + 1)) (by positivity)
    choose candidate hcandidate using hchoose
    apply _root_.GD.N0232.N0720.N1122.d017972
      s candidate
    exact squeeze_zero
      (fun j ↦ _root_.GD.N0232.N0720.N1130.d017085 m n s (candidate j))
      (fun j ↦ (hcandidate j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · intro henergy epsilon hepsilon
    obtain ⟨candidate, hdefect⟩ :=
      _root_.GD.N0232.N0720.N1122.d017971
        s henergy
    have heventually : ∀ᶠ j in atTop,
        _root_.GD.N0232.N0720.N1130.d017080 m n s (candidate j) < epsilon :=
      (tendsto_order.1 hdefect).2 epsilon hepsilon
    obtain ⟨j, hj⟩ := heventually.exists
    exact ⟨candidate j, hj⟩




theorem d017974
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    0 < _root_.GD.N0232.N0720.N1477.d015749 m n s ↔
      ∃ eta : ℝ, 0 < eta ∧
        ∀ candidate : _root_.GD.N0232.N0720.N1130.d017074,
          eta ≤ _root_.GD.N0232.N0720.N1130.d017080 m n s candidate := by
  constructor
  · intro hpositive
    by_contra hfloor
    have hsmall : _root_.GD.N0232.N0720.N1130.d017091 m n s := by
      intro epsilon hepsilon
      by_contra hnone
      have hall : ∀ candidate : _root_.GD.N0232.N0720.N1130.d017074,
          epsilon ≤ _root_.GD.N0232.N0720.N1130.d017080 m n s candidate := by
        intro candidate
        exact le_of_not_gt (fun hlt ↦ hnone ⟨candidate, hlt⟩)
      exact hfloor ⟨epsilon, hepsilon, hall⟩
    exact (ne_of_gt hpositive)
      ((_root_.GD.N0232.N0720.N1122.d017973
        s).1 hsmall)
  · rintro ⟨eta, heta, hfloor⟩
    have hnotSmall :
        ¬ _root_.GD.N0232.N0720.N1130.d017091 m n s := by
      intro hsmall
      obtain ⟨candidate, hcandidate⟩ := hsmall eta heta
      exact (not_lt_of_ge (hfloor candidate)) hcandidate
    have hne : _root_.GD.N0232.N0720.N1477.d015749 m n s ≠ 0 := by
      intro hzero
      exact hnotSmall
        ((_root_.GD.N0232.N0720.N1122.d017973
          s).2 hzero)
    exact lt_of_le_of_ne
      (_root_.GD.N0232.N0720.N1099.d015757 m n s) (Ne.symm hne)





theorem d017975
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ¬ _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      ∀ s : _root_.GD.N0232.N0720.N1159.d014639 m n,
        _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
            (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) →
          ∃ eta : ℝ, 0 < eta ∧
            ∀ candidate : _root_.GD.N0232.N0720.N1130.d017074,
              eta ≤ _root_.GD.N0232.N0720.N1130.d017080 m n s candidate := by
  constructor
  · intro hno s hstrict
    exact _root_.GD.N0232.N0720.N1130.d017093
      m n hm hn hno s hstrict
  · intro hfloor hexists
    obtain ⟨s, hstrict, hmaster⟩ :=
      (_root_.GD.N0232.N0720.N1482.d015173
        (m := m) (n := n) hm hn).1 hexists
    have henergy : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 :=
      (_root_.GD.N0232.N0720.N1477.d015755
        (m := m) (n := n) s).1 hmaster
    obtain ⟨eta, heta, hall⟩ := hfloor s hstrict
    have hsmall :=
      (_root_.GD.N0232.N0720.N1122.d017973
        s).2 henergy
    obtain ⟨candidate, hcandidate⟩ := hsmall eta heta
    exact (not_lt_of_ge (hall candidate)) hcandidate






theorem d017976
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1477.d015749 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) = 0 ↔
      _root_.GD.N0232.N0720.N1201.d015333 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) = 0 := by
  let s := _root_.GD.N0232.N0720.N1029.d015372 m n hm hn
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  constructor
  · intro henergy
    have hpSeed : p ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
    have hpFinite : _root_.GD.N0232.N0720.N1159.d014637 m n p :=
      _root_.GD.N0232.N0720.N1159.d014644 m n s p hpSeed
    obtain ⟨hTwoPoint, hThreePoint⟩ :=
      (_root_.GD.N0232.N0720.N1477.d015754
        (m := m) (n := n) s).1 henergy
    have hTwo : _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hpFinite = p := by
      have hvalue := congrArg Subtype.val hTwoPoint
      change _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hpFinite = p at hvalue
      exact hvalue
    have hThree :
        _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hpFinite = p := by
      have hvalue := congrArg Subtype.val hThreePoint
      change _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hpFinite = p
        at hvalue
      exact hvalue
    have hall : ∀ g : _root_.GD.N0232.N0720.N1482.d015118,
        _root_.GD.N0232.N0720.N1159.d014642 m n g p hpFinite = p :=
      _root_.GD.N0232.N0720.N1482.d015167
        (m := m) (n := n) p hpFinite hTwo hThree
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
    unfold _root_.GD.N0232.N0720.N1201.d015333
    change ‖s.value‖ ^ 2 - ‖p‖ ^ 2 = 0
    rw [heq]
    change ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ ^ 2 -
      ‖_root_.GD.N0232.N0720.N1029.d015364 m n hm hn‖ ^ 2 = 0
    exact sub_self _
  · intro hgap
    exact
      (_root_.GD.N0232.N0720.N1477.d015755
        (m := m) (n := n) s).1
        (_root_.GD.N0232.N0720.N1201.d015337
          m n s hgap)





theorem d017977
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1201.d015333 m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) = 0 ↔
      ∃ (width : ℕ → ℕ)
          (packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168)
          (weight : ∀ j, Fin (width j) → ℝ)
          (hweight : ∀ j i, 0 ≤ weight j i),
        Tendsto
          (fun j ↦
            ‖_root_.GD.N0232.N0720.N1159.d014633 m n
                (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn).value‖ ^ 2 -
              _root_.GD.N0232.N0720.N1126.d016432 (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn)
                (packet j) (weight j))
          atTop (nhds 0) ∧
        Tendsto
          (fun j ↦ _root_.GD.N0232.N0720.N1122.d017962 m n
            (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
              (packet j) (weight j) (hweight j)))
          atTop (nhds 0) := by
  rw [← _root_.GD.N0232.N0720.N1122.d017976
      (m := m) (n := n) hm hn]
  exact
    _root_.GD.N0232.N0720.N1122.d017969
      (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn)

end

end N1122
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1122.d017967
#print axioms _root_.GD.N0232.N0720.N1122.d017969
#print axioms _root_.GD.N0232.N0720.N1122.d017970
#print axioms _root_.GD.N0232.N0720.N1122.d017973
#print axioms _root_.GD.N0232.N0720.N1122.d017974
#print axioms _root_.GD.N0232.N0720.N1122.d017975
#print axioms _root_.GD.N0232.N0720.N1122.d017977
