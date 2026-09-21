import GD.Module1043











































open Filter MeasureTheory
open scoped ENNReal BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1481

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0617
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1127
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1162
open _root_.GD.N0232.N0720.N1163
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1461
open _root_.GD.N0232.N0720.N1499

abbrev d017060 :=
  _root_.GD.N0232.N0719.N0946.d009229

variable {m n : ℕ}
variable {ι : ℕ → Type*}
variable [∀ j, Fintype (ι j)] [∀ j, DecidableEq (ι j)]

set_option linter.unusedSectionVars false









def d017061
    (packet : ∀ j, ι j → _root_.GD.N0232.N0720.N1080.d014168) (weight : ∀ j, ι j → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i) (scale : ℕ → ℕ) (j : ℕ) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0232.N0720.N1126.d016426 (packet j)
    (_root_.GD.N0232.N0720.N1162.d016619 (scale j : ℝ) (weight j))
    (_root_.GD.N0232.N0720.N1163.d016632 (weight j) (hweight j)
      (Nat.cast_nonneg (scale j)))




def d017062
    (g : _root_.GD.N0232.N0720.N1481.d017060)
    (packet : ∀ j, ι j → _root_.GD.N0232.N0720.N1080.d014168) (weight : ∀ j, ι j → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i) (scale : ℕ → ℕ) (j : ℕ) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  _root_.GD.N0232.N0720.N1126.d016426
    (fun i ↦ _root_.GD.N0232.N0720.N1215.d014272 g (packet j i))
    (_root_.GD.N0232.N0720.N1162.d016619 (scale j : ℝ) (weight j))
    (_root_.GD.N0232.N0720.N1163.d016632 (weight j) (hweight j)
      (Nat.cast_nonneg (scale j)))




theorem d017063
    (g : _root_.GD.N0232.N0720.N1481.d017060) (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g)
    (packet : ∀ j, ι j → _root_.GD.N0232.N0720.N1080.d014168) (weight : ∀ j, ι j → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i) (scale : ℕ → ℕ) (j : ℕ) :
    ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate
          (_root_.GD.N0232.N0720.N1481.d017061 (m := m) (n := n)
            packet weight hweight scale j) -
        _root_.GD.N0232.N0720.N1481.d017061 (m := m) (n := n)
          packet weight hweight scale j‖ ≤
      ‖_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n) g (scale j) (packet j) (weight j) (hweight j)‖ +
        ‖_root_.GD.N0232.N0720.N1481.d017062 (m := m) (n := n)
            g packet weight hweight scale j -
          _root_.GD.N0232.N0720.N1481.d017061 (m := m) (n := n)
            packet weight hweight scale j‖ := by
  simpa only [_root_.GD.N0232.N0720.N1481.d017061,
    _root_.GD.N0232.N0720.N1481.d017062] using
    (_root_.GD.N0232.N0720.N1163.d016645
      (m := m) (n := n) g certificate (scale j)
      (packet j) (weight j) (hweight j))



theorem d017064
    (g : _root_.GD.N0232.N0720.N1481.d017060) (certificate : _root_.GD.N0232.N0720.N1146.d015208 m n g)
    (packet : ∀ j, ι j → _root_.GD.N0232.N0720.N1080.d014168) (weight : ∀ j, ι j → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i) (scale : ℕ → ℕ)
    (hcovariance : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n) g (scale j) (packet j) (weight j) (hweight j)‖)
      atTop (nhds 0))
    (hskeleton : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1481.d017062 (m := m) (n := n)
            g packet weight hweight scale j -
          _root_.GD.N0232.N0720.N1481.d017061 (m := m) (n := n)
            packet weight hweight scale j‖)
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate
            (_root_.GD.N0232.N0720.N1481.d017061 (m := m) (n := n)
              packet weight hweight scale j) -
          _root_.GD.N0232.N0720.N1481.d017061 (m := m) (n := n)
            packet weight hweight scale j‖)
      atTop (nhds 0) := by
  have hupper : ∀ j : ℕ,
      ‖_root_.GD.N0232.N0720.N1146.d015212 m n certificate
            (_root_.GD.N0232.N0720.N1481.d017061 (m := m) (n := n)
              packet weight hweight scale j) -
          _root_.GD.N0232.N0720.N1481.d017061 (m := m) (n := n)
            packet weight hweight scale j‖ ≤
        ‖_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n) g (scale j)
            (packet j) (weight j) (hweight j)‖ +
        ‖_root_.GD.N0232.N0720.N1481.d017062 (m := m) (n := n)
            g packet weight hweight scale j -
          _root_.GD.N0232.N0720.N1481.d017061 (m := m) (n := n)
            packet weight hweight scale j‖ := by
    intro j
    exact _root_.GD.N0232.N0720.N1481.d017063
      g certificate packet weight hweight scale j
  have hmajor : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n) g (scale j)
            (packet j) (weight j) (hweight j)‖ +
        ‖_root_.GD.N0232.N0720.N1481.d017062 (m := m) (n := n)
            g packet weight hweight scale j -
          _root_.GD.N0232.N0720.N1481.d017061 (m := m) (n := n)
            packet weight hweight scale j‖)
      atTop (nhds 0) := by
    simpa only [zero_add] using hcovariance.add hskeleton
  exact squeeze_zero
    (fun j ↦ norm_nonneg
      (_root_.GD.N0232.N0720.N1146.d015212 m n certificate
          (_root_.GD.N0232.N0720.N1481.d017061 (m := m) (n := n)
            packet weight hweight scale j) -
        _root_.GD.N0232.N0720.N1481.d017061 (m := m) (n := n)
          packet weight hweight scale j))
    hupper hmajor














theorem d017065
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (packet : ∀ j, ι j → _root_.GD.N0232.N0720.N1080.d014168) (weight : ∀ j, ι j → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i) (scale : ℕ → ℕ)
    (houter : Tendsto
      (fun j ↦ Metric.infDist
        (_root_.GD.N0232.N0720.N1481.d017061 (m := m) (n := n) packet weight hweight scale j)
        (_root_.GD.N0232.N0720.N1159.d014630 m n s.value))
      atTop (nhds 0))
    (hgap : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1481.d017061 (m := m) (n := n) packet weight hweight scale j‖ ^ 2 -
          _root_.GD.N0232.N0720.N1126.d016432 s (packet j)
            (_root_.GD.N0232.N0720.N1162.d016619 (scale j : ℝ) (weight j)))
      atTop (nhds 0))
    (hcovarianceTwo : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n)
          _root_.GD.N0232.N0720.N1482.d015130 (scale j)
          (packet j) (weight j) (hweight j)‖)
      atTop (nhds 0))
    (hcovarianceThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n)
          _root_.GD.N0232.N0720.N1482.d015131
          (scale j) (packet j) (weight j) (hweight j)‖)
      atTop (nhds 0))
    (hskeletonTwo : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1481.d017062 (m := m) (n := n)
            _root_.GD.N0232.N0720.N1482.d015130
            packet weight hweight scale j -
          _root_.GD.N0232.N0720.N1481.d017061 (m := m) (n := n) packet weight hweight scale j‖)
      atTop (nhds 0))
    (hskeletonThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1481.d017062 (m := m) (n := n)
            _root_.GD.N0232.N0720.N1482.d015131
            packet weight hweight scale j -
          _root_.GD.N0232.N0720.N1481.d017061 (m := m) (n := n) packet weight hweight scale j‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  let scaledWeight : ∀ j, ι j → ℝ := fun j ↦
    _root_.GD.N0232.N0720.N1162.d016619 (scale j : ℝ) (weight j)
  let scaledNonneg : ∀ j i, 0 ≤ scaledWeight j i := fun j ↦
    _root_.GD.N0232.N0720.N1163.d016632 (weight j) (hweight j)
      (Nat.cast_nonneg (scale j))
  have htwo :=
    _root_.GD.N0232.N0720.N1481.d017064
      (m := m) (n := n)
      _root_.GD.N0232.N0720.N1482.d015130
      (_root_.GD.N0232.N0720.N1146.d015221 m n)
      packet weight hweight scale hcovarianceTwo hskeletonTwo
  have hthree :=
    _root_.GD.N0232.N0720.N1481.d017064
      (m := m) (n := n)
      _root_.GD.N0232.N0720.N1482.d015131
      (_root_.GD.N0232.N0720.N1146.d015222 m n)
      packet weight hweight scale hcovarianceThree hskeletonThree
  let r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := fun j ↦
    _root_.GD.N0232.N0720.N1126.d016426 (packet j) (scaledWeight j) (scaledNonneg j)
  let epsilon : ℕ → ℝ := fun j ↦
    ‖r j‖ ^ 2 - _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (scaledWeight j)
  apply _root_.GD.N0232.N0720.N1461.d015690
    m n hm hn s hstrict r epsilon
  · simpa only [r, scaledWeight, scaledNonneg,
      _root_.GD.N0232.N0720.N1481.d017061] using houter
  · intro j
    have hreserve :=
      _root_.GD.N0232.N0720.N1126.d016437
        s (packet j) (scaledWeight j) (scaledNonneg j)
    have hdistanceNonneg :
        0 ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value - r j‖ ^ 2 :=
      sq_nonneg _
    dsimp only [epsilon]
    linarith
  · simpa only [epsilon, r, scaledWeight, scaledNonneg,
      _root_.GD.N0232.N0720.N1481.d017061] using hgap
  · simpa only [r, scaledWeight, scaledNonneg,
      _root_.GD.N0232.N0720.N1481.d017061, _root_.GD.N0232.N0720.N1146.d015228] using htwo
  · simpa only [r, scaledWeight, scaledNonneg,
      _root_.GD.N0232.N0720.N1481.d017061,
      _root_.GD.N0232.N0720.N1146.d015229] using hthree




def d017066
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet : ∀ j, ι j → _root_.GD.N0232.N0720.N1080.d014168) (weight : ∀ j, ι j → ℝ)
    (j : ℕ) : ℝ :=
  _root_.GD.N0232.N0720.N1127.d016545 m n s (packet j) (weight j)



theorem d017067
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet : ∀ j, ι j → _root_.GD.N0232.N0720.N1080.d014168) (weight : ∀ j, ι j → ℝ)
    (scale : ℕ → ℕ) (j : ℕ) :
    _root_.GD.N0232.N0720.N1127.d016545 m n s (packet j)
        (_root_.GD.N0232.N0720.N1162.d016619 (scale j : ℝ) (weight j)) =
      (scale j : ℝ) * _root_.GD.N0232.N0720.N1481.d017066 s packet weight j := by
  exact _root_.GD.N0232.N0720.N1163.d016649
    s (packet j) (weight j) (scale j : ℝ)









theorem d017068
    (onset : ℕ → ℕ) (honset : Tendsto onset atTop atTop)
    (slack : ℕ → ℝ) (hslack : ∀ j, 0 ≤ slack j) :
    (∃ scale : ℕ → ℕ,
      Tendsto scale atTop atTop ∧
      (∀ j, onset j ≤ scale j) ∧
      Tendsto (fun j ↦ (scale j : ℝ) * slack j) atTop (nhds 0)) ↔
    Tendsto (fun j ↦ (onset j : ℝ) * slack j) atTop (nhds 0) := by
  constructor
  · rintro ⟨scale, _hscale, hge, hproduct⟩
    apply squeeze_zero
      (fun j ↦ mul_nonneg (Nat.cast_nonneg _) (hslack j))
      (fun j ↦ ?_) hproduct
    exact mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (hge j)) (hslack j)
  · intro hproduct
    exact ⟨onset, honset, fun j ↦ le_rfl, hproduct⟩





theorem d017069
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet : ∀ j, ι j → _root_.GD.N0232.N0720.N1080.d014168) (weight : ∀ j, ι j → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (onset : ℕ → ℕ) (honset : Tendsto onset atTop atTop) :
    (∃ scale : ℕ → ℕ,
      Tendsto scale atTop atTop ∧
      (∀ j, onset j ≤ scale j) ∧
      Tendsto
        (fun j ↦
          _root_.GD.N0232.N0720.N1127.d016545 m n s (packet j)
            (_root_.GD.N0232.N0720.N1162.d016619 (scale j : ℝ) (weight j)))
        atTop (nhds 0)) ↔
    Tendsto
      (fun j ↦ (onset j : ℝ) *
        _root_.GD.N0232.N0720.N1481.d017066 s packet weight j)
      atTop (nhds 0) := by
  let slack : ℕ → ℝ := fun j ↦
    _root_.GD.N0232.N0720.N1481.d017066 s packet weight j
  have hslack : ∀ j, 0 ≤ slack j := by
    intro j
    exact _root_.GD.N0232.N0720.N1127.d016549
      m n s (packet j) (weight j) (hweight j)
  have habstract :=
    _root_.GD.N0232.N0720.N1481.d017068
      onset honset slack hslack
  constructor
  · rintro ⟨scale, hscale, hge, hscaled⟩
    have hproduct : Tendsto
        (fun j ↦ (scale j : ℝ) * slack j) atTop (nhds 0) := by
      apply hscaled.congr'
      filter_upwards with j
      exact _root_.GD.N0232.N0720.N1481.d017067 s packet weight scale j
    simpa only [slack] using habstract.mp ⟨scale, hscale, hge, hproduct⟩
  · intro honsetProduct
    have honsetProduct' : Tendsto
        (fun j ↦ (onset j : ℝ) * slack j) atTop (nhds 0) := by
      simpa only [slack] using honsetProduct
    obtain ⟨scale, hscale, hge, hproduct⟩ := habstract.mpr honsetProduct'
    refine ⟨scale, hscale, hge, ?_⟩
    apply hproduct.congr'
    filter_upwards with j
    exact (_root_.GD.N0232.N0720.N1481.d017067
      s packet weight scale j).symm



def d017070
    (packet : ∀ j, ι j → _root_.GD.N0232.N0720.N1080.d014168) (weight : ∀ j, ι j → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (onset : ℕ → ℕ) (tolerance : ℕ → ℝ) : Prop :=
  ∀ j N, onset j ≤ N →
    ‖_root_.GD.N0232.N0720.N1163.d016641
      (m := m) (n := n)
      _root_.GD.N0232.N0720.N1482.d015130 N
      (packet j) (weight j) (hweight j)‖ ≤ tolerance j ∧
    ‖_root_.GD.N0232.N0720.N1163.d016641
      (m := m) (n := n)
      _root_.GD.N0232.N0720.N1482.d015131 N
      (packet j) (weight j) (hweight j)‖ ≤ tolerance j





theorem d017071
    (packet : ∀ j, ι j → _root_.GD.N0232.N0720.N1080.d014168) (weight : ∀ j, ι j → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (hpositive : ∀ j, ∃ i, 0 < weight j i)
    (tolerance : ℕ → ℝ) (htolerance : ∀ j, 0 < tolerance j) :
    ∃ onset : ℕ → ℕ,
      Tendsto onset atTop atTop ∧
      _root_.GD.N0232.N0720.N1481.d017070
        (m := m) (n := n) packet weight hweight onset tolerance := by
  have hchoice : ∀ j : ℕ, ∃ onset : ℕ,
      j ≤ onset ∧
      ∀ N, onset ≤ N →
        ‖_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n)
          _root_.GD.N0232.N0720.N1482.d015130 N
          (packet j) (weight j) (hweight j)‖ ≤ tolerance j ∧
        ‖_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n)
          _root_.GD.N0232.N0720.N1482.d015131 N
          (packet j) (weight j) (hweight j)‖ ≤ tolerance j := by
    intro j
    have htwo := _root_.GD.N0232.N0720.N1163.d016643
      (m := m) (n := n)
      _root_.GD.N0232.N0720.N1482.d015130
      (packet j) (weight j) (hweight j) (hpositive j)
    have hthree := _root_.GD.N0232.N0720.N1163.d016643
      (m := m) (n := n)
      _root_.GD.N0232.N0720.N1482.d015131
      (packet j) (weight j) (hweight j) (hpositive j)
    rw [Metric.tendsto_atTop] at htwo hthree
    obtain ⟨N₂, hN₂⟩ := htwo (tolerance j) (htolerance j)
    obtain ⟨N₃, hN₃⟩ := hthree (tolerance j) (htolerance j)
    let onset := max j (max N₂ N₃)
    refine ⟨onset, le_max_left _ _, ?_⟩
    intro N hN
    have hN₂N : N₂ ≤ N :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
    have hN₃N : N₃ ≤ N :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
    have htwoN := hN₂ N hN₂N
    have hthreeN := hN₃ N hN₃N
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (norm_nonneg _)] at htwoN hthreeN
    exact ⟨htwoN.le, hthreeN.le⟩
  choose onset honsetLower honset using hchoice
  have honsetTendsto : Tendsto onset atTop atTop := by
    exact tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall honsetLower) tendsto_id
  exact ⟨onset, honsetTendsto, honset⟩









theorem d017072
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet : ∀ j, ι j → _root_.GD.N0232.N0720.N1080.d014168) (weight : ∀ j, ι j → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (onset : ℕ → ℕ) (honset : Tendsto onset atTop atTop)
    (tolerance : ℕ → ℝ)
    (htolerance : Tendsto tolerance atTop (nhds 0))
    (hcovarianceOnset : _root_.GD.N0232.N0720.N1481.d017070
      (m := m) (n := n) packet weight hweight onset tolerance)
    (hmatched : Tendsto
      (fun j ↦ (onset j : ℝ) *
        _root_.GD.N0232.N0720.N1481.d017066 s packet weight j)
      atTop (nhds 0)) :
    Tendsto onset atTop atTop ∧
      Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1163.d016641
            (m := m) (n := n)
            _root_.GD.N0232.N0720.N1482.d015130 (onset j)
            (packet j) (weight j) (hweight j)‖)
        atTop (nhds 0) ∧
      Tendsto
        (fun j ↦
          ‖_root_.GD.N0232.N0720.N1163.d016641
            (m := m) (n := n)
            _root_.GD.N0232.N0720.N1482.d015131
            (onset j) (packet j) (weight j) (hweight j)‖)
        atTop (nhds 0) ∧
      Tendsto
        (fun j ↦
          _root_.GD.N0232.N0720.N1127.d016545 m n s (packet j)
            (_root_.GD.N0232.N0720.N1162.d016619 (onset j : ℝ) (weight j)))
        atTop (nhds 0) := by
  have htwo : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n)
          _root_.GD.N0232.N0720.N1482.d015130 (onset j)
          (packet j) (weight j) (hweight j)‖)
      atTop (nhds 0) := by
    apply squeeze_zero (fun j ↦ norm_nonneg _)
      (fun j ↦ (hcovarianceOnset j (onset j) le_rfl).1)
      htolerance
  have hthree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n)
          _root_.GD.N0232.N0720.N1482.d015131
          (onset j) (packet j) (weight j) (hweight j)‖)
      atTop (nhds 0) := by
    apply squeeze_zero (fun j ↦ norm_nonneg _)
      (fun j ↦ (hcovarianceOnset j (onset j) le_rfl).2)
      htolerance
  have hcomplementarity : Tendsto
      (fun j ↦
        _root_.GD.N0232.N0720.N1127.d016545 m n s (packet j)
          (_root_.GD.N0232.N0720.N1162.d016619 (onset j : ℝ) (weight j)))
      atTop (nhds 0) := by
    apply hmatched.congr'
    filter_upwards with j
    exact (_root_.GD.N0232.N0720.N1481.d017067
      s packet weight onset j).symm
  exact ⟨honset, htwo, hthree, hcomplementarity⟩










theorem d017073
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (packet : ∀ j, ι j → _root_.GD.N0232.N0720.N1080.d014168) (weight : ∀ j, ι j → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (onset : ℕ → ℕ)
    (tolerance : ℕ → ℝ)
    (htolerance : Tendsto tolerance atTop (nhds 0))
    (hcovarianceOnset : _root_.GD.N0232.N0720.N1481.d017070
      (m := m) (n := n) packet weight hweight onset tolerance)
    (houter : Tendsto
      (fun j ↦ Metric.infDist
        (_root_.GD.N0232.N0720.N1481.d017061 (m := m) (n := n) packet weight hweight onset j)
        (_root_.GD.N0232.N0720.N1159.d014630 m n s.value))
      atTop (nhds 0))
    (hgap : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1481.d017061 (m := m) (n := n) packet weight hweight onset j‖ ^ 2 -
          _root_.GD.N0232.N0720.N1126.d016432 s (packet j)
            (_root_.GD.N0232.N0720.N1162.d016619 (onset j : ℝ) (weight j)))
      atTop (nhds 0))
    (hskeletonTwo : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1481.d017062 (m := m) (n := n)
            _root_.GD.N0232.N0720.N1482.d015130
            packet weight hweight onset j -
          _root_.GD.N0232.N0720.N1481.d017061 (m := m) (n := n) packet weight hweight onset j‖)
      atTop (nhds 0))
    (hskeletonThree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1481.d017062 (m := m) (n := n)
            _root_.GD.N0232.N0720.N1482.d015131
            packet weight hweight onset j -
          _root_.GD.N0232.N0720.N1481.d017061 (m := m) (n := n) packet weight hweight onset j‖)
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  have htwo : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n)
          _root_.GD.N0232.N0720.N1482.d015130 (onset j)
          (packet j) (weight j) (hweight j)‖)
      atTop (nhds 0) := by
    exact squeeze_zero (fun j ↦ norm_nonneg _)
      (fun j ↦ (hcovarianceOnset j (onset j) le_rfl).1)
      htolerance
  have hthree : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1163.d016641
          (m := m) (n := n)
          _root_.GD.N0232.N0720.N1482.d015131
          (onset j) (packet j) (weight j) (hweight j)‖)
      atTop (nhds 0) := by
    exact squeeze_zero (fun j ↦ norm_nonneg _)
      (fun j ↦ (hcovarianceOnset j (onset j) le_rfl).2)
      htolerance
  exact _root_.GD.N0232.N0720.N1481.d017065
    hm hn s hstrict packet weight hweight onset houter hgap
      htwo hthree hskeletonTwo hskeletonThree

end

end N1481
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1481.d017064
#print axioms _root_.GD.N0232.N0720.N1481.d017065
#print axioms _root_.GD.N0232.N0720.N1481.d017068
#print axioms _root_.GD.N0232.N0720.N1481.d017069
#print axioms _root_.GD.N0232.N0720.N1481.d017071
#print axioms _root_.GD.N0232.N0720.N1481.d017072
#print axioms _root_.GD.N0232.N0720.N1481.d017073
