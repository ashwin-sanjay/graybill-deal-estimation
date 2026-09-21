import GD.Module1037
import GD.Module1116



























open Filter MeasureTheory Set Topology
open scoped ENNReal BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1032

noncomputable section

open _root_.GD.N0230.N0617
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0685
open _root_.GD.N0230.N0714
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1100
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1146
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1219
open _root_.GD.N0232.N0720.N1461
open _root_.GD.N0232.N0720.N1482

variable {m n : ℕ}
variable {ι : ℕ → Type*}
variable [∀ j, Fintype (ι j)] [∀ j, DecidableEq (ι j)]

set_option linter.unusedSectionVars false









theorem d017955
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (packet : ∀ j, ι j → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ∀ j, ι j → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (htight : Tendsto
      (fun j ↦ ‖q‖ ^ 2 - _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
        (packet j) (weight j) (hweight j))
      atTop (nhds q) := by
  let r : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) := fun j ↦
    _root_.GD.N0232.N0720.N1126.d016426 (packet j) (weight j) (hweight j)
  have hcloseSq : Tendsto (fun j ↦ ‖q - r j‖ ^ 2)
      atTop (nhds 0) := by
    apply squeeze_zero (fun j ↦ sq_nonneg ‖q - r j‖)
      (fun j ↦ ?_) htight
    have hreserve :=
      _root_.GD.N0232.N0720.N1126.d016436
        s (packet j) (weight j) (hweight j) q hq
    simpa only [r] using (show
      ‖q - r j‖ ^ 2 ≤
        ‖q‖ ^ 2 - _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j) by
          linarith)
  have hclose : Tendsto (fun j ↦ ‖r j - q‖) atTop (nhds 0) := by
    have hsqrt := hcloseSq.sqrt
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero,
      norm_sub_rev] using hsqrt
  have hr : Tendsto r atTop (nhds q) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hclose
  simpa only [r] using hr






theorem d017956
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (packet : ∀ j, ι j → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ∀ j, ι j → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (htight : Tendsto
      (fun j ↦ ‖q‖ ^ 2 - _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014633 m n s.value = q := by
  let ell : ℕ → ℝ := fun j ↦
    _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j)
  have hell : Tendsto ell atTop (nhds (‖q‖ ^ 2)) := by
    have hconst : Tendsto (fun _ : ℕ ↦ ‖q‖ ^ 2)
        atTop (nhds (‖q‖ ^ 2)) := tendsto_const_nhds
    have h := hconst.sub htight
    simpa only [ell, sub_sub_cancel, sub_zero] using h
  have hellUpper : ∀ j,
      ell j ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
    intro j
    have hreserve :=
      _root_.GD.N0232.N0720.N1126.d016437
        s (packet j) (weight j) (hweight j)
    have hdistanceNonneg :
        0 ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value -
          _root_.GD.N0232.N0720.N1126.d016426 (packet j) (weight j) (hweight j)‖ ^ 2 :=
      sq_nonneg _
    dsimp only [ell]
    linarith
  have hqNormLe :
      ‖q‖ ^ 2 ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
    apply le_of_tendsto' hell
    exact hellUpper
  have htax := _root_.GD.N0230.N0685.d000512 (_root_.GD.N0232.N0720.N1100.d015487 m n s.value) hq
  simp only [sub_zero] at htax
  have hzero : ‖q - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ = 0 := by
    nlinarith [norm_nonneg (q - _root_.GD.N0232.N0720.N1159.d014633 m n s.value)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm





theorem d017957
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (hreserve : ∀ e ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value,
      ‖q‖ ^ 2 + ‖e - q‖ ^ 2 ≤ ‖e‖ ^ 2) :
    _root_.GD.N0232.N0720.N1159.d014633 m n s.value = q := by
  have hforward := hreserve
    (_root_.GD.N0232.N0720.N1159.d014633 m n s.value)
    (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  have hbackward := _root_.GD.N0230.N0685.d000512
    (_root_.GD.N0232.N0720.N1100.d015487 m n s.value) hq
  simp only [sub_zero] at hbackward
  have hreverseNorm :
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value - q‖ =
        ‖q - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ :=
    norm_sub_rev _ _
  have hzero : ‖q - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ = 0 := by
    nlinarith [norm_nonneg (q - _root_.GD.N0232.N0720.N1159.d014633 m n s.value)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm











theorem d017958
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (hrep : _root_.GD.N0232.N0720.N1159.d014652 m n q)
    (packet : ∀ j, ι j → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ∀ j, ι j → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (htight : Tendsto
      (fun j ↦ ‖q‖ ^ 2 - _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  have heq :=
    _root_.GD.N0232.N0720.N1032.d017956
      s q hq packet weight hweight htight
  have hqStrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) q
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
    simpa only [heq] using
      (_root_.GD.N0232.N0720.N1159.d014636
        m n s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) hstrict)
  have hqTerminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) q := by
    simpa only [heq] using
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).2.1
  exact (_root_.GD.N0232.N0720.N1159.d014664
    m n hm hn).2 ⟨q, hrep, hqStrict, hqTerminal⟩





theorem d017959
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hrep : _root_.GD.N0232.N0720.N1159.d014652 m n q)
    (hsection : ∀ (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) 1),
      _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz) q ≤
        _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1219.d017942 m n hm hn z hz) s.value)
    (packet : ∀ j, ι j → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ∀ j, ι j → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (htight : Tendsto
      (fun j ↦ ‖q‖ ^ 2 - _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  have hcharacter : _root_.GD.N0232.N0720.N1159.d014638 m n q :=
    _root_.GD.N0232.N0720.N1159.d014653
      m n q hrep
  have hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value :=
    (_root_.GD.N0232.N0720.N1219.d017952
      m n hm hn q hcharacter s).2 hsection
  exact
    _root_.GD.N0232.N0720.N1032.d017958
      hm hn s hstrict q hq hrep packet weight hweight htight




theorem d017960
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (hrep : _root_.GD.N0232.N0720.N1159.d014652 m n q)
    (hreserve : ∀ e ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value,
      ‖q‖ ^ 2 + ‖e - q‖ ^ 2 ≤ ‖e‖ ^ 2) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  have heq :=
    _root_.GD.N0232.N0720.N1032.d017957
      s q hq hreserve
  have hqStrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) q
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
    simpa only [heq] using
      (_root_.GD.N0232.N0720.N1159.d014636
        m n s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) hstrict)
  have hqTerminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) q := by
    simpa only [heq] using
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).2.1
  exact (_root_.GD.N0232.N0720.N1159.d014664
    m n hm hn).2 ⟨q, hrep, hqStrict, hqTerminal⟩












theorem d017961
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hq : q ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s.value)
    (hscaleTwo : _root_.GD.N0232.N0720.N1146.d015228 m n q = q)
    (hshiftOneScaleThree :
      _root_.GD.N0232.N0720.N1146.d015229 m n q = q)
    (packet : ∀ j, ι j → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ∀ j, ι j → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (htight : Tendsto
      (fun j ↦ ‖q‖ ^ 2 - _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  have heq :=
    _root_.GD.N0232.N0720.N1032.d017956
      s q hq packet weight hweight htight
  have hscaleP : _root_.GD.N0232.N0720.N1146.d015228 m n
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value := by
    simpa only [heq] using hscaleTwo
  have hthreeP : _root_.GD.N0232.N0720.N1146.d015229 m n
      (_root_.GD.N0232.N0720.N1159.d014633 m n s.value) =
        _root_.GD.N0232.N0720.N1159.d014633 m n s.value := by
    simpa only [heq] using hshiftOneScaleThree
  apply _root_.GD.N0232.N0720.N1461.d015687
    m n hm hn s hstrict
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n s.value
  let hp : _root_.GD.N0232.N0720.N1159.d014637 m n p :=
    _root_.GD.N0232.N0720.N1159.d014644 m n s p
      (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).1
  change _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp = p ∧
    _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp = p
  constructor
  · change _root_.GD.N0232.N0720.N1146.d015212 m n
      (_root_.GD.N0232.N0720.N1146.d015221 m n) p = p at hscaleP
    rw [← _root_.GD.N0232.N0720.N1146.d015218
      m n (_root_.GD.N0232.N0720.N1146.d015221 m n) p hp]
    exact hscaleP
  · change _root_.GD.N0232.N0720.N1146.d015212 m n
      (_root_.GD.N0232.N0720.N1146.d015222 m n) p = p at hthreeP
    rw [← _root_.GD.N0232.N0720.N1146.d015218
      m n (_root_.GD.N0232.N0720.N1146.d015222 m n) p hp]
    exact hthreeP

end

end N1032
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1032.d017955
#print axioms _root_.GD.N0232.N0720.N1032.d017956
#print axioms _root_.GD.N0232.N0720.N1032.d017957
#print axioms _root_.GD.N0232.N0720.N1032.d017958
#print axioms _root_.GD.N0232.N0720.N1032.d017959
#print axioms _root_.GD.N0232.N0720.N1032.d017960
#print axioms _root_.GD.N0232.N0720.N1032.d017961
