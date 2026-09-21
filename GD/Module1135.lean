import GD.Module1118
import GD.Module1134



























open Filter MeasureTheory Set Topology

namespace GD
namespace N0232
namespace N0720
namespace N1210

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1116
open _root_.GD.N0232.N0720.N1122
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1302
open _root_.GD.N0232.N0720.N1477
open _root_.GD.N0232.N0720.N1482

variable {m n : ℕ} {width : ℕ → ℕ}







theorem d018271
    (D observable : ℕ → ℝ) {kappa : ℝ} (hkappa : 0 < kappa)
    (hobservable : ∀ j, 0 ≤ observable j)
    (hDzero : Tendsto D atTop (nhds 0))
    (hcoercive : ∀ j, kappa * observable j ≤ D j) :
    Tendsto observable atTop (nhds 0) := by
  have hupper : Tendsto (fun j ↦ D j / kappa) atTop (nhds 0) := by
    simpa only [zero_div] using hDzero.div_const kappa
  exact squeeze_zero hobservable
    (fun j ↦ (le_div_iff₀ hkappa).2 (by
      simpa only [mul_comm] using hcoercive j)) hupper




private theorem d018272
    (C D : ℕ → ℝ) (htower : ∀ j, C j = C (j + 1) + D j)
    (N : ℕ) :
    C 0 = C N + ∑ j ∈ Finset.range N, D j := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [ih, htower N, Finset.sum_range_succ]
      ring




theorem d018273
    (C D : ℕ → ℝ)
    (htower : ∀ j, C j = C (j + 1) + D j)
    (hC : ∀ j, 0 ≤ C j) (hD : ∀ j, 0 ≤ D j) :
    Tendsto D atTop (nhds 0) := by
  have hsummable : Summable D := by
    apply summable_of_sum_range_le hD
    intro N
    have htelescope := _root_.GD.N0232.N0720.N1210.d018272 C D htower N
    linarith [hC N]
  exact hsummable.tendsto_atTop_zero





theorem d018274 :
    ∃ C D observable : ℕ → ℝ,
      (∀ j, C j = C (j + 1) + D j) ∧
      (∀ j, 0 ≤ C j) ∧ (∀ j, 0 ≤ D j) ∧
      (∀ j, 0 ≤ observable j) ∧
      ¬ Tendsto observable atTop (nhds 0) := by
  refine ⟨fun _ ↦ 1, fun _ ↦ 0, fun _ ↦ 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    norm_num
  · intro j
    norm_num
  · intro j
    norm_num
  · intro j
    norm_num
  · intro honeZero
    have honeOne : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have : (1 : ℝ) = 0 := tendsto_nhds_unique honeOne honeZero
    norm_num at this







theorem d018275
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ∀ j, Fin (width j) → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (htight : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0))
    (D : ℕ → ℝ) (hDzero : Tendsto D atTop (nhds 0))
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hcoercive : ∀ j,
      kappa * _root_.GD.N0232.N0720.N1122.d017962 m n
        (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
          (packet j) (weight j) (hweight j)) ≤ D j) :
    _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 := by
  let residual : ℕ → ℝ := fun j ↦
    _root_.GD.N0232.N0720.N1122.d017962 m n
      (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
        (packet j) (weight j) (hweight j))
  have hresidualZero : Tendsto residual atTop (nhds 0) := by
    apply _root_.GD.N0232.N0720.N1210.d018271
      D residual hkappa
    · intro j
      exact _root_.GD.N0232.N0720.N1122.d017963 _
    · exact hDzero
    · exact hcoercive
  have hresidualLimit : Tendsto residual atTop
      (nhds (_root_.GD.N0232.N0720.N1477.d015749 m n s)) := by
    simpa only [residual] using
      _root_.GD.N0232.N0720.N1122.d017967
        s packet weight hweight htight
  exact tendsto_nhds_unique hresidualLimit hresidualZero



theorem d018276
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ∀ j, Fin (width j) → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (htight : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0))
    (C D : ℕ → ℝ)
    (htower : ∀ j, C j = C (j + 1) + D j)
    (hC : ∀ j, 0 ≤ C j) (hD : ∀ j, 0 ≤ D j)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hcoercive : ∀ j,
      kappa * _root_.GD.N0232.N0720.N1122.d017962 m n
        (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
          (packet j) (weight j) (hweight j)) ≤ D j) :
    _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 := by
  exact _root_.GD.N0232.N0720.N1210.d018275
    s packet weight hweight htight D
      (_root_.GD.N0232.N0720.N1210.d018273
        C D htower hC hD)
      hkappa hcoercive





theorem d018277
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ∀ j, Fin (width j) → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (htight : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016432 s (packet j) (weight j))
      atTop (nhds 0))
    (C D : ℕ → ℝ)
    (htower : ∀ j, C j = C (j + 1) + D j)
    (hC : ∀ j, 0 ≤ C j) (hD : ∀ j, 0 ≤ D j)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hcoercive : ∀ j,
      kappa * _root_.GD.N0232.N0720.N1122.d017962 m n
        (_root_.GD.N0232.N0720.N1126.d016426 (m := m) (n := n)
          (packet j) (weight j) (hweight j)) ≤ D j) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  have henergy : _root_.GD.N0232.N0720.N1477.d015749 m n s = 0 :=
    _root_.GD.N0232.N0720.N1210.d018276
      s packet weight hweight htight C D htower hC hD hkappa hcoercive
  apply
    (_root_.GD.N0232.N0720.N1482.d015173
      (m := m) (n := n) hm hn).2
  exact ⟨s, hstrict,
    (_root_.GD.N0232.N0720.N1477.d015755
      (m := m) (n := n) s).2 henergy⟩




theorem d018278
    (packet : ∀ j, Fin (width j) → _root_.GD.N0232.N0720.N1080.d014168)
    (weight : ∀ j, Fin (width j) → ℝ)
    (hweight : ∀ j i, 0 ≤ weight j i)
    (htight : Tendsto
      (fun j ↦
        ‖_root_.GD.N0232.N0720.N1159.d014633 2 2 _root_.GD.N0232.N0720.N1302.d018268.value‖ ^ 2 -
          _root_.GD.N0232.N0720.N1126.d016432 _root_.GD.N0232.N0720.N1302.d018268
            (packet j) (weight j))
      atTop (nhds 0))
    (C D : ℕ → ℝ)
    (htower : ∀ j, C j = C (j + 1) + D j)
    (hC : ∀ j, 0 ≤ C j) (hD : ∀ j, 0 ≤ D j)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hcoercive : ∀ j,
      kappa * _root_.GD.N0232.N0720.N1122.d017962 2 2
        (_root_.GD.N0232.N0720.N1126.d016426 (m := 2) (n := 2)
          (packet j) (weight j) (hweight j)) ≤ D j) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  have hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2)
      _root_.GD.N0232.N0720.N1302.d018268.value
      (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by norm_num) (by norm_num)) := by
    simpa only [_root_.GD.N0232.N0720.N1302.d018269] using
      _root_.GD.N0232.N0720.N1302.d018266
  exact _root_.GD.N0232.N0720.N1210.d018277
    (m := 2) (n := 2) (width := width)
      (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1302.d018268 hstrict
      packet weight hweight htight C D htower hC hD hkappa hcoercive

end

end N1210
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1210.d018271
#print axioms _root_.GD.N0232.N0720.N1210.d018273
#print axioms _root_.GD.N0232.N0720.N1210.d018274
#print axioms _root_.GD.N0232.N0720.N1210.d018276
#print axioms _root_.GD.N0232.N0720.N1210.d018277
#print axioms _root_.GD.N0232.N0720.N1210.d018278
