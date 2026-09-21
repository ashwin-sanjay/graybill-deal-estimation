import GD.Module0475
import GD.Module0473
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic












set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators Interval

namespace GD.N0166
noncomputable section

open _root_.GD.N0181 _root_.GD.N0167 _root_.GD.N0193


theorem d007379 {N : ℕ} (hN : 2 ≤ N) (j : ℕ) :
    Real.exp (-((j : ℝ) * _root_.GD.N0167.d007304 N)) = _root_.GD.N0181.d007268 N ^ j := by
  calc
    Real.exp (-((j : ℝ) * _root_.GD.N0167.d007304 N)) = Real.exp ((j : ℝ) * (-_root_.GD.N0167.d007304 N)) := by
      congr 1
      ring
    _ = Real.exp (-_root_.GD.N0167.d007304 N) ^ j := Real.exp_nat_mul (-_root_.GD.N0167.d007304 N) j
    _ = _root_.GD.N0181.d007268 N ^ j := by rw [← _root_.GD.N0167.d007310 hN]


theorem d007380 {N j : ℕ} (hN : 2 ≤ N) {r : ℝ}
    (hr : r ∈ Icc ((j : ℝ) * _root_.GD.N0167.d007304 N) (((j + 1 : ℕ) : ℝ) * _root_.GD.N0167.d007304 N)) :
    Real.exp (-r) ∈ Icc (_root_.GD.N0181.d007268 N * _root_.GD.N0181.d007268 N ^ j) (_root_.GD.N0181.d007268 N ^ j) := by
  constructor
  · calc
      _root_.GD.N0181.d007268 N * _root_.GD.N0181.d007268 N ^ j = Real.exp (-(((j + 1 : ℕ) : ℝ) * _root_.GD.N0167.d007304 N)) := by
        rw [_root_.GD.N0166.d007379 hN, pow_succ]
        ring
      _ ≤ Real.exp (-r) := Real.exp_le_exp_of_le (neg_le_neg hr.2)
  · calc
      Real.exp (-r) ≤ Real.exp (-((j : ℝ) * _root_.GD.N0167.d007304 N)) :=
        Real.exp_le_exp_of_le (neg_le_neg hr.1)
      _ = _root_.GD.N0181.d007268 N ^ j := _root_.GD.N0166.d007379 hN j

theorem d007381 {N j : ℕ} (hN : 2 ≤ N) (hj : N ^ 2 ≤ j) :
    _root_.GD.N0181.d007268 N ^ j ≤ _root_.GD.N0181.d007269 N := by
  exact pow_le_pow_of_le_one (_root_.GD.N0181.d007276 hN).le (_root_.GD.N0181.d007277 hN).le hj


theorem d007382 {N j : ℕ} (hN : 2 ≤ N) (hj : N ^ 2 ≤ j) {r : ℝ}
    (hr : r ∈ Icc ((j : ℝ) * _root_.GD.N0167.d007304 N) (((j + 1 : ℕ) : ℝ) * _root_.GD.N0167.d007304 N)) :
    _root_.GD.N0181.d007268 N * _root_.GD.N0181.d007268 N ^ j ≤ Real.exp (-r) ∧
      Real.exp (-r) ≤ _root_.GD.N0181.d007268 N ^ j ∧ _root_.GD.N0181.d007268 N ^ j ≤ _root_.GD.N0181.d007269 N :=
  ⟨(_root_.GD.N0166.d007380 hN hr).1, (_root_.GD.N0166.d007380 hN hr).2, _root_.GD.N0166.d007381 hN hj⟩

theorem d007383 {N : ℕ} (hN : 2 ≤ N) (j : ℕ) :
    (j : ℝ) * _root_.GD.N0167.d007304 N ≤ ((j + 1 : ℕ) : ℝ) * _root_.GD.N0167.d007304 N :=
  mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ j) (_root_.GD.N0167.d007313 hN).le


theorem d007384 {N j : ℕ} (hN : 2 ≤ N)
    (hj : j ∈ Ico (N ^ 2) (N ^ 3)) :
    Icc ((j : ℝ) * _root_.GD.N0167.d007304 N) (((j + 1 : ℕ) : ℝ) * _root_.GD.N0167.d007304 N) ⊆ Icc (_root_.GD.N0167.d007305 N) (_root_.GD.N0167.d007305 N + _root_.GD.N0167.d007306 N) := by
  have hlo : _root_.GD.N0167.d007305 N ≤ (j : ℝ) * _root_.GD.N0167.d007304 N := by
    unfold _root_.GD.N0167.d007305
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj.1) (_root_.GD.N0167.d007313 hN).le
  have hhi : ((j + 1 : ℕ) : ℝ) * _root_.GD.N0167.d007304 N ≤ _root_.GD.N0167.d007305 N + _root_.GD.N0167.d007306 N := by
    rw [_root_.GD.N0167.d007309 hN]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Nat.succ_le_of_lt hj.2)) (_root_.GD.N0167.d007313 hN).le
  intro r hr
  exact ⟨hlo.trans hr.1, hr.2.trans hhi⟩


theorem d007385 {N j : ℕ} (hN : 2 ≤ N)
    (hj : j ∈ Ico (N ^ 2) (N ^ 3)) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (_root_.GD.N0167.d007305 N) (_root_.GD.N0167.d007305 N + _root_.GD.N0167.d007306 N)) :
    IntervalIntegrable f volume ((j : ℝ) * _root_.GD.N0167.d007304 N) (((j + 1 : ℕ) : ℝ) * _root_.GD.N0167.d007304 N) := by
  apply hf.mono_set
  rw [uIcc_of_le (_root_.GD.N0166.d007383 hN j),
    uIcc_of_le (show _root_.GD.N0167.d007305 N ≤ _root_.GD.N0167.d007305 N + _root_.GD.N0167.d007306 N by linarith [_root_.GD.N0167.d007318 hN])]
  exact _root_.GD.N0166.d007384 hN hj


theorem d007386 {N : ℕ} (hN : 2 ≤ N) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (_root_.GD.N0167.d007305 N) (_root_.GD.N0167.d007305 N + _root_.GD.N0167.d007306 N)) :
    (∑ j ∈ Finset.Ico (N ^ 2) (N ^ 3),
      ∫ r in ((j : ℝ) * _root_.GD.N0167.d007304 N)..(((j + 1 : ℕ) : ℝ) * _root_.GD.N0167.d007304 N), f r) =
        ∫ r in (_root_.GD.N0167.d007305 N)..(_root_.GD.N0167.d007305 N + _root_.GD.N0167.d007306 N), f r := by
  have hs := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (μ := volume) (f := f) (a := fun j : ℕ => (j : ℝ) * _root_.GD.N0167.d007304 N)
    (_root_.GD.N0193.d007354 hN) (fun j hj => _root_.GD.N0166.d007385 hN hj f hf)
  simpa only [Nat.cast_pow, ← _root_.GD.N0167.d007309 hN, _root_.GD.N0167.d007305] using hs


theorem d007387 (N : ℕ) (F : ℕ → ℝ) :
    (∑ i : Fin (_root_.GD.N0193.d007343 N), F (_root_.GD.N0193.d007345 N i)) =
      ∑ j ∈ Finset.Ico (N ^ 2) (N ^ 3), F j := by
  rw [Finset.sum_Ico_eq_sum_range]
  simpa only [_root_.GD.N0193.d007345, _root_.GD.N0193.d007343] using
    (Fin.sum_univ_eq_sum_range (fun j => F (N ^ 2 + j)) (_root_.GD.N0193.d007343 N))


theorem d007388 {N : ℕ} (hN : 2 ≤ N) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (_root_.GD.N0167.d007305 N) (_root_.GD.N0167.d007305 N + _root_.GD.N0167.d007306 N)) :
    (∑ i : Fin (_root_.GD.N0193.d007343 N),
      ∫ r in ((_root_.GD.N0193.d007345 N i : ℝ) * _root_.GD.N0167.d007304 N)..
        (((_root_.GD.N0193.d007345 N i + 1 : ℕ) : ℝ) * _root_.GD.N0167.d007304 N), f r) =
          ∫ r in (_root_.GD.N0167.d007305 N)..(_root_.GD.N0167.d007305 N + _root_.GD.N0167.d007306 N), f r := by
  calc
    _ = ∑ j ∈ Finset.Ico (N ^ 2) (N ^ 3),
        ∫ r in ((j : ℝ) * _root_.GD.N0167.d007304 N)..(((j + 1 : ℕ) : ℝ) * _root_.GD.N0167.d007304 N), f r :=
      _root_.GD.N0166.d007387 N (fun j =>
        ∫ r in ((j : ℝ) * _root_.GD.N0167.d007304 N)..(((j + 1 : ℕ) : ℝ) * _root_.GD.N0167.d007304 N), f r)
    _ = _ := _root_.GD.N0166.d007386 hN f hf

theorem d007389 (N j : ℕ) :
    ((j + 1 : ℕ) : ℝ) * _root_.GD.N0167.d007304 N - (j : ℝ) * _root_.GD.N0167.d007304 N = _root_.GD.N0167.d007304 N := by
  push_cast
  ring

theorem d007390 (N : ℕ) : _root_.GD.N0167.d007306 N = (_root_.GD.N0193.d007343 N : ℝ) * _root_.GD.N0167.d007304 N := rfl


theorem d007391 {N : ℕ} (hN : 2 ≤ N) :
    _root_.GD.N0167.d007304 N / (2 * _root_.GD.N0167.d007306 N) = _root_.GD.N0193.d007348 N := by
  have hk : (_root_.GD.N0193.d007343 N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (_root_.GD.N0193.d007353 hN).ne'
  have hh : _root_.GD.N0167.d007304 N ≠ 0 := (_root_.GD.N0167.d007313 hN).ne'
  rw [_root_.GD.N0166.d007390, _root_.GD.N0193.d007348]
  field_simp [hk, hh] <;> ring

end
end GD.N0166

#print axioms _root_.GD.N0166.d007380
#print axioms _root_.GD.N0166.d007382
#print axioms _root_.GD.N0166.d007386
#print axioms _root_.GD.N0166.d007387
#print axioms _root_.GD.N0166.d007388
#print axioms _root_.GD.N0166.d007391
