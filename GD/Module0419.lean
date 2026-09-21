import Mathlib










namespace GD.N0133

open MeasureTheory Set



theorem d006480 {N r : ℝ} (hN : 0 < N) :
    (1 / N) ^ r = N ^ (-r) := by
  rw [one_div, Real.inv_rpow hN.le, ← Real.rpow_neg hN.le]






theorem d006481 {r N : ℝ} (hr : 0 < r) (hN : 0 < N) :
    ∫ H : ℝ in Ioi 0, H ^ (r - 1) * Real.exp (-(N * H))
      = Real.Gamma r * N ^ (-r) := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hr hN,
    _root_.GD.N0133.d006480 hN]
  ring



theorem d006482 {r N C : ℝ} (hr : 0 < r) (hN : 0 < N) :
    ∫ H : ℝ in Ioi 0, C * (H ^ (r - 1) * Real.exp (-(N * H)))
      = C * Real.Gamma r * N ^ (-r) := by
  rw [MeasureTheory.integral_const_mul, _root_.GD.N0133.d006481 hr hN]
  ring


theorem d006483 (k : ℕ) {N : ℝ} (hN : 0 < N) :
    ∫ H : ℝ in Ioi 0, H ^ (k : ℝ) * Real.exp (-(N * H))
      = (k.factorial : ℝ) * N ^ (-((k : ℝ) + 1)) := by
  have h :=
    _root_.GD.N0133.d006481 (r := (k : ℝ) + 1) (N := N) (by positivity) hN
  rw [Real.Gamma_nat_eq_factorial] at h
  convert h using 1
  all_goals ring_nf


noncomputable def d006484 (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, ((j : ℝ) + 1 / 2)


theorem d006485 (k : ℕ) :
    Real.Gamma ((k : ℝ) + 1 / 2) =
      _root_.GD.N0133.d006484 k * Real.sqrt Real.pi := by
  induction k with
  | zero =>
      unfold _root_.GD.N0133.d006484
      simp only [Nat.cast_zero, zero_add, Finset.range_zero,
        Finset.prod_empty, one_mul]
      exact Real.Gamma_one_half_eq
  | succ k ih =>
      rw [show ((k.succ : ℕ) : ℝ) + 1 / 2 =
          ((k : ℝ) + 1 / 2) + 1 by push_cast; ring]
      rw [Real.Gamma_add_one (by positivity :
        (k : ℝ) + 1 / 2 ≠ 0), ih]
      simp [_root_.GD.N0133.d006484, Finset.prod_range_succ]
      ring



theorem d006486 {N : ℝ} (hN : 0 < N) :
    ∫ H : ℝ in Ioi 0, H ^ (-(1 : ℝ) / 2) * Real.exp (-(N * H))
      = Real.sqrt Real.pi * N ^ (-(1 : ℝ) / 2) := by
  have h :=
    _root_.GD.N0133.d006481 (r := (1 : ℝ) / 2) (N := N) (by norm_num) hN
  rw [Real.Gamma_one_half_eq] at h
  convert h using 1
  all_goals ring_nf



theorem d006487 (k : ℕ) {N : ℝ} (hN : 0 < N) :
    ∫ H : ℝ in Ioi 0,
        H ^ ((k : ℝ) - 1 / 2) * Real.exp (-(N * H))
      = _root_.GD.N0133.d006484 k * Real.sqrt Real.pi *
          N ^ (-((k : ℝ) + 1 / 2)) := by
  have h := _root_.GD.N0133.d006481
    (r := (k : ℝ) + 1 / 2) (N := N) (by positivity) hN
  rw [_root_.GD.N0133.d006485] at h
  convert h using 1
  all_goals ring_nf




theorem d006488 (α β : ℝ) :
    (α - 1) + (β - 1) + ((3 : ℝ) / 2 - 1) + 2
      = (α + β + (3 : ℝ) / 2) - 1 := by
  ring


theorem d006489 {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    0 < α + β + (3 : ℝ) / 2 := by
  positivity


theorem d006490 {α β N C : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hN : 0 < N) :
    ∫ H : ℝ in Ioi 0,
        C * (H ^ ((α + β + (3 : ℝ) / 2) - 1) *
          Real.exp (-(N * H)))
      = C * Real.Gamma (α + β + (3 : ℝ) / 2) *
          N ^ (-(α + β + (3 : ℝ) / 2)) := by
  exact _root_.GD.N0133.d006482
    (_root_.GD.N0133.d006489 hα hβ) hN

end GD.N0133
