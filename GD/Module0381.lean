import GD.Module0371
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Tactic













set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1646
noncomputable section

open Complex
open scoped Topology BigOperators


private theorem d005810 {s : ℤ → ℂ}
    {C₀ C₁ k₀ k₁ : ℝ} (hk₀ : 0 < k₀) (hk₁ : 0 < k₁)
    (hs : Summable s)
    (hb : ∀ n : ℤ, n ≠ 0 →
      ‖s n‖ ≤ C₀ * Real.exp (-k₀ * |(n : ℝ)|) +
        C₁ * Real.exp (-k₁ * |(n : ℝ)|)) :
    ‖(∑' n : ℤ, s n) - s 0‖ ≤
      2 * C₀ / (Real.exp k₀ - 1) +
        2 * C₁ / (Real.exp k₁ - 1) := by
  have hp : Summable (fun n : ℕ => s n) := hs.comp_injective Nat.cast_injective
  have hn : Summable (fun n : ℕ => s (-(n + 1))) := by
    apply hs.comp_injective
    intro m n hmn
    have hcast : (m : ℤ) = (n : ℤ) := by linarith
    exact_mod_cast hcast
  have hsplit : (∑' n : ℤ, s n) - s 0 =
      (∑' n : ℕ, s ((n : ℤ) + 1)) + ∑' n : ℕ, s (-(n + 1)) := by
    rw [tsum_of_nat_of_neg_add_one hp hn, hp.tsum_eq_zero_add]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero]
    abel
  have hgeom := (_root_.GD.N0106.N0428.N0765.N1613.d005629 hk₀ C₀).add
    (_root_.GD.N0106.N0428.N0765.N1613.d005629 hk₁ C₁)
  have hpbound : ‖∑' n : ℕ, s ((n : ℤ) + 1)‖ ≤
      C₀ / (Real.exp k₀ - 1) + C₁ / (Real.exp k₁ - 1) := by
    apply tsum_of_norm_bounded hgeom
    intro n
    have hne : (n : ℤ) + 1 ≠ 0 := by omega
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one,
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)] using hb (n + 1) hne
  have hnbound : ‖∑' n : ℕ, s (-(n + 1))‖ ≤
      C₀ / (Real.exp k₀ - 1) + C₁ / (Real.exp k₁ - 1) := by
    apply tsum_of_norm_bounded hgeom
    intro n
    have hne : -(n + 1 : ℤ) ≠ 0 := by omega
    simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      abs_neg, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)] using
      hb (-(n + 1)) hne
  rw [hsplit]
  calc
    _ ≤ ‖∑' n : ℕ, s ((n : ℤ) + 1)‖ +
        ‖∑' n : ℕ, s (-(n + 1))‖ := norm_add_le _ _
    _ ≤ (C₀ / (Real.exp k₀ - 1) + C₁ / (Real.exp k₁ - 1)) +
          (C₀ / (Real.exp k₀ - 1) + C₁ / (Real.exp k₁ - 1)) :=
        add_le_add hpbound hnbound
    _ = _ := by ring


private theorem d005811 {s : ℤ → ℂ} {C k : ℝ}
    (hk : 0 < k) (hs : Summable s)
    (hb : ∀ n : ℤ, n ≠ 0 → ‖s n‖ ≤ C * Real.exp (-k * |(n : ℝ)|)) :
    ‖(∑' n : ℤ, s n) - s 0‖ ≤ 2 * C / (Real.exp k - 1) := by
  have hb' : ∀ n : ℤ, n ≠ 0 → ‖s n‖ ≤
      C * Real.exp (-k * |(n : ℝ)|) +
        0 * Real.exp (-k * |(n : ℝ)|) := by
    intro n hn
    simpa only [zero_mul, add_zero] using hb n hn
  have h := _root_.GD.N0106.N0428.N0765.N1646.d005810 hk hk hs hb'
  simpa only [mul_zero, zero_mul, zero_div, add_zero] using h





theorem d005812
    {c : ℤ → ℤ → ℂ} {φa φb : ℤ → ℂ}
    {I T Ma Mb Mab k₀ k₁ : ℝ}
    (hk₀ : 0 < k₀) (hk₁ : 0 < k₁)
    (hφa : ∀ n, ‖φa n‖ = 1) (hφb : ∀ n, ‖φb n‖ = 1)
    (hφa0 : φa 0 = 1) (hφb0 : φb 0 = 1)
    (hc : Summable (fun p : ℤ × ℤ => c p.1 p.2))
    (hzero : c 0 0 = (I : ℂ))
    (hrep : (T : ℂ) = ∑' p : ℤ × ℤ, c p.1 p.2 * φa p.1 * φb p.2)
    (haxisA : ∀ m : ℤ, m ≠ 0 →
      ‖c m 0‖ ≤ Ma * Real.exp (-k₀ * |(m : ℝ)|))
    (haxisB : ∀ n : ℤ, n ≠ 0 →
      ‖c 0 n‖ ≤ Mb * Real.exp (-k₀ * |(n : ℝ)|))
    (hmixed : ∀ m n : ℤ, m ≠ 0 → n ≠ 0 →
      ‖c m n‖ ≤ Mab * Real.exp (-k₁ * |(m : ℝ)|) *
        Real.exp (-k₁ * |(n : ℝ)|)) :
    |I - T| ≤
      (2 * Ma + 2 * Mb) / (Real.exp k₀ - 1) +
        4 * Mab / (Real.exp k₁ - 1) ^ 2 := by
  let mode (p : ℤ × ℤ) : ℂ := c p.1 p.2 * φa p.1 * φb p.2
  have hmode_norm (p : ℤ × ℤ) : ‖mode p‖ = ‖c p.1 p.2‖ := by
    simp only [mode, norm_mul, hφa, hφb, mul_one]
  have hmode : Summable mode := by
    apply Summable.of_norm
    simpa only [hmode_norm] using hc.norm
  let row (m : ℤ) : ℂ := ∑' n : ℤ, mode (m, n)
  have hrow (m : ℤ) : Summable (fun n : ℤ => mode (m, n)) := hmode.prod_factor m
  have hrows : Summable row := hmode.prod
  have hflat : (∑' p : ℤ × ℤ, mode p) = ∑' m : ℤ, row m := hmode.tsum_prod
  have hzero_mode : mode (0, 0) = (I : ℂ) := by
    simp only [mode, hφa0, hφb0, hzero, mul_one]
  have haxisB_row : ‖row 0 - (I : ℂ)‖ ≤ 2 * Mb / (Real.exp k₀ - 1) := by
    have h := _root_.GD.N0106.N0428.N0765.N1646.d005811 hk₀ (hrow 0) (by
      intro n hn
      simpa only [hmode_norm] using haxisB n hn)
    simpa only [row, hzero_mode] using h
  have hrow_bound (m : ℤ) (hm : m ≠ 0) :
      ‖row m‖ ≤ Ma * Real.exp (-k₀ * |(m : ℝ)|) +
        (2 * Mab / (Real.exp k₁ - 1)) * Real.exp (-k₁ * |(m : ℝ)|) := by
    have htail : ‖row m - mode (m, 0)‖ ≤
        2 * (Mab * Real.exp (-k₁ * |(m : ℝ)|)) / (Real.exp k₁ - 1) := by
      apply _root_.GD.N0106.N0428.N0765.N1646.d005811 hk₁ (hrow m)
      intro n hn
      simpa only [hmode_norm, mul_assoc] using hmixed m n hm hn
    have hmode_axis : ‖mode (m, 0)‖ ≤
        Ma * Real.exp (-k₀ * |(m : ℝ)|) := by
      simpa only [hmode_norm] using haxisA m hm
    calc
      ‖row m‖ ≤ ‖row m - mode (m, 0)‖ + ‖mode (m, 0)‖ := by
        simpa only [sub_add_cancel] using norm_add_le (row m - mode (m, 0)) (mode (m, 0))
      _ ≤ 2 * (Mab * Real.exp (-k₁ * |(m : ℝ)|)) / (Real.exp k₁ - 1) +
          Ma * Real.exp (-k₀ * |(m : ℝ)|) := add_le_add htail hmode_axis
      _ = _ := by ring
  have houter := _root_.GD.N0106.N0428.N0765.N1646.d005810 hk₀ hk₁ hrows hrow_bound
  have hid : (I : ℂ) - (T : ℂ) =
      -(((∑' m : ℤ, row m) - row 0) + (row 0 - I)) := by
    rw [hrep]
    change (I : ℂ) - (∑' p : ℤ × ℤ, mode p) = _
    rw [hflat]
    ring
  have hnorm : |I - T| = ‖(I : ℂ) - (T : ℂ)‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, hid, norm_neg]
  calc
    _ ≤ ‖(∑' m : ℤ, row m) - row 0‖ + ‖row 0 - (I : ℂ)‖ := norm_add_le _ _
    _ ≤ (2 * Ma / (Real.exp k₀ - 1) +
          2 * (2 * Mab / (Real.exp k₁ - 1)) / (Real.exp k₁ - 1)) +
          2 * Mb / (Real.exp k₀ - 1) := add_le_add houter haxisB_row
    _ = (2 * Ma + 2 * Mb) / (Real.exp k₀ - 1) +
          4 * Mab / (Real.exp k₁ - 1) ^ 2 := by
      simp only [div_eq_mul_inv, ← inv_pow]
      ring

end
end GD.N0106.N0428.N0765.N1646
