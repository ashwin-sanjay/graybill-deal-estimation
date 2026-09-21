import GD.Module0451
import GD.Module0512
import GD.Module0446




set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open _root_.GD.N0232.N0720.N1164

namespace GD.N0106.N0428.N0765.N1548.d006926
open _root_.GD.N0106.N0428.N0765.N1623

theorem d007725 {s : ℤ} {I J : _root_.GD.N0106.N0428.N0765.N1548.d006926} {x y : ℝ}
    (hs : 0 < s) (hx : I.d006928 s x) (hy : J.d006928 s y) :
    (I.d006940 s J).d006928 s (x * y) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  let lo : ℤ := min (min (I.lo * J.lo) (I.lo * J.hi))
    (min (I.hi * J.lo) (I.hi * J.hi))
  let hi : ℤ := max (max (I.lo * J.lo) (I.lo * J.hi))
    (max (I.hi * J.lo) (I.hi * J.hi))
  let Q := _root_.GD.N0106.N0428.N0765.N1623.d007722 (I.d006929 s) (J.d006929 s)
  have hQ : Q.d006810 (x * y) :=
    _root_.GD.N0106.N0428.N0765.N1623.d007724 ((_root_.GD.N0106.N0428.N0765.N1548.d006926.d006931 s I x).mp hx) ((_root_.GD.N0106.N0428.N0765.N1548.d006926.d006931 s J y).mp hy)
  have heqlo : (Q.lo : ℝ) = (lo : ℝ) / (s : ℝ) / (s : ℝ) := by
    dsimp [Q, lo, _root_.GD.N0106.N0428.N0765.N1623.d007722, _root_.GD.N0106.N0428.N0765.N1548.d006926.d006929]
    push_cast
    simp only [div_mul_div_comm, min_div_div_right (mul_nonneg hsR.le hsR.le), div_div]
  have heqhi : (Q.hi : ℝ) = (hi : ℝ) / (s : ℝ) / (s : ℝ) := by
    dsimp [Q, hi, _root_.GD.N0106.N0428.N0765.N1623.d007722, _root_.GD.N0106.N0428.N0765.N1548.d006926.d006929]
    push_cast
    simp only [div_mul_div_comm, max_div_div_right (mul_nonneg hsR.le hsR.le), div_div]
  have hl := _root_.GD.N0106.N0428.N0765.N1548.d006960 lo hs hs
  have hu := _root_.GD.N0106.N0428.N0765.N1548.d006961 hi hs hs
  rw [← heqlo] at hl
  rw [← heqhi] at hu
  exact ⟨hl.trans hQ.1, hQ.2.trans hu⟩

theorem d007726 {s : ℤ} {I : _root_.GD.N0106.N0428.N0765.N1548.d006926} {x : ℝ}
    (hs : 0 < s) (hx : I.d006928 s x) : (I.d006941 s).d006928 s (x ^ 2) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hsQ : (0 : ℚ) < s := by exact_mod_cast hs
  have hq := _root_.GD.N0106.N0428.N0765.N1545.d006834 ((_root_.GD.N0106.N0428.N0765.N1548.d006926.d006931 s I x).mp hx)
  have hlo_iff : 0 ≤ (I.d006929 s).lo ↔ 0 ≤ I.lo := by
    change 0 ≤ (I.lo : ℚ) / (s : ℚ) ↔ 0 ≤ I.lo
    rw [le_div_iff₀ hsQ]
    norm_num
  have hhi_iff : (I.d006929 s).hi ≤ 0 ↔ I.hi ≤ 0 := by
    change (I.hi : ℚ) / (s : ℚ) ≤ 0 ↔ I.hi ≤ 0
    rw [div_le_iff₀ hsQ]
    norm_num
  have hu : x ^ 2 ≤ max (((I.lo : ℝ) / (s : ℝ)) ^ 2)
      (((I.hi : ℝ) / (s : ℝ)) ^ 2) := by
    by_cases h0 : 0 ≤ (I.d006929 s).lo
    · simp only [_root_.GD.N0106.N0428.N0765.N1545.d006833, if_pos h0] at hq
      simp only [_root_.GD.N0232.N0720.N1164.d006809.d006810, _root_.GD.N0106.N0428.N0765.N1548.d006926.d006929] at hq
      push_cast at hq
      exact hq.2.trans (le_max_right _ _)
    · by_cases h1 : (I.d006929 s).hi ≤ 0
      · simp only [_root_.GD.N0106.N0428.N0765.N1545.d006833, if_neg h0, if_pos h1] at hq
        simp only [_root_.GD.N0232.N0720.N1164.d006809.d006810, _root_.GD.N0106.N0428.N0765.N1548.d006926.d006929] at hq
        push_cast at hq
        exact hq.2.trans (le_max_left _ _)
      · simp only [_root_.GD.N0106.N0428.N0765.N1545.d006833, if_neg h0, if_neg h1] at hq
        simpa only [_root_.GD.N0232.N0720.N1164.d006809.d006810, _root_.GD.N0106.N0428.N0765.N1548.d006926.d006929, Rat.cast_max, Rat.cast_pow, Rat.cast_div,
          Rat.cast_intCast] using hq.2
  have heqhi : max (((I.lo : ℝ) / (s : ℝ)) ^ 2) (((I.hi : ℝ) / (s : ℝ)) ^ 2) =
      ((max (I.lo ^ 2) (I.hi ^ 2) : ℤ) : ℝ) / (s : ℝ) / (s : ℝ) := by
    push_cast
    rw [div_pow, div_pow, max_div_div_right (sq_nonneg (s : ℝ)), div_div]
    simp only [pow_two]
  have hu' := hu.trans (heqhi.trans_le (_root_.GD.N0106.N0428.N0765.N1548.d006961 (max (I.lo ^ 2) (I.hi ^ 2)) hs hs))
  by_cases hc : I.lo ≤ 0 ∧ 0 ≤ I.hi
  · simp only [_root_.GD.N0106.N0428.N0765.N1548.d006926.d006941, if_pos hc, _root_.GD.N0106.N0428.N0765.N1548.d006926.d006928, Int.cast_zero, zero_div]
    exact ⟨sq_nonneg x, hu'⟩
  · have hl : min (((I.lo : ℝ) / (s : ℝ)) ^ 2)
        (((I.hi : ℝ) / (s : ℝ)) ^ 2) ≤ x ^ 2 := by
      by_cases h0 : 0 ≤ (I.d006929 s).lo
      · simp only [_root_.GD.N0106.N0428.N0765.N1545.d006833, if_pos h0] at hq
        simp only [_root_.GD.N0232.N0720.N1164.d006809.d006810, _root_.GD.N0106.N0428.N0765.N1548.d006926.d006929] at hq
        push_cast at hq
        exact (min_le_left _ _).trans hq.1
      · by_cases h1 : (I.d006929 s).hi ≤ 0
        · simp only [_root_.GD.N0106.N0428.N0765.N1545.d006833, if_neg h0, if_pos h1] at hq
          simp only [_root_.GD.N0232.N0720.N1164.d006809.d006810, _root_.GD.N0106.N0428.N0765.N1548.d006926.d006929] at hq
          push_cast at hq
          exact (min_le_right _ _).trans hq.1
        · exfalso
          exact hc ⟨le_of_not_ge (fun h => h0 (hlo_iff.mpr h)),
            le_of_not_ge (fun h => h1 (hhi_iff.mpr h))⟩
    have heqlo : min (((I.lo : ℝ) / (s : ℝ)) ^ 2) (((I.hi : ℝ) / (s : ℝ)) ^ 2) =
        ((min (I.lo ^ 2) (I.hi ^ 2) : ℤ) : ℝ) / (s : ℝ) / (s : ℝ) := by
      push_cast
      rw [div_pow, div_pow, min_div_div_right (sq_nonneg (s : ℝ)), div_div]
      simp only [pow_two]
    have hl' := (_root_.GD.N0106.N0428.N0765.N1548.d006960 (min (I.lo ^ 2) (I.hi ^ 2)) hs hs).trans
      (heqlo.symm.trans_le hl)
    simp only [_root_.GD.N0106.N0428.N0765.N1548.d006926.d006941, if_neg hc, _root_.GD.N0106.N0428.N0765.N1548.d006926.d006928]
    exact ⟨hl', hu'⟩

end GD.N0106.N0428.N0765.N1548.d006926

#print axioms _root_.GD.N0106.N0428.N0765.N1548.d006926.d007725
#print axioms _root_.GD.N0106.N0428.N0765.N1548.d006926.d007726
