import GD.Module1427
import GD.Module1429

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GD.N0031
noncomputable section

open _root_.GD.N0051



theorem d022788 {A s D w r b : ℝ}
    (hA : 0 ≤ A) (hs : 0 < s) (hD : 0 ≤ D) (hw : 0 < w)
    (hb : 0 < b) (hrb : r * b = 1) :
    D * ((A * s ^ r * D ^ (1 - r)) / w) ^ b =
      A ^ b * s * (D / w) ^ b := by
  by_cases hzero : D = 0
  · simp only [hzero, zero_mul, zero_div, Real.zero_rpow hb.ne', mul_zero]
  · have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm hzero)
    have hexp : (1 - r) * b = b - 1 := by nlinarith [hrb]
    rw [Real.div_rpow (by positivity) hw.le,
      Real.mul_rpow (by positivity) (Real.rpow_nonneg hD _),
      Real.mul_rpow hA (Real.rpow_nonneg hs.le _),
      ← Real.rpow_mul hs.le, ← Real.rpow_mul hD,
      hrb, Real.rpow_one, hexp, Real.rpow_sub hDp, Real.rpow_one,
      Real.div_rpow hD hw.le]
    field_simp

theorem d022789 (p q y z s t : ℝ) :
    (_root_.GD.N0051.d022763 p q y z s t - y) ^ 2 ≤ (z - y) ^ 2 := by
  unfold _root_.GD.N0051.d022763
  split_ifs
  · simpa using sq_nonneg (z - y)
  · exact le_rfl

theorem d022790 {p q y z s t : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hs : 0 < s) (ht : 0 < t) :
    (_root_.GD.N0051.d022763 p q y z s t - z) ^ 2 ≤ t + (y - z) ^ 2 *
      (Iic (_root_.GD.N0031.d022775 (q / p) t (y - z))).indicator (fun _ => (1 : ℝ)) s := by
  have hInd : 0 ≤ (Iic (_root_.GD.N0031.d022775 (q / p) t (y - z))).indicator
      (fun _ => (1 : ℝ)) s := indicator_nonneg (fun _ _ => by norm_num) _
  unfold _root_.GD.N0051.d022763
  split_ifs with h
  · by_cases hd : (y - z) ^ 2 ≤ t
    · exact hd.trans (le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) hInd))
    · have hcomp : _root_.GD.N0051.d022762 s (y - z) ^ p ≤ _root_.GD.N0051.d022762 t (y - z) ^ q := by
        simpa only [_root_.GD.N0051.d022762, sub_sq_comm] using h
      have hscut := _root_.GD.N0031.d022778 hq hp ht hs (lt_of_not_ge hd) hcomp
      rw [indicator_of_mem (show s ∈ Iic (_root_.GD.N0031.d022775 (q / p) t (y - z)) from hscut), mul_one]
      exact le_add_of_nonneg_left ht.le
  · simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact add_nonneg ht.le (mul_nonneg (sq_nonneg _) hInd)



theorem d022791
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hpos : ∀ᵐ x ∂P, 0 < x)
    {p q y z s w b B : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hs : 0 < s) (hw : 0 < w)
    (hb : 0 < b) (hB : 0 ≤ B) (hrb : (p / q) * b = 1)
    (hcdf : ∀ u : ℝ, 0 ≤ u → P (Iic u) ≤ ENNReal.ofReal (B * u ^ b))
    (f : ℝ → ℝ)
    (hcutoff : ∀ x : ℝ, 0 < x → (f x - y) ^ 2 ≤ s + (z - y) ^ 2 *
      (Iic (_root_.GD.N0031.d022775 (p / q) s (z - y))).indicator (fun _ => (1 : ℝ)) (w * x)) :
    (∫⁻ x, ENNReal.ofReal ((f x - y) ^ 2) ∂P) ≤
      ENNReal.ofReal (s * (1 + B * _root_.GD.N0031.d022773 (p / q) ^ b *
        ((z - y) ^ 2 / w) ^ b)) := by
  let r := p / q
  let D := (z - y) ^ 2
  let u := _root_.GD.N0031.d022775 r s (z - y) / w
  have hr : 0 < r := div_pos hp hq
  have hD : 0 ≤ D := sq_nonneg _
  have hu : 0 ≤ u := div_nonneg (_root_.GD.N0031.d022776 hr hs.le) hw.le
  have hpoint : ∀ᵐ x ∂P,
      ENNReal.ofReal ((f x - y) ^ 2) ≤
        ENNReal.ofReal s + ENNReal.ofReal D * (Iic u).indicator (fun _ => 1) x := by
    filter_upwards [hpos] with x hx
    have h := hcutoff x hx
    have hc : w * x ≤ _root_.GD.N0031.d022775 r s (z - y) ↔ x ≤ u := by
      dsimp only [u]
      rw [le_div_iff₀ hw, mul_comm x w]
    by_cases hxu : x ≤ u
    · have hxt : w * x ∈ Iic (_root_.GD.N0031.d022775 r s (z - y)) := hc.mpr hxu
      rw [indicator_of_mem hxt, mul_one] at h
      rw [indicator_of_mem (show x ∈ Iic u from hxu), mul_one]
      rw [← ENNReal.ofReal_add hs.le hD]
      exact ENNReal.ofReal_le_ofReal h
    · have hxt : w * x ∉ Iic (_root_.GD.N0031.d022775 r s (z - y)) := fun hh => hxu (hc.mp hh)
      rw [indicator_of_notMem hxt, mul_zero, add_zero] at h
      rw [indicator_of_notMem (show x ∉ Iic u from hxu), mul_zero, add_zero]
      exact ENNReal.ofReal_le_ofReal h
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal s + ENNReal.ofReal D * (Iic u).indicator (fun _ => 1) x ∂P :=
      lintegral_mono_ae hpoint
    _ = ENNReal.ofReal s + ENNReal.ofReal D * P (Iic u) := by
      rw [lintegral_add_left measurable_const,
        lintegral_const_mul _ (measurable_const.indicator measurableSet_Iic),
        lintegral_indicator measurableSet_Iic]
      simp
    _ ≤ ENNReal.ofReal s + ENNReal.ofReal D * ENNReal.ofReal (B * u ^ b) :=
      add_le_add le_rfl (mul_le_mul_right (hcdf u hu) _)
    _ = ENNReal.ofReal (s * (1 + B * _root_.GD.N0031.d022773 (p / q) ^ b *
        ((z - y) ^ 2 / w) ^ b)) := by
      rw [← ENNReal.ofReal_mul hD,
        ← ENNReal.ofReal_add hs.le (mul_nonneg hD (mul_nonneg hB (Real.rpow_nonneg hu _)))]
      congr 1
      have heq := _root_.GD.N0031.d022788 (_root_.GD.N0031.d022774 hr).le hs hD hw hb hrb
      change D * ((_root_.GD.N0031.d022773 r * s ^ r * D ^ (1 - r)) / w) ^ b =
        _root_.GD.N0031.d022773 r ^ b * s * (D / w) ^ b at heq
      dsimp only [u, _root_.GD.N0031.d022775] at *
      nlinarith [heq]

end
end GD.N0031

#print axioms _root_.GD.N0031.d022788
#print axioms _root_.GD.N0031.d022789
#print axioms _root_.GD.N0031.d022790
#print axioms _root_.GD.N0031.d022791
