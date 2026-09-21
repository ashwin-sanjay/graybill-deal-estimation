import GD.Module0640
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped ENNReal

namespace GD.N0051
noncomputable section

def d022762 (s d : ℝ) : ℝ := s / (s + d ^ 2)

def d022763 (p q : ℝ) (y z s t : ℝ) : ℝ :=
  if _root_.GD.N0051.d022762 s (z - y) ^ p ≤ _root_.GD.N0051.d022762 t (z - y) ^ q then y else z

theorem d022764 {s d : ℝ} (hs : 0 < s) : 0 < _root_.GD.N0051.d022762 s d := by
  unfold _root_.GD.N0051.d022762
  positivity

theorem d022765 {s d : ℝ} (hs : 0 < s) : _root_.GD.N0051.d022762 s d ≤ 1 := by
  unfold _root_.GD.N0051.d022762
  exact (div_le_one (by positivity)).mpr (le_add_of_nonneg_right (sq_nonneg d))

theorem d022766 {s d : ℝ} (hs : 0 < s) :
    (_root_.GD.N0051.d022762 s d)⁻¹ = 1 + d ^ 2 / s := by
  unfold _root_.GD.N0051.d022762
  field_simp

theorem d022767 {s t d p q : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hp : 0 < p) (hcomp : _root_.GD.N0051.d022762 t d ^ q ≤ _root_.GD.N0051.d022762 s d ^ p) :
    _root_.GD.N0051.d022762 t d ^ (q / p) ≤ _root_.GD.N0051.d022762 s d := by
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg (_root_.GD.N0051.d022764 ht).le _)
    hcomp (inv_nonneg.mpr hp.le)
  rw [← Real.rpow_mul (_root_.GD.N0051.d022764 ht).le, ← Real.rpow_mul (_root_.GD.N0051.d022764 hs).le,
    mul_inv_cancel₀ hp.ne', Real.rpow_one] at hh
  simpa only [div_eq_mul_inv] using hh



theorem d022768 {s t d p q : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hp : 0 < p) (hcomp : _root_.GD.N0051.d022762 t d ^ q ≤ _root_.GD.N0051.d022762 s d ^ p) :
    d ^ 2 ≤ s * (1 + d ^ 2 / t) ^ (q / p) := by
  have hpow := _root_.GD.N0051.d022767 hs ht hp hcomp
  have hprod : d ^ 2 * _root_.GD.N0051.d022762 s d ≤ s := by
    unfold _root_.GD.N0051.d022762
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < s + d ^ 2)).mpr
    nlinarith [sq_nonneg s]
  have hb : d ^ 2 * _root_.GD.N0051.d022762 t d ^ (q / p) ≤ s :=
    (mul_le_mul_of_nonneg_left hpow (sq_nonneg d)).trans hprod
  have hqp : 0 < _root_.GD.N0051.d022762 t d ^ (q / p) := Real.rpow_pos_of_pos (_root_.GD.N0051.d022764 ht) _
  have hh := (le_div_iff₀ hqp).mpr hb
  rw [← _root_.GD.N0051.d022766 ht, Real.inv_rpow (_root_.GD.N0051.d022764 ht).le]
  simpa only [div_eq_mul_inv] using hh

theorem d022769 {p q y z s t : ℝ}
    (hp : 0 < p) (hs : 0 < s) (ht : 0 < t) :
    (_root_.GD.N0051.d022763 p q y z s t - y) ^ 2 ≤
      s * (1 + (z - y) ^ 2 / t) ^ (q / p) := by
  unfold _root_.GD.N0051.d022763
  split_ifs with h
  · simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  · exact _root_.GD.N0051.d022768 hs ht hp (le_of_not_ge h)

theorem d022770 {p q y z s t : ℝ}
    (hq : 0 < q) (hs : 0 < s) (ht : 0 < t) :
    (_root_.GD.N0051.d022763 p q y z s t - z) ^ 2 ≤
      t * (1 + (z - y) ^ 2 / s) ^ (p / q) := by
  unfold _root_.GD.N0051.d022763
  split_ifs with h
  · simpa only [sub_sq_comm] using _root_.GD.N0051.d022768 ht hs hq h
  · simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

theorem d022771 (p q : ℝ) :
    Measurable (fun v : (ℝ × ℝ) × (ℝ × ℝ) => _root_.GD.N0051.d022763 p q v.1.1 v.1.2 v.2.1 v.2.2) := by
  unfold _root_.GD.N0051.d022763
  apply Measurable.ite (measurableSet_le (by unfold _root_.GD.N0051.d022762; fun_prop)
    (by unfold _root_.GD.N0051.d022762; fun_prop)) (by fun_prop) (by fun_prop)

theorem d022772 {a b : ℝ} (ha : 0 < a) :
    (∃ r : ℝ, 0 < r ∧ r < b ∧ 1 / r < a) ↔ 1 < a * b := by
  constructor
  · rintro ⟨r, hr, hrb, hra⟩
    have hh : 1 < a * r := (div_lt_iff₀ hr).mp hra
    nlinarith
  · intro hab
    have hlt : 1 / a < b := (div_lt_iff₀ ha).mpr (by nlinarith)
    obtain ⟨r, har, hrb⟩ := exists_between hlt
    have hr : 0 < r := (div_pos (by norm_num) ha).trans har
    refine ⟨r, hr, hrb, (div_lt_iff₀ hr).mpr ?_⟩
    have hh := (div_lt_iff₀ ha).mp har
    nlinarith

#print axioms _root_.GD.N0051.d022768
#print axioms _root_.GD.N0051.d022769
#print axioms _root_.GD.N0051.d022770
#print axioms _root_.GD.N0051.d022771
#print axioms _root_.GD.N0051.d022772
end
end GD.N0051
