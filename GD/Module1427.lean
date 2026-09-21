import GD.Module1426

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0031
noncomputable section

open _root_.GD.N0051

def d022773 (r : ℝ) : ℝ := (1 - (1 / 2 : ℝ) ^ r)⁻¹

theorem d022774 {r : ℝ} (hr : 0 < r) : 0 < _root_.GD.N0031.d022773 r := by
  apply inv_pos.mpr
  exact sub_pos.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) hr)

def d022775 (r s d : ℝ) : ℝ :=
  _root_.GD.N0031.d022773 r * s ^ r * (d ^ 2) ^ (1 - r)

theorem d022776 {r s d : ℝ} (hr : 0 < r) (hs : 0 ≤ s) :
    0 ≤ _root_.GD.N0031.d022775 r s d :=
  mul_nonneg (mul_nonneg (_root_.GD.N0031.d022774 hr).le (Real.rpow_nonneg hs _))
    (Real.rpow_nonneg (sq_nonneg d) _)



theorem d022777 {p q s t d : ℝ} (hq : 0 < q)
    (hs : 0 < s) (ht : 0 < t)
    (hcomp : _root_.GD.N0051.d022762 t d ^ q ≤ _root_.GD.N0051.d022762 s d ^ p) :
    _root_.GD.N0051.d022762 t d ≤ _root_.GD.N0051.d022762 s d ^ (p / q) := by
  have h := Real.rpow_le_rpow (Real.rpow_nonneg (_root_.GD.N0051.d022764 ht).le _)
    hcomp (inv_nonneg.mpr hq.le)
  rw [← Real.rpow_mul (_root_.GD.N0051.d022764 ht).le, ← Real.rpow_mul (_root_.GD.N0051.d022764 hs).le,
    mul_inv_cancel₀ hq.ne', Real.rpow_one] at h
  simpa only [div_eq_mul_inv] using h



theorem d022778 {p q s t d : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hs : 0 < s) (ht : 0 < t)
    (hd : s < d ^ 2) (hcomp : _root_.GD.N0051.d022762 t d ^ q ≤ _root_.GD.N0051.d022762 s d ^ p) :
    t ≤ _root_.GD.N0031.d022775 (p / q) s d := by
  let r := p / q
  have hr : 0 < r := div_pos hp hq
  have hD : 0 < d ^ 2 := hs.trans hd
  have hhalf : _root_.GD.N0051.d022762 s d ≤ (1 / 2 : ℝ) := by
    unfold _root_.GD.N0051.d022762
    apply (div_le_iff₀ (by positivity : 0 < s + d ^ 2)).mpr
    linarith
  have hratio : _root_.GD.N0051.d022762 s d ≤ s / d ^ 2 := by
    exact div_le_div_of_nonneg_left hs.le hD (le_add_of_nonneg_left hs.le)
  have hroot : _root_.GD.N0051.d022762 t d ≤ _root_.GD.N0051.d022762 s d ^ r := _root_.GD.N0031.d022777 hq hs ht hcomp
  have hpowhalf : _root_.GD.N0051.d022762 s d ^ r ≤ (1 / 2 : ℝ) ^ r :=
    Real.rpow_le_rpow (_root_.GD.N0051.d022764 hs).le hhalf hr.le
  have hpowratio : _root_.GD.N0051.d022762 s d ^ r ≤ (s / d ^ 2) ^ r :=
    Real.rpow_le_rpow (_root_.GD.N0051.d022764 hs).le hratio hr.le
  have hH : 0 < 1 - (1 / 2 : ℝ) ^ r :=
    sub_pos.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) hr)
  have htq : t ≤ _root_.GD.N0051.d022762 s d ^ r * (t + d ^ 2) := by
    exact (div_le_iff₀ (by positivity : 0 < t + d ^ 2)).mp hroot
  have hmul : (1 - (1 / 2 : ℝ) ^ r) * t ≤ (s / d ^ 2) ^ r * d ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hpowhalf ht.le,
      mul_le_mul_of_nonneg_right hpowratio hD.le]
  have hh : t ≤ _root_.GD.N0031.d022773 r * ((s / d ^ 2) ^ r * d ^ 2) := by
    have hh' : t ≤ ((s / d ^ 2) ^ r * d ^ 2) / (1 - (1 / 2 : ℝ) ^ r) :=
      (le_div_iff₀ hH).mpr (by nlinarith [hmul])
    simpa only [_root_.GD.N0031.d022773, div_eq_mul_inv, mul_comm] using hh'
  have heq : (s / d ^ 2) ^ r * d ^ 2 = s ^ r * (d ^ 2) ^ (1 - r) := by
    rw [Real.div_rpow hs.le hD.le, Real.rpow_sub hD, Real.rpow_one]
    ring
  rw [heq] at hh
  simpa only [_root_.GD.N0031.d022775, r, mul_assoc] using hh



theorem d022779 {p q y z s t : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hs : 0 < s) (ht : 0 < t) :
    (_root_.GD.N0051.d022763 p q y z s t - y) ^ 2 ≤ s + (z - y) ^ 2 *
      (Iic (_root_.GD.N0031.d022775 (p / q) s (z - y))).indicator (fun _ => (1 : ℝ)) t := by
  have hInd : 0 ≤ (Iic (_root_.GD.N0031.d022775 (p / q) s (z - y))).indicator
      (fun _ => (1 : ℝ)) t := indicator_nonneg (fun _ _ => by norm_num) _
  unfold _root_.GD.N0051.d022763
  split_ifs with h
  · simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact add_nonneg hs.le (mul_nonneg (sq_nonneg _) hInd)
  · by_cases hd : (z - y) ^ 2 ≤ s
    · exact hd.trans (le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) hInd))
    · have htcut := _root_.GD.N0031.d022778 hp hq hs ht (lt_of_not_ge hd) (le_of_not_ge h)
      rw [indicator_of_mem (show t ∈ Iic (_root_.GD.N0031.d022775 (p / q) s (z - y)) from htcut), mul_one]
      exact le_add_of_nonneg_left hs.le

end
end GD.N0031

#print axioms _root_.GD.N0031.d022774
#print axioms _root_.GD.N0031.d022777
#print axioms _root_.GD.N0031.d022778
#print axioms _root_.GD.N0031.d022779
