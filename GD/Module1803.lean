import GD.Module1801
import GD.Module0889

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0101.N0391
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1336 _root_.GD.N0232.N0720.N1312
open _root_.GD.N0232.N0720.N1266 (d013712 d013726)
open _root_.GD.N0232.N0720.N1271 (d013403)
open _root_.GD.N0045 _root_.GD.N0101.N0390


def d029981 (m n : ℕ) (t : _root_.GD.N0232.N0720.N1441.d013676) : ℝ :=
  _root_.GD.N0232.N0720.N1336.d013426 m n t.1 / _root_.GD.N0232.N0720.N1336.d013426 m n _root_.GD.N0232.N0720.N1441.d013677.1 *
    (3 / 2 : ℝ) ^ (-_root_.GD.N0232.N0720.N1436.d013210 m n)


def d029982 (m n : ℕ) : ℝ :=
  min (_root_.GD.N0101.N0391.d029981 m n _root_.GD.N0101.N0390.d029964) (_root_.GD.N0101.N0391.d029981 m n _root_.GD.N0101.N0390.d029965)

theorem d029983 (m n : ℕ) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    0 < _root_.GD.N0101.N0391.d029981 m n t := by
  exact mul_pos
    (div_pos (_root_.GD.N0232.N0720.N1336.d013427 m n t.2.1 t.2.2)
      (_root_.GD.N0232.N0720.N1336.d013427 m n _root_.GD.N0232.N0720.N1441.d013677.2.1 _root_.GD.N0232.N0720.N1441.d013677.2.2))
    (Real.rpow_pos_of_pos (by norm_num) _)

theorem d029984 (m n : ℕ) : 0 < _root_.GD.N0101.N0391.d029982 m n :=
  lt_min (_root_.GD.N0101.N0391.d029983 m n _root_.GD.N0101.N0390.d029964) (_root_.GD.N0101.N0391.d029983 m n _root_.GD.N0101.N0390.d029965)

theorem d029985 (m n : ℕ) (t : _root_.GD.N0232.N0720.N1441.d013676)
    (ht : t.1 = 1 / 4 ∨ t.1 = 3 / 4) (x : _root_.GD.N0232.N0720.N1266.d013712) :
    _root_.GD.N0232.N0720.N1312.d013793 m n t x ≤ (3 / 2 : ℝ) * _root_.GD.N0232.N0720.N1312.d013793 m n _root_.GD.N0232.N0720.N1441.d013677 x := by
  have hA : 0 ≤ (1 - (x.2 : ℝ)) * (((n - 1 : ℕ) : ℝ) * (x.1 : ℝ)) :=
    mul_nonneg (sub_nonneg.mpr x.2.2.2) (mul_nonneg (Nat.cast_nonneg _) x.1.2.1)
  have hB : 0 ≤ (1 - (x.2 : ℝ)) * (((m - 1 : ℕ) : ℝ) * (1 - (x.1 : ℝ))) :=
    mul_nonneg (sub_nonneg.mpr x.2.2.2)
      (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr x.1.2.2))
  have hx := x.2.2.1
  unfold _root_.GD.N0232.N0720.N1312.d013793 _root_.GD.N0232.N0720.N1271.d013403
  rcases ht with ht | ht
  · rw [ht]
    norm_num only [_root_.GD.N0232.N0720.N1441.d013677]
    nlinarith
  · rw [ht]
    norm_num only [_root_.GD.N0232.N0720.N1441.d013677]
    nlinarith

theorem d029986
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (t : _root_.GD.N0232.N0720.N1441.d013676)
    (ht : t.1 = 1 / 4 ∨ t.1 = 3 / 4) (x : _root_.GD.N0232.N0720.N1266.d013712) :
    _root_.GD.N0101.N0391.d029981 m n t ≤ _root_.GD.N0232.N0720.N1312.d013797 m n t x := by
  have hmid := _root_.GD.N0232.N0720.N1312.d013795 m n hm hn _root_.GD.N0232.N0720.N1441.d013677 x
  have hpow := Real.rpow_le_rpow_of_nonpos (_root_.GD.N0232.N0720.N1312.d013795 m n hm hn t x)
    (_root_.GD.N0101.N0391.d029985 m n t ht x) (neg_nonpos.mpr (_root_.GD.N0232.N0720.N1436.d013216 hm hn).le)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3 / 2) hmid.le] at hpow
  have hF := _root_.GD.N0232.N0720.N1336.d013427 m n _root_.GD.N0232.N0720.N1441.d013677.2.1 _root_.GD.N0232.N0720.N1441.d013677.2.2
  have hM := Real.rpow_pos_of_pos hmid (-_root_.GD.N0232.N0720.N1436.d013210 m n)
  unfold _root_.GD.N0101.N0391.d029981 _root_.GD.N0232.N0720.N1312.d013797
  apply (le_div_iff₀ (mul_pos hF hM)).mpr
  calc
    _ = _root_.GD.N0232.N0720.N1336.d013426 m n t.1 *
        ((3 / 2 : ℝ) ^ (-_root_.GD.N0232.N0720.N1436.d013210 m n) *
          _root_.GD.N0232.N0720.N1312.d013793 m n _root_.GD.N0232.N0720.N1441.d013677 x ^ (-_root_.GD.N0232.N0720.N1436.d013210 m n)) := by
      field_simp [hF.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (_root_.GD.N0232.N0720.N1336.d013427 m n t.2.1 t.2.2).le

theorem d029987 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0101.N0391.d029982 m n ≤ _root_.GD.N0101.N0390.d029966 m n := by
  have hpoint : (fun x => _root_.GD.N0101.N0391.d029982 m n *
      _root_.GD.N0232.N0720.N1436.d013273 m n _root_.GD.N0232.N0720.N1441.d013677.1 x) ≤ᵐ[_root_.GD.N0232.N0720.N1436.d013288]
      (fun x => min (_root_.GD.N0232.N0720.N1436.d013273 m n _root_.GD.N0101.N0390.d029964.1 x)
        (_root_.GD.N0232.N0720.N1436.d013273 m n _root_.GD.N0101.N0390.d029965.1 x)) := by
    filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with x hx
    have hp0 := (_root_.GD.N0232.N0720.N1436.d013286 hm hn _root_.GD.N0232.N0720.N1441.d013677.2.1 _root_.GD.N0232.N0720.N1441.d013677.2.2 hx).le
    have hleft := _root_.GD.N0101.N0391.d029986 m n hm hn _root_.GD.N0101.N0390.d029964
      (Or.inl rfl) (_root_.GD.N0232.N0720.N1266.d013726 x)
    have hright := _root_.GD.N0101.N0391.d029986 m n hm hn _root_.GD.N0101.N0390.d029965
      (Or.inr rfl) (_root_.GD.N0232.N0720.N1266.d013726 x)
    apply le_min
    · rw [_root_.GD.N0232.N0720.N1312.d013804 m n hm hn hx _root_.GD.N0101.N0390.d029964]
      exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hp0).trans
        (by simpa only [mul_comm, _root_.GD.N0232.N0720.N1441.d013677] using mul_le_mul_of_nonneg_left hleft hp0)
    · rw [_root_.GD.N0232.N0720.N1312.d013804 m n hm hn hx _root_.GD.N0101.N0390.d029965]
      exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hp0).trans
        (by simpa only [mul_comm, _root_.GD.N0232.N0720.N1441.d013677] using mul_le_mul_of_nonneg_left hright hp0)
  have h := integral_mono_ae ((_root_.GD.N0045.d021925 m n hm hn _root_.GD.N0232.N0720.N1441.d013677).const_mul _)
    (_root_.GD.N0101.N0393.d029959 (_root_.GD.N0045.d021925 m n hm hn _root_.GD.N0101.N0390.d029964)
      (_root_.GD.N0045.d021925 m n hm hn _root_.GD.N0101.N0390.d029965)) hpoint
  simpa only [integral_const_mul, _root_.GD.N0101.N0390.d029967 m n hm hn _root_.GD.N0232.N0720.N1441.d013677,
    mul_one, _root_.GD.N0101.N0390.d029966] using h

theorem d029988 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0101.N0391.d029982 m n ≤ 1 :=
  (_root_.GD.N0101.N0391.d029987 m n hm hn).trans (_root_.GD.N0101.N0390.d029970 m n hm hn)


theorem d029989
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ENNReal.ofReal (1 + _root_.GD.N0101.N0391.d029982 m n / 3) ≤
      _root_.GD.N0232.N0720.N1256.d015549 m n := by
  apply (ENNReal.ofReal_le_ofReal ?_).trans (_root_.GD.N0101.N0390.d029973 m n hm hn)
  linarith [_root_.GD.N0101.N0391.d029987 m n hm hn]

end
end GD.N0101.N0391

#print axioms _root_.GD.N0101.N0391.d029983
#print axioms _root_.GD.N0101.N0391.d029984
#print axioms _root_.GD.N0101.N0391.d029985
#print axioms _root_.GD.N0101.N0391.d029986
#print axioms _root_.GD.N0101.N0391.d029987
#print axioms _root_.GD.N0101.N0391.d029988
#print axioms _root_.GD.N0101.N0391.d029989
