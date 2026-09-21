













import Mathlib
import GD.Module0403
import GD.Module0404

namespace GD.N0155

noncomputable def d006217 (t : ℝ) : ℝ :=
  (-65 : ℝ) * t^2 + (5270 : ℝ) * t^3 + (617950 : ℝ) * t^4 + (5568910 : ℝ) * t^5 + (12009470 : ℝ) * t^6 + (5568910 : ℝ) * t^7 + (617950 : ℝ) * t^8 + (5270 : ℝ) * t^9 - (65 : ℝ) * t^10

noncomputable def d006218 (t : ℝ) : ℝ :=
  (-21000 : ℝ) * t^4 - (339150 : ℝ) * t^5 - (1492575 : ℝ) * t^6 - (2392950 : ℝ) * t^7 - (1492575 : ℝ) * t^8 - (339150 : ℝ) * t^9 - (21000 : ℝ) * t^10

noncomputable def d006219 (t : ℝ) : ℝ :=
  (2945 : ℝ) * t^2 + (1205760 : ℝ) * t^3 + (31291235 : ℝ) * t^4 + (248103164 : ℝ) * t^5 + (804015764 : ℝ) * t^6 + (1179227384 : ℝ) * t^7 + (804015764 : ℝ) * t^8 + (248103164 : ℝ) * t^9 + (31291235 : ℝ) * t^10 + (1205760 : ℝ) * t^11 + (2945 : ℝ) * t^12

noncomputable def d006220 (t : ℝ) : ℝ :=
  (-65625 : ℝ) * t^3 - (2561475 : ℝ) * t^4 - (28268940 : ℝ) * t^5 - (126465150 : ℝ) * t^6 - (261196950 : ℝ) * t^7 - (261196950 : ℝ) * t^8 - (126465150 : ℝ) * t^9 - (28268940 : ℝ) * t^10 - (2561475 : ℝ) * t^11 - (65625 : ℝ) * t^12

noncomputable def d006221 (t : ℝ) : ℝ :=
  _root_.GD.N0155.d006217 t / (16 * (t - 1) ^ 12) + _root_.GD.N0155.d006218 t / (2 * (t - 1) ^ 13 * (t + 1)) * Real.log t

noncomputable def d006222 (t : ℝ) : ℝ :=
  _root_.GD.N0155.d006219 t / (32 * (t - 1) ^ 14) + _root_.GD.N0155.d006220 t / (8 * (t - 1) ^ 15) * Real.log t

open Classical in


noncomputable def d006223 (t : ℝ) : ℝ := if t = 1 then (-5 : ℝ) / 6864 else _root_.GD.N0155.d006221 t

open Classical in


noncomputable def d006224 (t : ℝ) : ℝ := if t = 1 then (39 : ℝ) / 4576 else _root_.GD.N0155.d006222 t

theorem d006225 : _root_.GD.N0155.d006223 1 = (-5 : ℝ) / 6864 := if_pos rfl
theorem d006226 : _root_.GD.N0155.d006224 1 = (39 : ℝ) / 4576 := if_pos rfl
theorem d006227 {t : ℝ} (h : t ≠ 1) : _root_.GD.N0155.d006223 t = _root_.GD.N0155.d006221 t := if_neg h
theorem d006228 {t : ℝ} (h : t ≠ 1) : _root_.GD.N0155.d006224 t = _root_.GD.N0155.d006222 t := if_neg h

theorem d006229 (t : ℝ) (ht : t ≠ 0) : t^12 * _root_.GD.N0155.d006217 (1/t) = _root_.GD.N0155.d006217 t := by
  simp only [_root_.GD.N0155.d006217]; first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf
theorem d006230 (t : ℝ) (ht : t ≠ 0) : t^14 * _root_.GD.N0155.d006218 (1/t) = _root_.GD.N0155.d006218 t := by
  simp only [_root_.GD.N0155.d006218]; first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf
theorem d006231 (t : ℝ) (ht : t ≠ 0) : t^14 * _root_.GD.N0155.d006219 (1/t) = _root_.GD.N0155.d006219 t := by
  simp only [_root_.GD.N0155.d006219]; first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf
theorem d006232 (t : ℝ) (ht : t ≠ 0) : t^15 * _root_.GD.N0155.d006220 (1/t) = _root_.GD.N0155.d006220 t := by
  simp only [_root_.GD.N0155.d006220]; first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf

private theorem d006233 {t : ℝ} (h0 : t ≠ 0) {n : ℕ} (hn : Even n) :
    (1 / t - 1) ^ n = (t - 1) ^ n / t ^ n := by
  have h : 1 / t - 1 = -(t - 1) / t := by first | (field_simp; done) | (field_simp; ring)
  rw [h, div_pow, hn.neg_pow]

private theorem d006234 {t : ℝ} (h0 : t ≠ 0) {n : ℕ} (hn : Odd n) :
    (1 / t - 1) ^ n = -((t - 1) ^ n) / t ^ n := by
  have h : 1 / t - 1 = -(t - 1) / t := by first | (field_simp; done) | (field_simp; ring)
  rw [h, div_pow, hn.neg_pow]

theorem d006235 {t : ℝ} (ht : 0 < t) (ht1 : t ≠ 1) :
    _root_.GD.N0155.d006221 (1 / t) = _root_.GD.N0155.d006221 t := by
  have h0 : t ≠ 0 := ne_of_gt ht
  have h1 : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have h2 : t + 1 ≠ 0 := ne_of_gt (by linarith)
  have hplus : 1 / t + 1 = (t + 1) / t := by first | (field_simp; done) | (field_simp; ring)
  have hlog : Real.log (1 / t) = -Real.log t := by rw [one_div, Real.log_inv]
  unfold _root_.GD.N0155.d006221
  rw [_root_.GD.N0155.d006233 h0 (by norm_num : Even 12),
      _root_.GD.N0155.d006234 h0 (by norm_num : Odd 13), hplus, hlog,
      ← _root_.GD.N0155.d006229 t h0, ← _root_.GD.N0155.d006230 t h0]
  first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf

theorem d006236 {t : ℝ} (ht : 0 < t) (ht1 : t ≠ 1) :
    _root_.GD.N0155.d006222 (1 / t) = _root_.GD.N0155.d006222 t := by
  have h0 : t ≠ 0 := ne_of_gt ht
  have h1 : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have hlog : Real.log (1 / t) = -Real.log t := by rw [one_div, Real.log_inv]
  unfold _root_.GD.N0155.d006222
  rw [_root_.GD.N0155.d006233 h0 (by norm_num : Even 14),
      _root_.GD.N0155.d006234 h0 (by norm_num : Odd 15), hlog,
      ← _root_.GD.N0155.d006231 t h0, ← _root_.GD.N0155.d006232 t h0]
  first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf




theorem d006237 {t : ℝ} (ht : 0 < t) (ht1 : t ≠ 1) :
    -(2 * _root_.GD.N0155.d006221 t) - 11 / 125 * _root_.GD.N0155.d006222 t = _root_.GD.N0155.d006211 t := by
  have h0 : t ≠ 0 := ne_of_gt ht
  have h1 : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have h2 : t + 1 ≠ 0 := ne_of_gt (by linarith)
  unfold _root_.GD.N0155.d006221 _root_.GD.N0155.d006222 _root_.GD.N0155.d006211
  simp only [_root_.GD.N0155.d006217, _root_.GD.N0155.d006218, _root_.GD.N0155.d006219, _root_.GD.N0155.d006220, _root_.GD.N0155.d006199, _root_.GD.N0155.d006200]
  first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf

theorem d006238 {t : ℝ} (ht : 0 < t) : _root_.GD.N0155.d006223 (1 / t) = _root_.GD.N0155.d006223 t := by
  by_cases h1 : t = 1
  · subst h1; norm_num
  · have hne : t ≠ 0 := ne_of_gt ht
    have h1' : (1 : ℝ) / t ≠ 1 := by
      intro h
      rw [div_eq_one_iff_eq hne] at h
      exact h1 h.symm
    rw [_root_.GD.N0155.d006227 h1', _root_.GD.N0155.d006227 h1, _root_.GD.N0155.d006235 ht h1]

theorem d006239 {t : ℝ} (ht : 0 < t) : _root_.GD.N0155.d006224 (1 / t) = _root_.GD.N0155.d006224 t := by
  by_cases h1 : t = 1
  · subst h1; norm_num
  · have hne : t ≠ 0 := ne_of_gt ht
    have h1' : (1 : ℝ) / t ≠ 1 := by
      intro h
      rw [div_eq_one_iff_eq hne] at h
      exact h1 h.symm
    rw [_root_.GD.N0155.d006228 h1', _root_.GD.N0155.d006228 h1, _root_.GD.N0155.d006236 ht h1]

end GD.N0155
