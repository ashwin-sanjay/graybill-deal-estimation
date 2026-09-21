


























import Mathlib
import GD.Module0402
import GD.Module0405
import GD.Module0406
import GD.Module0407

set_option maxHeartbeats 64000000
set_option maxRecDepth 4096

namespace GD.N0155
open MeasureTheory


theorem d006291 (n : ℕ) :
    ∫ x in Set.Ioi (0:ℝ), x ^ n * Real.exp (-x) = n.factorial := by
  have h := (Real.Gamma_eq_integral (show (0:ℝ) < (n:ℝ) + 1 by positivity)).symm
  rw [show ((n:ℝ) + 1 - 1) = (n:ℝ) by ring] at h
  have hc : (∫ x in Set.Ioi (0:ℝ), x ^ n * Real.exp (-x))
      = ∫ x in Set.Ioi (0:ℝ), Real.exp (-x) * x ^ (n:ℝ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [Real.rpow_natCast]
    ring
  rw [hc, h]
  exact Real.Gamma_nat_eq_factorial n


theorem d006292 (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ n * Real.exp (-x)) (Set.Ioi 0) := by
  have h := Real.GammaIntegral_convergent (show (0:ℝ) < (n:ℝ) + 1 by positivity)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only []
  rw [show ((n:ℝ) + 1 - 1) = (n:ℝ) by ring, Real.rpow_natCast]
  ring


noncomputable def d006293 (b x : ℝ) : ℝ := 5^5 / (24 * b^5) * x^4 * Real.exp (-(5 * x / b))


noncomputable def d006294 (v1 v2 u : ℝ) : ℝ := 5 * (u * v2 + (1 - u) * v1) / (v1 * v2)

theorem d006295 {v1 v2 : ℝ} (h1 : 0 < v1) (h2 : 0 < v2) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 0 < _root_.GD.N0155.d006294 v1 v2 u := by
  unfold _root_.GD.N0155.d006294
  have hnum : 0 < u * v2 + (1 - u) * v1 := by
    rcases eq_or_lt_of_le hu0 with h | h
    · rw [← h]; simpa using h1
    · have h2' : 0 < u * v2 := mul_pos h h2
      have h3' : 0 ≤ (1 - u) * v1 := mul_nonneg (by linarith) h1.le
      linarith
  positivity



theorem d006296 {b : ℝ} (hb : 0 < b) : ∫ x in Set.Ioi (0:ℝ), _root_.GD.N0155.d006293 b x = 1 := by
  have hs : (0:ℝ) < 5 / b := by positivity
  have hb' : b ≠ 0 := ne_of_gt hb
  have hcg : (∫ x in Set.Ioi (0:ℝ), _root_.GD.N0155.d006293 b x)
      = ∫ x in Set.Ioi (0:ℝ),
          (fun y => 5^5 / (24 * b^5) / (5/b)^4 * (y ^ 4 * Real.exp (-y))) (5 / b * x) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [_root_.GD.N0155.d006293]
    rw [show -(5 * x / b) = -(5 / b * x) by ring]
    first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf
  rw [hcg, MeasureTheory.integral_comp_mul_left_Ioi
        (fun y : ℝ => 5^5 / (24 * b^5) / (5/b)^4 * (y ^ 4 * Real.exp (-y))) 0 hs,
    mul_zero, smul_eq_mul,
    MeasureTheory.integral_const_mul, _root_.GD.N0155.d006291 4]
  norm_num [Nat.factorial]
  first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf



noncomputable def d006297 (v1 v2 : ℝ) : ℝ :=
  ∫ a in Set.Ioi (0:ℝ), ∫ b in Set.Ioi (0:ℝ),
    (_root_.GD.N0155.d006193 (11 * b / (11 * b + 11 * a)) * (11 * b / (11 * b + 11 * a) - _root_.GD.N0155.d006267 (v2/v1)) *
      (3 * ((v1 + v2) / (a + b)) - 7/2)) * _root_.GD.N0155.d006293 v1 a * _root_.GD.N0155.d006293 v2 b


noncomputable def d006298 (v1 v2 : ℝ) : ℝ :=
  ∫ a in Set.Ioi (0:ℝ), ∫ b in Set.Ioi (0:ℝ),
    (_root_.GD.N0155.d006193 (11 * b / (11 * b + 11 * a)) ^ 2 *
      (15 * ((v1 + v2) / (a + b)) ^ 2 - 21 * ((v1 + v2) / (a + b)) + 49/4)) *
      _root_.GD.N0155.d006293 v1 a * _root_.GD.N0155.d006293 v2 b



noncomputable def d006299 (v1 v2 : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..1, ∫ T in Set.Ioi (0:ℝ),
    (_root_.GD.N0155.d006193 (11 * ((1-u)*T) / (11 * ((1-u)*T) + 11 * (u*T))) *
      (11 * ((1-u)*T) / (11 * ((1-u)*T) + 11 * (u*T)) - _root_.GD.N0155.d006267 (v2/v1)) *
      (3 * ((v1 + v2) / (u*T + (1-u)*T)) - 7/2)) * _root_.GD.N0155.d006293 v1 (u*T) * _root_.GD.N0155.d006293 v2 ((1-u)*T) * T


noncomputable def d006300 (v1 v2 : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..1, ∫ T in Set.Ioi (0:ℝ),
    (_root_.GD.N0155.d006193 (11 * ((1-u)*T) / (11 * ((1-u)*T) + 11 * (u*T))) ^ 2 *
      (15 * ((v1 + v2) / (u*T + (1-u)*T)) ^ 2
        - 21 * ((v1 + v2) / (u*T + (1-u)*T)) + 49/4)) *
      _root_.GD.N0155.d006293 v1 (u*T) * _root_.GD.N0155.d006293 v2 ((1-u)*T) * T


theorem d006301 (v1 v2 : ℝ) (h1 : 0 < v1) (h2 : 0 < v2)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∫ T in Set.Ioi (0:ℝ),
      (_root_.GD.N0155.d006193 (11 * ((1-u)*T) / (11 * ((1-u)*T) + 11 * (u*T))) *
        (11 * ((1-u)*T) / (11 * ((1-u)*T) + 11 * (u*T)) - _root_.GD.N0155.d006267 (v2/v1)) *
        (3 * ((v1 + v2) / (u*T + (1-u)*T)) - 7/2)) * _root_.GD.N0155.d006293 v1 (u*T) * _root_.GD.N0155.d006293 v2 ((1-u)*T) * T)
      = _root_.GD.N0155.d006193 (1-u) * ((1-u) - _root_.GD.N0155.d006267 (v2/v1)) * (u^4 * (1-u)^4) * (5^10 / (576 * v1^5 * v2^5)) *
          (3 * (v1+v2) * 40320 / (_root_.GD.N0155.d006294 v1 v2 u)^9 - 7/2 * 362880 / (_root_.GD.N0155.d006294 v1 v2 u)^10) := by
  have hs := _root_.GD.N0155.d006295 h1 h2 hu0 hu1
  have hsne : _root_.GD.N0155.d006294 v1 v2 u ≠ 0 := ne_of_gt hs
  have hv1 : v1 ≠ 0 := ne_of_gt h1
  have hv2 : v2 ≠ 0 := ne_of_gt h2
  have hvv : v1 + v2 ≠ 0 := by positivity
  have hcg : (∫ T in Set.Ioi (0:ℝ),
      (_root_.GD.N0155.d006193 (11 * ((1-u)*T) / (11 * ((1-u)*T) + 11 * (u*T))) *
        (11 * ((1-u)*T) / (11 * ((1-u)*T) + 11 * (u*T)) - _root_.GD.N0155.d006267 (v2/v1)) *
        (3 * ((v1 + v2) / (u*T + (1-u)*T)) - 7/2)) * _root_.GD.N0155.d006293 v1 (u*T) * _root_.GD.N0155.d006293 v2 ((1-u)*T) * T)
      = ∫ T in Set.Ioi (0:ℝ),
        (fun y => (_root_.GD.N0155.d006193 (1-u) * ((1-u) - _root_.GD.N0155.d006267 (v2/v1)) * (u^4 * (1-u)^4) *
            (5^10 / (576 * v1^5 * v2^5)) * (3 * (v1+v2) / (_root_.GD.N0155.d006294 v1 v2 u)^8) *
              (y ^ 8 * Real.exp (-y))
          + (-(_root_.GD.N0155.d006193 (1-u) * ((1-u) - _root_.GD.N0155.d006267 (v2/v1)) * (u^4 * (1-u)^4) *
            (5^10 / (576 * v1^5 * v2^5)) * (7/2) / (_root_.GD.N0155.d006294 v1 v2 u)^9)) *
              (y ^ 9 * Real.exp (-y)))) (_root_.GD.N0155.d006294 v1 v2 u * T) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun T hT => ?_
    have hT0 : (0:ℝ) < T := hT
    have hTne : T ≠ 0 := ne_of_gt hT0
    have h11 : 11 * ((1-u)*T) + 11 * (u*T) ≠ 0 := by
      rw [show 11 * ((1-u)*T) + 11 * (u*T) = 11 * T by ring]
      positivity
    have hexp : Real.exp (-(5 * (u*T) / v1)) * Real.exp (-(5 * ((1-u)*T) / v2))
        = Real.exp (-(_root_.GD.N0155.d006294 v1 v2 u * T)) := by
      rw [← Real.exp_add]
      congr 1
      unfold _root_.GD.N0155.d006294
      first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf
    simp only [_root_.GD.N0155.d006293]
    rw [← hexp]
    unfold _root_.GD.N0155.d006193 _root_.GD.N0155.d006267 _root_.GD.N0155.d006294
    have hnum : u * v2 + (1 - u) * v1 ≠ 0 := by
      intro h; apply hsne; unfold _root_.GD.N0155.d006294; rw [h]; simp
    have h1p : (1 : ℝ) + v2 / v1 ≠ 0 := by
      rw [show (1 : ℝ) + v2 / v1 = (v1 + v2) / v1 by field_simp]
      exact div_ne_zero hvv hv1
    field_simp [hnum, h1p]
    ring
  rw [hcg, MeasureTheory.integral_comp_mul_left_Ioi
        (fun y : ℝ => _root_.GD.N0155.d006193 (1-u) * ((1-u) - _root_.GD.N0155.d006267 (v2/v1)) * (u^4 * (1-u)^4) *
            (5^10 / (576 * v1^5 * v2^5)) * (3 * (v1+v2) / (_root_.GD.N0155.d006294 v1 v2 u)^8) *
              (y ^ 8 * Real.exp (-y))
          + (-(_root_.GD.N0155.d006193 (1-u) * ((1-u) - _root_.GD.N0155.d006267 (v2/v1)) * (u^4 * (1-u)^4) *
            (5^10 / (576 * v1^5 * v2^5)) * (7/2) / (_root_.GD.N0155.d006294 v1 v2 u)^9)) *
              (y ^ 9 * Real.exp (-y))) 0 hs, mul_zero, smul_eq_mul]
  rw [MeasureTheory.integral_add
      (((_root_.GD.N0155.d006292 8).const_mul _))
      (((_root_.GD.N0155.d006292 9).const_mul _)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    _root_.GD.N0155.d006291 8, _root_.GD.N0155.d006291 9]
  norm_num [Nat.factorial]
  first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf


theorem d006302 (v1 v2 : ℝ) (h1 : 0 < v1) (h2 : 0 < v2)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∫ T in Set.Ioi (0:ℝ),
      (_root_.GD.N0155.d006193 (11 * ((1-u)*T) / (11 * ((1-u)*T) + 11 * (u*T))) ^ 2 *
        (15 * ((v1 + v2) / (u*T + (1-u)*T)) ^ 2
          - 21 * ((v1 + v2) / (u*T + (1-u)*T)) + 49/4)) *
        _root_.GD.N0155.d006293 v1 (u*T) * _root_.GD.N0155.d006293 v2 ((1-u)*T) * T)
      = _root_.GD.N0155.d006193 (1-u) ^ 2 * (u^4 * (1-u)^4) * (5^10 / (576 * v1^5 * v2^5)) *
          (15 * (v1+v2)^2 * 5040 / (_root_.GD.N0155.d006294 v1 v2 u)^8
            - 21 * (v1+v2) * 40320 / (_root_.GD.N0155.d006294 v1 v2 u)^9
            + 49/4 * 362880 / (_root_.GD.N0155.d006294 v1 v2 u)^10) := by
  have hs := _root_.GD.N0155.d006295 h1 h2 hu0 hu1
  have hsne : _root_.GD.N0155.d006294 v1 v2 u ≠ 0 := ne_of_gt hs
  have hv1 : v1 ≠ 0 := ne_of_gt h1
  have hv2 : v2 ≠ 0 := ne_of_gt h2
  have hvv : v1 + v2 ≠ 0 := by positivity
  have hcg : (∫ T in Set.Ioi (0:ℝ),
      (_root_.GD.N0155.d006193 (11 * ((1-u)*T) / (11 * ((1-u)*T) + 11 * (u*T))) ^ 2 *
        (15 * ((v1 + v2) / (u*T + (1-u)*T)) ^ 2
          - 21 * ((v1 + v2) / (u*T + (1-u)*T)) + 49/4)) *
        _root_.GD.N0155.d006293 v1 (u*T) * _root_.GD.N0155.d006293 v2 ((1-u)*T) * T)
      = ∫ T in Set.Ioi (0:ℝ),
        (fun y => (_root_.GD.N0155.d006193 (1-u) ^ 2 * (u^4 * (1-u)^4) * (5^10 / (576 * v1^5 * v2^5)) *
            (15 * (v1+v2)^2 / (_root_.GD.N0155.d006294 v1 v2 u)^7) * (y ^ 7 * Real.exp (-y))
          + ((-(_root_.GD.N0155.d006193 (1-u) ^ 2 * (u^4 * (1-u)^4) * (5^10 / (576 * v1^5 * v2^5)) *
            (21 * (v1+v2)) / (_root_.GD.N0155.d006294 v1 v2 u)^8)) * (y ^ 8 * Real.exp (-y))
          + (_root_.GD.N0155.d006193 (1-u) ^ 2 * (u^4 * (1-u)^4) * (5^10 / (576 * v1^5 * v2^5)) *
            (49/4) / (_root_.GD.N0155.d006294 v1 v2 u)^9) * (y ^ 9 * Real.exp (-y))))) (_root_.GD.N0155.d006294 v1 v2 u * T) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun T hT => ?_
    have hT0 : (0:ℝ) < T := hT
    have hTne : T ≠ 0 := ne_of_gt hT0
    have h11 : 11 * ((1-u)*T) + 11 * (u*T) ≠ 0 := by
      rw [show 11 * ((1-u)*T) + 11 * (u*T) = 11 * T by ring]
      positivity
    have hexp : Real.exp (-(5 * (u*T) / v1)) * Real.exp (-(5 * ((1-u)*T) / v2))
        = Real.exp (-(_root_.GD.N0155.d006294 v1 v2 u * T)) := by
      rw [← Real.exp_add]
      congr 1
      unfold _root_.GD.N0155.d006294
      first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf
    simp only [_root_.GD.N0155.d006293]
    rw [← hexp]
    unfold _root_.GD.N0155.d006193 _root_.GD.N0155.d006294
    have hnum : u * v2 + (1 - u) * v1 ≠ 0 := by
      intro h; apply hsne; unfold _root_.GD.N0155.d006294; rw [h]; simp
    field_simp [hnum]
    ring
  have h_int7 : Integrable (fun x : ℝ =>
      _root_.GD.N0155.d006193 (1-u) ^ 2 * (u^4 * (1-u)^4) * (5^10 / (576 * v1^5 * v2^5)) *
        (15 * (v1+v2)^2 / (_root_.GD.N0155.d006294 v1 v2 u)^7) * (x ^ 7 * Real.exp (-x)))
      (volume.restrict (Set.Ioi (0:ℝ))) :=
    (_root_.GD.N0155.d006292 7).const_mul _
  have h_int8 : Integrable (fun x : ℝ =>
      (-(_root_.GD.N0155.d006193 (1-u) ^ 2 * (u^4 * (1-u)^4) * (5^10 / (576 * v1^5 * v2^5)) *
        (21 * (v1+v2)) / (_root_.GD.N0155.d006294 v1 v2 u)^8)) * (x ^ 8 * Real.exp (-x)))
      (volume.restrict (Set.Ioi (0:ℝ))) :=
    (_root_.GD.N0155.d006292 8).const_mul _
  have h_int9 : Integrable (fun x : ℝ =>
      (_root_.GD.N0155.d006193 (1-u) ^ 2 * (u^4 * (1-u)^4) * (5^10 / (576 * v1^5 * v2^5)) *
        (49/4) / (_root_.GD.N0155.d006294 v1 v2 u)^9) * (x ^ 9 * Real.exp (-x)))
      (volume.restrict (Set.Ioi (0:ℝ))) :=
    (_root_.GD.N0155.d006292 9).const_mul _
  have h_int89 : Integrable (fun x : ℝ =>
      (-(_root_.GD.N0155.d006193 (1-u) ^ 2 * (u^4 * (1-u)^4) * (5^10 / (576 * v1^5 * v2^5)) *
        (21 * (v1+v2)) / (_root_.GD.N0155.d006294 v1 v2 u)^8)) * (x ^ 8 * Real.exp (-x))
      + (_root_.GD.N0155.d006193 (1-u) ^ 2 * (u^4 * (1-u)^4) * (5^10 / (576 * v1^5 * v2^5)) *
        (49/4) / (_root_.GD.N0155.d006294 v1 v2 u)^9) * (x ^ 9 * Real.exp (-x)))
      (volume.restrict (Set.Ioi (0:ℝ))) :=
    h_int8.add h_int9
  rw [hcg, MeasureTheory.integral_comp_mul_left_Ioi
        (fun y : ℝ => _root_.GD.N0155.d006193 (1-u) ^ 2 * (u^4 * (1-u)^4) * (5^10 / (576 * v1^5 * v2^5)) *
            (15 * (v1+v2)^2 / (_root_.GD.N0155.d006294 v1 v2 u)^7) * (y ^ 7 * Real.exp (-y))
          + ((-(_root_.GD.N0155.d006193 (1-u) ^ 2 * (u^4 * (1-u)^4) * (5^10 / (576 * v1^5 * v2^5)) *
            (21 * (v1+v2)) / (_root_.GD.N0155.d006294 v1 v2 u)^8)) * (y ^ 8 * Real.exp (-y))
          + (_root_.GD.N0155.d006193 (1-u) ^ 2 * (u^4 * (1-u)^4) * (5^10 / (576 * v1^5 * v2^5)) *
            (49/4) / (_root_.GD.N0155.d006294 v1 v2 u)^9) * (y ^ 9 * Real.exp (-y)))) 0 hs, mul_zero, smul_eq_mul]
  rw [MeasureTheory.integral_add h_int7 h_int89,
    MeasureTheory.integral_add h_int8 h_int9,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul,
    _root_.GD.N0155.d006291 7, _root_.GD.N0155.d006291 8,
    _root_.GD.N0155.d006291 9]
  norm_num [Nat.factorial]
  first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf



theorem d006303 (v1 v2 : ℝ) (h1 : 0 < v1) (h2 : 0 < v2) :
    _root_.GD.N0155.d006299 v1 v2 = _root_.GD.N0155.d006273 (v2 / v1) := by
  unfold _root_.GD.N0155.d006299 _root_.GD.N0155.d006273
  refine intervalIntegral.integral_congr fun u hu => ?_
  obtain ⟨hu0, hu1⟩ := _root_.GD.N0155.d006245 hu
  rw [_root_.GD.N0155.d006301 v1 v2 h1 h2 u hu0 hu1]
  have hv1 : v1 ≠ 0 := ne_of_gt h1
  have hv2 : v2 ≠ 0 := ne_of_gt h2
  have hvv : v1 + v2 ≠ 0 := by positivity
  have hsne : _root_.GD.N0155.d006294 v1 v2 u ≠ 0 := ne_of_gt (_root_.GD.N0155.d006295 h1 h2 hu0 hu1)
  have hdlin : _root_.GD.N0155.d006241 (v2/v1) u ≠ 0 := by
    have hd : _root_.GD.N0155.d006241 (v2/v1) u = (u * v2 + (1-u) * v1) / v1 := by
      unfold _root_.GD.N0155.d006241
      first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf
    rw [hd]
    refine div_ne_zero ?_ hv1
    intro hc
    apply hsne
    unfold _root_.GD.N0155.d006294
    rw [hc]
    simp
  simp only [_root_.GD.N0155.d006271, _root_.GD.N0155.d006193, _root_.GD.N0155.d006267, _root_.GD.N0155.d006268, _root_.GD.N0155.d006269, _root_.GD.N0155.d006270, _root_.GD.N0155.d006241, _root_.GD.N0155.d006294] at *
  first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf


theorem d006304 (v1 v2 : ℝ) (h1 : 0 < v1) (h2 : 0 < v2) :
    _root_.GD.N0155.d006300 v1 v2 = _root_.GD.N0155.d006274 (v2 / v1) := by
  unfold _root_.GD.N0155.d006300 _root_.GD.N0155.d006274
  refine intervalIntegral.integral_congr fun u hu => ?_
  obtain ⟨hu0, hu1⟩ := _root_.GD.N0155.d006245 hu
  rw [_root_.GD.N0155.d006302 v1 v2 h1 h2 u hu0 hu1]
  have hv1 : v1 ≠ 0 := ne_of_gt h1
  have hv2 : v2 ≠ 0 := ne_of_gt h2
  have hvv : v1 + v2 ≠ 0 := by positivity
  have hsne : _root_.GD.N0155.d006294 v1 v2 u ≠ 0 := ne_of_gt (_root_.GD.N0155.d006295 h1 h2 hu0 hu1)
  have hdlin : _root_.GD.N0155.d006241 (v2/v1) u ≠ 0 := by
    have hd : _root_.GD.N0155.d006241 (v2/v1) u = (u * v2 + (1-u) * v1) / v1 := by
      unfold _root_.GD.N0155.d006241
      first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf
    rw [hd]
    refine div_ne_zero ?_ hv1
    intro hc
    apply hsne
    unfold _root_.GD.N0155.d006294
    rw [hc]
    simp
  simp only [_root_.GD.N0155.d006272, _root_.GD.N0155.d006193, _root_.GD.N0155.d006267, _root_.GD.N0155.d006268, _root_.GD.N0155.d006269, _root_.GD.N0155.d006270, _root_.GD.N0155.d006241, _root_.GD.N0155.d006294] at *
  first | done | (field_simp; ring) | (push_cast; field_simp; ring) | (field_simp; done) | (push_cast; field_simp; done) | ring | (push_cast; ring) | (field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; field_simp; ring_nf; first | rfl | linarith | done) | (push_cast; ring_nf; first | rfl | linarith | done) | (field_simp; push_cast; ring_nf; first | rfl | linarith | done) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; field_simp; ring) | (simp only [Pi.pow_apply, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ, Nat.cast_add_one]; push_cast; field_simp; ring) | (field_simp; ring_nf; first | done | (field_simp; ring) | ring) | (field_simp; linear_combination hkey) | (norm_cast; first | done | ring | (field_simp; ring)) | (push_cast [Nat.cast_succ, Nat.cast_add_one, Pi.pow_apply]; first | done | ring | (field_simp; ring)) | ring_nf

end GD.N0155
