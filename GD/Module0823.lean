import GD.Module0752
import GD.Module0643
import GD.Module0816





























open scoped BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1498

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0954
open _root_.GD.N0232.N0719.N1011
open _root_.GD.N0232.N0719.N0928
open _root_.GD.N0232.N0720.N1034





def d012562
    (sampleSize : ℕ) (mean meanVariance : ℝ) : ℝ :=
  (sampleSize : ℝ) ^ (-(sampleSize : ℝ) / 2) *
    Real.exp
      ((_root_.GD.N0232.N0719.N1011.d011283 sampleSize meanVariance +
        (sampleSize : ℝ) * mean ^ 2) / 2)



def d012563
    (sampleSize : ℕ) (precision location mean meanVariance : ℝ) : ℝ :=
  precision ^ ((sampleSize : ℝ) / 2) *
    Real.exp
      (-(precision *
        ((((sampleSize - 1 : ℕ) : ℝ) / 2) * meanVariance +
          (mean - location) ^ 2 / 2)))


def d012564
    (m n : ℕ) (u : _root_.GD.N0232.N0719.N0900.d009096 2) : ℝ :=
  _root_.GD.N0232.N0720.N1498.d012562 m (u.mean 0) (u.meanVariance 0) *
    _root_.GD.N0232.N0720.N1498.d012562 n (u.mean 1) (u.meanVariance 1)



theorem d012565
    {sampleSize : ℕ} (hsize : 0 < sampleSize)
    (mean meanVariance : ℝ) :
    0 < _root_.GD.N0232.N0720.N1498.d012562 sampleSize mean meanVariance := by
  unfold _root_.GD.N0232.N0720.N1498.d012562
  exact mul_pos
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hsize) _)
    (Real.exp_pos _)

theorem d012566
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) :
    0 < _root_.GD.N0232.N0720.N1498.d012564 m n u := by
  exact mul_pos
    (_root_.GD.N0232.N0720.N1498.d012565 hm _ _)
    (_root_.GD.N0232.N0720.N1498.d012565 hn _ _)




def d012567 (m : ℕ) (q z : ℝ) : ℝ :=
  Real.sqrt ((m : ℝ) * q / z)


def d012568 (n : ℕ) (q z : ℝ) : ℝ :=
  Real.sqrt ((n : ℝ) * q / (1 - z))

theorem d012569
    {m : ℕ} (hm : 0 < m) {q z : ℝ}
    (hq : 0 < q) (hz : 0 < z) :
    0 < _root_.GD.N0232.N0720.N1498.d012567 m q z := by
  unfold _root_.GD.N0232.N0720.N1498.d012567
  exact Real.sqrt_pos.2 (div_pos (mul_pos (Nat.cast_pos.mpr hm) hq) hz)

theorem d012570
    {n : ℕ} (hn : 0 < n) {q z : ℝ}
    (hq : 0 < q) (hz : z < 1) :
    0 < _root_.GD.N0232.N0720.N1498.d012568 n q z := by
  unfold _root_.GD.N0232.N0720.N1498.d012568
  exact Real.sqrt_pos.2
    (div_pos (mul_pos (Nat.cast_pos.mpr hn) hq) (sub_pos.mpr hz))

theorem d012571
    {m : ℕ} (hm : 0 < m) {q z : ℝ}
    (hq : 0 < q) (hz : 0 < z) :
    _root_.GD.N0232.N0720.N1498.d012567 m q z ^ 2 = (m : ℝ) * q / z := by
  unfold _root_.GD.N0232.N0720.N1498.d012567
  exact Real.sq_sqrt
    (div_nonneg (mul_nonneg (Nat.cast_nonneg m) hq.le) hz.le)

theorem d012572
    {n : ℕ} (hn : 0 < n) {q z : ℝ}
    (hq : 0 < q) (hz : z < 1) :
    _root_.GD.N0232.N0720.N1498.d012568 n q z ^ 2 = (n : ℝ) * q / (1 - z) := by
  unfold _root_.GD.N0232.N0720.N1498.d012568
  exact Real.sq_sqrt
    (div_nonneg (mul_nonneg (Nat.cast_nonneg n) hq.le)
      (sub_nonneg.mpr hz.le))

theorem d012573
    {m : ℕ} (hm : 0 < m) {q z : ℝ}
    (hq : 0 < q) (hz : 0 < z) :
    (m : ℝ) / _root_.GD.N0232.N0720.N1498.d012567 m q z ^ 2 = z / q := by
  rw [_root_.GD.N0232.N0720.N1498.d012571 hm hq hz]
  field_simp [Nat.cast_ne_zero.mpr hm.ne', hq.ne', hz.ne']

theorem d012574
    {n : ℕ} (hn : 0 < n) {q z : ℝ}
    (hq : 0 < q) (hz : z < 1) :
    (n : ℝ) / _root_.GD.N0232.N0720.N1498.d012568 n q z ^ 2 = (1 - z) / q := by
  rw [_root_.GD.N0232.N0720.N1498.d012572 hn hq hz]
  field_simp [Nat.cast_ne_zero.mpr hn.ne', hq.ne', sub_ne_zero.mpr hz.ne']





theorem d012575
    {sampleSize : ℕ} (hsize : 0 < sampleSize)
    (location : ℝ) {scale : ℝ} (hscale : 0 < scale)
    (mean meanVariance : ℝ) :
    _root_.GD.N0232.N0719.N1011.d011284 sampleSize location scale mean meanVariance =
      _root_.GD.N0232.N0720.N1498.d012562 sampleSize mean meanVariance *
        _root_.GD.N0232.N0720.N1498.d012563 sampleSize
          ((sampleSize : ℝ) / scale ^ 2)
          location mean meanVariance := by
  let N : ℝ := sampleSize
  have hN : 0 < N := by
    simpa [N] using (Nat.cast_pos.mpr hsize : 0 < (sampleSize : ℝ))
  have hscale0 : scale ≠ 0 := hscale.ne'
  have htwoPi : 0 < 2 * Real.pi := by positivity
  have hsqrt :
      Real.sqrt (2 * Real.pi * scale ^ 2) =
        Real.sqrt (2 * Real.pi) * scale := by
    rw [Real.sqrt_mul (show 0 ≤ 2 * Real.pi by positivity)]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hscale]
  have hnormalization :
      ((Real.sqrt (2 * Real.pi * scale ^ 2))⁻¹ /
          (Real.sqrt (2 * Real.pi))⁻¹) ^ sampleSize =
        (sampleSize : ℝ) ^ (-(sampleSize : ℝ) / 2) *
          ((sampleSize : ℝ) / scale ^ 2) ^
            ((sampleSize : ℝ) / 2) := by
    rw [hsqrt]
    have hsqrtTwoPi : Real.sqrt (2 * Real.pi) ≠ 0 :=
      (Real.sqrt_pos.2 htwoPi).ne'
    have hleft :
        (Real.sqrt (2 * Real.pi) * scale)⁻¹ /
            (Real.sqrt (2 * Real.pi))⁻¹ = scale⁻¹ := by
      field_simp [hsqrtTwoPi, hscale0]
    rw [hleft]
    rw [Real.div_rpow hN.le (sq_nonneg scale)]
    rw [show -(sampleSize : ℝ) / 2 = -((sampleSize : ℝ) / 2) by ring,
      Real.rpow_neg hN.le]
    have hscalePow :
        (scale ^ 2) ^ ((sampleSize : ℝ) / 2) =
          scale ^ (sampleSize : ℝ) := by
      rw [show scale ^ 2 = scale ^ (2 : ℝ) by
        simp [Real.rpow_two]]
      rw [← Real.rpow_mul hscale.le]
      congr 1
      ring
    rw [hscalePow, Real.rpow_natCast]
    field_simp [(Real.rpow_pos_of_pos hN _).ne', hscale0]
    rw [one_div, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hscale0)]
  have hsubCast :
      (((sampleSize - 1 : ℕ) : ℝ)) = (sampleSize : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr hsize)]
    norm_num
  have hcost :
      ((sampleSize : ℝ) / scale ^ 2) *
          ((((sampleSize - 1 : ℕ) : ℝ) / 2) * meanVariance +
            (mean - location) ^ 2 / 2) =
        (_root_.GD.N0232.N0719.N1011.d011283 sampleSize meanVariance +
            (sampleSize : ℝ) * (mean - location) ^ 2) /
          (2 * scale ^ 2) := by
    unfold _root_.GD.N0232.N0719.N1011.d011283
    rw [hsubCast]
    field_simp [hscale0]
  unfold _root_.GD.N0232.N0719.N1011.d011284 _root_.GD.N0232.N0720.N1498.d012562
    _root_.GD.N0232.N0720.N1498.d012563
  have hexp (a b : ℝ) : Real.exp (a - b) = Real.exp a * Real.exp (-b) := by
    rw [sub_eq_add_neg, Real.exp_add]
  rw [hnormalization, hcost, hexp]
  ring




theorem d012576
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (location : ℝ) {q z : ℝ}
    (hq : 0 < q) (hz0 : 0 < z) (hz1 : z < 1) :
    _root_.GD.N0232.N0719.N1011.d011288 2 (_root_.GD.N0232.N0720.N1034.d012430 m n) location
        ![_root_.GD.N0232.N0720.N1498.d012567 m q z, _root_.GD.N0232.N0720.N1498.d012568 n q z] u =
      _root_.GD.N0232.N0720.N1498.d012564 m n u *
        _root_.GD.N0232.N0719.N0928.d009411
          (_root_.GD.N0232.N0719.N0954.d009355 (_root_.GD.N0232.N0720.N1034.d012430 m n))
          (_root_.GD.N0232.N0720.N1034.d012417 z) u.mean u.meanVariance location q := by
  rw [show _root_.GD.N0232.N0719.N1011.d011288 2 (_root_.GD.N0232.N0720.N1034.d012430 m n) location
      ![_root_.GD.N0232.N0720.N1498.d012567 m q z, _root_.GD.N0232.N0720.N1498.d012568 n q z] u =
      _root_.GD.N0232.N0719.N1011.d011284 m location (_root_.GD.N0232.N0720.N1498.d012567 m q z)
          (u.mean 0) (u.meanVariance 0) *
        _root_.GD.N0232.N0719.N1011.d011284 n location (_root_.GD.N0232.N0720.N1498.d012568 n q z)
          (u.mean 1) (u.meanVariance 1) by
    unfold _root_.GD.N0232.N0719.N1011.d011288
    rw [Fin.prod_univ_two]
    rfl]
  rw [_root_.GD.N0232.N0720.N1498.d012575
      hm location (_root_.GD.N0232.N0720.N1498.d012569 hm hq hz0)
      (u.mean 0) (u.meanVariance 0),
    _root_.GD.N0232.N0720.N1498.d012575
      hn location (_root_.GD.N0232.N0720.N1498.d012570 hn hq hz1)
      (u.mean 1) (u.meanVariance 1)]
  rw [_root_.GD.N0232.N0720.N1498.d012573 hm hq hz0,
    _root_.GD.N0232.N0720.N1498.d012574 hn hq hz1]
  have hmCast : (((m - 1 : ℕ) : ℝ)) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr hm)]
    norm_num
  have hnCast : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr hn)]
    norm_num
  have hmPower :
      (((m - 1 : ℕ) : ℝ) / 2 + 1 / 2) = (m : ℝ) / 2 := by
    rw [hmCast]
    ring
  have hnPower :
      (((n - 1 : ℕ) : ℝ) / 2 + 1 / 2) = (n : ℝ) / 2 := by
    rw [hnCast]
    ring
  unfold _root_.GD.N0232.N0719.N0928.d009411
  rw [Fin.prod_univ_two]
  unfold _root_.GD.N0232.N0719.N0928.d009410 _root_.GD.N0232.N0720.N1498.d012563
    _root_.GD.N0232.N0720.N1498.d012564 _root_.GD.N0232.N0720.N1034.d012417
    _root_.GD.N0232.N0720.N1034.d012430 _root_.GD.N0232.N0719.N0954.d009355
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hmPower, hnPower, hmCast, hnCast]
  ring





theorem d012577
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (location : ℝ) {q z : ℝ}
    (hq : 0 < q) (hz0 : 0 < z) (hz1 : z < 1) :
    _root_.GD.N0232.N0719.N1011.d011288 2 (_root_.GD.N0232.N0720.N1034.d012430 m n) location
        ![_root_.GD.N0232.N0720.N1498.d012567 m q z, _root_.GD.N0232.N0720.N1498.d012568 n q z] u =
      _root_.GD.N0232.N0720.N1498.d012564 m n u *
        _root_.GD.N0232.N0719.N0928.d009412
          (_root_.GD.N0232.N0719.N0954.d009355 (_root_.GD.N0232.N0720.N1034.d012430 m n))
          (_root_.GD.N0232.N0720.N1034.d012417 z) u.mean u.meanVariance location q := by
  rw [_root_.GD.N0232.N0720.N1498.d012576
    hm hn u location hq hz0 hz1]
  congr 1
  apply _root_.GD.N0232.N0719.N0928.d009423
  · intro i
    fin_cases i
    · simpa [_root_.GD.N0232.N0720.N1034.d012417] using hz0
    · simpa [_root_.GD.N0232.N0720.N1034.d012417] using sub_pos.mpr hz1
  · exact hq
  · simp [_root_.GD.N0232.N0720.N1034.d012417]

end

end N1498
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1498.d012575
#print axioms _root_.GD.N0232.N0720.N1498.d012577
