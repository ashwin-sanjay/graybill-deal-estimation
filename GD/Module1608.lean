import GD.Module1574
import GD.Module1573













set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped Interval

namespace GD.N0106.N0428.N0770.N1731
noncomputable section

open _root_.GD.N0118
open _root_.GD.N0106.N0428.N0770.N1725


def d027426 (n r : ℕ) (w : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..w, x ^ n * ((w - x) / w ^ 2) ^ r

theorem d027427 (c w x : ℝ) (n r : ℕ) (hr : 0 < r) :
    (x - c) ^ n * _root_.GD.N0118.d008582 c w x ^ r =
      (Ioc (c - w) c).indicator
        (fun y => (y - c) ^ n * _root_.GD.N0118.d008580 c w y ^ r) x +
      (Ioc c (c + w)).indicator
        (fun y => (y - c) ^ n * _root_.GD.N0118.d008581 c w y ^ r) x := by
  by_cases hL : x ∈ Ioc (c - w) c
  · have hR : x ∉ Ioc c (c + w) := by
      intro hx
      linarith [hL.2, hx.1]
    simp [_root_.GD.N0118.d008582, hL, hR]
  · by_cases hR : x ∈ Ioc c (c + w)
    · simp [_root_.GD.N0118.d008582, hL, hR]
    · simp [_root_.GD.N0118.d008582, hL, hR, zero_pow hr.ne']

theorem d027428 (c w : ℝ) (n r : ℕ) (hr : 0 < r) :
    Integrable (fun x => (x - c) ^ n * _root_.GD.N0118.d008582 c w x ^ r) := by
  have hL : Continuous (fun x : ℝ => (x - c) ^ n * _root_.GD.N0118.d008580 c w x ^ r) := by
    unfold _root_.GD.N0118.d008580
    fun_prop
  have hR : Continuous (fun x : ℝ => (x - c) ^ n * _root_.GD.N0118.d008581 c w x ^ r) := by
    unfold _root_.GD.N0118.d008581
    fun_prop
  simp_rw [_root_.GD.N0106.N0428.N0770.N1731.d027427 c w _ n r hr]
  exact (hL.integrableOn_Ioc.integrable_indicator measurableSet_Ioc).add
    (hR.integrableOn_Ioc.integrable_indicator measurableSet_Ioc)

theorem d027429 (c w : ℝ) (n r : ℕ)
    (hw : 0 < w) (hr : 0 < r) :
    (∫ x, (x - c) ^ n * _root_.GD.N0118.d008582 c w x ^ r) =
      ((-1 : ℝ) ^ n + 1) * _root_.GD.N0106.N0428.N0770.N1731.d027426 n r w := by
  have hL : Continuous (fun x : ℝ => (x - c) ^ n * _root_.GD.N0118.d008580 c w x ^ r) := by
    unfold _root_.GD.N0118.d008580
    fun_prop
  have hR : Continuous (fun x : ℝ => (x - c) ^ n * _root_.GD.N0118.d008581 c w x ^ r) := by
    unfold _root_.GD.N0118.d008581
    fun_prop
  have left : (∫ x in Ioc (c - w) c, (x - c) ^ n * _root_.GD.N0118.d008580 c w x ^ r) =
      (-1 : ℝ) ^ n * _root_.GD.N0106.N0428.N0770.N1731.d027426 n r w := by
    rw [← intervalIntegral.integral_of_le (by linarith : c - w ≤ c)]
    have heq : (fun x => (x - c) ^ n * _root_.GD.N0118.d008580 c w x ^ r) =
        fun x => (-1 : ℝ) ^ n *
          ((c - x) ^ n * ((w - (c - x)) / w ^ 2) ^ r) := by
      funext x
      rw [show _root_.GD.N0118.d008580 c w x = (w - (c - x)) / w ^ 2 by unfold _root_.GD.N0118.d008580; ring,
        show x - c = -(c - x) by ring, neg_pow]
      ring
    rw [heq, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left
        (fun x : ℝ => x ^ n * ((w - x) / w ^ 2) ^ r) c]
    simp only [sub_self, sub_sub_cancel]
    rfl
  have right : (∫ x in Ioc c (c + w), (x - c) ^ n * _root_.GD.N0118.d008581 c w x ^ r) =
      _root_.GD.N0106.N0428.N0770.N1731.d027426 n r w := by
    rw [← intervalIntegral.integral_of_le (by linarith : c ≤ c + w)]
    have heq : (fun x => (x - c) ^ n * _root_.GD.N0118.d008581 c w x ^ r) =
        fun x => (x - c) ^ n * ((w - (x - c)) / w ^ 2) ^ r := by
      funext x
      rw [show _root_.GD.N0118.d008581 c w x = (w - (x - c)) / w ^ 2 by unfold _root_.GD.N0118.d008581; ring]
    rw [heq, intervalIntegral.integral_comp_sub_right
      (fun x : ℝ => x ^ n * ((w - x) / w ^ 2) ^ r) c]
    simp only [sub_self, add_sub_cancel_left]
    rfl
  simp_rw [_root_.GD.N0106.N0428.N0770.N1731.d027427 c w _ n r hr]
  rw [integral_add
      (hL.integrableOn_Ioc.integrable_indicator measurableSet_Ioc)
      (hR.integrableOn_Ioc.integrable_indicator measurableSet_Ioc),
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc,
    left, right]
  ring


theorem d027430 (c w : ℝ) (r : ℕ) (hw : 0 < w) (hr : 0 < r) :
    (∫ x, (x - c) * _root_.GD.N0118.d008582 c w x ^ r) = 0 := by
  have h := _root_.GD.N0106.N0428.N0770.N1731.d027429 c w 1 r hw hr
  simpa only [pow_one, neg_add_cancel, zero_mul] using h

theorem d027431 (w : ℝ) (hw : 0 < w) :
    _root_.GD.N0106.N0428.N0770.N1731.d027426 2 1 w = w ^ 2 / 12 := by
  let primitive : ℝ → ℝ := fun x => (w * x ^ 3 / 3 - x ^ 4 / 4) / w ^ 2
  have hd (x : ℝ) : HasDerivAt primitive (x ^ 2 * ((w - x) / w ^ 2)) x := by
    apply ((((((hasDerivAt_id x).pow 3).const_mul w).div_const 3).sub
      (((hasDerivAt_id x).pow 4).div_const 4)).div_const (w ^ 2)).congr_deriv
    simp only [id_eq]
    ring
  have hc : Continuous (fun x : ℝ => x ^ 2 * ((w - x) / w ^ 2)) := by fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hd x) (hc.intervalIntegrable (0 : ℝ) w)
  change (∫ x in (0 : ℝ)..w, x ^ 2 * ((w - x) / w ^ 2) ^ 1) = _
  rw [show (fun x : ℝ => x ^ 2 * ((w - x) / w ^ 2) ^ 1) =
      (fun x : ℝ => x ^ 2 * ((w - x) / w ^ 2)) by funext x; rw [pow_one], hi]
  dsimp [primitive]
  field_simp [hw.ne']
  <;> ring

theorem d027432 (w : ℝ) (hw : 0 < w) :
    _root_.GD.N0106.N0428.N0770.N1731.d027426 2 2 w = w / 30 := by
  let primitive : ℝ → ℝ := fun x =>
    (w ^ 2 * x ^ 3 / 3 - w * x ^ 4 / 2 + x ^ 5 / 5) / w ^ 4
  have hd (x : ℝ) : HasDerivAt primitive (x ^ 2 * ((w - x) / w ^ 2) ^ 2) x := by
    have h3 := (((hasDerivAt_id x).pow 3).const_mul (w ^ 2)).div_const 3
    have h4 := (((hasDerivAt_id x).pow 4).const_mul w).div_const 2
    have h5 := ((hasDerivAt_id x).pow 5).div_const 5
    apply (((h3.sub h4).add h5).div_const (w ^ 4)).congr_deriv
    simp only [id_eq]
    ring
  have hc : Continuous (fun x : ℝ => x ^ 2 * ((w - x) / w ^ 2) ^ 2) := by fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hd x) (hc.intervalIntegrable (0 : ℝ) w)
  change (∫ x in (0 : ℝ)..w, x ^ 2 * ((w - x) / w ^ 2) ^ 2) = _
  rw [hi]
  dsimp [primitive]
  field_simp [hw.ne']
  <;> ring

theorem d027433 (c w : ℝ) (hw : 0 < w) :
    (∫ x, (x - c) ^ 2 * _root_.GD.N0118.d008582 c w x) = w ^ 2 / 6 := by
  have h := _root_.GD.N0106.N0428.N0770.N1731.d027429 c w 2 1 hw (by norm_num)
  rw [_root_.GD.N0106.N0428.N0770.N1731.d027431 w hw] at h
  norm_num only [pow_one, neg_sq, one_pow] at h
  convert h using 1 <;> ring

theorem d027434 (c w : ℝ) (hw : 0 < w) :
    (∫ x, (x - c) ^ 2 * _root_.GD.N0118.d008582 c w x ^ 2) = w / 15 := by
  have h := _root_.GD.N0106.N0428.N0770.N1731.d027429 c w 2 2 hw (by norm_num)
  rw [_root_.GD.N0106.N0428.N0770.N1731.d027432 w hw] at h
  norm_num only [neg_sq, one_pow] at h
  convert h using 1 <;> ring


theorem d027435 (c w : ℝ) (hw : 0 < w) :
    (∫ x, (x - c) ^ 2 * _root_.GD.N0118.d008582 c w x ^ 2) / (∫ x, _root_.GD.N0118.d008582 c w x ^ 2) =
      w ^ 2 / 10 := by
  rw [_root_.GD.N0106.N0428.N0770.N1731.d027434 c w hw, _root_.GD.N0118.d008599 c w hw]
  field_simp [hw.ne']
  <;> ring


theorem d027436 (c f w : ℝ) (n m r : ℕ)
    (hw : 0 < w) (p : ℝ × ℝ) :
    (p.1 - c) ^ n * (p.2 - f) ^ m * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ^ r =
      w ^ (2 * r) *
        (((p.1 - c) ^ n * _root_.GD.N0118.d008582 c w p.1 ^ r) *
          ((p.2 - f) ^ m * _root_.GD.N0118.d008582 f w p.2 ^ r)) := by
  rw [_root_.GD.N0106.N0428.N0770.N1725.d024151 c f w p hw]
  simp only [_root_.GD.N0118.d008583, mul_pow, ← pow_mul]
  ring

theorem d027437 (c f w : ℝ) (n m r : ℕ)
    (hw : 0 < w) (hr : 0 < r) :
    Integrable (fun p => (p.1 - c) ^ n * (p.2 - f) ^ m * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ^ r)
      (volume.prod volume) := by
  simp_rw [_root_.GD.N0106.N0428.N0770.N1731.d027436 c f w n m r hw]
  exact ((_root_.GD.N0106.N0428.N0770.N1731.d027428 c w n r hr).mul_prod
    (_root_.GD.N0106.N0428.N0770.N1731.d027428 f w m r hr)).const_mul (w ^ (2 * r))

theorem d027438 (c f w : ℝ) (n m r : ℕ) (hw : 0 < w) :
    (∫ p, (p.1 - c) ^ n * (p.2 - f) ^ m * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ^ r
      ∂(volume.prod volume)) =
      w ^ (2 * r) *
        ((∫ x, (x - c) ^ n * _root_.GD.N0118.d008582 c w x ^ r) *
          (∫ y, (y - f) ^ m * _root_.GD.N0118.d008582 f w y ^ r)) := by
  simp_rw [_root_.GD.N0106.N0428.N0770.N1731.d027436 c f w n m r hw]
  rw [integral_const_mul]
  exact congrArg (fun z : ℝ => w ^ (2 * r) * z)
    (integral_prod_mul (μ := volume) (ν := volume)
      (fun x : ℝ => (x - c) ^ n * _root_.GD.N0118.d008582 c w x ^ r)
      (fun y : ℝ => (y - f) ^ m * _root_.GD.N0118.d008582 f w y ^ r))


theorem d027439 (c f w : ℝ) (r : ℕ)
    (hw : 0 < w) (hr : 0 < r) :
    (∫ p, (p.1 - c) * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ^ r ∂(volume.prod volume)) = 0 ∧
    (∫ p, (p.2 - f) * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ^ r ∂(volume.prod volume)) = 0 ∧
    (∫ p, (p.1 - c) * (p.2 - f) * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ^ r
      ∂(volume.prod volume)) = 0 := by
  have h10 := _root_.GD.N0106.N0428.N0770.N1731.d027438 c f w 1 0 r hw
  have h01 := _root_.GD.N0106.N0428.N0770.N1731.d027438 c f w 0 1 r hw
  have h11 := _root_.GD.N0106.N0428.N0770.N1731.d027438 c f w 1 1 r hw
  norm_num only [pow_zero, pow_one, one_mul, mul_one] at h10 h01 h11
  rw [_root_.GD.N0106.N0428.N0770.N1731.d027430 c w r hw hr, zero_mul, mul_zero] at h10 h11
  rw [_root_.GD.N0106.N0428.N0770.N1731.d027430 f w r hw hr, mul_zero, mul_zero] at h01
  exact ⟨h10, h01, h11⟩


theorem d027440 (c f w : ℝ) (hw : 0 < w) :
    (∫ p, (p.1 - c) ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ∂(volume.prod volume)) = w ^ 4 / 6 ∧
    (∫ p, (p.2 - f) ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ∂(volume.prod volume)) = w ^ 4 / 6 := by
  have h20 := _root_.GD.N0106.N0428.N0770.N1731.d027438 c f w 2 0 1 hw
  have h02 := _root_.GD.N0106.N0428.N0770.N1731.d027438 c f w 0 2 1 hw
  norm_num only [pow_zero, pow_one, one_mul, mul_one] at h20 h02
  rw [_root_.GD.N0106.N0428.N0770.N1731.d027433 c w hw, _root_.GD.N0118.d008594 f w hw] at h20
  rw [_root_.GD.N0118.d008594 c w hw, _root_.GD.N0106.N0428.N0770.N1731.d027433 f w hw] at h02
  constructor
  · convert h20 using 1 <;> ring
  · convert h02 using 1 <;> ring


theorem d027441 (c f w : ℝ) (hw : 0 < w) :
    (∫ p, (p.1 - c) ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ^ 2 ∂(volume.prod volume)) =
      2 * w ^ 4 / 45 ∧
    (∫ p, (p.2 - f) ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ^ 2 ∂(volume.prod volume)) =
      2 * w ^ 4 / 45 := by
  have h20 := _root_.GD.N0106.N0428.N0770.N1731.d027438 c f w 2 0 2 hw
  have h02 := _root_.GD.N0106.N0428.N0770.N1731.d027438 c f w 0 2 2 hw
  norm_num only [pow_zero, one_mul, mul_one] at h20 h02
  rw [_root_.GD.N0106.N0428.N0770.N1731.d027434 c w hw, _root_.GD.N0118.d008599 f w hw] at h20
  rw [_root_.GD.N0118.d008599 c w hw, _root_.GD.N0106.N0428.N0770.N1731.d027434 f w hw] at h02
  constructor
  · rw [h20]
    field_simp [hw.ne']
    <;> ring
  · rw [h02]
    field_simp [hw.ne']
    <;> ring


theorem d027442 (c f w : ℝ) (hw : 0 < w) :
    (∫ p, (p.1 - c) ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ∂(volume.prod volume)) /
        (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ∂(volume.prod volume)) = w ^ 2 / 6 ∧
    (∫ p, (p.2 - f) ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ∂(volume.prod volume)) /
        (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ∂(volume.prod volume)) = w ^ 2 / 6 := by
  rw [(_root_.GD.N0106.N0428.N0770.N1731.d027440 c f w hw).1,
    (_root_.GD.N0106.N0428.N0770.N1731.d027440 c f w hw).2, _root_.GD.N0106.N0428.N0770.N1725.d024152 c f w hw]
  constructor <;> field_simp [hw.ne'] <;> ring


theorem d027443 (c f w : ℝ) (hw : 0 < w) :
    (∫ p, (p.1 - c) ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ^ 2 ∂(volume.prod volume)) /
        (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ^ 2 ∂(volume.prod volume)) = w ^ 2 / 10 ∧
    (∫ p, (p.2 - f) ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ^ 2 ∂(volume.prod volume)) /
        (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ^ 2 ∂(volume.prod volume)) = w ^ 2 / 10 := by
  rw [(_root_.GD.N0106.N0428.N0770.N1731.d027441 c f w hw).1,
    (_root_.GD.N0106.N0428.N0770.N1731.d027441 c f w hw).2, _root_.GD.N0106.N0428.N0770.N1725.d024153 c f w hw]
  constructor <;> field_simp [hw.ne'] <;> ring


theorem d027444 (c f w : ℝ) (hw : 0 < w) :
    ((∫ p, (p.1 - c) ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ∂(volume.prod volume)) /
      (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ∂(volume.prod volume))) / w ^ 2 = 1 / 6 ∧
    ((∫ p, (p.2 - f) ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ∂(volume.prod volume)) /
      (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ∂(volume.prod volume))) / w ^ 2 = 1 / 6 ∧
    ((∫ p, (p.1 - c) ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ^ 2 ∂(volume.prod volume)) /
      (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ^ 2 ∂(volume.prod volume))) / w ^ 2 = 1 / 10 ∧
    ((∫ p, (p.2 - f) ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ^ 2 ∂(volume.prod volume)) /
      (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ^ 2 ∂(volume.prod volume))) / w ^ 2 = 1 / 10 := by
  rw [(_root_.GD.N0106.N0428.N0770.N1731.d027442 c f w hw).1,
    (_root_.GD.N0106.N0428.N0770.N1731.d027442 c f w hw).2,
    (_root_.GD.N0106.N0428.N0770.N1731.d027443 c f w hw).1,
    (_root_.GD.N0106.N0428.N0770.N1731.d027443 c f w hw).2]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp [hw.ne'] <;> ring




open _root_.GD.N0106.N0428.N0770.N1726

theorem d027445 (i : Fin 12) (r : ℕ) (hr : 0 < r)
    (phi : (ℝ × ℝ) → ℝ) :
    (∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, phi p * _root_.GD.N0106.N0428.N0770.N1726.d024364 i p ^ r ∂(volume.prod volume)) =
      ∫ p, phi p * _root_.GD.N0106.N0428.N0770.N1726.d024364 i p ^ r ∂(volume.prod volume) := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  have hz : _root_.GD.N0106.N0428.N0770.N1726.d024364 i p = 0 := by
    by_contra hn
    exact hp (_root_.GD.N0106.N0428.N0770.N1726.d024380 i (subset_tsupport _ hn))
  rw [hz, zero_pow hr.ne', mul_zero]

theorem d027446 (i : Fin 12) :
    (∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, _root_.GD.N0106.N0428.N0770.N1726.d024364 i p ∂(volume.prod volume)) = _root_.GD.N0106.N0428.N0770.N1726.d024363 i ^ 2 := by
  have h := _root_.GD.N0106.N0428.N0770.N1731.d027445 i 1 (by norm_num) (fun _ => 1)
  simp only [pow_one, one_mul] at h
  rw [h]
  exact _root_.GD.N0106.N0428.N0770.N1725.d024152 _ _ _ (_root_.GD.N0106.N0428.N0770.N1726.d024369 i)

theorem d027447 (i : Fin 12) :
    (∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, _root_.GD.N0106.N0428.N0770.N1726.d024364 i p ^ 2 ∂(volume.prod volume)) = 4 * _root_.GD.N0106.N0428.N0770.N1726.d024363 i ^ 2 / 9 := by
  have h := _root_.GD.N0106.N0428.N0770.N1731.d027445 i 2 (by norm_num) (fun _ => 1)
  simp only [one_mul] at h
  rw [h]
  exact _root_.GD.N0106.N0428.N0770.N1725.d024153 _ _ _ (_root_.GD.N0106.N0428.N0770.N1726.d024369 i)

theorem d027448 (i : Fin 12) (r : ℕ) (hr : 0 < r) :
    (∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, (p.1 - _root_.GD.N0106.N0428.N0770.N1726.d024361 i) * _root_.GD.N0106.N0428.N0770.N1726.d024364 i p ^ r ∂(volume.prod volume)) = 0 ∧
    (∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, (p.2 - _root_.GD.N0106.N0428.N0770.N1726.d024362 i) * _root_.GD.N0106.N0428.N0770.N1726.d024364 i p ^ r ∂(volume.prod volume)) = 0 ∧
    (∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, (p.1 - _root_.GD.N0106.N0428.N0770.N1726.d024361 i) * (p.2 - _root_.GD.N0106.N0428.N0770.N1726.d024362 i) * _root_.GD.N0106.N0428.N0770.N1726.d024364 i p ^ r
      ∂(volume.prod volume)) = 0 := by
  simp_rw [_root_.GD.N0106.N0428.N0770.N1731.d027445 i r hr]
  exact _root_.GD.N0106.N0428.N0770.N1731.d027439
    (_root_.GD.N0106.N0428.N0770.N1726.d024361 i) (_root_.GD.N0106.N0428.N0770.N1726.d024362 i) (_root_.GD.N0106.N0428.N0770.N1726.d024363 i) r (_root_.GD.N0106.N0428.N0770.N1726.d024369 i) hr


theorem d027449 (i : Fin 12) :
    ((∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, (p.1 - _root_.GD.N0106.N0428.N0770.N1726.d024361 i) ^ 2 * _root_.GD.N0106.N0428.N0770.N1726.d024364 i p ∂(volume.prod volume)) /
      (∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, _root_.GD.N0106.N0428.N0770.N1726.d024364 i p ∂(volume.prod volume))) / _root_.GD.N0106.N0428.N0770.N1726.d024363 i ^ 2 = 1 / 6 ∧
    ((∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, (p.2 - _root_.GD.N0106.N0428.N0770.N1726.d024362 i) ^ 2 * _root_.GD.N0106.N0428.N0770.N1726.d024364 i p ∂(volume.prod volume)) /
      (∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, _root_.GD.N0106.N0428.N0770.N1726.d024364 i p ∂(volume.prod volume))) / _root_.GD.N0106.N0428.N0770.N1726.d024363 i ^ 2 = 1 / 6 ∧
    ((∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, (p.1 - _root_.GD.N0106.N0428.N0770.N1726.d024361 i) ^ 2 * _root_.GD.N0106.N0428.N0770.N1726.d024364 i p ^ 2 ∂(volume.prod volume)) /
      (∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, _root_.GD.N0106.N0428.N0770.N1726.d024364 i p ^ 2 ∂(volume.prod volume))) / _root_.GD.N0106.N0428.N0770.N1726.d024363 i ^ 2 = 1 / 10 ∧
    ((∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, (p.2 - _root_.GD.N0106.N0428.N0770.N1726.d024362 i) ^ 2 * _root_.GD.N0106.N0428.N0770.N1726.d024364 i p ^ 2 ∂(volume.prod volume)) /
      (∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, _root_.GD.N0106.N0428.N0770.N1726.d024364 i p ^ 2 ∂(volume.prod volume))) / _root_.GD.N0106.N0428.N0770.N1726.d024363 i ^ 2 = 1 / 10 := by
  have hfirst (phi : (ℝ × ℝ) → ℝ) :
      (∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, phi p * _root_.GD.N0106.N0428.N0770.N1726.d024364 i p ∂(volume.prod volume)) =
        ∫ p, phi p * _root_.GD.N0106.N0428.N0770.N1726.d024364 i p ∂(volume.prod volume) := by
    simpa only [pow_one] using
      _root_.GD.N0106.N0428.N0770.N1731.d027445 i 1 (by norm_num) phi
  rw [hfirst, hfirst, _root_.GD.N0106.N0428.N0770.N1731.d027445 i 2 (by norm_num),
    _root_.GD.N0106.N0428.N0770.N1731.d027445 i 2 (by norm_num),
    _root_.GD.N0106.N0428.N0770.N1731.d027446, _root_.GD.N0106.N0428.N0770.N1731.d027447]
  have h := _root_.GD.N0106.N0428.N0770.N1731.d027444
    (_root_.GD.N0106.N0428.N0770.N1726.d024361 i) (_root_.GD.N0106.N0428.N0770.N1726.d024362 i) (_root_.GD.N0106.N0428.N0770.N1726.d024363 i) (_root_.GD.N0106.N0428.N0770.N1726.d024369 i)
  rw [_root_.GD.N0106.N0428.N0770.N1725.d024152 _ _ _ (_root_.GD.N0106.N0428.N0770.N1726.d024369 i),
    _root_.GD.N0106.N0428.N0770.N1725.d024153 _ _ _ (_root_.GD.N0106.N0428.N0770.N1726.d024369 i)] at h
  exact h

end
end GD.N0106.N0428.N0770.N1731

#print axioms _root_.GD.N0106.N0428.N0770.N1731.d027430
#print axioms _root_.GD.N0106.N0428.N0770.N1731.d027433
#print axioms _root_.GD.N0106.N0428.N0770.N1731.d027435
#print axioms _root_.GD.N0106.N0428.N0770.N1731.d027437
#print axioms _root_.GD.N0106.N0428.N0770.N1731.d027439
#print axioms _root_.GD.N0106.N0428.N0770.N1731.d027442
#print axioms _root_.GD.N0106.N0428.N0770.N1731.d027443
#print axioms _root_.GD.N0106.N0428.N0770.N1731.d027444

#print axioms _root_.GD.N0106.N0428.N0770.N1731.d027446
#print axioms _root_.GD.N0106.N0428.N0770.N1731.d027447
#print axioms _root_.GD.N0106.N0428.N0770.N1731.d027448
#print axioms _root_.GD.N0106.N0428.N0770.N1731.d027449
