import GD.Module1609
import GD.Module1566
import GD.Module1610
import GD.Module1611
import GD.Module1612






set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped BigOperators

namespace GD.N0106.N0428.N0770.N1732
noncomputable section
open _root_.GD.N0106.N0428.N0770.N1725
open _root_.GD.N0106.N0428.N0770.N1726
open _root_.GD.N0106.N0428.N0770.N1728
open _root_.GD.N0106.N0428.N0770.N1709
open _root_.GD.N0106.N0428.N0770.N1710
open _root_.GD.N0106.N0428.N0770.N1713

def d027528 (m q : ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024130 p + m * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1725.d024130 p ^ 2

def d027529 (m q : ℝ) : ℝ :=
  (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ * ∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1732.d027528 m q p ∂(volume.prod volume)

def d027530 : ℝ := ∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, 2 * |_root_.GD.N0106.N0428.N0770.N1728.d024390 i| * _root_.GD.N0106.N0428.N0770.N1710.d027504 i
def d027531 : ℝ := ∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 * _root_.GD.N0106.N0428.N0770.N1710.d027505 i

theorem d027532 (q : ℝ) : _root_.GD.N0106.N0428.N0770.N1732.d027529 1 q = _root_.GD.N0106.N0428.N0770.N1709.d027471 q := by
  simp only [_root_.GD.N0106.N0428.N0770.N1732.d027529, _root_.GD.N0106.N0428.N0770.N1709.d027471, _root_.GD.N0106.N0428.N0770.N1732.d027528, _root_.GD.N0106.N0428.N0770.N1709.d027470, one_mul]

theorem d027533 (m q : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1732.d027529 m q = (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ * ∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1732.d027528 m q p ∂(volume.prod volume) := by
  unfold _root_.GD.N0106.N0428.N0770.N1732.d027529
  congr 1
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  simp [_root_.GD.N0106.N0428.N0770.N1732.d027528, _root_.GD.N0106.N0428.N0770.N1709.d027480 hp]

theorem d027534 (m : ℝ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) :
    Integrable (fun p : ℝ × ℝ =>
      2 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i * ((p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p) +
      m * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ^ 2))
      (volume.prod volume) :=
  ((_root_.GD.N0106.N0428.N0770.N1709.d027491 hq (_root_.GD.N0106.N0428.N0770.N1710.d027506 i).1 (_root_.GD.N0106.N0428.N0770.N1710.d027506 i).2.1 (_root_.GD.N0106.N0428.N0770.N1710.d027506 i).2.2).const_mul _).add
    ((_root_.GD.N0106.N0428.N0770.N1709.d027492 hq (_root_.GD.N0106.N0428.N0770.N1710.d027506 i).1 (_root_.GD.N0106.N0428.N0770.N1710.d027506 i).2.1 (_root_.GD.N0106.N0428.N0770.N1710.d027506 i).2.2).const_mul _)

theorem d027535 (m q : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1732.d027528 m q p = ∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386,
      (2 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i * ((p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p) +
      m * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ^ 2)) := by
  rw [_root_.GD.N0106.N0428.N0770.N1732.d027528, _root_.GD.N0106.N0428.N0770.N1709.d027478, _root_.GD.N0106.N0428.N0770.N1709.d027473, mul_add, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem d027536 (m : ℝ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    Integrable (fun p => _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1732.d027528 m q p) (volume.prod volume) := by
  simp_rw [_root_.GD.N0106.N0428.N0770.N1732.d027535]
  exact integrable_finsetSum _ (fun i _ => _root_.GD.N0106.N0428.N0770.N1732.d027534 m hq i)

theorem d027537 (m : ℝ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0770.N1732.d027529 m q - _root_.GD.N0106.N0428.N0770.N1728.d024396 m q = ∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386,
      (2 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i * ((_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ *
        (∫ p, (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ∂(volume.prod volume)) -
        ((_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i)) +
      m * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 * ((_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ *
        (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ^ 2 ∂(volume.prod volume)) -
        (4 / 9) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i))) := by
  rw [_root_.GD.N0106.N0428.N0770.N1732.d027533]
  simp_rw [_root_.GD.N0106.N0428.N0770.N1732.d027535]
  rw [integral_finsetSum _ (fun i _ => _root_.GD.N0106.N0428.N0770.N1732.d027534 m hq i),
    _root_.GD.N0106.N0428.N0770.N1728.d024407, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_add
    ((_root_.GD.N0106.N0428.N0770.N1709.d027491 hq (_root_.GD.N0106.N0428.N0770.N1710.d027506 i).1 (_root_.GD.N0106.N0428.N0770.N1710.d027506 i).2.1 (_root_.GD.N0106.N0428.N0770.N1710.d027506 i).2.2).const_mul _)
    ((_root_.GD.N0106.N0428.N0770.N1709.d027492 hq (_root_.GD.N0106.N0428.N0770.N1710.d027506 i).1 (_root_.GD.N0106.N0428.N0770.N1710.d027506 i).2.1 (_root_.GD.N0106.N0428.N0770.N1710.d027506 i).2.2).const_mul _),
    integral_const_mul, integral_const_mul]
  ring

theorem d027538 (m : ℝ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) (1 / 2)) :
    |_root_.GD.N0106.N0428.N0770.N1732.d027529 m q - _root_.GD.N0106.N0428.N0770.N1728.d024396 m q| ≤ _root_.GD.N0106.N0428.N0770.N1732.d027530 + |m| * _root_.GD.N0106.N0428.N0770.N1732.d027531 := by
  rw [_root_.GD.N0106.N0428.N0770.N1732.d027537 m ⟨hq.1, hq.2.trans (by norm_num)⟩]
  unfold _root_.GD.N0106.N0428.N0770.N1732.d027530 _root_.GD.N0106.N0428.N0770.N1732.d027531
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  have h1 := (_root_.GD.N0106.N0428.N0770.N1710.d027515 hq i).1
  have h2 := (_root_.GD.N0106.N0428.N0770.N1710.d027515 hq i).2
  calc
    _ ≤ |2 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i * ((_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ *
          (∫ p, (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ∂(volume.prod volume)) -
          ((_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i))| +
        |m * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 * ((_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ *
          (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1709.d027472 i p ^ 2 ∂(volume.prod volume)) -
          (4 / 9) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i))| := abs_add_le _ _
    _ ≤ 2 * |_root_.GD.N0106.N0428.N0770.N1728.d024390 i| * _root_.GD.N0106.N0428.N0770.N1710.d027504 i +
        |m| * (_root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 * _root_.GD.N0106.N0428.N0770.N1710.d027505 i) := by
      simp only [abs_mul, abs_two, abs_of_pos _root_.GD.N0106.N0428.N0770.N1725.d024122, abs_pow, sq_abs]
      have hlinear := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * |_root_.GD.N0106.N0428.N0770.N1728.d024390 i| by positivity)
      have hquad := mul_le_mul_of_nonneg_left h2
        (mul_nonneg (mul_nonneg (abs_nonneg m) _root_.GD.N0106.N0428.N0770.N1725.d024122.le) (sq_nonneg (_root_.GD.N0106.N0428.N0770.N1728.d024390 i)))
      nlinarith

theorem d027539 (m : ℝ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0770.N1732.d027529 m (1 - q) = _root_.GD.N0106.N0428.N0770.N1732.d027529 m q := by
  have hq' : 1 - q ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hq.2], by linarith [hq.1]⟩
  rw [_root_.GD.N0106.N0428.N0770.N1732.d027533, _root_.GD.N0106.N0428.N0770.N1732.d027533]
  congr 1
  rw [integral_prod _ (_root_.GD.N0106.N0428.N0770.N1732.d027536 m hq'), integral_prod _ (_root_.GD.N0106.N0428.N0770.N1732.d027536 m hq)]
  calc
    _ = ∫ e, ∫ F, _root_.GD.N0106.N0428.N0770.N1725.d024170 (1 - q) (1 - e, F) * _root_.GD.N0106.N0428.N0770.N1732.d027528 m (1 - q) (1 - e, F) :=
      (integral_sub_left_eq_self
        (fun e => ∫ F, _root_.GD.N0106.N0428.N0770.N1725.d024170 (1 - q) (e, F) * _root_.GD.N0106.N0428.N0770.N1732.d027528 m (1 - q) (e, F)) volume 1).symm
    _ = _ := by
      congr 1
      funext e
      congr 1
      funext F
      rw [_root_.GD.N0106.N0428.N0770.N1713.d027521]
      unfold _root_.GD.N0106.N0428.N0770.N1732.d027528
      rw [_root_.GD.N0106.N0428.N0770.N1725.d024146 (e,F)]
      ring

theorem d027540 (m q : ℝ) : _root_.GD.N0106.N0428.N0770.N1728.d024396 m (1 - q) = _root_.GD.N0106.N0428.N0770.N1728.d024396 m q := by
  rw [_root_.GD.N0106.N0428.N0770.N1728.d024399, _root_.GD.N0106.N0428.N0770.N1728.d024399]
  apply Finset.sum_congr rfl
  intro r _
  have h1 := _root_.GD.N0106.N0428.N0770.N1713.d027521 q (_root_.GD.N0106.N0428.N0770.N1725.d024127 r) (_root_.GD.N0106.N0428.N0770.N1725.d024128 r)
  have h2 : _root_.GD.N0106.N0428.N0770.N1725.d024170 (1 - q) (_root_.GD.N0106.N0428.N0770.N1725.d024127 r, _root_.GD.N0106.N0428.N0770.N1725.d024128 r) =
      _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 - _root_.GD.N0106.N0428.N0770.N1725.d024127 r, _root_.GD.N0106.N0428.N0770.N1725.d024128 r) := by
    simpa only [sub_sub_cancel] using _root_.GD.N0106.N0428.N0770.N1713.d027521 q (1 - _root_.GD.N0106.N0428.N0770.N1725.d024127 r) (_root_.GD.N0106.N0428.N0770.N1725.d024128 r)
  rw [h1,h2]
  ring

theorem d027541 (m : ℝ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    |_root_.GD.N0106.N0428.N0770.N1732.d027529 m q - _root_.GD.N0106.N0428.N0770.N1728.d024396 m q| ≤ _root_.GD.N0106.N0428.N0770.N1732.d027530 + |m| * _root_.GD.N0106.N0428.N0770.N1732.d027531 := by
  rcases le_or_gt q (1 / 2) with h | h
  · exact _root_.GD.N0106.N0428.N0770.N1732.d027538 m ⟨hq.1,h⟩
  · have hb := _root_.GD.N0106.N0428.N0770.N1732.d027538 m (q := 1 - q) ⟨by linarith [hq.2],by linarith⟩
    rwa [_root_.GD.N0106.N0428.N0770.N1732.d027539 m hq,_root_.GD.N0106.N0428.N0770.N1732.d027540] at hb

theorem d027542 : 0 ≤ _root_.GD.N0106.N0428.N0770.N1732.d027531 := by
  unfold _root_.GD.N0106.N0428.N0770.N1732.d027531
  apply Finset.sum_nonneg
  intro i _
  have hi : 0 ≤ _root_.GD.N0106.N0428.N0770.N1710.d027505 i := (abs_nonneg _).trans (_root_.GD.N0106.N0428.N0770.N1710.d027515 (q := 0) (by constructor <;> norm_num) i).2
  exact mul_nonneg (mul_nonneg _root_.GD.N0106.N0428.N0770.N1725.d024122.le (sq_nonneg _)) hi

theorem d027543 : _root_.GD.N0106.N0428.N0770.N1732.d027530 + 3 * _root_.GD.N0106.N0428.N0770.N1732.d027531 < 718 / 1000000 := by
  have h := _root_.GD.N0106.N0428.N0770.N1710.d027517
  unfold _root_.GD.N0106.N0428.N0770.N1732.d027530 _root_.GD.N0106.N0428.N0770.N1732.d027531
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  convert h using 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem d027544 {m q : ℝ} (hm : |m| ≤ 3) (hq : q ∈ Icc (0 : ℝ) 1) :
    |_root_.GD.N0106.N0428.N0770.N1732.d027529 m q - _root_.GD.N0106.N0428.N0770.N1728.d024396 m q| < 718 / 1000000 :=
  (_root_.GD.N0106.N0428.N0770.N1732.d027541 m hq).trans_lt ((add_le_add le_rfl (mul_le_mul_of_nonneg_right hm _root_.GD.N0106.N0428.N0770.N1732.d027542)).trans_lt _root_.GD.N0106.N0428.N0770.N1732.d027543)

theorem d027545 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    |_root_.GD.N0106.N0428.N0770.N1732.d027529 3 q - _root_.GD.N0106.N0428.N0770.N1728.d024398 q| < 718 / 1000000 := _root_.GD.N0106.N0428.N0770.N1732.d027544 (by norm_num) hq

end
end GD.N0106.N0428.N0770.N1732

#print axioms _root_.GD.N0106.N0428.N0770.N1732.d027541
#print axioms _root_.GD.N0106.N0428.N0770.N1732.d027544
#print axioms _root_.GD.N0106.N0428.N0770.N1732.d027545
