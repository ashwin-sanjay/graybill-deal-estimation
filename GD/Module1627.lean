import GD.Module1609
import GD.Module1566
import GD.Module1610
import GD.Module1611
import GD.Module1612
import GD.Module1613
import GD.Module1606
import GD.Module1625





set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set MeasureTheory
open _root_.GD.N0232.N0720.N1436
namespace GD.N0106.N0428.N0770.N1714
noncomputable section
open _root_.GD.N0106.N0428.N0770.N1725
open _root_.GD.N0106.N0428.N0770.N1726
open _root_.GD.N0106.N0428.N0770.N1724
open _root_.GD.N0106.N0428.N0770.N1722
open _root_.GD.N0106.N0428.N0770.N1732
open _root_.GD.N0106.N0428.N0770.N1716
open _root_.GD.N0106.N0428.N0770.N1742

theorem d027805 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (p : ℝ × ℝ) :
    0 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024130 p ^ 2 := by
  by_cases hp : p ∈ _root_.GD.N0106.N0428.N0770.N1726.d024366
  · have hw := _root_.GD.N0106.N0428.N0770.N1741.d027699 hq hp.1 hp.2
    exact mul_nonneg hw (sq_nonneg _)
  · rw [_root_.GD.N0106.N0428.N0770.N1709.d027480 hp]
    simp

theorem d027806 {q m n : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (hmn : m ≤ n) :
    _root_.GD.N0106.N0428.N0770.N1732.d027529 m q ≤ _root_.GD.N0106.N0428.N0770.N1732.d027529 n q := by
  rw [_root_.GD.N0106.N0428.N0770.N1732.d027533,_root_.GD.N0106.N0428.N0770.N1732.d027533]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono (_root_.GD.N0106.N0428.N0770.N1732.d027536 m hq) (_root_.GD.N0106.N0428.N0770.N1732.d027536 n hq)
  intro p
  have h := mul_nonneg (mul_nonneg (sub_nonneg.mpr hmn) _root_.GD.N0106.N0428.N0770.N1725.d024122.le) (_root_.GD.N0106.N0428.N0770.N1714.d027805 hq p)
  unfold _root_.GD.N0106.N0428.N0770.N1732.d027528
  nlinarith

theorem d027807 (alpha beta q : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * (_root_.GD.N0106.N0428.N0770.N1725.d024154 beta 0 p - q)^2 - _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * (_root_.GD.N0106.N0428.N0770.N1725.d024154 alpha 0 p - q)^2 =
      (beta - alpha) * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1732.d027528 ((alpha + beta) / _root_.GD.N0106.N0428.N0770.N1725.d024117) q p) := by
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024154 _root_.GD.N0106.N0428.N0770.N1732.d027528 _root_.GD.N0106.N0428.N0770.N1725.d024117
  ring

theorem d027808 (m q : ℝ) :
    (∫ p in _root_.GD.N0232.N0720.N1436.d013218, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1732.d027528 m q p) = _root_.GD.N0106.N0428.N0770.N1725.d024116^2 * _root_.GD.N0106.N0428.N0770.N1732.d027529 m q := by
  change (∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1732.d027528 m q p ∂(volume.prod volume)) = _
  unfold _root_.GD.N0106.N0428.N0770.N1732.d027529
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 _root_.GD.N0106.N0428.N0770.N1725.d024120.ne'), one_mul]


theorem d027809 (mu sigma zeta alpha beta : ℝ) (hs : 0 < sigma) (hz : 0 < zeta) :
    _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta beta 0 - _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta alpha 0 =
      _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * ((beta-alpha) * _root_.GD.N0106.N0428.N0770.N1725.d024116^2 *
        _root_.GD.N0106.N0428.N0770.N1732.d027529 ((alpha+beta)/_root_.GD.N0106.N0428.N0770.N1725.d024117) (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta)) := by
  have h1 := _root_.GD.N0106.N0428.N0770.N1742.d027782 mu sigma zeta beta 0 hs hz
  have h0 := _root_.GD.N0106.N0428.N0770.N1742.d027782 mu sigma zeta alpha 0 hs hz
  rw [_root_.GD.N0106.N0428.N0770.N1742.d027781 mu sigma zeta beta 0 hs hz,
    _root_.GD.N0106.N0428.N0770.N1742.d027781 mu sigma zeta alpha 0 hs hz]
  rw [add_sub_add_left_eq_sub, ← mul_sub, ← integral_sub h1 h0]
  have hfun : (fun p : ℝ × ℝ =>
      _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) p * (_root_.GD.N0106.N0428.N0770.N1725.d024154 beta 0 p - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta)^2 -
      _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) p * (_root_.GD.N0106.N0428.N0770.N1725.d024154 alpha 0 p - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta)^2) =
      (fun p => (beta-alpha) * (_root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) p *
        _root_.GD.N0106.N0428.N0770.N1732.d027528 ((alpha+beta)/_root_.GD.N0106.N0428.N0770.N1725.d024117) (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) p)) := by
    funext p
    exact _root_.GD.N0106.N0428.N0770.N1714.d027807 alpha beta (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) p
  rw [hfun, integral_const_mul, _root_.GD.N0106.N0428.N0770.N1714.d027808]
  ring


theorem d027810 : (369791 / 500000 : ℝ) < _root_.GD.N0106.N0428.N0770.N1732.d027529 3 (1 / 362) := by
  have hS := _root_.GD.N0106.N0428.N0770.N1716.d027401
  have hE := _root_.GD.N0106.N0428.N0770.N1732.d027545 (q := 1 / 362) (by constructor <;> norm_num)
  have hL := (abs_lt.mp hE).1
  linarith

theorem d027811 : (739 / 1000 : ℝ) < _root_.GD.N0106.N0428.N0770.N1732.d027529 3 (1 / 362) :=
  (by norm_num : (739 / 1000 : ℝ) < 369791 / 500000).trans _root_.GD.N0106.N0428.N0770.N1714.d027810

theorem d027812 : (93141 / 500000 : ℝ) < _root_.GD.N0106.N0428.N0770.N1732.d027529 2 (1 / 362) := by
  have hS := _root_.GD.N0106.N0428.N0770.N1716.d027404
  have hE := _root_.GD.N0106.N0428.N0770.N1732.d027544 (m := 2) (q := 1/362) (by norm_num) (by constructor <;> norm_num)
  have hL := (abs_lt.mp hE).1
  linarith


theorem d027813 {r : ℝ} (hr : 0 < r) : _root_.GD.N0106.N0428.N0770.N1724.d024296 (19*r) r = (1/362 : ℝ) := by
  rw [_root_.GD.N0106.N0428.N0770.N1724.d024305]
  field_simp [hr.ne'] <;> ring


theorem d027814 (mu : ℝ) {r : ℝ} (hr : 0 < r) :
    _root_.GD.N0106.N0428.N0770.N1742.d027779 mu (19*r) r _root_.GD.N0106.N0428.N0770.N1725.d024117 0 < _root_.GD.N0106.N0428.N0770.N1742.d027779 mu (19*r) r (2*_root_.GD.N0106.N0428.N0770.N1725.d024117) 0 := by
  have hs : 0 < 19*r := mul_pos (by norm_num) hr
  have hd := _root_.GD.N0106.N0428.N0770.N1714.d027809 mu (19*r) r _root_.GD.N0106.N0428.N0770.N1725.d024117 (2*_root_.GD.N0106.N0428.N0770.N1725.d024117) hs hr
  have hm : (_root_.GD.N0106.N0428.N0770.N1725.d024117+2*_root_.GD.N0106.N0428.N0770.N1725.d024117)/_root_.GD.N0106.N0428.N0770.N1725.d024117 = (3 : ℝ) := by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024117]
  rw [_root_.GD.N0106.N0428.N0770.N1714.d027813 hr, hm] at hd
  have hpos : 0 < _root_.GD.N0106.N0428.N0770.N1722.d024329 (19*r) r * ((2*_root_.GD.N0106.N0428.N0770.N1725.d024117-_root_.GD.N0106.N0428.N0770.N1725.d024117)*_root_.GD.N0106.N0428.N0770.N1725.d024116^2*_root_.GD.N0106.N0428.N0770.N1732.d027529 3 (1/362)) := by
    apply mul_pos (_root_.GD.N0106.N0428.N0770.N1722.d024331 (19*r) r hs hr)
    apply mul_pos
    · exact mul_pos (by linarith [_root_.GD.N0106.N0428.N0770.N1725.d024122]) (pow_pos _root_.GD.N0106.N0428.N0770.N1725.d024120 2)
    · exact (by norm_num : (0 : ℝ) < 739/1000).trans _root_.GD.N0106.N0428.N0770.N1714.d027811
  linarith

theorem d027815 (mu : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1742.d027779 mu 19 1 _root_.GD.N0106.N0428.N0770.N1725.d024117 0 < _root_.GD.N0106.N0428.N0770.N1742.d027779 mu 19 1 (2*_root_.GD.N0106.N0428.N0770.N1725.d024117) 0 := by
  simpa only [mul_one] using _root_.GD.N0106.N0428.N0770.N1714.d027814 mu (r := 1) (by norm_num)



theorem d027816 (mu alpha beta : ℝ) {r : ℝ} (hr : 0 < r)
    (hab : alpha < beta) (hsum : 2*_root_.GD.N0106.N0428.N0770.N1725.d024117 ≤ alpha+beta) :
    _root_.GD.N0106.N0428.N0770.N1742.d027779 mu (19*r) r alpha 0 < _root_.GD.N0106.N0428.N0770.N1742.d027779 mu (19*r) r beta 0 := by
  have hs : 0 < 19*r := mul_pos (by norm_num) hr
  have hm : 2 ≤ (alpha+beta)/_root_.GD.N0106.N0428.N0770.N1725.d024117 := (le_div_iff₀ _root_.GD.N0106.N0428.N0770.N1725.d024122).mpr hsum
  have hT := _root_.GD.N0106.N0428.N0770.N1714.d027812.trans_le
    (_root_.GD.N0106.N0428.N0770.N1714.d027806 (q := 1/362) (by constructor <;> norm_num) hm)
  have hpos := mul_pos (_root_.GD.N0106.N0428.N0770.N1722.d024331 (19*r) r hs hr)
    (mul_pos (mul_pos (sub_pos.mpr hab) (pow_pos _root_.GD.N0106.N0428.N0770.N1725.d024120 2))
      ((by norm_num : (0 : ℝ) < 93141/500000).trans hT))
  have hd := _root_.GD.N0106.N0428.N0770.N1714.d027809 mu (19*r) r alpha beta hs hr
  rw [_root_.GD.N0106.N0428.N0770.N1714.d027813 hr] at hd
  linarith

theorem d027817 (mu alpha beta : ℝ)
    (hab : alpha < beta) (hsum : 2*_root_.GD.N0106.N0428.N0770.N1725.d024117 ≤ alpha+beta) :
    _root_.GD.N0106.N0428.N0770.N1742.d027779 mu 19 1 alpha 0 < _root_.GD.N0106.N0428.N0770.N1742.d027779 mu 19 1 beta 0 := by
  simpa only [mul_one] using _root_.GD.N0106.N0428.N0770.N1714.d027816 mu alpha beta (r := 1) (by norm_num) hab hsum

end
end GD.N0106.N0428.N0770.N1714

#print axioms _root_.GD.N0106.N0428.N0770.N1714.d027809
#print axioms _root_.GD.N0106.N0428.N0770.N1714.d027810
#print axioms _root_.GD.N0106.N0428.N0770.N1714.d027815
#print axioms _root_.GD.N0106.N0428.N0770.N1714.d027817
