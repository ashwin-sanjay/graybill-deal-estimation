import GD.Module1617
import GD.Module1605
import GD.Module1625










set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set MeasureTheory

namespace GD.N0106.N0428.N0770.N1707
noncomputable section
open _root_.GD.N0106.N0428.N0770.N1725 _root_.GD.N0106.N0428.N0770.N1724 _root_.GD.N0106.N0428.N0770.N1722
open _root_.GD.N0106.N0428.N0770.N1728 _root_.GD.N0106.N0428.N0770.N1730
open _root_.GD.N0106.N0428.N0770.N1742
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1207

theorem d027799 (a b s : ℝ) (x : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 (b * _root_.GD.N0106.N0428.N0770.N1725.d024117) 0 x - s) ^ 2 -
      _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 (a * _root_.GD.N0106.N0428.N0770.N1725.d024117) 0 x - s) ^ 2 =
      ((b - a) * _root_.GD.N0106.N0428.N0770.N1725.d024117) * (_root_.GD.N0106.N0428.N0770.N1725.d024170 s x * _root_.GD.N0106.N0428.N0770.N1730.d027616 (a + b) s x) := by
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024154 _root_.GD.N0106.N0428.N0770.N1730.d027616
  ring

theorem d027800 (m s : ℝ) :
    (∫ x in _root_.GD.N0232.N0720.N1436.d013218, _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * _root_.GD.N0106.N0428.N0770.N1730.d027616 m s x) =
      _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * _root_.GD.N0106.N0428.N0770.N1730.d027617 m s := by
  have heta : _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 ≠ 0 := pow_ne_zero 2 _root_.GD.N0106.N0428.N0770.N1725.d024120.ne'
  change (∫ x in _root_.GD.N0232.N0720.N1436.d013218, _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * _root_.GD.N0106.N0428.N0770.N1730.d027616 m s x ∂(volume.prod volume)) = _
  unfold _root_.GD.N0106.N0428.N0770.N1730.d027617
  rw [show _root_.GD.N0232.N0720.N1436.d013218 =
    _root_.GD.N0106.N0428.N0770.N1726.d024366 by rfl]
  rw [← mul_assoc, mul_inv_cancel₀ heta, one_mul]


theorem d027801 (mu sigma zeta a b : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta (b * _root_.GD.N0106.N0428.N0770.N1725.d024117) 0 -
      _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta (a * _root_.GD.N0106.N0428.N0770.N1725.d024117) 0 =
      _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta *
        (((b - a) * _root_.GD.N0106.N0428.N0770.N1725.d024117) * (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * _root_.GD.N0106.N0428.N0770.N1730.d027617 (a + b) (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta))) := by
  have hb := _root_.GD.N0106.N0428.N0770.N1742.d027782 mu sigma zeta (b * _root_.GD.N0106.N0428.N0770.N1725.d024117) 0 hsigma hzeta
  have ha := _root_.GD.N0106.N0428.N0770.N1742.d027782 mu sigma zeta (a * _root_.GD.N0106.N0428.N0770.N1725.d024117) 0 hsigma hzeta
  have hd : (∫ x in _root_.GD.N0232.N0720.N1436.d013218,
        _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 (b * _root_.GD.N0106.N0428.N0770.N1725.d024117) 0 x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2) -
      (∫ x in _root_.GD.N0232.N0720.N1436.d013218,
        _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 (a * _root_.GD.N0106.N0428.N0770.N1725.d024117) 0 x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2) =
      ((b - a) * _root_.GD.N0106.N0428.N0770.N1725.d024117) * (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * _root_.GD.N0106.N0428.N0770.N1730.d027617 (a + b) (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta)) := by
    rw [← integral_sub hb ha]
    calc
      (∫ x in _root_.GD.N0232.N0720.N1436.d013218,
        _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 (b * _root_.GD.N0106.N0428.N0770.N1725.d024117) 0 x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2 -
          _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 (a * _root_.GD.N0106.N0428.N0770.N1725.d024117) 0 x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2) =
        ∫ x in _root_.GD.N0232.N0720.N1436.d013218,
          ((b - a) * _root_.GD.N0106.N0428.N0770.N1725.d024117) * (_root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x *
            _root_.GD.N0106.N0428.N0770.N1730.d027616 (a + b) (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x) :=
        integral_congr_ae (Filter.Eventually.of_forall (_root_.GD.N0106.N0428.N0770.N1707.d027799 a b (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta)))
      _ = ((b - a) * _root_.GD.N0106.N0428.N0770.N1725.d024117) *
          (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * _root_.GD.N0106.N0428.N0770.N1730.d027617 (a + b) (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta)) := by
        rw [integral_const_mul, _root_.GD.N0106.N0428.N0770.N1707.d027800]
  rw [_root_.GD.N0106.N0428.N0770.N1742.d027781 mu sigma zeta (b * _root_.GD.N0106.N0428.N0770.N1725.d024117) 0 hsigma hzeta,
    _root_.GD.N0106.N0428.N0770.N1742.d027781 mu sigma zeta (a * _root_.GD.N0106.N0428.N0770.N1725.d024117) 0 hsigma hzeta]
  linear_combination _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * hd

theorem d027802 : (739 / 1000 : ℝ) < _root_.GD.N0106.N0428.N0770.N1730.d027617 3 (1 / 362) := by
  exact _root_.GD.N0106.N0428.N0770.N1708.d027384
    (_root_.GD.N0106.N0428.N0770.N1730.d027623 (by constructor <;> norm_num)).le

theorem d027803 {r : ℝ} (hr : 0 < r) : _root_.GD.N0106.N0428.N0770.N1724.d024296 (19 * r) r = 1 / 362 := by
  rw [_root_.GD.N0106.N0428.N0770.N1724.d024305]
  field_simp [hr.ne']
  <;> ring


theorem d027804 (mu : ℝ) {r : ℝ} (hr : 0 < r) :
    _root_.GD.N0106.N0428.N0770.N1742.d027779 mu (19 * r) r _root_.GD.N0106.N0428.N0770.N1725.d024117 0 <
      _root_.GD.N0106.N0428.N0770.N1742.d027779 mu (19 * r) r (2 * _root_.GD.N0106.N0428.N0770.N1725.d024117) 0 := by
  have hs : 0 < 19 * r := mul_pos (by norm_num) hr
  have hd := _root_.GD.N0106.N0428.N0770.N1707.d027801 mu (19 * r) r 1 2 hs hr
  have ht : 0 < _root_.GD.N0106.N0428.N0770.N1730.d027617 3 (1 / 362) := lt_trans (by norm_num) _root_.GD.N0106.N0428.N0770.N1707.d027802
  have hp : 0 < _root_.GD.N0106.N0428.N0770.N1722.d024329 (19 * r) r *
      (_root_.GD.N0106.N0428.N0770.N1725.d024117 * (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * _root_.GD.N0106.N0428.N0770.N1730.d027617 3 (1 / 362))) :=
    mul_pos (_root_.GD.N0106.N0428.N0770.N1722.d024331 _ _ hs hr)
      (mul_pos _root_.GD.N0106.N0428.N0770.N1725.d024122 (mul_pos (pow_pos _root_.GD.N0106.N0428.N0770.N1725.d024120 2) ht))
  norm_num only [one_mul, show (2 : ℝ) - 1 = 1 by norm_num,
    show (1 : ℝ) + 2 = 3 by norm_num, _root_.GD.N0106.N0428.N0770.N1707.d027803 hr] at hd
  linarith

end
end GD.N0106.N0428.N0770.N1707

#print axioms _root_.GD.N0106.N0428.N0770.N1707.d027801
#print axioms _root_.GD.N0106.N0428.N0770.N1707.d027802
#print axioms _root_.GD.N0106.N0428.N0770.N1707.d027804
