import GD.Module1609
import GD.Module1566
import GD.Module1610
import GD.Module1611
import GD.Module1613
import GD.Module1606
import GD.Module1581
import GD.Module1582
import GD.Module1583
import GD.Module1584
import GD.Module1585
import GD.Module1586
import GD.Module1587
import GD.Module1588
import GD.Module1589
import GD.Module1590
import GD.Module1591
import GD.Module1592
import GD.Module1593
import GD.Module1594
import GD.Module1595
import GD.Module1596
import GD.Module1597
import GD.Module1598
import GD.Module1599
import GD.Module1600
import GD.Module1601
import GD.Module1602
import GD.Module1603
import GD.Module1627
import GD.Module1612
import GD.Module1604
import GD.Module1625
import GD.Module1571


































set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set MeasureTheory

namespace GD.N0106.N0428.N0770.N1712
noncomputable section

open _root_.GD.N0137 _root_.GD.N0107 _root_.GD.N0141
open _root_.GD.N0232.N0720.N1207
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0106.N0428.N0770.N1725
open _root_.GD.N0106.N0428.N0770.N1724
open _root_.GD.N0106.N0428.N0770.N1722
open _root_.GD.N0106.N0428.N0770.N1726
open _root_.GD.N0106.N0428.N0770.N1728
open _root_.GD.N0106.N0428.N0770.N1709
open _root_.GD.N0106.N0428.N0770.N1713
open _root_.GD.N0106.N0428.N0770.N1706
open _root_.GD.N0106.N0428.N0770.N1742 (d027779 d027780 d027781 d027782)




theorem d027818 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : _root_.GD.N0106.N0428.N0770.N1728.d024397 q < -47 / 200 := by
  rcases le_or_gt q (1 / 2) with h | h
  · exact _root_.GD.N0106.N0428.N0770.N1706.d027364 q ⟨hq.1, h⟩
  · have h' := _root_.GD.N0106.N0428.N0770.N1706.d027364 (1 - q) ⟨by linarith [hq.2], by linarith⟩
    rwa [_root_.GD.N0106.N0428.N0770.N1713.d027525] at h'


theorem d027819 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : _root_.GD.N0106.N0428.N0770.N1709.d027471 q < -(117141/500000) := by
  have h := _root_.GD.N0106.N0428.N0770.N1732.d027544 (m := 1) (by norm_num) hq
  rw [_root_.GD.N0106.N0428.N0770.N1732.d027532] at h
  have hS := _root_.GD.N0106.N0428.N0770.N1712.d027818 hq
  have hU := (abs_lt.mp h).2
  change _root_.GD.N0106.N0428.N0770.N1709.d027471 q - _root_.GD.N0106.N0428.N0770.N1728.d024397 q < 718/1000000 at hU
  linarith


theorem d027820 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : _root_.GD.N0106.N0428.N0770.N1709.d027471 q < -117 / 500 :=
  _root_.GD.N0106.N0428.N0770.N1713.d027527 hq (_root_.GD.N0106.N0428.N0770.N1712.d027818 hq)








theorem d027821 (s : ℝ) (x : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 _root_.GD.N0106.N0428.N0770.N1725.d024117 0 x - s) ^ 2 - _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 0 0 x - s) ^ 2
      = _root_.GD.N0106.N0428.N0770.N1725.d024117 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 s x * _root_.GD.N0106.N0428.N0770.N1709.d027470 s x) := by
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024154 _root_.GD.N0106.N0428.N0770.N1709.d027470
  ring



theorem d027822 (s : ℝ) :
    ∫ x in _root_.GD.N0232.N0720.N1436.d013218, _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * _root_.GD.N0106.N0428.N0770.N1709.d027470 s x = _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * _root_.GD.N0106.N0428.N0770.N1709.d027471 s := by
  have heta : _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 ≠ 0 := pow_ne_zero 2 _root_.GD.N0106.N0428.N0770.N1725.d024120.ne'
  have hT : _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * _root_.GD.N0106.N0428.N0770.N1709.d027471 s = ∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, _root_.GD.N0106.N0428.N0770.N1725.d024170 s p * _root_.GD.N0106.N0428.N0770.N1709.d027470 s p ∂(volume.prod volume) := by
    unfold _root_.GD.N0106.N0428.N0770.N1709.d027471
    rw [← mul_assoc, mul_inv_cancel₀ heta, one_mul]
  calc ∫ x in _root_.GD.N0232.N0720.N1436.d013218, _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * _root_.GD.N0106.N0428.N0770.N1709.d027470 s x
      = ∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, _root_.GD.N0106.N0428.N0770.N1725.d024170 s p * _root_.GD.N0106.N0428.N0770.N1709.d027470 s p ∂(volume.prod volume) := rfl
    _ = _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * _root_.GD.N0106.N0428.N0770.N1709.d027471 s := hT.symm



theorem d027823 (mu sigma zeta : ℝ) (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta _root_.GD.N0106.N0428.N0770.N1725.d024117 0 - _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta 0 0 =
      _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (_root_.GD.N0106.N0428.N0770.N1725.d024117 * (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * _root_.GD.N0106.N0428.N0770.N1709.d027471 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta))) := by
  have h1 := _root_.GD.N0106.N0428.N0770.N1742.d027782 mu sigma zeta _root_.GD.N0106.N0428.N0770.N1725.d024117 0 hsigma hzeta
  have h0 := _root_.GD.N0106.N0428.N0770.N1742.d027782 mu sigma zeta 0 0 hsigma hzeta
  have hdiff : (∫ x in _root_.GD.N0232.N0720.N1436.d013218,
        _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 _root_.GD.N0106.N0428.N0770.N1725.d024117 0 x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2)
      - (∫ x in _root_.GD.N0232.N0720.N1436.d013218,
        _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 0 0 x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2)
      = _root_.GD.N0106.N0428.N0770.N1725.d024117 * (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * _root_.GD.N0106.N0428.N0770.N1709.d027471 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta)) := by
    rw [← integral_sub h1 h0]
    have hpt : (∫ x in _root_.GD.N0232.N0720.N1436.d013218,
        (_root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 _root_.GD.N0106.N0428.N0770.N1725.d024117 0 x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2
          - _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 0 0 x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2))
        = ∫ x in _root_.GD.N0232.N0720.N1436.d013218,
            _root_.GD.N0106.N0428.N0770.N1725.d024117 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * _root_.GD.N0106.N0428.N0770.N1709.d027470 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => _root_.GD.N0106.N0428.N0770.N1712.d027821 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x)
    rw [hpt, integral_const_mul, _root_.GD.N0106.N0428.N0770.N1712.d027822]
  rw [_root_.GD.N0106.N0428.N0770.N1742.d027781 mu sigma zeta _root_.GD.N0106.N0428.N0770.N1725.d024117 0 hsigma hzeta,
    _root_.GD.N0106.N0428.N0770.N1742.d027781 mu sigma zeta 0 0 hsigma hzeta]
  linear_combination _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * hdiff





theorem d027824 (sigma zeta : ℝ) (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (_root_.GD.N0106.N0428.N0770.N1725.d024117 * (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * (117 / 500))) =
      351 * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * sigma ^ 4 * zeta ^ 4 /
        (500000 * Real.pi * (sigma ^ 2 + zeta ^ 2) ^ 3) := by
  have hS : sigma ^ 2 + zeta ^ 2 ≠ 0 := (add_pos (pow_pos hsigma 2) (pow_pos hzeta 2)).ne'
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  unfold _root_.GD.N0106.N0428.N0770.N1722.d024329
  rw [_root_.GD.N0106.N0428.N0770.N1724.d024305]
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024117
  field_simp
  ring

theorem d027825 (sigma zeta : ℝ) (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    0 < 351 * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * sigma ^ 4 * zeta ^ 4 /
      (500000 * Real.pi * (sigma ^ 2 + zeta ^ 2) ^ 3) := by
  apply div_pos
  · exact mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos _root_.GD.N0106.N0428.N0770.N1725.d024120 2)) (pow_pos hsigma 4))
      (pow_pos hzeta 4)
  · exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (pow_pos (add_pos (pow_pos hsigma 2) (pow_pos hzeta 2)) 3)



theorem d027826 (mu sigma zeta : ℝ) (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta _root_.GD.N0106.N0428.N0770.N1725.d024117 0 - _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta 0 0 <
      -(351 * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * sigma ^ 4 * zeta ^ 4 /
        (500000 * Real.pi * (sigma ^ 2 + zeta ^ 2) ^ 3)) := by
  have hs0 : 0 < _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta :=
    _root_.GD.N0107.d009050 (by norm_num) (by norm_num) hsigma hzeta
  have hs1 : _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta < 1 :=
    _root_.GD.N0107.d009051 (by norm_num) (by norm_num) hsigma hzeta
  have hT := _root_.GD.N0106.N0428.N0770.N1712.d027820 (q := _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ⟨hs0.le, hs1.le⟩
  have hK := _root_.GD.N0106.N0428.N0770.N1722.d024331 sigma zeta hsigma hzeta
  have hpos : 0 < _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (_root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2) :=
    mul_pos hK (mul_pos _root_.GD.N0106.N0428.N0770.N1725.d024122 (pow_pos _root_.GD.N0106.N0428.N0770.N1725.d024120 2))
  rw [_root_.GD.N0106.N0428.N0770.N1712.d027823 mu sigma zeta hsigma hzeta, ← _root_.GD.N0106.N0428.N0770.N1712.d027824 sigma zeta hsigma hzeta]
  calc _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (_root_.GD.N0106.N0428.N0770.N1725.d024117 * (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * _root_.GD.N0106.N0428.N0770.N1709.d027471 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta)))
      = _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (_root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2) * _root_.GD.N0106.N0428.N0770.N1709.d027471 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) := by ring
    _ < _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (_root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2) * (-117 / 500) :=
        mul_lt_mul_of_pos_left hT hpos
    _ = -(_root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (_root_.GD.N0106.N0428.N0770.N1725.d024117 * (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * (117 / 500)))) := by ring


theorem d027827 (mu sigma zeta : ℝ)
    (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta _root_.GD.N0106.N0428.N0770.N1725.d024117 0 - _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta 0 0 <
      -(351423 * _root_.GD.N0106.N0428.N0770.N1725.d024116^2 * sigma^4 * zeta^4 /
        (500000000 * Real.pi * (sigma^2+zeta^2)^3)) := by
  have hq : _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta ∈ Icc (0 : ℝ) 1 :=
    ⟨(_root_.GD.N0107.d009050 (by norm_num) (by norm_num) hsigma hzeta).le,
     (_root_.GD.N0107.d009051 (by norm_num) (by norm_num) hsigma hzeta).le⟩
  have hp : 0 < _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (_root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1725.d024116^2) :=
    mul_pos (_root_.GD.N0106.N0428.N0770.N1722.d024331 sigma zeta hsigma hzeta)
      (mul_pos _root_.GD.N0106.N0428.N0770.N1725.d024122 (pow_pos _root_.GD.N0106.N0428.N0770.N1725.d024120 2))
  have hc : _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (_root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1725.d024116^2) * (117141/500000) =
      351423 * _root_.GD.N0106.N0428.N0770.N1725.d024116^2 * sigma^4 * zeta^4 /
        (500000000 * Real.pi * (sigma^2+zeta^2)^3) := by
    have hS : sigma^2+zeta^2 ≠ 0 := (add_pos (pow_pos hsigma 2) (pow_pos hzeta 2)).ne'
    have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
    unfold _root_.GD.N0106.N0428.N0770.N1722.d024329
    rw [_root_.GD.N0106.N0428.N0770.N1724.d024305]
    unfold _root_.GD.N0106.N0428.N0770.N1725.d024117
    field_simp
    ring
  have h := mul_lt_mul_of_pos_left (_root_.GD.N0106.N0428.N0770.N1712.d027819 hq) hp
  rw [mul_neg, hc] at h
  rw [_root_.GD.N0106.N0428.N0770.N1712.d027823 mu sigma zeta hsigma hzeta]
  nlinarith





theorem d027828 (mu sigma zeta : ℝ) (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024158 (_root_.GD.N0107.d009084 w.1) (_root_.GD.N0107.d009084 w.2)
          (_root_.GD.N0107.d009085 w.1) (_root_.GD.N0107.d009085 w.2) - mu) -
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024157 (_root_.GD.N0107.d009084 w.1) (_root_.GD.N0107.d009084 w.2)
          (_root_.GD.N0107.d009085 w.1) (_root_.GD.N0107.d009085 w.2) - mu) <
      -(351 * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * sigma ^ 4 * zeta ^ 4 /
        (500000 * Real.pi * (sigma ^ 2 + zeta ^ 2) ^ 3)) :=
  _root_.GD.N0106.N0428.N0770.N1712.d027826 mu sigma zeta hsigma hzeta



theorem d027829 (mu sigma zeta : ℝ) (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024158 (_root_.GD.N0107.d009084 w.1) (_root_.GD.N0107.d009084 w.2)
          (_root_.GD.N0107.d009085 w.1) (_root_.GD.N0107.d009085 w.2) - mu) <
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024157 (_root_.GD.N0107.d009084 w.1) (_root_.GD.N0107.d009084 w.2)
          (_root_.GD.N0107.d009085 w.1) (_root_.GD.N0107.d009085 w.2) - mu) := by
  have h := _root_.GD.N0106.N0428.N0770.N1712.d027828 mu sigma zeta hsigma hzeta
  have hm := _root_.GD.N0106.N0428.N0770.N1712.d027825 sigma zeta hsigma hzeta
  linarith [h, hm]




theorem d027830 (mu sigma zeta alpha beta : ℝ)
    (hs : 0 < sigma) (hz : 0 < zeta) (hab : alpha < beta)
    (hsum : alpha + beta ≤ _root_.GD.N0106.N0428.N0770.N1725.d024117) :
    _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta beta 0 < _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta alpha 0 := by
  have hq : _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta ∈ Icc (0 : ℝ) 1 :=
    ⟨(_root_.GD.N0107.d009050 (by norm_num) (by norm_num) hs hz).le,
     (_root_.GD.N0107.d009051 (by norm_num) (by norm_num) hs hz).le⟩
  have hm : (alpha+beta)/_root_.GD.N0106.N0428.N0770.N1725.d024117 ≤ 1 :=
    (div_le_iff₀ _root_.GD.N0106.N0428.N0770.N1725.d024122).mpr (by simpa using hsum)
  have hT := _root_.GD.N0106.N0428.N0770.N1714.d027806 hq hm
  rw [_root_.GD.N0106.N0428.N0770.N1732.d027532] at hT
  have hneg : _root_.GD.N0106.N0428.N0770.N1732.d027529 ((alpha+beta)/_root_.GD.N0106.N0428.N0770.N1725.d024117) (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) < 0 :=
    (hT.trans_lt (_root_.GD.N0106.N0428.N0770.N1712.d027820 hq)).trans (by norm_num)
  have hd := _root_.GD.N0106.N0428.N0770.N1714.d027809 mu sigma zeta alpha beta hs hz
  have hp : 0 < _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * ((beta-alpha)*_root_.GD.N0106.N0428.N0770.N1725.d024116^2) :=
    mul_pos (_root_.GD.N0106.N0428.N0770.N1722.d024331 sigma zeta hs hz)
      (mul_pos (sub_pos.mpr hab) (pow_pos _root_.GD.N0106.N0428.N0770.N1725.d024120 2))
  have hn := mul_neg_of_pos_of_neg hp hneg
  change _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta beta 0 - _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta alpha 0 = _ at hd
  rw [← mul_assoc] at hd
  linarith

end
end GD.N0106.N0428.N0770.N1712

#print axioms _root_.GD.N0106.N0428.N0770.N1712.d027818
#print axioms _root_.GD.N0106.N0428.N0770.N1712.d027820
#print axioms _root_.GD.N0106.N0428.N0770.N1712.d027823
#print axioms _root_.GD.N0106.N0428.N0770.N1712.d027824
#print axioms _root_.GD.N0106.N0428.N0770.N1712.d027828
#print axioms _root_.GD.N0106.N0428.N0770.N1712.d027829

#print axioms _root_.GD.N0106.N0428.N0770.N1712.d027830

#print axioms _root_.GD.N0106.N0428.N0770.N1712.d027827
