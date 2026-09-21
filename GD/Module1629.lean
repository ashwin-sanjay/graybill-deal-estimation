import GD.Module1618
import GD.Module1580
import GD.Module1625
import GD.Module1571


































set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set MeasureTheory

namespace GD.N0106.N0428.N0770.N1717
noncomputable section

open _root_.GD.N0137 _root_.GD.N0107 _root_.GD.N0141
open _root_.GD.N0232.N0720.N1207
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0106.N0428.N0770.N1725
open _root_.GD.N0106.N0428.N0770.N1724
open _root_.GD.N0106.N0428.N0770.N1722
open _root_.GD.N0106.N0428.N0770.N1726
open _root_.GD.N0106.N0428.N0770.N1728
open _root_.GD.N0106.N0428.N0770.N1733
open _root_.GD.N0106.N0428.N0770.N1735
open _root_.GD.N0106.N0428.N0770.N1703
open _root_.GD.N0106.N0428.N0770.N1742 (d027779 d027780 d027781 d027782)




theorem d027831 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : _root_.GD.N0106.N0428.N0770.N1728.d024397 q < -47 / 200 := by
  rcases le_or_gt q (1 / 2) with h | h
  · exact _root_.GD.N0106.N0428.N0770.N1703.d026288 q ⟨hq.1, h⟩
  · have h' := _root_.GD.N0106.N0428.N0770.N1703.d026288 (1 - q) ⟨by linarith [hq.2], by linarith⟩
    rwa [_root_.GD.N0106.N0428.N0770.N1735.d027629] at h'


theorem d027832 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : _root_.GD.N0106.N0428.N0770.N1733.d027567 q < -117 / 500 :=
  _root_.GD.N0106.N0428.N0770.N1735.d027631 hq (_root_.GD.N0106.N0428.N0770.N1717.d027831 hq)








theorem d027833 (s : ℝ) (x : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 _root_.GD.N0106.N0428.N0770.N1725.d024117 0 x - s) ^ 2 - _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 0 0 x - s) ^ 2
      = _root_.GD.N0106.N0428.N0770.N1725.d024117 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 s x * _root_.GD.N0106.N0428.N0770.N1733.d027566 s x) := by
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024154 _root_.GD.N0106.N0428.N0770.N1733.d027566
  ring



theorem d027834 (s : ℝ) :
    ∫ x in _root_.GD.N0232.N0720.N1436.d013218, _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * _root_.GD.N0106.N0428.N0770.N1733.d027566 s x = _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * _root_.GD.N0106.N0428.N0770.N1733.d027567 s := by
  have heta : _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 ≠ 0 := pow_ne_zero 2 _root_.GD.N0106.N0428.N0770.N1725.d024120.ne'
  have hT : _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * _root_.GD.N0106.N0428.N0770.N1733.d027567 s = ∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, _root_.GD.N0106.N0428.N0770.N1725.d024170 s p * _root_.GD.N0106.N0428.N0770.N1733.d027566 s p ∂(volume.prod volume) := by
    unfold _root_.GD.N0106.N0428.N0770.N1733.d027567
    rw [← mul_assoc, mul_inv_cancel₀ heta, one_mul]
  calc ∫ x in _root_.GD.N0232.N0720.N1436.d013218, _root_.GD.N0106.N0428.N0770.N1725.d024170 s x * _root_.GD.N0106.N0428.N0770.N1733.d027566 s x
      = ∫ p in _root_.GD.N0106.N0428.N0770.N1726.d024366, _root_.GD.N0106.N0428.N0770.N1725.d024170 s p * _root_.GD.N0106.N0428.N0770.N1733.d027566 s p ∂(volume.prod volume) := rfl
    _ = _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * _root_.GD.N0106.N0428.N0770.N1733.d027567 s := hT.symm



theorem d027835 (mu sigma zeta : ℝ) (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta _root_.GD.N0106.N0428.N0770.N1725.d024117 0 - _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta 0 0 =
      _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (_root_.GD.N0106.N0428.N0770.N1725.d024117 * (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * _root_.GD.N0106.N0428.N0770.N1733.d027567 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta))) := by
  have h1 := _root_.GD.N0106.N0428.N0770.N1742.d027782 mu sigma zeta _root_.GD.N0106.N0428.N0770.N1725.d024117 0 hsigma hzeta
  have h0 := _root_.GD.N0106.N0428.N0770.N1742.d027782 mu sigma zeta 0 0 hsigma hzeta
  have hdiff : (∫ x in _root_.GD.N0232.N0720.N1436.d013218,
        _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 _root_.GD.N0106.N0428.N0770.N1725.d024117 0 x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2)
      - (∫ x in _root_.GD.N0232.N0720.N1436.d013218,
        _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 0 0 x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2)
      = _root_.GD.N0106.N0428.N0770.N1725.d024117 * (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * _root_.GD.N0106.N0428.N0770.N1733.d027567 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta)) := by
    rw [← integral_sub h1 h0]
    have hpt : (∫ x in _root_.GD.N0232.N0720.N1436.d013218,
        (_root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 _root_.GD.N0106.N0428.N0770.N1725.d024117 0 x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2
          - _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * (_root_.GD.N0106.N0428.N0770.N1725.d024154 0 0 x - _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ^ 2))
        = ∫ x in _root_.GD.N0232.N0720.N1436.d013218,
            _root_.GD.N0106.N0428.N0770.N1725.d024117 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x * _root_.GD.N0106.N0428.N0770.N1733.d027566 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => _root_.GD.N0106.N0428.N0770.N1717.d027833 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) x)
    rw [hpt, integral_const_mul, _root_.GD.N0106.N0428.N0770.N1717.d027834]
  rw [_root_.GD.N0106.N0428.N0770.N1742.d027781 mu sigma zeta _root_.GD.N0106.N0428.N0770.N1725.d024117 0 hsigma hzeta,
    _root_.GD.N0106.N0428.N0770.N1742.d027781 mu sigma zeta 0 0 hsigma hzeta]
  linear_combination _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * hdiff





theorem d027836 (sigma zeta : ℝ) (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
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

theorem d027837 (sigma zeta : ℝ) (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    0 < 351 * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * sigma ^ 4 * zeta ^ 4 /
      (500000 * Real.pi * (sigma ^ 2 + zeta ^ 2) ^ 3) := by
  apply div_pos
  · exact mul_pos (mul_pos (mul_pos (by norm_num) (pow_pos _root_.GD.N0106.N0428.N0770.N1725.d024120 2)) (pow_pos hsigma 4))
      (pow_pos hzeta 4)
  · exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (pow_pos (add_pos (pow_pos hsigma 2) (pow_pos hzeta 2)) 3)



theorem d027838 (mu sigma zeta : ℝ) (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta _root_.GD.N0106.N0428.N0770.N1725.d024117 0 - _root_.GD.N0106.N0428.N0770.N1742.d027779 mu sigma zeta 0 0 <
      -(351 * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * sigma ^ 4 * zeta ^ 4 /
        (500000 * Real.pi * (sigma ^ 2 + zeta ^ 2) ^ 3)) := by
  have hs0 : 0 < _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta :=
    _root_.GD.N0107.d009050 (by norm_num) (by norm_num) hsigma hzeta
  have hs1 : _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta < 1 :=
    _root_.GD.N0107.d009051 (by norm_num) (by norm_num) hsigma hzeta
  have hT := _root_.GD.N0106.N0428.N0770.N1717.d027832 (q := _root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) ⟨hs0.le, hs1.le⟩
  have hK := _root_.GD.N0106.N0428.N0770.N1722.d024331 sigma zeta hsigma hzeta
  have hpos : 0 < _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (_root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2) :=
    mul_pos hK (mul_pos _root_.GD.N0106.N0428.N0770.N1725.d024122 (pow_pos _root_.GD.N0106.N0428.N0770.N1725.d024120 2))
  rw [_root_.GD.N0106.N0428.N0770.N1717.d027835 mu sigma zeta hsigma hzeta, ← _root_.GD.N0106.N0428.N0770.N1717.d027836 sigma zeta hsigma hzeta]
  calc _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (_root_.GD.N0106.N0428.N0770.N1725.d024117 * (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * _root_.GD.N0106.N0428.N0770.N1733.d027567 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta)))
      = _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (_root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2) * _root_.GD.N0106.N0428.N0770.N1733.d027567 (_root_.GD.N0106.N0428.N0770.N1724.d024296 sigma zeta) := by ring
    _ < _root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (_root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2) * (-117 / 500) :=
        mul_lt_mul_of_pos_left hT hpos
    _ = -(_root_.GD.N0106.N0428.N0770.N1722.d024329 sigma zeta * (_root_.GD.N0106.N0428.N0770.N1725.d024117 * (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * (117 / 500)))) := by ring





theorem d027839 (mu sigma zeta : ℝ) (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024158 (_root_.GD.N0107.d009084 w.1) (_root_.GD.N0107.d009084 w.2)
          (_root_.GD.N0107.d009085 w.1) (_root_.GD.N0107.d009085 w.2) - mu) -
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024157 (_root_.GD.N0107.d009084 w.1) (_root_.GD.N0107.d009084 w.2)
          (_root_.GD.N0107.d009085 w.1) (_root_.GD.N0107.d009085 w.2) - mu) <
      -(351 * _root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2 * sigma ^ 4 * zeta ^ 4 /
        (500000 * Real.pi * (sigma ^ 2 + zeta ^ 2) ^ 3)) :=
  _root_.GD.N0106.N0428.N0770.N1717.d027838 mu sigma zeta hsigma hzeta



theorem d027840 (mu sigma zeta : ℝ) (hsigma : 0 < sigma) (hzeta : 0 < zeta) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024158 (_root_.GD.N0107.d009084 w.1) (_root_.GD.N0107.d009084 w.2)
          (_root_.GD.N0107.d009085 w.1) (_root_.GD.N0107.d009085 w.2) - mu) <
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 2 2 mu sigma zeta)
        (fun w : _root_.GD.N0106.N0428.N0770.N1724.d024295 => _root_.GD.N0106.N0428.N0770.N1725.d024157 (_root_.GD.N0107.d009084 w.1) (_root_.GD.N0107.d009084 w.2)
          (_root_.GD.N0107.d009085 w.1) (_root_.GD.N0107.d009085 w.2) - mu) := by
  have h := _root_.GD.N0106.N0428.N0770.N1717.d027839 mu sigma zeta hsigma hzeta
  have hm := _root_.GD.N0106.N0428.N0770.N1717.d027837 sigma zeta hsigma hzeta
  linarith [h, hm]

end
end GD.N0106.N0428.N0770.N1717

#print axioms _root_.GD.N0106.N0428.N0770.N1717.d027831
#print axioms _root_.GD.N0106.N0428.N0770.N1717.d027832
#print axioms _root_.GD.N0106.N0428.N0770.N1717.d027835
#print axioms _root_.GD.N0106.N0428.N0770.N1717.d027836
#print axioms _root_.GD.N0106.N0428.N0770.N1717.d027839
#print axioms _root_.GD.N0106.N0428.N0770.N1717.d027840
