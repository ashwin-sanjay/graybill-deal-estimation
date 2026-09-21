import GD.Module0872
import GD.Module0526
import Mathlib.Tactic.FunProp

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0024.N0280

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1336
open _root_.GD.N0232.N0720.N1290 (d004131)

def d023588 (t : ℝ) (z : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  5 * z.1 * (1 - t) + 5 * (1 - z.1) * t + z.2 * (t * (1 - t))

theorem d023589 (t : _root_.GD.N0232.N0720.N1290.d004131) (z : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0024.N0280.d023588 t.1 z = _root_.GD.N0232.N0720.N1336.d013420 6 6 z t := by
  norm_num [_root_.GD.N0024.N0280.d023588, _root_.GD.N0232.N0720.N1336.d013420, _root_.GD.N0232.N0720.N1271.d013403]

theorem d023590 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (z : _root_.GD.N0232.N0720.N1436.d013217) (hz : z ∈ _root_.GD.N0232.N0720.N1436.d013218) : 0 < _root_.GD.N0024.N0280.d023588 t z := by
  exact (_root_.GD.N0024.N0280.d023589 ⟨t, ht⟩ z) ▸ _root_.GD.N0232.N0720.N1336.d013423 6 6 (by norm_num) (by norm_num) hz ⟨t, ht⟩

def d023591 (p : ℝ × _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  _root_.GD.N0232.N0720.N1336.d013429 6 6 p.2 * (p.1 * (1 - p.1)) ^ 3 *
    (_root_.GD.N0024.N0280.d023588 p.1 p.2) ^ (-(13 / 2 : ℝ))

theorem d023592 :
    Continuous (fun p : ℝ × _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0024.N0280.d023588 p.1 p.2) := by
  unfold _root_.GD.N0024.N0280.d023588
  fun_prop

theorem d023593 :
    Continuous (_root_.GD.N0232.N0720.N1336.d013429 6 6) := by
  unfold _root_.GD.N0232.N0720.N1336.d013429 _root_.GD.N0232.N0720.N1436.d013269
    _root_.GD.N0232.N0720.N1436.d013207 _root_.GD.N0232.N0720.N1436.d013208 _root_.GD.N0232.N0720.N1436.d013209
  norm_num
  fun_prop (disch := norm_num)

theorem d023594 :
    ContinuousOn _root_.GD.N0024.N0280.d023591 (Icc (0 : ℝ) 1 ×ˢ _root_.GD.N0232.N0720.N1436.d013218) := by
  unfold _root_.GD.N0024.N0280.d023591
  apply ContinuousOn.mul
  · exact (_root_.GD.N0024.N0280.d023593.comp continuous_snd).continuousOn.mul
      (by fun_prop : Continuous (fun p : ℝ × _root_.GD.N0232.N0720.N1436.d013217 => (p.1 * (1 - p.1)) ^ 3)).continuousOn
  · exact _root_.GD.N0024.N0280.d023592.continuousOn.rpow_const
      (fun p hp => Or.inl (_root_.GD.N0024.N0280.d023590 p.1 hp.1 p.2 hp.2).ne')

theorem d023595 (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (z : _root_.GD.N0232.N0720.N1436.d013217) (hz : z ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    0 < _root_.GD.N0024.N0280.d023591 (t, z) := by
  unfold _root_.GD.N0024.N0280.d023591
  exact mul_pos
    (mul_pos (_root_.GD.N0232.N0720.N1336.d013430 6 6 (by norm_num) (by norm_num) hz)
      (pow_pos (mul_pos ht.1 (sub_pos.mpr ht.2)) _))
    (Real.rpow_pos_of_pos (_root_.GD.N0024.N0280.d023590 t ⟨ht.1.le, ht.2.le⟩ z hz) _)

theorem d023596 (z : _root_.GD.N0232.N0720.N1436.d013217) : _root_.GD.N0024.N0280.d023591 (0, z) = 0 := by
  simp [_root_.GD.N0024.N0280.d023591]

theorem d023597 (z : _root_.GD.N0232.N0720.N1436.d013217) : _root_.GD.N0024.N0280.d023591 (1, z) = 0 := by
  simp [_root_.GD.N0024.N0280.d023591]

theorem d023598 (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0232.N0720.N1336.d013426 6 6 t = (t * (1 - t)) ^ 4 := by
  have ht' : 0 < 1 - t := sub_pos.mpr ht1
  unfold _root_.GD.N0232.N0720.N1336.d013426 _root_.GD.N0232.N0720.N1436.d013270 _root_.GD.N0232.N0720.N1436.d013210
    _root_.GD.N0232.N0720.N1436.d013207 _root_.GD.N0232.N0720.N1436.d013208 _root_.GD.N0232.N0720.N1436.d013209 _root_.GD.N0232.N0720.N1271.d013403
  norm_num
  rw [Real.mul_rpow ht0.le ht'.le]
  calc
    (1 - t) ^ (-(5 / 2 : ℝ)) * t ^ (-(5 / 2 : ℝ)) *
        (t ^ (13 / 2 : ℝ) * (1 - t) ^ (13 / 2 : ℝ)) =
      (t ^ (-(5 / 2 : ℝ)) * t ^ (13 / 2 : ℝ)) *
        ((1 - t) ^ (-(5 / 2 : ℝ)) * (1 - t) ^ (13 / 2 : ℝ)) := by ring
    _ = (t * (1 - t)) ^ 4 := by
      rw [← Real.rpow_add ht0, ← Real.rpow_add ht']
      norm_num
      ring

theorem d023599 (t : _root_.GD.N0024.N0277.d007878)
    (z : _root_.GD.N0232.N0720.N1436.d013217) (hz : z ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0024.N0280.d023591 (t.1, z) =
      _root_.GD.N0232.N0720.N1436.d013273 6 6 t.1 z / _root_.GD.N0024.N0277.d007879 t := by
  let s : _root_.GD.N0232.N0720.N1290.d004131 := ⟨t.1, t.2.1.le, t.2.2.le⟩
  have hk := _root_.GD.N0232.N0720.N1336.d013431 6 6 (by norm_num) (by norm_num)
    hz s t.2.1 t.2.2
  have hp := _root_.GD.N0024.N0280.d023598 t.1 t.2.1 t.2.2
  have hshape : _root_.GD.N0232.N0720.N1436.d013210 6 6 = (13 / 2 : ℝ) := by
    norm_num [_root_.GD.N0232.N0720.N1436.d013210, _root_.GD.N0232.N0720.N1436.d013207, _root_.GD.N0232.N0720.N1436.d013208, _root_.GD.N0232.N0720.N1436.d013209]
  have hpoly : _root_.GD.N0232.N0720.N1336.d013420 6 6 z s = _root_.GD.N0024.N0280.d023588 t.1 z := (_root_.GD.N0024.N0280.d023589 s z).symm
  dsimp only [s] at hk hpoly
  rw [hk, hp, hshape, hpoly]
  unfold _root_.GD.N0024.N0280.d023591 _root_.GD.N0024.N0277.d007879
  have hw : t.1 * (1 - t.1) ≠ 0 := (_root_.GD.N0024.N0277.d007880 t).ne'
  field_simp [hw]

#print axioms _root_.GD.N0024.N0280.d023589
#print axioms _root_.GD.N0024.N0280.d023590
#print axioms _root_.GD.N0024.N0280.d023592
#print axioms _root_.GD.N0024.N0280.d023593
#print axioms _root_.GD.N0024.N0280.d023594
#print axioms _root_.GD.N0024.N0280.d023595
#print axioms _root_.GD.N0024.N0280.d023596
#print axioms _root_.GD.N0024.N0280.d023597
#print axioms _root_.GD.N0024.N0280.d023598
#print axioms _root_.GD.N0024.N0280.d023599

end
end GD.N0024.N0280
