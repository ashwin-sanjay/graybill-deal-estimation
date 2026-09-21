import GD.Module0872
import GD.Module0526
import Mathlib.Tactic.FunProp

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0023.N0260

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1436 _root_.GD.N0232.N0720.N1336
open _root_.GD.N0232.N0720.N1290 (d004131)
open _root_.GD.N0024

def d021880 (m n : ℕ) (t : ℝ) (z : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  ((n - 1 : ℕ) : ℝ) * z.1 * (1 - t) +
    ((m - 1 : ℕ) : ℝ) * (1 - z.1) * t + z.2 * (t * (1 - t))

theorem d021881 (m n : ℕ) (t : _root_.GD.N0232.N0720.N1290.d004131) (z : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0023.N0260.d021880 m n t.1 z = _root_.GD.N0232.N0720.N1336.d013420 m n z t := rfl

theorem d021882 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (z : _root_.GD.N0232.N0720.N1436.d013217) (hz : z ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    0 < _root_.GD.N0023.N0260.d021880 m n t z :=
  _root_.GD.N0232.N0720.N1336.d013423 m n hm hn hz ⟨t, ht⟩

def d021883 (m n : ℕ) (t : ℝ) : ℝ :=
  t ^ (_root_.GD.N0232.N0720.N1436.d013207 m + 1 / 2) * (1 - t) ^ (_root_.GD.N0232.N0720.N1436.d013208 n + 1 / 2)

def d021884 (m n : ℕ) (p : ℝ × _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  _root_.GD.N0232.N0720.N1336.d013429 m n p.2 * _root_.GD.N0023.N0260.d021883 m n p.1 *
    (_root_.GD.N0023.N0260.d021880 m n p.1 p.2) ^ (-_root_.GD.N0232.N0720.N1436.d013210 m n)

theorem d021885
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (t : ℝ) :
    _root_.GD.N0023.N0260.d021883 m n t = t ^ ((m : ℝ) / 2) * (1 - t) ^ ((n : ℝ) / 2) := by
  have hm' : _root_.GD.N0232.N0720.N1436.d013207 m + (1 / 2 : ℝ) = (m : ℝ) / 2 := by
    unfold _root_.GD.N0232.N0720.N1436.d013207
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    push_cast
    ring
  have hn' : _root_.GD.N0232.N0720.N1436.d013208 n + (1 / 2 : ℝ) = (n : ℝ) / 2 := by
    unfold _root_.GD.N0232.N0720.N1436.d013208
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  simp only [_root_.GD.N0023.N0260.d021883, hm', hn']

theorem d021886 (m n : ℕ) :
    Continuous (fun p : ℝ × _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0023.N0260.d021880 m n p.1 p.2) := by
  unfold _root_.GD.N0023.N0260.d021880
  fun_prop

theorem d021887 (m n : ℕ) :
    ContinuousOn (_root_.GD.N0232.N0720.N1336.d013429 m n) _root_.GD.N0232.N0720.N1436.d013218 := by
  have hleft : ContinuousOn (fun z : _root_.GD.N0232.N0720.N1436.d013217 =>
      (1 - z.1) ^ (_root_.GD.N0232.N0720.N1436.d013207 m - 1)) _root_.GD.N0232.N0720.N1436.d013218 :=
    (continuous_const.sub continuous_fst).continuousOn.rpow_const
      (fun z hz => Or.inl (sub_pos.mpr hz.1.2).ne')
  have hright : ContinuousOn (fun z : _root_.GD.N0232.N0720.N1436.d013217 =>
      z.1 ^ (_root_.GD.N0232.N0720.N1436.d013208 n - 1)) _root_.GD.N0232.N0720.N1436.d013218 :=
    continuous_fst.continuousOn.rpow_const (fun z hz => Or.inl hz.1.1.ne')
  have hscale : ContinuousOn (fun z : _root_.GD.N0232.N0720.N1436.d013217 =>
      z.2 ^ (_root_.GD.N0232.N0720.N1436.d013209 - 1)) _root_.GD.N0232.N0720.N1436.d013218 :=
    continuous_snd.continuousOn.rpow_const (fun z hz => Or.inl hz.2.ne')
  exact (((continuousOn_const.mul (hleft.mul hright |>.mul hscale)).mul
    continuousOn_const).mul continuousOn_const)

theorem d021888 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    Continuous (_root_.GD.N0023.N0260.d021883 m n) := by
  have ha : 0 ≤ _root_.GD.N0232.N0720.N1436.d013207 m + (1 / 2 : ℝ) := by
    linarith [_root_.GD.N0232.N0720.N1436.d013211 hm]
  have hb : 0 ≤ _root_.GD.N0232.N0720.N1436.d013208 n + (1 / 2 : ℝ) := by
    linarith [_root_.GD.N0232.N0720.N1436.d013212 hn]
  exact (continuous_id.rpow_const (fun _ => Or.inr ha)).mul
    ((continuous_const.sub continuous_id).rpow_const (fun _ => Or.inr hb))

theorem d021889 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ContinuousOn (_root_.GD.N0023.N0260.d021884 m n) (Icc (0 : ℝ) 1 ×ˢ _root_.GD.N0232.N0720.N1436.d013218) := by
  unfold _root_.GD.N0023.N0260.d021884
  apply ContinuousOn.mul
  · exact ((_root_.GD.N0023.N0260.d021887 m n).comp continuous_snd.continuousOn
      (fun _ hp => hp.2)).mul
      ((_root_.GD.N0023.N0260.d021888 m n hm hn).comp continuous_fst).continuousOn
  · exact (_root_.GD.N0023.N0260.d021886 m n).continuousOn.rpow_const
      (fun p hp => Or.inl (_root_.GD.N0023.N0260.d021882 m n hm hn p.1 hp.1 p.2 hp.2).ne')

theorem d021890 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (z : _root_.GD.N0232.N0720.N1436.d013217) (hz : z ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    0 < _root_.GD.N0023.N0260.d021884 m n (t, z) := by
  unfold _root_.GD.N0023.N0260.d021884 _root_.GD.N0023.N0260.d021883
  exact mul_pos
    (mul_pos (_root_.GD.N0232.N0720.N1336.d013430 m n hm hn hz)
      (mul_pos (Real.rpow_pos_of_pos ht.1 _) (Real.rpow_pos_of_pos (sub_pos.mpr ht.2) _)))
    (Real.rpow_pos_of_pos (_root_.GD.N0023.N0260.d021882 m n hm hn t ⟨ht.1.le, ht.2.le⟩ z hz) _)

theorem d021891 (m n : ℕ) (hm : 2 ≤ m) (z : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0023.N0260.d021884 m n (0, z) = 0 := by
  have ha : _root_.GD.N0232.N0720.N1436.d013207 m + (1 / 2 : ℝ) ≠ 0 := by
    linarith [_root_.GD.N0232.N0720.N1436.d013211 hm]
  simp only [_root_.GD.N0023.N0260.d021884, _root_.GD.N0023.N0260.d021883, Real.zero_rpow ha, zero_mul, mul_zero]

theorem d021892 (m n : ℕ) (hn : 2 ≤ n) (z : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0023.N0260.d021884 m n (1, z) = 0 := by
  have hb : _root_.GD.N0232.N0720.N1436.d013208 n + (1 / 2 : ℝ) ≠ 0 := by
    linarith [_root_.GD.N0232.N0720.N1436.d013212 hn]
  simp only [_root_.GD.N0023.N0260.d021884, _root_.GD.N0023.N0260.d021883, sub_self, Real.zero_rpow hb, mul_zero, zero_mul]

theorem d021893 (m n : ℕ) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0232.N0720.N1336.d013426 m n t =
      t ^ (_root_.GD.N0232.N0720.N1436.d013207 m + 3 / 2) * (1 - t) ^ (_root_.GD.N0232.N0720.N1436.d013208 n + 3 / 2) := by
  have ht' : 0 < 1 - t := sub_pos.mpr ht1
  unfold _root_.GD.N0232.N0720.N1336.d013426 _root_.GD.N0232.N0720.N1436.d013270 _root_.GD.N0232.N0720.N1271.d013403
  rw [Real.mul_rpow ht0.le ht'.le]
  calc
    (1 - t) ^ (-_root_.GD.N0232.N0720.N1436.d013207 m) * t ^ (-_root_.GD.N0232.N0720.N1436.d013208 n) *
        (t ^ _root_.GD.N0232.N0720.N1436.d013210 m n * (1 - t) ^ _root_.GD.N0232.N0720.N1436.d013210 m n) =
      (t ^ (-_root_.GD.N0232.N0720.N1436.d013208 n) * t ^ _root_.GD.N0232.N0720.N1436.d013210 m n) *
        ((1 - t) ^ (-_root_.GD.N0232.N0720.N1436.d013207 m) * (1 - t) ^ _root_.GD.N0232.N0720.N1436.d013210 m n) := by ring
    _ = _ := by
      rw [← Real.rpow_add ht0, ← Real.rpow_add ht']
      congr 1 <;> congr 1 <;> unfold _root_.GD.N0232.N0720.N1436.d013210 _root_.GD.N0232.N0720.N1436.d013209 <;> ring

theorem d021894 (m n : ℕ) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0023.N0260.d021883 m n t * (t * (1 - t)) = _root_.GD.N0232.N0720.N1336.d013426 m n t := by
  have ht' : 0 < 1 - t := sub_pos.mpr ht1
  have hleft : t ^ (_root_.GD.N0232.N0720.N1436.d013207 m + 1 / 2) * t =
      t ^ (_root_.GD.N0232.N0720.N1436.d013207 m + 3 / 2) := by
    have he := Real.rpow_add ht0 (_root_.GD.N0232.N0720.N1436.d013207 m + 1 / 2) 1
    rw [Real.rpow_one] at he
    convert he.symm using 1
    congr 1
    ring
  have hright : (1 - t) ^ (_root_.GD.N0232.N0720.N1436.d013208 n + 1 / 2) * (1 - t) =
      (1 - t) ^ (_root_.GD.N0232.N0720.N1436.d013208 n + 3 / 2) := by
    have he := Real.rpow_add ht' (_root_.GD.N0232.N0720.N1436.d013208 n + 1 / 2) 1
    rw [Real.rpow_one] at he
    convert he.symm using 1
    congr 1
    ring
  rw [_root_.GD.N0023.N0260.d021893 m n t ht0 ht1]
  unfold _root_.GD.N0023.N0260.d021883
  calc
    _ = (t ^ (_root_.GD.N0232.N0720.N1436.d013207 m + 1 / 2) * t) *
      ((1 - t) ^ (_root_.GD.N0232.N0720.N1436.d013208 n + 1 / 2) * (1 - t)) := by ring
    _ = _ := by rw [hleft, hright]

theorem d021895 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0024.N0277.d007878) (z : _root_.GD.N0232.N0720.N1436.d013217) (hz : z ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0023.N0260.d021884 m n (t.1, z) =
      _root_.GD.N0232.N0720.N1436.d013273 m n t.1 z / _root_.GD.N0024.N0277.d007879 t := by
  let s : _root_.GD.N0232.N0720.N1290.d004131 := ⟨t.1, t.2.1.le, t.2.2.le⟩
  have hk := _root_.GD.N0232.N0720.N1336.d013431 m n hm hn hz s t.2.1 t.2.2
  have hpoly : _root_.GD.N0232.N0720.N1336.d013420 m n z s = _root_.GD.N0023.N0260.d021880 m n t.1 z := rfl
  dsimp only [s] at hk hpoly
  rw [hk, hpoly]
  apply (eq_div_iff (_root_.GD.N0024.N0277.d007880 t).ne').mpr
  have hp := _root_.GD.N0023.N0260.d021894 m n t.1 t.2.1 t.2.2
  unfold _root_.GD.N0023.N0260.d021884 _root_.GD.N0024.N0277.d007879
  rw [← hp]
  ring

end
end GD.N0023.N0260

#print axioms _root_.GD.N0023.N0260.d021881
#print axioms _root_.GD.N0023.N0260.d021882
#print axioms _root_.GD.N0023.N0260.d021885
#print axioms _root_.GD.N0023.N0260.d021886
#print axioms _root_.GD.N0023.N0260.d021887
#print axioms _root_.GD.N0023.N0260.d021888
#print axioms _root_.GD.N0023.N0260.d021889
#print axioms _root_.GD.N0023.N0260.d021890
#print axioms _root_.GD.N0023.N0260.d021891
#print axioms _root_.GD.N0023.N0260.d021892
#print axioms _root_.GD.N0023.N0260.d021893
#print axioms _root_.GD.N0023.N0260.d021894
#print axioms _root_.GD.N0023.N0260.d021895
