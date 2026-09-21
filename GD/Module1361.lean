import GD.Module1176
import GD.Module0932

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory

namespace GD.N0034.N0290

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1459 _root_.GD.N0232.N0720.N1467
open _root_.GD.N0107

variable (m n : ℕ)

def d021948 (z : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  if 0 < _root_.GD.N0107.d009085 z.1 / (m : ℝ) +
      _root_.GD.N0107.d009085 z.2 / (n : ℝ) then
    ((_root_.GD.N0107.d009085 z.2 / (n : ℝ)) * _root_.GD.N0107.d009084 z.1 +
      (_root_.GD.N0107.d009085 z.1 / (m : ℝ)) * _root_.GD.N0107.d009084 z.2) /
        (_root_.GD.N0107.d009085 z.1 / (m : ℝ) +
          _root_.GD.N0107.d009085 z.2 / (n : ℝ))
  else 0

theorem d021949 : Measurable (_root_.GD.N0034.N0290.d021948 m n) := by
  unfold _root_.GD.N0034.N0290.d021948
  apply Measurable.ite
  · exact measurableSet_lt measurable_const (by fun_prop)
  · fun_prop
  · exact measurable_const

theorem d021950
    (z : _root_.GD.N0232.N0720.N1080.d014170 m n)
    (hpos : 0 < _root_.GD.N0107.d009085 z.1 / (m : ℝ) +
      _root_.GD.N0107.d009085 z.2 / (n : ℝ)) :
    _root_.GD.N0034.N0290.d021948 m n z = _root_.GD.N0232.N0720.N1080.d014175 m n z := by
  unfold _root_.GD.N0034.N0290.d021948
  rw [if_pos hpos]
  unfold _root_.GD.N0232.N0720.N1080.d014175 _root_.GD.N0107.d012733 _root_.GD.N0107.d009091 _root_.GD.N0107.d009090
  have hidentity (u v a b : ℝ) (huv : u + v ≠ 0) :
      (v * a + u * b) / (u + v) = b + v / (u + v) * (a - b) := by
    field_simp [huv]
    ring
  exact hidentity _ _ _ _ hpos.ne'

theorem d021951
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0034.N0290.d021948 m n =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] _root_.GD.N0232.N0720.N1080.d014175 m n := by
  filter_upwards [_root_.GD.N0232.N0720.N1459.d018933 m n hm hn] with z hz
  apply _root_.GD.N0034.N0290.d021950 m n z
  simpa only [_root_.GD.N0232.N0720.N1467.d012547, _root_.GD.N0232.N0720.N1467.d012548] using hz

theorem d021952
    (hm : 2 ≤ m) (hn : 2 ≤ n) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0034.N0290.d021948 m n =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] _root_.GD.N0232.N0720.N1080.d014175 m n :=
  (_root_.GD.N0232.N0720.N1080.d014173 m n θ).ae_le
    (_root_.GD.N0034.N0290.d021951 m n hm hn)

theorem d021953
    (hm : 2 ≤ m) (hn : 2 ≤ n) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0034.N0290.d021948 m n) =
      _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1080.d014175 m n) :=
  _root_.GD.N0232.N0720.N1159.d014662 m n θ
    (_root_.GD.N0034.N0290.d021952 m n hm hn θ)

end
end GD.N0034.N0290

#print axioms _root_.GD.N0034.N0290.d021949
#print axioms _root_.GD.N0034.N0290.d021950
#print axioms _root_.GD.N0034.N0290.d021951
#print axioms _root_.GD.N0034.N0290.d021952
#print axioms _root_.GD.N0034.N0290.d021953
