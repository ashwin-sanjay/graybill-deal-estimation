import Mathlib.Tactic












namespace GD.N0232.N0720.N1250

def d002191 (a : ℕ) (x : ℝ) : ℝ := x ^ (a + 1) * (1 - x)

theorem d002192 (x : ℝ) :
    _root_.GD.N0232.N0720.N1250.d002191 0 (1 - x) = _root_.GD.N0232.N0720.N1250.d002191 0 x := by
  simp [_root_.GD.N0232.N0720.N1250.d002191]
  ring

theorem d002193 (x : ℝ) :
    _root_.GD.N0232.N0720.N1250.d002191 1 (1 - x) = _root_.GD.N0232.N0720.N1250.d002191 0 x - _root_.GD.N0232.N0720.N1250.d002191 1 x := by
  simp [_root_.GD.N0232.N0720.N1250.d002191]
  ring

theorem d002194 (x : ℝ) :
    _root_.GD.N0232.N0720.N1250.d002191 2 (1 - x) =
      _root_.GD.N0232.N0720.N1250.d002191 0 x - 2 * _root_.GD.N0232.N0720.N1250.d002191 1 x + _root_.GD.N0232.N0720.N1250.d002191 2 x := by
  simp [_root_.GD.N0232.N0720.N1250.d002191]
  ring

theorem d002195 (x : ℝ) :
    _root_.GD.N0232.N0720.N1250.d002191 3 (1 - x) =
      _root_.GD.N0232.N0720.N1250.d002191 0 x - 3 * _root_.GD.N0232.N0720.N1250.d002191 1 x + 3 * _root_.GD.N0232.N0720.N1250.d002191 2 x - _root_.GD.N0232.N0720.N1250.d002191 3 x := by
  simp [_root_.GD.N0232.N0720.N1250.d002191]
  ring

theorem d002196 (x : ℝ) :
    _root_.GD.N0232.N0720.N1250.d002191 4 (1 - x) =
      _root_.GD.N0232.N0720.N1250.d002191 0 x - 4 * _root_.GD.N0232.N0720.N1250.d002191 1 x + 6 * _root_.GD.N0232.N0720.N1250.d002191 2 x -
        4 * _root_.GD.N0232.N0720.N1250.d002191 3 x + _root_.GD.N0232.N0720.N1250.d002191 4 x := by
  simp [_root_.GD.N0232.N0720.N1250.d002191]
  ring

end GD.N0232.N0720.N1250
