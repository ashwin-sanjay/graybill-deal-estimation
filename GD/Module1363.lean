import GD.Module1320
import GD.Module0466

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory

namespace GD.N0034.N0291

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0719.N0946.d009229
open _root_.GD.N0034.N0287

variable (m n : ℕ)

theorem d021967 (z : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1482.d015130 • z = (2 : ℝ) • z := by
  ext i <;>
    simp [_root_.GD.N0232.N0720.N1214.d014259, _root_.GD.N0232.N0720.N1482.d015130, _root_.GD.N0232.N0720.N1482.d015129, _root_.GD.N0232.N0719.N0946.d009229.d009239,
      _root_.GD.N0107.d009024, _root_.GD.N0107.d009018,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem d021968 (z : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1482.d015131 • z =
      ((fun i => 3 * z.1 i + 1), (fun j => 3 * z.2 j + 1)) := by
  ext i <;>
    simp [_root_.GD.N0232.N0720.N1214.d014259, _root_.GD.N0232.N0720.N1482.d015131, _root_.GD.N0232.N0719.N0946.d009229.d009239,
      _root_.GD.N0107.d009024, _root_.GD.N0107.d009018,
      add_comm, Real.exp_log (by norm_num : (0 : ℝ) < 3)]

theorem d021969 (y : ℝ) : _root_.GD.N0232.N0720.N1482.d015130 • y = 2 * y := by
  simp [_root_.GD.N0232.N0719.N0946.d009229.d009244, _root_.GD.N0232.N0720.N1482.d015130, _root_.GD.N0232.N0720.N1482.d015129, _root_.GD.N0232.N0719.N0946.d009229.d009239,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem d021970 (y : ℝ) : _root_.GD.N0232.N0720.N1482.d015131 • y = 3 * y + 1 := by
  simp [_root_.GD.N0232.N0719.N0946.d009229.d009244, _root_.GD.N0232.N0720.N1482.d015131, _root_.GD.N0232.N0719.N0946.d009229.d009239, add_comm,
    Real.exp_log (by norm_num : (0 : ℝ) < 3)]

theorem d021971
    (p : _root_.GD.N0034.N0287.d021568 m n) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0034.N0287.d021571 m n p = _root_.GD.N0034.N0292.d007212
      (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (fun z : _root_.GD.N0232.N0720.N1080.d014170 m n => (2 : ℝ) • z)
      (fun z : _root_.GD.N0232.N0720.N1080.d014170 m n =>
        ((fun i => 3 * z.1 i + 1), (fun j => 3 * z.2 j + 1)))
      (_root_.GD.N0232.N0720.N1214.d014265 m n p) := by
  rw [_root_.GD.N0034.N0287.d021582 m n p hp]
  unfold _root_.GD.N0034.N0292.d007212
  apply integral_congr_ae
  filter_upwards with z
  simp only [_root_.GD.N0034.N0287.d021569, _root_.GD.N0034.N0291.d021967, _root_.GD.N0034.N0291.d021968,
    _root_.GD.N0034.N0291.d021969, _root_.GD.N0034.N0291.d021970]
  ring

end
end GD.N0034.N0291

#print axioms _root_.GD.N0034.N0291.d021971
