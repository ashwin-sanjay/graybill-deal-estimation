import GD.Module1819
import GD.Module0752

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0005.N0248

open _root_.GD.N0232.N0719.N1011

noncomputable section

theorem d030133 (v : ℝ) (hv : 0 < v) :
    (Real.sqrt (2 * Real.pi * v))⁻¹ / (Real.sqrt (2 * Real.pi))⁻¹ =
      (Real.sqrt v)⁻¹ := by
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  rw [Real.sqrt_mul hπ]
  have hπ0 : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have hv0 : Real.sqrt v ≠ 0 := by positivity
  field_simp

theorem d030134 (n : ℕ) (μ scale x z : ℝ) (hscale : 0 < scale) :
    Real.log (_root_.GD.N0232.N0719.N1011.d011284 n μ scale x z) =
      (_root_.GD.N0232.N0719.N1011.d011283 n z + (n : ℝ)*x^2)/2 -
        (n : ℝ) * _root_.GD.N0005.N0248.d030118 (_root_.GD.N0005.N0248.d030070 (((n-1 : ℕ) : ℝ)*z) x μ) (scale^2)/2 := by
  have hv : 0 < scale^2 := sq_pos_of_pos hscale
  rw [_root_.GD.N0232.N0719.N1011.d011284, _root_.GD.N0005.N0248.d030133 (scale^2) hv,
    Real.log_mul (pow_ne_zero _ (inv_ne_zero (Real.sqrt_pos.2 hv).ne')) (Real.exp_ne_zero _),
    Real.log_pow, Real.log_inv, Real.log_sqrt hv.le, Real.log_exp]
  dsimp [_root_.GD.N0005.N0248.d030118, _root_.GD.N0005.N0248.d030070, _root_.GD.N0232.N0719.N1011.d011283]
  field_simp
  ring

theorem d030135
    (m n : ℕ) (u v w x y zX zY : ℝ) (hv : 0 < v) (hw : 0 < w) :
    Real.log
      (_root_.GD.N0232.N0719.N1011.d011284 m u (Real.sqrt v) x zX *
        _root_.GD.N0232.N0719.N1011.d011284 n u (Real.sqrt w) y zY) =
      (_root_.GD.N0232.N0719.N1011.d011283 m zX + (m : ℝ)*x^2 +
        _root_.GD.N0232.N0719.N1011.d011283 n zY + (n : ℝ)*y^2)/2 +
      _root_.GD.N0005.N0248.d030122 m n
        (((m-1 : ℕ) : ℝ)*zX) (((n-1 : ℕ) : ℝ)*zY) x y u v w := by
  have hleft : 0 < _root_.GD.N0232.N0719.N1011.d011284 m u (Real.sqrt v) x zX := by
    unfold _root_.GD.N0232.N0719.N1011.d011284
    positivity
  have hright : 0 < _root_.GD.N0232.N0719.N1011.d011284 n u (Real.sqrt w) y zY := by
    unfold _root_.GD.N0232.N0719.N1011.d011284
    positivity
  rw [Real.log_mul hleft.ne' hright.ne',
    _root_.GD.N0005.N0248.d030134 m u (Real.sqrt v) x zX (Real.sqrt_pos.2 hv),
    _root_.GD.N0005.N0248.d030134 n u (Real.sqrt w) y zY (Real.sqrt_pos.2 hw),
    Real.sq_sqrt hv.le, Real.sq_sqrt hw.le]
  unfold _root_.GD.N0005.N0248.d030122
  ring

end
end GD.N0005.N0248

#print axioms _root_.GD.N0005.N0248.d030134
#print axioms _root_.GD.N0005.N0248.d030135
