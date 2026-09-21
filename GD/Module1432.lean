import GD.Module0355
import GD.Module0963

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0096.N0343

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1482
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ)

def d022801 (g : _root_.GD.N0232.N0720.N1482.d015118) : _root_.GD.N0232.N0720.N1080.d014170 m n → _root_.GD.N0232.N0720.N1080.d014170 m n :=
  fun z => g • z

def d022802 (g : _root_.GD.N0232.N0720.N1482.d015118) (f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (z : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ := f (g • z) - (g • f z)

theorem d022803 (g : _root_.GD.N0232.N0720.N1482.d015118) (f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (z : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0096.N0343.d022802 m n g f z =
      g.d009239 * (_root_.GD.N0232.N0720.N1214.d014261 m n g⁻¹ f z - f z) := by
  simp only [_root_.GD.N0096.N0343.d022802, _root_.GD.N0232.N0720.N1214.d014261, inv_inv, _root_.GD.N0232.N0719.N0946.d009229.d009244, _root_.GD.N0232.N0719.N0946.d009229.d009237,
    _root_.GD.N0232.N0719.N0946.d009229.d009239, _root_.GD.N0232.N0719.N0946.d009229.d009238, Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  ring

theorem d022804 (g : _root_.GD.N0232.N0720.N1482.d015118)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    MemLp (_root_.GD.N0096.N0343.d022802 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p)) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have h := ((_root_.GD.N0232.N0720.N1159.d014641 m n g⁻¹ p hp).sub
    (_root_.GD.N0232.N0720.N1214.d014268 m n p)).const_mul g.d009239
  simpa only [Pi.sub_apply, ← _root_.GD.N0096.N0343.d022803] using h

theorem d022805 (g : _root_.GD.N0232.N0720.N1482.d015118) (f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :
    _root_.GD.N0232.N0720.N1214.d014261 m n g⁻¹ f =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] f ↔
      _root_.GD.N0232.N0720.N1214.d014261 m n g f =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] f := by
  constructor
  · intro h
    have hh := _root_.GD.N0232.N0720.N1081.d014625 m n g h
    simpa only [_root_.GD.N0232.N0720.N1214.d014264, mul_inv_cancel, _root_.GD.N0232.N0720.N1214.d014263] using hh.symm
  · intro h
    have hh := _root_.GD.N0232.N0720.N1081.d014625 m n g⁻¹ h
    simpa only [_root_.GD.N0232.N0720.N1214.d014264, inv_mul_cancel, _root_.GD.N0232.N0720.N1214.d014263] using hh.symm

theorem d022806 (g : _root_.GD.N0232.N0720.N1482.d015118)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g p hp = p ↔
      _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014265 m n p := by
  have h := MemLp.toLp_eq_toLp_iff (_root_.GD.N0232.N0720.N1159.d014641 m n g p hp)
    (_root_.GD.N0232.N0720.N1214.d014268 m n p)
  simpa only [_root_.GD.N0232.N0720.N1159.d014642, _root_.GD.N0232.N0720.N1214.d014269] using h

theorem d022807 (g : _root_.GD.N0232.N0720.N1482.d015118)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    (∀ᵐ z ∂_root_.GD.N0232.N0720.N1080.d014172 m n, _root_.GD.N0096.N0343.d022802 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) z = 0) ↔
      _root_.GD.N0232.N0720.N1159.d014642 m n g p hp = p := by
  simp only [_root_.GD.N0096.N0343.d022803, mul_eq_zero, _root_.GD.N0232.N0719.N0946.d009229.d009241, false_or, sub_eq_zero]
  exact (_root_.GD.N0096.N0343.d022805 m n g _).trans (_root_.GD.N0096.N0343.d022806 m n g p hp).symm

def d022808 (f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : ℝ :=
  _root_.GD.N0018.N0253.d005250 (_root_.GD.N0232.N0720.N1080.d014172 m n)
    (_root_.GD.N0096.N0343.d022801 m n _root_.GD.N0232.N0720.N1482.d015130)
    (_root_.GD.N0096.N0343.d022801 m n _root_.GD.N0232.N0720.N1482.d015131) f

theorem d022809 (z : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0096.N0343.d022801 m n _root_.GD.N0232.N0720.N1482.d015130 z =
      ((fun i => 2 * z.1 i), (fun j => 2 * z.2 j)) := by
  apply Prod.ext
  · funext i
    change 0 + Real.exp (Real.log 2) * z.1 i = 2 * z.1 i
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2), zero_add]
  · funext j
    change 0 + Real.exp (Real.log 2) * z.2 j = 2 * z.2 j
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2), zero_add]

theorem d022810 (z : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0096.N0343.d022801 m n _root_.GD.N0232.N0720.N1482.d015131 z =
      ((fun i => 3 * z.1 i + 1), (fun j => 3 * z.2 j + 1)) := by
  apply Prod.ext
  · funext i
    change 1 + Real.exp (Real.log 3) * z.1 i = 3 * z.1 i + 1
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 3), add_comm]
  · funext j
    change 1 + Real.exp (Real.log 3) * z.2 j = 3 * z.2 j + 1
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 3), add_comm]

theorem d022811 (f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :
    _root_.GD.N0096.N0343.d022808 m n f = ∫ z,
      (f ((fun i => 2 * z.1 i), (fun j => 2 * z.2 j)) - 2 * f z) ^ 2 +
      (f ((fun i => 3 * z.1 i + 1), (fun j => 3 * z.2 j + 1)) -
        3 * f z - 1) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  simp only [_root_.GD.N0096.N0343.d022808, _root_.GD.N0018.N0253.d005250,
    _root_.GD.N0018.N0253.d005249, _root_.GD.N0018.N0253.d005248,
    _root_.GD.N0096.N0343.d022809, _root_.GD.N0096.N0343.d022810, sub_zero]

theorem d022812 (f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (z : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0096.N0343.d022802 m n _root_.GD.N0232.N0720.N1482.d015130 f z =
      _root_.GD.N0018.N0253.d005248 (_root_.GD.N0096.N0343.d022801 m n _root_.GD.N0232.N0720.N1482.d015130) 2 0 f z := by
  simp [_root_.GD.N0096.N0343.d022802, _root_.GD.N0018.N0253.d005248, _root_.GD.N0096.N0343.d022801,
    _root_.GD.N0232.N0720.N1482.d015130, _root_.GD.N0232.N0720.N1482.d015129, _root_.GD.N0232.N0719.N0946.d009229.d009239,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem d022813 (f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (z : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0096.N0343.d022802 m n _root_.GD.N0232.N0720.N1482.d015131 f z =
      _root_.GD.N0018.N0253.d005248 (_root_.GD.N0096.N0343.d022801 m n _root_.GD.N0232.N0720.N1482.d015131) 3 1 f z := by
  simp [_root_.GD.N0096.N0343.d022802, _root_.GD.N0018.N0253.d005248, _root_.GD.N0096.N0343.d022801,
    _root_.GD.N0232.N0720.N1482.d015131, _root_.GD.N0232.N0719.N0946.d009229.d009239,
    Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  ring

theorem d022814 (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    Integrable (_root_.GD.N0018.N0253.d005249
      (_root_.GD.N0096.N0343.d022801 m n _root_.GD.N0232.N0720.N1482.d015130)
      (_root_.GD.N0096.N0343.d022801 m n _root_.GD.N0232.N0720.N1482.d015131) (_root_.GD.N0232.N0720.N1214.d014265 m n p))
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  unfold _root_.GD.N0018.N0253.d005249
  apply Integrable.add
  · simpa only [← _root_.GD.N0096.N0343.d022812] using
      (_root_.GD.N0096.N0343.d022804 m n _root_.GD.N0232.N0720.N1482.d015130 p hp).integrable_sq
  · simpa only [← _root_.GD.N0096.N0343.d022813] using
      (_root_.GD.N0096.N0343.d022804 m n _root_.GD.N0232.N0720.N1482.d015131 p hp).integrable_sq

theorem d022815 (f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) :
    0 ≤ _root_.GD.N0096.N0343.d022808 m n f :=
  _root_.GD.N0018.N0253.d005256 _ _ _ _

theorem d022816 (g : _root_.GD.N0232.N0720.N1482.d015118)
    {f h : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ} (heq : f =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] h) :
    _root_.GD.N0096.N0343.d022802 m n g f =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] _root_.GD.N0096.N0343.d022802 m n g h := by
  have ht := _root_.GD.N0232.N0720.N1081.d014625 m n g⁻¹ heq
  filter_upwards [heq, ht] with z hz htz
  simp only [_root_.GD.N0096.N0343.d022803, hz, htz]

theorem d022817 {f h : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (heq : f =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] h) :
    _root_.GD.N0096.N0343.d022808 m n f = _root_.GD.N0096.N0343.d022808 m n h := by
  unfold _root_.GD.N0096.N0343.d022808 _root_.GD.N0018.N0253.d005250
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0096.N0343.d022816 m n _root_.GD.N0232.N0720.N1482.d015130 heq,
    _root_.GD.N0096.N0343.d022816 m n _root_.GD.N0232.N0720.N1482.d015131 heq] with z hz₂ hz₃
  simp only [_root_.GD.N0018.N0253.d005249, ← _root_.GD.N0096.N0343.d022812,
    ← _root_.GD.N0096.N0343.d022813, hz₂, hz₃]

theorem d022818 (f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)
    (hf : MemLp f 2 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0096.N0343.d022808 m n (_root_.GD.N0232.N0720.N1214.d014265 m n (hf.toLp f)) =
      _root_.GD.N0096.N0343.d022808 m n f := by
  apply _root_.GD.N0096.N0343.d022817
  exact (_root_.GD.N0232.N0720.N1214.d014267 m n (hf.toLp f)).trans hf.coeFn_toLp

theorem d022819 (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0096.N0343.d022808 m n (_root_.GD.N0232.N0720.N1214.d014265 m n p) = 0 ↔
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp = p ∧
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp = p := by
  have h := _root_.GD.N0018.N0253.d005257 (_root_.GD.N0096.N0343.d022814 m n p hp)
  rw [← _root_.GD.N0096.N0343.d022807 m n _root_.GD.N0232.N0720.N1482.d015130 p hp,
    ← _root_.GD.N0096.N0343.d022807 m n _root_.GD.N0232.N0720.N1482.d015131 p hp]
  simpa only [_root_.GD.N0096.N0343.d022808, _root_.GD.N0096.N0343.d022812, _root_.GD.N0096.N0343.d022813,
    _root_.GD.N0018.N0253.d005248, sub_zero, sub_eq_zero,
    sub_eq_iff_eq_add, zero_add, add_comm] using h

theorem d022820 (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    0 < _root_.GD.N0096.N0343.d022808 m n (_root_.GD.N0232.N0720.N1214.d014265 m n p) ↔
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp ≠ p ∨
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp ≠ p := by
  rw [← not_and_or, ← _root_.GD.N0096.N0343.d022819 m n p hp]
  constructor
  · exact fun h => h.ne'
  · exact fun h => lt_of_le_of_ne (_root_.GD.N0096.N0343.d022815 m n _) (Ne.symm h)

end
end GD.N0096.N0343

#print axioms _root_.GD.N0096.N0343.d022814
#print axioms _root_.GD.N0096.N0343.d022811
#print axioms _root_.GD.N0096.N0343.d022819
#print axioms _root_.GD.N0096.N0343.d022817
#print axioms _root_.GD.N0096.N0343.d022818
#print axioms _root_.GD.N0096.N0343.d022820
