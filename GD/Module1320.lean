import GD.Module0963

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory
open scoped ENNReal

namespace GD.N0034.N0287

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0230.N0602
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ)

abbrev d021568 := _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)

def d021569 (g : _root_.GD.N0232.N0720.N1482.d015118) (p : _root_.GD.N0034.N0287.d021568 m n)
    (z : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  _root_.GD.N0232.N0720.N1214.d014265 m n p (g • z) - g • _root_.GD.N0232.N0720.N1214.d014265 m n p z

def d021570 (g : _root_.GD.N0232.N0720.N1482.d015118) (p : _root_.GD.N0034.N0287.d021568 m n) : ℝ :=
  ∫ z, (_root_.GD.N0034.N0287.d021569 m n g p z) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n

def d021571 (p : _root_.GD.N0034.N0287.d021568 m n) : ℝ :=
  _root_.GD.N0034.N0287.d021570 m n _root_.GD.N0232.N0720.N1482.d015130 p + _root_.GD.N0034.N0287.d021570 m n _root_.GD.N0232.N0720.N1482.d015131 p

theorem d021572 (g : _root_.GD.N0232.N0720.N1482.d015118) (p : _root_.GD.N0034.N0287.d021568 m n)
    (z : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0034.N0287.d021569 m n g p z = g.d009239 *
      (_root_.GD.N0232.N0720.N1214.d014261 m n g⁻¹ (_root_.GD.N0232.N0720.N1214.d014265 m n p) z - _root_.GD.N0232.N0720.N1214.d014265 m n p z) := by
  have h := smul_inv_smul g (_root_.GD.N0232.N0720.N1214.d014265 m n p (g • z))
  rw [_root_.GD.N0232.N0719.N0946.d009229.d009244] at h
  simp only [_root_.GD.N0034.N0287.d021569, _root_.GD.N0232.N0720.N1214.d014261, inv_inv, _root_.GD.N0232.N0719.N0946.d009229.d009244] at *
  nlinarith

theorem d021573 (g : _root_.GD.N0232.N0720.N1482.d015118) (p : _root_.GD.N0034.N0287.d021568 m n)
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    MemLp (_root_.GD.N0034.N0287.d021569 m n g p) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have h := ((_root_.GD.N0232.N0720.N1159.d014641 m n g⁻¹ p hp).sub
    (_root_.GD.N0232.N0720.N1214.d014268 m n p)).const_mul g.d009239
  simpa only [Pi.sub_apply, ← _root_.GD.N0034.N0287.d021572] using h

theorem d021574 (g : _root_.GD.N0232.N0720.N1482.d015118) (p : _root_.GD.N0034.N0287.d021568 m n) :
    0 ≤ _root_.GD.N0034.N0287.d021570 m n g p := integral_nonneg (fun _ => sq_nonneg _)

theorem d021575 (p : _root_.GD.N0034.N0287.d021568 m n) : 0 ≤ _root_.GD.N0034.N0287.d021571 m n p :=
  add_nonneg (_root_.GD.N0034.N0287.d021574 m n _ p) (_root_.GD.N0034.N0287.d021574 m n _ p)

theorem d021576 (g : _root_.GD.N0232.N0720.N1482.d015118) (p : _root_.GD.N0034.N0287.d021568 m n)
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g p hp = p ↔
      _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014265 m n p := by
  have h := MemLp.toLp_eq_toLp_iff
    (_root_.GD.N0232.N0720.N1159.d014641 m n g p hp) (_root_.GD.N0232.N0720.N1214.d014268 m n p)
  rw [_root_.GD.N0232.N0720.N1214.d014269] at h
  exact h

theorem d021577 (g : _root_.GD.N0232.N0720.N1482.d015118) (p : _root_.GD.N0034.N0287.d021568 m n) :
    _root_.GD.N0232.N0720.N1214.d014261 m n g⁻¹ (_root_.GD.N0232.N0720.N1214.d014265 m n p) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014265 m n p ↔
      _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014265 m n p := by
  constructor
  · intro h
    have ht := _root_.GD.N0232.N0720.N1081.d014625 m n g h
    simpa only [_root_.GD.N0232.N0720.N1214.d014264, mul_inv_cancel, _root_.GD.N0232.N0720.N1214.d014263] using ht.symm
  · intro h
    have ht := _root_.GD.N0232.N0720.N1081.d014625 m n g⁻¹ h
    simpa only [_root_.GD.N0232.N0720.N1214.d014264, inv_mul_cancel, _root_.GD.N0232.N0720.N1214.d014263] using ht.symm

theorem d021578 (g : _root_.GD.N0232.N0720.N1482.d015118) (p : _root_.GD.N0034.N0287.d021568 m n)
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0034.N0287.d021570 m n g p = 0 ↔ _root_.GD.N0232.N0720.N1159.d014642 m n g p hp = p := by
  have hint := (memLp_two_iff_integrable_sq
    (_root_.GD.N0034.N0287.d021573 m n g p hp).aestronglyMeasurable).mp (_root_.GD.N0034.N0287.d021573 m n g p hp)
  rw [_root_.GD.N0034.N0287.d021570, integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hint,
    _root_.GD.N0034.N0287.d021576, ← _root_.GD.N0034.N0287.d021577]
  constructor
  · intro h
    filter_upwards [h] with z hz
    have hr : _root_.GD.N0034.N0287.d021569 m n g p z = 0 := (sq_eq_zero_iff).mp hz
    rw [_root_.GD.N0034.N0287.d021572] at hr
    exact sub_eq_zero.mp ((mul_eq_zero.mp hr).resolve_left g.d009241)
  · intro h
    filter_upwards [h] with z hz
    simp [_root_.GD.N0034.N0287.d021572, hz]

theorem d021579 (p : _root_.GD.N0034.N0287.d021568 m n) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0034.N0287.d021571 m n p = 0 ↔
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp = p ∧
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp = p := by
  rw [_root_.GD.N0034.N0287.d021571, add_eq_zero_iff_of_nonneg (_root_.GD.N0034.N0287.d021574 m n _ p)
    (_root_.GD.N0034.N0287.d021574 m n _ p), _root_.GD.N0034.N0287.d021578 m n _ p hp,
    _root_.GD.N0034.N0287.d021578 m n _ p hp]

theorem d021580 (p : _root_.GD.N0034.N0287.d021568 m n) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0034.N0287.d021571 m n p = 0 ↔ ∀ g : _root_.GD.N0232.N0720.N1482.d015118, _root_.GD.N0232.N0720.N1159.d014642 m n g p hp = p := by
  rw [_root_.GD.N0034.N0287.d021579 m n p hp]
  exact ⟨fun h => _root_.GD.N0232.N0720.N1482.d015167 p hp h.1 h.2,
    fun h => ⟨h _, h _⟩⟩

theorem d021581 (p : _root_.GD.N0034.N0287.d021568 m n) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    0 < _root_.GD.N0034.N0287.d021571 m n p ↔
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp ≠ p ∨
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp ≠ p := by
  constructor
  · intro h
    exact not_and_or.mp (fun hf => h.ne' ((_root_.GD.N0034.N0287.d021579 m n p hp).mpr hf))
  · intro h
    exact lt_of_le_of_ne (_root_.GD.N0034.N0287.d021575 m n p)
      (fun hz => (not_and_or.mpr h) ((_root_.GD.N0034.N0287.d021579 m n p hp).mp hz.symm))

theorem d021582 (p : _root_.GD.N0034.N0287.d021568 m n) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0034.N0287.d021571 m n p = ∫ z,
      (_root_.GD.N0034.N0287.d021569 m n _root_.GD.N0232.N0720.N1482.d015130 p z) ^ 2 +
      (_root_.GD.N0034.N0287.d021569 m n _root_.GD.N0232.N0720.N1482.d015131 p z) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
  symm
  exact integral_add
    ((memLp_two_iff_integrable_sq (_root_.GD.N0034.N0287.d021573 m n _ p hp).aestronglyMeasurable).mp
      (_root_.GD.N0034.N0287.d021573 m n _ p hp))
    ((memLp_two_iff_integrable_sq (_root_.GD.N0034.N0287.d021573 m n _ p hp).aestronglyMeasurable).mp
      (_root_.GD.N0034.N0287.d021573 m n _ p hp))

end
end GD.N0034.N0287

#print axioms _root_.GD.N0034.N0287.d021580
#print axioms _root_.GD.N0034.N0287.d021581
#print axioms _root_.GD.N0034.N0287.d021582
