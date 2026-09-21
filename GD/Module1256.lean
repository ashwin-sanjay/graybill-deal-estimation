import GD.Module0316
import GD.Module1252












open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace GD.N0232.N0720.N1323

open _root_.GD.N0232.N0720.N1373 _root_.GD.N0232.N0720.N1377
open _root_.GD.N0232.N0720.N1376 _root_.GD.N0232.N0720.N1382
open _root_.GD.N0232.N0720.N1386 _root_.GD.N0232.N0720.N1270
open _root_.GD.N0232.N0720.N1352 _root_.GD.N0232.N0720.N1351

noncomputable section

abbrev d020302 := _root_.GD.N0232.N0720.N1352.d002739

def d020303 (n : ℕ) (ν : Measure _root_.GD.N0232.N0720.N1373.d004629) (x : _root_.GD.N0232.N0720.N1323.d020302) : ℝ :=
  _root_.GD.N0232.N0720.N1386.d004705 (n + 1) 0 (fun _ ↦ 1) ν x

def d020304 (n : ℕ) (ν : Measure _root_.GD.N0232.N0720.N1373.d004629) (x : _root_.GD.N0232.N0720.N1323.d020302) : ℝ :=
  _root_.GD.N0232.N0720.N1386.d004705 n 1 (fun _ ↦ 1) ν x

theorem d020305 (n : ℕ) (ν : Measure _root_.GD.N0232.N0720.N1373.d004629)
    (hν : _root_.GD.N0232.N0720.N1382.d004657 ν) : ContDiffOn ℝ ∞ (_root_.GD.N0232.N0720.N1323.d020303 n ν) _root_.GD.N0232.N0720.N1270.d020224 :=
  _root_.GD.N0232.N0720.N1386.d004713 (n + 1) 0 continuous_const ν hν

theorem d020306 (n : ℕ) (ν : Measure _root_.GD.N0232.N0720.N1373.d004629)
    (hν : _root_.GD.N0232.N0720.N1382.d004657 ν) : ContDiffOn ℝ ∞ (_root_.GD.N0232.N0720.N1323.d020304 n ν) _root_.GD.N0232.N0720.N1270.d020224 :=
  _root_.GD.N0232.N0720.N1386.d004713 n 1 continuous_const ν hν

theorem d020307 (n : ℕ) (ν : Measure _root_.GD.N0232.N0720.N1373.d004629) [IsProbabilityMeasure ν]
    (hν : _root_.GD.N0232.N0720.N1382.d004657 ν) {x : _root_.GD.N0232.N0720.N1323.d020302} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) :
    0 < _root_.GD.N0232.N0720.N1323.d020303 n ν x := by
  have hp (p : _root_.GD.N0232.N0720.N1373.d004629) : 0 < _root_.GD.N0232.N0720.N1382.d004668 (n + 1) 0 (fun _ ↦ 1) x p := by
    simpa only [_root_.GD.N0232.N0720.N1382.d004668, pow_zero, mul_one, one_mul] using
      _root_.GD.N0232.N0720.N1377.d002861 (n + 1) (_root_.GD.N0232.N0720.N1382.d004656 hx p.2) (_root_.GD.N0232.N0720.N1382.d004655 x p.2 * p.1)
  have hi := _root_.GD.N0232.N0720.N1382.d004671 (n + 1) 0 (phi := fun _ ↦ 1)
    continuous_const ν hν hx
  have hs : Function.support (_root_.GD.N0232.N0720.N1382.d004668 (n + 1) 0 (fun _ ↦ 1) x) = univ := by
    ext p
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (hp p).ne'
  apply (integral_pos_iff_support_of_nonneg (fun p ↦ (hp p).le) hi).2
  rw [hs, measure_univ]
  exact zero_lt_one

theorem d020308 (n : ℕ) (ν : Measure _root_.GD.N0232.N0720.N1373.d004629)
    (hν : _root_.GD.N0232.N0720.N1382.d004657 ν) {x : _root_.GD.N0232.N0720.N1323.d020302} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) :
    HasFDerivAt (_root_.GD.N0232.N0720.N1323.d020303 n ν)
      (_root_.GD.N0232.N0720.N1386.d004706 (n + 1) 0 (fun _ ↦ 1) ν x) x :=
  _root_.GD.N0232.N0720.N1386.d004712 (n + 1) 0 continuous_const ν hν hx

theorem d020309 (n : ℕ) (ν : Measure _root_.GD.N0232.N0720.N1373.d004629)
    (hν : _root_.GD.N0232.N0720.N1382.d004657 ν) {x : _root_.GD.N0232.N0720.N1323.d020302} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) :
    HasFDerivAt (_root_.GD.N0232.N0720.N1323.d020304 n ν)
      (_root_.GD.N0232.N0720.N1386.d004706 n 1 (fun _ ↦ 1) ν x) x :=
  _root_.GD.N0232.N0720.N1386.d004712 n 1 continuous_const ν hν hx

theorem d020310 (n : ℕ) (ν : Measure _root_.GD.N0232.N0720.N1373.d004629)
    (hν : _root_.GD.N0232.N0720.N1382.d004657 ν) {x : _root_.GD.N0232.N0720.N1323.d020302} (hx : x ∈ _root_.GD.N0232.N0720.N1270.d020224) :
    fderiv ℝ (_root_.GD.N0232.N0720.N1323.d020304 n ν) x (_root_.GD.N0232.N0720.N1352.d002740 2) =
        x 0 * fderiv ℝ (_root_.GD.N0232.N0720.N1323.d020303 n ν) x (_root_.GD.N0232.N0720.N1352.d002740 2) -
          fderiv ℝ (_root_.GD.N0232.N0720.N1323.d020303 n ν) x (_root_.GD.N0232.N0720.N1352.d002740 0) ∧
      fderiv ℝ (_root_.GD.N0232.N0720.N1323.d020304 n ν) x (_root_.GD.N0232.N0720.N1352.d002740 3) =
        x 1 * fderiv ℝ (_root_.GD.N0232.N0720.N1323.d020303 n ν) x (_root_.GD.N0232.N0720.N1352.d002740 3) -
          fderiv ℝ (_root_.GD.N0232.N0720.N1323.d020303 n ν) x (_root_.GD.N0232.N0720.N1352.d002740 1) := by
  simp only [(_root_.GD.N0232.N0720.N1323.d020308 n ν hν hx).fderiv,
    (_root_.GD.N0232.N0720.N1323.d020309 n ν hν hx).fderiv]
  constructor <;>
    simp [_root_.GD.N0232.N0720.N1386.d004706, _root_.GD.N0232.N0720.N1386.d004702, _root_.GD.N0232.N0720.N1386.d004703,
      _root_.GD.N0232.N0720.N1386.d004697, _root_.GD.N0232.N0720.N1352.d002740, smul_eq_mul, Nat.add_assoc] <;> ring

theorem d020311 (x : _root_.GD.N0232.N0720.N1323.d020302) (a : ℝ) (t : _root_.GD.N0232.N0720.N1373.d004628) :
    _root_.GD.N0232.N0720.N1382.d004654 (_root_.GD.N0232.N0720.N1352.d002795 x a) t = a ^ 2 * _root_.GD.N0232.N0720.N1382.d004654 x t := by
  simp [_root_.GD.N0232.N0720.N1382.d004654, _root_.GD.N0232.N0720.N1376.d002892, _root_.GD.N0232.N0720.N1352.d002795, _root_.GD.N0232.N0720.N1352.d002793, _root_.GD.N0232.N0720.N1352.d002794, _root_.GD.N0232.N0720.N1352.d002740, smul_eq_mul]
  ring

theorem d020312 (x : _root_.GD.N0232.N0720.N1323.d020302) (a : ℝ) (t : _root_.GD.N0232.N0720.N1373.d004628) :
    _root_.GD.N0232.N0720.N1382.d004655 (_root_.GD.N0232.N0720.N1352.d002795 x a) t = a * _root_.GD.N0232.N0720.N1382.d004655 x t := by
  simp [_root_.GD.N0232.N0720.N1382.d004655, _root_.GD.N0232.N0720.N1376.d002893, _root_.GD.N0232.N0720.N1352.d002795, _root_.GD.N0232.N0720.N1352.d002793, _root_.GD.N0232.N0720.N1352.d002794, _root_.GD.N0232.N0720.N1352.d002740, smul_eq_mul]
  ring

theorem d020313 (n m : ℕ) (phi : _root_.GD.N0232.N0720.N1373.d004628 → ℝ)
    (x : _root_.GD.N0232.N0720.N1323.d020302) (p : _root_.GD.N0232.N0720.N1373.d004629) {a : ℝ} (ha : 0 < a) :
    _root_.GD.N0232.N0720.N1382.d004668 n m phi (_root_.GD.N0232.N0720.N1352.d002795 x a) p =
      (a ^ (n + 1))⁻¹ * _root_.GD.N0232.N0720.N1382.d004668 n m phi x p := by
  unfold _root_.GD.N0232.N0720.N1382.d004668
  rw [_root_.GD.N0232.N0720.N1323.d020311, _root_.GD.N0232.N0720.N1323.d020312]
  rw [show a * _root_.GD.N0232.N0720.N1382.d004655 x p.2 * p.1 = a * (_root_.GD.N0232.N0720.N1382.d004655 x p.2 * p.1) by ring]
  rw [_root_.GD.N0232.N0720.N1377.d002866 n (_root_.GD.N0232.N0720.N1382.d004654 x p.2) (_root_.GD.N0232.N0720.N1382.d004655 x p.2 * p.1) ha]
  ring

theorem d020314 (n m : ℕ) (phi : _root_.GD.N0232.N0720.N1373.d004628 → ℝ)
    (ν : Measure _root_.GD.N0232.N0720.N1373.d004629) (x : _root_.GD.N0232.N0720.N1323.d020302) {a : ℝ} (ha : 0 < a) :
    _root_.GD.N0232.N0720.N1386.d004705 n m phi ν (_root_.GD.N0232.N0720.N1352.d002795 x a) =
      (a ^ (n + 1))⁻¹ * _root_.GD.N0232.N0720.N1386.d004705 n m phi ν x := by
  unfold _root_.GD.N0232.N0720.N1386.d004705
  simp_rw [_root_.GD.N0232.N0720.N1323.d020313 n m phi x _ ha]
  exact integral_const_mul _ _

theorem d020315 (n : ℕ) (ν : Measure _root_.GD.N0232.N0720.N1373.d004629) (x : _root_.GD.N0232.N0720.N1323.d020302)
    {a : ℝ} (ha : 0 < a) :
    _root_.GD.N0232.N0720.N1323.d020303 n ν (_root_.GD.N0232.N0720.N1352.d002795 x a) = (a ^ (n + 2))⁻¹ * _root_.GD.N0232.N0720.N1323.d020303 n ν x := by
  simpa only [_root_.GD.N0232.N0720.N1323.d020303, Nat.add_assoc] using
    _root_.GD.N0232.N0720.N1323.d020314 (n + 1) 0 (fun _ ↦ 1) ν x ha

theorem d020316 (n : ℕ) (ν : Measure _root_.GD.N0232.N0720.N1373.d004629) (x : _root_.GD.N0232.N0720.N1323.d020302)
    {a : ℝ} (ha : 0 < a) :
    _root_.GD.N0232.N0720.N1323.d020304 n ν (_root_.GD.N0232.N0720.N1352.d002795 x a) = (a ^ (n + 1))⁻¹ * _root_.GD.N0232.N0720.N1323.d020304 n ν x :=
  _root_.GD.N0232.N0720.N1323.d020314 n 1 (fun _ ↦ 1) ν x ha

def d020317 (n : ℕ)
    (ν : ProbabilityMeasure _root_.GD.N0232.N0720.N1373.d004629) (hν : _root_.GD.N0232.N0720.N1382.d004657 (ν : Measure _root_.GD.N0232.N0720.N1373.d004629))
    {g : _root_.GD.N0232.N0720.N1351.d002812 → ℝ}
    (hpost : ∀ x ∈ _root_.GD.N0232.N0720.N1270.d020224,
      _root_.GD.N0232.N0720.N1323.d020304 n (ν : Measure _root_.GD.N0232.N0720.N1373.d004629) x / _root_.GD.N0232.N0720.N1323.d020303 n (ν : Measure _root_.GD.N0232.N0720.N1373.d004629) x =
        _root_.GD.N0232.N0720.N1352.d002804 (g ∘ _root_.GD.N0232.N0720.N1351.d002814) x) : _root_.GD.N0232.N0720.N1270.d020238 (n + 2) g where
  M := _root_.GD.N0232.N0720.N1323.d020303 n (ν : Measure _root_.GD.N0232.N0720.N1373.d004629)
  N := _root_.GD.N0232.N0720.N1323.d020304 n (ν : Measure _root_.GD.N0232.N0720.N1373.d004629)
  smooth_M := _root_.GD.N0232.N0720.N1323.d020305 n _ hν
  positive_M := fun _ hx ↦ _root_.GD.N0232.N0720.N1323.d020307 n _ hν hx
  numerator := fun x hx ↦ (div_eq_iff (_root_.GD.N0232.N0720.N1323.d020307 n _ hν hx).ne').1 (hpost x hx)
  pde := fun _ hx ↦ _root_.GD.N0232.N0720.N1323.d020310 n _ hν hx
  homogeneous := by
    intro x _ a ha
    rw [_root_.GD.N0232.N0720.N1323.d020315 n _ x ha, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero (n + 2) ha.ne'), one_mul]

end
end GD.N0232.N0720.N1323

#print axioms _root_.GD.N0232.N0720.N1323.d020310
#print axioms _root_.GD.N0232.N0720.N1323.d020315
#print axioms _root_.GD.N0232.N0720.N1323.d020317
