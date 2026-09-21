import GD.Module0757
import GD.Module1260

set_option autoImplicit false
set_option warningAsError true












open MeasureTheory Set
open scoped Topology BigOperators ContDiff

namespace GD.N0232.N0719.N0993

open _root_.GD.N0232.N0719.N0873
open _root_.GD.N0232.N0719.N0989 (d011338 d011346 d011361 d011345)
open _root_.GD.N0232.N0719.N0994 _root_.GD.N0232.N0719.N0995
open _root_.GD.N0232.N0719.N0983 (d009709)
open _root_.GD.N0232.N0720.N1377 (d002861)

noncomputable section
variable {k : ℕ}

def d020540 (n : ℕ) (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) : ℝ :=
  _root_.GD.N0232.N0719.N0995.d011389 (n + 1) 0 (fun _ => 1) nu x

def d020541 (n : ℕ) (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) : ℝ :=
  _root_.GD.N0232.N0719.N0995.d011389 n 1 (fun _ => 1) nu x

theorem d020542 (n : ℕ) (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) [IsProbabilityMeasure nu]
    (hnu : _root_.GD.N0232.N0719.N0994.d011375 nu) {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)} (hx : x ∈ _root_.GD.N0232.N0719.N0989.d011338) :
    0 < _root_.GD.N0232.N0719.N0993.d020540 n nu x := by
  have hp (p : _root_.GD.N0232.N0719.N0994.d011371 k) : 0 < _root_.GD.N0232.N0719.N0994.d011381 (n + 1) 0 (fun _ => 1) x p := by
    simpa only [_root_.GD.N0232.N0719.N0994.d011381, pow_zero, mul_one, one_mul, _root_.GD.N0232.N0719.N0989.d011346] using
      _root_.GD.N0232.N0720.N1377.d002861 (n + 1)
        (_root_.GD.N0232.N0719.N0989.d011345 _ (_root_.GD.N0232.N0719.N0994.d011373 p.2) (_root_.GD.N0232.N0719.N0994.d011374 p.2) hx) _
  have hi := _root_.GD.N0232.N0719.N0994.d011384 (n + 1) 0 (phi := fun _ => 1)
    continuous_const nu hnu hx
  have hs : Function.support (_root_.GD.N0232.N0719.N0994.d011381 (n + 1) 0 (fun _ => 1) x) = univ := by
    ext p
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (hp p).ne'
  apply (integral_pos_iff_support_of_nonneg (fun p => (hp p).le) hi).2
  rw [hs, measure_univ]
  exact zero_lt_one

theorem d020543 (n : ℕ) (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k))
    (hnu : _root_.GD.N0232.N0719.N0994.d011375 nu) {x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)} (hx : x ∈ _root_.GD.N0232.N0719.N0989.d011338) (i : Fin k) :
    fderiv ℝ (_root_.GD.N0232.N0719.N0993.d020541 n nu) x (_root_.GD.N0232.N0719.N0873.d011297 i) =
      x.1 i * fderiv ℝ (_root_.GD.N0232.N0719.N0993.d020540 n nu) x (_root_.GD.N0232.N0719.N0873.d011297 i) -
        fderiv ℝ (_root_.GD.N0232.N0719.N0993.d020540 n nu) x (_root_.GD.N0232.N0719.N0873.d011296 i) := by
  change fderiv ℝ (_root_.GD.N0232.N0719.N0995.d011389 n 1 (fun _ => 1) nu) x (_root_.GD.N0232.N0719.N0873.d011297 i) =
    x.1 i * fderiv ℝ (_root_.GD.N0232.N0719.N0995.d011389 (n + 1) 0 (fun _ => 1) nu) x (_root_.GD.N0232.N0719.N0873.d011297 i) -
      fderiv ℝ (_root_.GD.N0232.N0719.N0995.d011389 (n + 1) 0 (fun _ => 1) nu) x (_root_.GD.N0232.N0719.N0873.d011296 i)
  rw [(_root_.GD.N0232.N0719.N0995.d011395 (n + 1) 0 continuous_const nu hnu hx).fderiv,
    (_root_.GD.N0232.N0719.N0995.d011395 n 1 continuous_const nu hnu hx).fderiv]
  simp [_root_.GD.N0232.N0719.N0995.d011390, _root_.GD.N0232.N0719.N0995.d011387, _root_.GD.N0232.N0719.N0873.d011296, _root_.GD.N0232.N0719.N0873.d011297, _root_.GD.N0232.N0719.N0873.d011298, _root_.GD.N0232.N0719.N0873.d011299,
    Pi.single_apply, smul_eq_mul, Nat.add_assoc, Finset.sum_add_distrib]
  ring

theorem d020544 (n m : ℕ) (phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ)
    (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) (p : _root_.GD.N0232.N0719.N0994.d011371 k) {a : ℝ} (ha : 0 < a) :
    _root_.GD.N0232.N0719.N0994.d011381 n m phi (_root_.GD.N0232.N0719.N0982.d020345 x a) p =
      (a ^ (n + 1))⁻¹ * _root_.GD.N0232.N0719.N0994.d011381 n m phi x p := by
  change p.1 ^ m * phi p.2 * _root_.GD.N0232.N0719.N0989.d011346 n p.1 (_root_.GD.N0232.N0719.N0994.d011372 p.2)
    (_root_.GD.N0232.N0719.N0989.d011358 a x) = _
  rw [_root_.GD.N0232.N0719.N0989.d011361 _ _ _ ha]
  unfold _root_.GD.N0232.N0719.N0994.d011381
  ring

theorem d020545 (n m : ℕ) (phi : _root_.GD.N0232.N0719.N0983.d009709 k → ℝ)
    (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) {a : ℝ} (ha : 0 < a) :
    _root_.GD.N0232.N0719.N0995.d011389 n m phi nu (_root_.GD.N0232.N0719.N0982.d020345 x a) =
      (a ^ (n + 1))⁻¹ * _root_.GD.N0232.N0719.N0995.d011389 n m phi nu x := by
  unfold _root_.GD.N0232.N0719.N0995.d011389
  simp_rw [_root_.GD.N0232.N0719.N0993.d020544 n m phi x _ ha]
  exact integral_const_mul _ _



def d020546 (n : ℕ) (nu : ProbabilityMeasure (_root_.GD.N0232.N0719.N0994.d011371 k))
    (hnu : _root_.GD.N0232.N0719.N0994.d011375 (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k))) :
    _root_.GD.N0232.N0719.N0982.d020351 (n + 2)
      (fun x => _root_.GD.N0232.N0719.N0993.d020541 n (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) x /
        _root_.GD.N0232.N0719.N0993.d020540 n (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) x) where
  M := _root_.GD.N0232.N0719.N0993.d020540 n (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k))
  N := _root_.GD.N0232.N0719.N0993.d020541 n (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k))
  smooth_M := _root_.GD.N0232.N0719.N0995.d011396 (n + 1) 0 continuous_const _ hnu
  smooth_N := _root_.GD.N0232.N0719.N0995.d011396 n 1 continuous_const _ hnu
  positive_M := fun _ hx => _root_.GD.N0232.N0719.N0993.d020542 n _ hnu hx
  numerator := fun _ hx => (div_mul_cancel₀ _ (_root_.GD.N0232.N0719.N0993.d020542 n _ hnu hx).ne').symm
  pde := fun _ hx i => _root_.GD.N0232.N0719.N0993.d020543 n _ hnu hx i
  homogeneous := by
    intro x hx a ha
    change a ^ (n + 2) * _root_.GD.N0232.N0719.N0995.d011389 (n + 1) 0 (fun _ => 1)
      (nu : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) (_root_.GD.N0232.N0719.N0982.d020345 x a) = _
    rw [_root_.GD.N0232.N0719.N0993.d020545 _ _ _ _ _ ha]
    simp only [Nat.add_assoc]
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero (n + 2) ha.ne'), one_mul]
    rfl

end
end GD.N0232.N0719.N0993

#print axioms _root_.GD.N0232.N0719.N0993.d020543
#print axioms _root_.GD.N0232.N0719.N0993.d020546
