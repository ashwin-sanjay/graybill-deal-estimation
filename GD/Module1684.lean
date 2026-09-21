import GD.Module1683







set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0101.N0404
noncomputable section

open _root_.GD.N0213.N0508
open _root_.GD.N0213.N0509
open _root_.GD.N0213.N0522
open _root_.GD.N0101.N0357 _root_.GD.N0101.N0403

variable {k : ℕ}

theorem d028451 (a : Fin k → ℝ) (S : Set (Fin k → ℝ)) :
    _root_.GD.N0213.N0508.d028429 a S = 0 ↔ volume (_root_.GD.N0101.N0357.d023158 ∩ S) = 0 := by
  rw [_root_.GD.N0213.N0508.d028429, withDensity_apply_eq_zero
    ((_root_.GD.N0213.N0509.d023110 a).pow_const 2).ennreal_ofReal, _root_.GD.N0213.N0522.d008028]
  have heq : {β : Fin k → ℝ | ∀ i, 0 < β i} ∩
      ({β | ENNReal.ofReal (_root_.GD.N0213.N0509.d023108 a β ^ 2) ≠ 0} ∩ S) = _root_.GD.N0101.N0357.d023158 ∩ S := by
    ext β
    constructor
    · intro hβ
      exact ⟨hβ.1, hβ.2.2⟩
    · intro hβ
      refine ⟨hβ.1, ?_, hβ.2⟩
      exact ne_of_gt (ENNReal.ofReal_pos.mpr
        (sq_pos_of_pos (_root_.GD.N0213.N0509.d023112 a β hβ.1).1))
  rw [heq]

theorem d028452 (a : Fin k → ℝ) {S : Set (Fin k → ℝ)}
    (hSpos : S ⊆ _root_.GD.N0101.N0357.d023158) (hvol : 0 < volume S) : 0 < _root_.GD.N0213.N0508.d028429 a S := by
  apply pos_iff_ne_zero.mpr
  rw [ne_eq, _root_.GD.N0101.N0404.d028451, inter_eq_right.mpr hSpos]
  exact hvol.ne'



theorem d028453 (a : Fin k → ℝ) (h : (Fin k → ℝ) → ℝ)
    {S : Set (Fin k → ℝ)} (hS : MeasurableSet S) (hone : ∀ β ∈ S, h β = 1) :
    (_root_.GD.N0101.N0403.d028436 a h).restrict S = (_root_.GD.N0213.N0508.d028429 a).restrict S := by
  rw [_root_.GD.N0101.N0403.d028436, restrict_withDensity hS]
  calc
    _ = ((_root_.GD.N0213.N0508.d028429 a).restrict S).withDensity 1 := by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem hS] with β hβ
      simp only [hone β hβ, one_pow, ENNReal.ofReal_one, Pi.one_apply]
    _ = _ := withDensity_one

theorem d028454 (a : Fin k → ℝ) (h : (Fin k → ℝ) → ℝ)
    {S : Set (Fin k → ℝ)} (hS : MeasurableSet S) (hone : ∀ β ∈ S, h β = 1) :
    _root_.GD.N0101.N0403.d028436 a h S = _root_.GD.N0213.N0508.d028429 a S := by
  have heq := congrArg (fun μ : Measure (Fin k → ℝ) => μ univ)
    (_root_.GD.N0101.N0404.d028453 a h hS hone)
  simpa only [Measure.restrict_apply_univ] using heq



theorem d028455 (a : Fin k → ℝ) (h : (Fin k → ℝ) → ℝ)
    {S : Set (Fin k → ℝ)} (hS : MeasurableSet S) (hone : ∀ β ∈ S, h β = 1) :
    (_root_.GD.N0213.N0508.d028429 a).restrict S ≤ _root_.GD.N0101.N0403.d028436 a h := by
  rw [← _root_.GD.N0101.N0404.d028453 a h hS hone]
  exact Measure.restrict_le_self

theorem d028456 (a : Fin k → ℝ) (h : (Fin k → ℝ) → ℝ)
    {S : Set (Fin k → ℝ)} (hS : MeasurableSet S) (hone : ∀ β ∈ S, h β = 1)
    (hSpos : S ⊆ _root_.GD.N0101.N0357.d023158) (hvol : 0 < volume S) :
    0 < _root_.GD.N0101.N0403.d028436 a h S := by
  rw [_root_.GD.N0101.N0404.d028454 a h hS hone]
  exact _root_.GD.N0101.N0404.d028452 a hSpos hvol

theorem d028457 (a : Fin k → ℝ) (h : (Fin k → ℝ) → ℝ)
    {S : Set (Fin k → ℝ)} (hS : MeasurableSet S) (hone : ∀ β ∈ S, h β = 1)
    (hSpos : S ⊆ _root_.GD.N0101.N0357.d023158) (hvol : 0 < volume S) :
    0 < _root_.GD.N0101.N0403.d028436 a h univ :=
  (_root_.GD.N0101.N0404.d028456 a h hS hone hSpos hvol).trans_le (measure_mono (subset_univ S))

end
end GD.N0101.N0404

#print axioms _root_.GD.N0101.N0404.d028451
#print axioms _root_.GD.N0101.N0404.d028453
#print axioms _root_.GD.N0101.N0404.d028455
#print axioms _root_.GD.N0101.N0404.d028456
#print axioms _root_.GD.N0101.N0404.d028457
