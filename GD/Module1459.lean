import GD.Module1364
import GD.Module1454
import GD.Module1272

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal

namespace GD.N0212.N0472

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0990
open _root_.GD.N0232.N0719.N0991 _root_.GD.N0232.N0719.N0998
open _root_.GD.N0232.N0719.N0996 _root_.GD.N0232.N0719.N0988
open _root_.GD.N0232.N0719.N0896 _root_.GD.N0232.N0719.N0986
open _root_.GD.N0232.N0719.N0983
open _root_.GD.N0213.N0496
open _root_.GD.N0156.N0444 _root_.GD.N0232.N0719.N0981
open _root_.GD.N0232.N0719.N0962

variable {k d : ℕ}

theorem d023045 {I : Type*} [Fintype I]
    (p : I → _root_.GD.N0232.N0719.N0990.d020496 k) (a : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (f : _root_.GD.N0232.N0719.N0990.d020496 k → ℝ) :
    (∫ x, f x ∂(∑ i, ENNReal.ofReal (a i) • Measure.dirac (p i))) =
      ∑ i, a i * f (p i) := by
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (ha i), smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure (by simp)

theorem d023046 {I : Type*} [Fintype I]
    (p : I → _root_.GD.N0232.N0719.N0990.d020496 k) (a : I → ℝ) (f : _root_.GD.N0232.N0719.N0990.d020496 k → ℝ) :
    Integrable f (∑ i, ENNReal.ofReal (a i) • Measure.dirac (p i)) := by
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact (integrable_dirac (by simp)).smul_measure (by simp)

theorem d023047 {I : Type*} [Fintype I]
    (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1)
    (p : I → _root_.GD.N0232.N0719.N0990.d020496 k) (a : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (x : _root_.GD.N0213.N0496.d021972 d) :
    _root_.GD.N0232.N0719.N0991.d020538 sizes hdim (∑ i, ENNReal.ofReal (a i) • Measure.dirac (p i)) x =
      _root_.GD.N0213.N0496.d021984 d p a (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x) := by
  simp only [_root_.GD.N0232.N0719.N0991.d020538, _root_.GD.N0212.N0472.d023045 p a ha, _root_.GD.N0213.N0496.d021984]

variable [NeZero k]




theorem d023048
    (sizes : Fin k → ℕ) (hdim : (∑ i, sizes i) = d + 1)
    (hn : ∀ i, 2 ≤ sizes i) (hd : 1 ≤ d)
    {s : _root_.GD.N0232.N0719.N0997.d019804 sizes → ℝ} (hs : _root_.GD.N0232.N0719.N0896.d011131 k sizes s) :
    ∃ ν : ℕ → ProbabilityMeasure (_root_.GD.N0232.N0719.N0990.d020496 k),
      (∀ beta : ℝ, 0 < beta → beta < 1 / 2 → ∃ B : ℝ, ∀ j,
        Integrable (fun p : _root_.GD.N0232.N0719.N0990.d020496 k => Real.exp (beta * p.1 ^ 2))
          (ν j : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) ∧
        (∫ p, Real.exp (beta * p.1 ^ 2) ∂(ν j : Measure (_root_.GD.N0232.N0719.N0990.d020496 k))) ≤ B) ∧
      (∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)),
        Tendsto (fun j => _root_.GD.N0232.N0719.N0991.d020538 sizes hdim (ν j : Measure (_root_.GD.N0232.N0719.N0990.d020496 k)) x)
          atTop (𝓝 (s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x)))) := by
  have hn0 : ∀ i, 0 < sizes i := fun i => lt_of_lt_of_le (by decide : 0 < 2) (hn i)
  obtain ⟨ell, p, a, ν, ha, hsum, hν, _hpi, hlim⟩ :=
    _root_.GD.N0232.N0719.N0998.d020551 sizes hdim hn0 hs
  obtain ⟨hupper, hlower⟩ := _root_.GD.N0212.N0470.d023017 sizes hdim hn0 hs
  have hatom : ∀ᵐ x ∂(volume : Measure (_root_.GD.N0213.N0496.d021972 d)), Tendsto
      (fun j => _root_.GD.N0213.N0496.d021984 d (p j) (a j) (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x)) atTop
      (𝓝 (s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x))) := by
    simpa only [hν, _root_.GD.N0212.N0472.d023047 sizes hdim _ _ (ha _)] using hlim
  refine ⟨ν, ?_, hlim⟩
  intro beta hbeta hhalf
  obtain ⟨B, hB⟩ := _root_.GD.N0213.N0496.d021999 sizes hdim hn hd p a ha hsum
    (fun x => s ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x)) hatom hupper hlower hbeta.le hhalf
  refine ⟨B, fun j => ?_⟩
  rw [hν j]
  exact ⟨_root_.GD.N0212.N0472.d023046 (p j) (a j) _, by
    rw [_root_.GD.N0212.N0472.d023045 _ _ (ha j)]
    exact hB j⟩

end
end GD.N0212.N0472

#print axioms _root_.GD.N0212.N0472.d023048
