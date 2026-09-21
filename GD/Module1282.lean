import GD.Module0664
import GD.Module1255
import GD.Module1260
import GD.Module0866

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GD.N0212.N0462
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0983 _root_.GD.N0232.N0719.N0982
open _root_.GD.N0232.N0719.N1006
open _root_.GD.N0232.N0720.N1290 (d004131)

noncomputable section
variable {k : ℕ}

theorem d020722 (y r : Fin k → ℝ) (p : _root_.GD.N0232.N0719.N0983.d009709 k) :
    _root_.GD.N0232.N0719.N0983.d009714 y r p = _root_.GD.N0232.N0719.N0987.d020295
      (fun i => (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ)) y r := by
  have hvar : (∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * (y i - _root_.GD.N0232.N0719.N0983.d009713 y p) ^ 2) =
      (∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * y i ^ 2) - _root_.GD.N0232.N0719.N0983.d009713 y p ^ 2 := by
    calc
      _ = ∑ i, ((_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * y i ^ 2 -
        (2 * _root_.GD.N0232.N0719.N0983.d009713 y p) * ((_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * y i) +
        _root_.GD.N0232.N0719.N0983.d009713 y p ^ 2 * (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, _root_.GD.N0232.N0719.N0983.d009712]
        change _ - (2 * _root_.GD.N0232.N0719.N0983.d009713 y p) * _root_.GD.N0232.N0719.N0983.d009713 y p + _root_.GD.N0232.N0719.N0983.d009713 y p ^ 2 * 1 = _
        ring
  unfold _root_.GD.N0232.N0719.N0983.d009714 _root_.GD.N0232.N0719.N0987.d020295
  rw [hvar]
  unfold _root_.GD.N0232.N0719.N0983.d009713
  ring

def d020723 (q : ℝ) (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))
    (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) : ℝ :=
  _root_.GD.N0232.N0719.N0983.d009724 q x.1 x.2 μ

theorem d020724 (q : ℝ) (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))
    (x : _root_.GD.N0232.N0719.N0873.d011295 (Fin k)) :
    _root_.GD.N0212.N0462.d020723 q μ x = _root_.GD.N0232.N0719.N0987.d020298 q μ _root_.GD.N0232.N0719.N0983.d009710 x := by
  simp only [_root_.GD.N0212.N0462.d020723, _root_.GD.N0232.N0719.N0983.d009724, _root_.GD.N0232.N0719.N0983.d009723, _root_.GD.N0232.N0719.N0983.d009713, _root_.GD.N0232.N0719.N0983.d009720,
    _root_.GD.N0212.N0462.d020722, _root_.GD.N0232.N0719.N0987.d020298]

theorem d020725 (i : Fin k)
    (x : _root_.GD.N0232.N0720.N1352.d002739) :
    _root_.GD.N0232.N0719.N0982.d020335 i x = _root_.GD.N0232.N0719.N0987.d020296 i x := by
  ext j <;> simp [_root_.GD.N0232.N0719.N0987.d020296, _root_.GD.N0232.N0719.N0987.d020293]




theorem d020726 (hk : 3 ≤ k) (D : ℕ)
    (hD : 3 / 2 ≤ (D : ℝ) / 2)
    (μ : ProbabilityMeasure (_root_.GD.N0232.N0719.N0983.d009709 k))
    (hceiling : ∀ i : Fin k, ∀ c : ℝ, c < 1 →
      ¬ (∀ᵐ z : _root_.GD.N0232.N0720.N1290.d004131 ∂_root_.GD.N0232.N0719.N1006.d013356 (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) _root_.GD.N0232.N0719.N0983.d009710 i,
        (z : ℝ) ≤ c)) :
    ¬ Nonempty (_root_.GD.N0232.N0719.N0982.d020351 (D + 1)
      (_root_.GD.N0212.N0462.d020723 ((D : ℝ) / 2) (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)))) := by
  rintro ⟨m⟩
  have ht (i : Fin k) : Measurable (_root_.GD.N0232.N0719.N0983.d009710 i) := (_root_.GD.N0232.N0719.N0983.d009711 i).measurable
  have hsum : ∀ᵐ p ∂(μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)), ∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) = 1 :=
    ae_of_all _ _root_.GD.N0232.N0719.N0983.d009712
  apply _root_.GD.N0232.N0719.N1006.d013360 (by simpa using hk)
    ((D : ℝ) / 2) hD (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) _root_.GD.N0232.N0719.N0983.d009710 ht hsum _ hceiling
  intro i
  letI := _root_.GD.N0232.N0719.N1006.d013357 (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) _root_.GD.N0232.N0719.N0983.d009710 ht i
  apply _root_.GD.N0232.N0719.N0982.d020354 D m i
  intro x hx
  rw [_root_.GD.N0212.N0462.d020724, _root_.GD.N0212.N0462.d020725]
  exact _root_.GD.N0232.N0719.N0987.d020301 D
    (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) _root_.GD.N0232.N0719.N0983.d009710 ht hsum i hx

end
end GD.N0212.N0462

#print axioms _root_.GD.N0212.N0462.d020726
