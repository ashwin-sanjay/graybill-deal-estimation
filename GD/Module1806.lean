import GD.Module0335
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0005.N0243

open MeasureTheory Matrix
open scoped BigOperators
open _root_.GD.N0233.N0722
open _root_.GD.N0233.N0721

variable {Ω I J : Type*} [MeasurableSpace Ω]
variable [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable section

def d029999 (law : I → Measure Ω) (v : J → Ω → ℝ) : Matrix I J ℝ :=
  fun i j => ∫ ω, v j ω ∂law i

def d030000 (v : J → Ω → ℝ) (x : J → ℝ) (ω : Ω) : ℝ :=
  ∑ j, x j * v j ω

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
theorem d030001
    (law : I → Measure Ω) (v : J → Ω → ℝ)
    (hv : ∀ i j, Integrable (v j) (law i)) (x : J → ℝ) :
    (_root_.GD.N0005.N0243.d029999 law v) *ᵥ x = fun i => ∫ ω, _root_.GD.N0005.N0243.d030000 v x ω ∂law i := by
  funext i
  unfold _root_.GD.N0005.N0243.d029999 _root_.GD.N0005.N0243.d030000 Matrix.mulVec dotProduct
  rw [integral_finsetSum _ (fun j _ => (hv i j).const_mul (x j))]
  simp_rw [integral_const_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
theorem d030002
    (law : I → Measure Ω) (v : J → Ω → ℝ)
    (hv : ∀ i j, Integrable (v j) (law i)) (x : J → ℝ) (target : I → ℝ) :
    (∀ i, ∫ ω, _root_.GD.N0005.N0243.d030000 v x ω ∂law i = target i) ↔
      (_root_.GD.N0005.N0243.d029999 law v) *ᵥ x = target := by
  rw [_root_.GD.N0005.N0243.d030001 law v hv x]
  exact funext_iff.symm

theorem d030003
    (law : I → Measure Ω) (v : J → Ω → ℝ)
    (hv : ∀ i j, Integrable (v j) (law i))
    (hdet : Matrix.det ((_root_.GD.N0005.N0243.d029999 law v).transpose * _root_.GD.N0005.N0243.d029999 law v) ≠ 0)
    (target : I → ℝ) :
    (∃ x : J → ℝ, ∀ i, ∫ ω, _root_.GD.N0005.N0243.d030000 v x ω ∂law i = target i) ↔
      _root_.GD.N0233.N0721.d004998 (_root_.GD.N0005.N0243.d029999 law v) target = 0 := by
  simp_rw [_root_.GD.N0005.N0243.d030002 law v hv]
  exact (_root_.GD.N0233.N0721.d005003 (_root_.GD.N0005.N0243.d029999 law v) hdet target).symm

theorem d030004
    (law : I → Measure Ω) (v : J → Ω → ℝ)
    (hv : ∀ i j, Integrable (v j) (law i))
    (hdet : Matrix.det ((_root_.GD.N0005.N0243.d029999 law v).transpose * _root_.GD.N0005.N0243.d029999 law v) ≠ 0)
    (target : I → ℝ)
    (hpos : 0 < _root_.GD.N0233.N0721.d004998 (_root_.GD.N0005.N0243.d029999 law v) target) :
    ¬ ∃ x : J → ℝ, ∀ i, ∫ ω, _root_.GD.N0005.N0243.d030000 v x ω ∂law i = target i := by
  intro h
  have heq := (_root_.GD.N0005.N0243.d030003 law v hv hdet target).1 h
  exact hpos.ne' heq

end
end GD.N0005.N0243

#print axioms _root_.GD.N0005.N0243.d030001
#print axioms _root_.GD.N0005.N0243.d030003
#print axioms _root_.GD.N0005.N0243.d030004
