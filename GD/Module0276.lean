import GD.Module0232
import Mathlib.Topology.ContinuousMap.Weierstrass


















open MeasureTheory Set
open scoped BoundedContinuousFunction Polynomial

namespace GD
namespace N0235
namespace N0743

variable {X : Type*}
variable [TopologicalSpace X] [MeasurableSpace X]
variable [OpensMeasurableSpace X] [HasOuterApproxClosed X] [BorelSpace X]



noncomputable def d004067
    (μ : Measure X) [IsFiniteMeasure μ] :
    (X →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ∫ x, f x ∂μ
      map_add' := fun f g ↦ integral_add (f.integrable μ) (g.integrable μ)
      map_smul' := fun c f ↦ by
        simpa only [RingHom.id_apply, BoundedContinuousFunction.coe_smul,
          Pi.smul_apply, smul_eq_mul] using integral_smul c (fun x ↦ f x) }
    (μ.real univ)
    (fun f ↦ f.norm_integral_le_mul_norm μ)

@[simp]
theorem d004068
    (μ : Measure X) [IsFiniteMeasure μ]
    (f : X →ᵇ ℝ) :
    _root_.GD.N0235.N0743.d004067 μ f = ∫ x, f x ∂μ :=
  rfl





theorem d004069
    (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A : Set (X →ᵇ ℝ))
    (hA : Dense A)
    (hEq :
      ∀ f ∈ A,
        ∫ x, f x ∂μ = ∫ x, f x ∂ν) :
    μ = ν := by
  have hfun :
      _root_.GD.N0235.N0743.d004067 μ = _root_.GD.N0235.N0743.d004067 ν := by
    ext f
    exact congr_fun
      (Continuous.ext_on hA
        (_root_.GD.N0235.N0743.d004067 μ).continuous
        (_root_.GD.N0235.N0743.d004067 ν).continuous
        (fun f hf ↦ hEq f hf))
      f
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact congrArg (fun L : (X →ᵇ ℝ) →L[ℝ] ℝ ↦ L f) hfun

section Interval

variable (a b : ℝ)





theorem d004070
    (μ ν : Measure (Set.Icc a b))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hpoly :
      ∀ p : ℝ[X],
        ∫ x, p.eval (x : ℝ) ∂μ =
          ∫ x, p.eval (x : ℝ) ∂ν) :
    μ = ν := by
  let Lμ : C(Set.Icc a b, ℝ) →L[ℝ] ℝ :=
    (_root_.GD.N0235.N0743.d004067 μ).comp
      (ContinuousMap.linearIsometryBoundedOfCompact
        (Set.Icc a b) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let Lν : C(Set.Icc a b, ℝ) →L[ℝ] ℝ :=
    (_root_.GD.N0235.N0743.d004067 ν).comp
      (ContinuousMap.linearIsometryBoundedOfCompact
        (Set.Icc a b) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hA :
      Dense
        ((polynomialFunctions (Set.Icc a b)) :
          Set C(Set.Icc a b, ℝ)) := by
    rw [dense_iff_closure_eq,
      ← Subalgebra.topologicalClosure_coe,
      polynomialFunctions_closure_eq_top]
    rfl
  have hL : Lμ = Lν := by
    ext f
    exact congr_fun
      (Continuous.ext_on hA Lμ.continuous Lν.continuous
        (fun f hf ↦ by
          rw [polynomialFunctions_coe] at hf
          obtain ⟨p, rfl⟩ := hf
          simpa [Lμ, Lν, _root_.GD.N0235.N0743.d004068] using hpoly p))
      f
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let fc : C(Set.Icc a b, ℝ) :=
    (ContinuousMap.linearIsometryBoundedOfCompact
      (Set.Icc a b) ℝ ℝ).symm f
  have hfc := congrArg
    (fun L : C(Set.Icc a b, ℝ) →L[ℝ] ℝ ↦ L fc) hL
  simpa [Lμ, Lν, fc, _root_.GD.N0235.N0743.d004068] using hfc

end Interval

end N0743
end N0235
end GD
