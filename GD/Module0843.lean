import GD.Module0839

set_option warningAsError true










open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace GD
namespace N0228
namespace N0547
namespace N0797

noncomputable section


def d012874 (rho : ℝ) (z : ℝ × ℝ) : ℝ :=
  Real.sqrt rho * z.1 + Real.sqrt (1 - rho) * z.2

@[fun_prop]
theorem d012875 (rho : ℝ) :
    Measurable (_root_.GD.N0228.N0547.N0797.d012874 rho) := by
  unfold _root_.GD.N0228.N0547.N0797.d012874
  fun_prop



theorem d012876
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (_root_.GD.N0228.N0547.N0797.d012874 rho) =
      gaussianReal 0 1 := by
  let P : Measure (ℝ × ℝ) :=
    (gaussianReal 0 1).prod (gaussianReal 0 1)
  let X : ℝ × ℝ → ℝ := fun z => Real.sqrt rho * z.1
  let Y : ℝ × ℝ → ℝ := fun z => Real.sqrt (1 - rho) * z.2
  have hXY : IndepFun X Y P := by
    exact indepFun_prod
      (X := fun z : ℝ => Real.sqrt rho * z)
      (Y := fun z : ℝ => Real.sqrt (1 - rho) * z)
      (by fun_prop) (by fun_prop)
  have hfst : HasLaw (fun z : ℝ × ℝ => z.1)
      (gaussianReal 0 1) P := by
    exact MeasurePreserving.hasLaw measurePreserving_fst
  have hsnd : HasLaw (fun z : ℝ × ℝ => z.2)
      (gaussianReal 0 1) P := by
    exact MeasurePreserving.hasLaw measurePreserving_snd
  have hX : P.map X =
      gaussianReal 0
        (.mk ((Real.sqrt rho) ^ 2) (sq_nonneg _) * (1 : ℝ≥0)) := by
    simpa only [X, mul_zero] using
      (gaussianReal_const_mul hfst (Real.sqrt rho)).map_eq
  have hY : P.map Y =
      gaussianReal 0
        (.mk ((Real.sqrt (1 - rho)) ^ 2) (sq_nonneg _) * (1 : ℝ≥0)) := by
    simpa only [Y, mul_zero] using
      (gaussianReal_const_mul hsnd (Real.sqrt (1 - rho))).map_eq
  have hsum := gaussianReal_add_gaussianReal_of_indepFun hXY hX hY
  have hfun : X + Y = _root_.GD.N0228.N0547.N0797.d012874 rho := by
    funext z
    rfl
  rw [hfun] at hsum
  have hsqrt0 : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt hrho0
  have hsqrt1 : (Real.sqrt (1 - rho)) ^ 2 = 1 - rho :=
    Real.sq_sqrt (sub_nonneg.mpr hrho1)
  have hvar :
      NNReal.mk rho hrho0 + NNReal.mk (1 - rho) (sub_nonneg.mpr hrho1) = 1 := by
    apply NNReal.eq
    simp only [NNReal.coe_add, NNReal.coe_mk, NNReal.coe_one]
    ring
  simpa only [P, zero_add, hsqrt0, hsqrt1, mul_one, hvar] using hsum

end

end N0797
end N0547
end N0228
end GD

#print axioms _root_.GD.N0228.N0547.N0797.d012876
