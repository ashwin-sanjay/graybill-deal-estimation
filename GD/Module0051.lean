import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.Dirac

















open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace GD
namespace N0230
namespace N0688

noncomputable section


@[ext]
structure d000642 where
  measure : Measure ℝ
  isProbability : IsProbabilityMeasure measure
  memLp_id : MemLp id 2 measure

namespace d000642


local instance (law : _root_.GD.N0230.N0688.d000642) : IsProbabilityMeasure law.measure :=
  law.isProbability


def d000643 (law : _root_.GD.N0230.N0688.d000642) : ℝ :=
  ∫ x, x ∂law.measure


def d000644 (law : _root_.GD.N0230.N0688.d000642) : ℝ :=
  variance id law.measure


def d000645 (law : _root_.GD.N0230.N0688.d000642) (target : ℝ) : ℝ :=
  ∫ x, (x - target) ^ 2 ∂law.measure


def d000646 (decision : ℝ) : _root_.GD.N0230.N0688.d000642 where
  measure := Measure.dirac decision
  isProbability := inferInstance
  memLp_id := by
    apply (memLp_const decision).ae_eq
    exact (MeasureTheory.ae_eq_dirac id).symm

@[simp]
theorem d000647 (decision : ℝ) :
    (_root_.GD.N0230.N0688.d000642.d000646 decision).d000643 = decision := by
  simp [_root_.GD.N0230.N0688.d000642.d000643, _root_.GD.N0230.N0688.d000642.d000646]

@[simp]
theorem d000648 (decision : ℝ) :
    (_root_.GD.N0230.N0688.d000642.d000646 decision).d000644 = 0 := by
  simp [_root_.GD.N0230.N0688.d000642.d000644, _root_.GD.N0230.N0688.d000642.d000646]

@[simp]
theorem d000649 (decision target : ℝ) :
    (_root_.GD.N0230.N0688.d000642.d000646 decision).d000645 target = (decision - target) ^ 2 := by
  simp [_root_.GD.N0230.N0688.d000642.d000645, _root_.GD.N0230.N0688.d000642.d000646]






theorem d000650 (law : _root_.GD.N0230.N0688.d000642) (target : ℝ) :
    law.d000645 target =
      (law.d000643 - target) ^ 2 + law.d000644 := by
  rw [_root_.GD.N0230.N0688.d000642.d000645, _root_.GD.N0230.N0688.d000642.d000644, variance_eq_integral measurable_id.aemeasurable]
  have hcenter :
      ∫ x, (x - law.d000643) ∂law.measure = 0 := by
    calc
      (∫ x, (x - law.d000643) ∂law.measure) =
          (∫ x, x ∂law.measure) -
            ∫ _ : ℝ, law.d000643 ∂law.measure :=
        integral_sub (law.memLp_id.integrable (by norm_num))
          (integrable_const _)
      _ = 0 := by simp [_root_.GD.N0230.N0688.d000642.d000643]
  have hcenter_sq : Integrable (fun x : ℝ => (x - law.d000643) ^ 2)
      law.measure := by
    exact (law.memLp_id.sub (memLp_const law.d000643)).integrable_sq
  have hcenter_linear : Integrable (fun x : ℝ => x - law.d000643)
      law.measure :=
    (law.memLp_id.integrable (by norm_num)).sub (integrable_const _)
  have hrest : Integrable
      (fun x : ℝ =>
        2 * (law.d000643 - target) * (x - law.d000643) +
          (law.d000643 - target) ^ 2) law.measure :=
    (hcenter_linear.const_mul
      (2 * (law.d000643 - target))).add (integrable_const _)
  calc
    (∫ x, (x - target) ^ 2 ∂law.measure) =
        ∫ x,
          ((x - law.d000643) ^ 2 +
            2 * (law.d000643 - target) * (x - law.d000643) +
            (law.d000643 - target) ^ 2) ∂law.measure := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = (∫ x, (x - law.d000643) ^ 2 ∂law.measure) +
          ∫ x,
            (2 * (law.d000643 - target) * (x - law.d000643) +
              (law.d000643 - target) ^ 2) ∂law.measure := by
      have hfun :
          (fun x : ℝ =>
            (x - law.d000643) ^ 2 +
              2 * (law.d000643 - target) * (x - law.d000643) +
              (law.d000643 - target) ^ 2) =
            (fun x : ℝ =>
              (x - law.d000643) ^ 2 +
                (2 * (law.d000643 - target) * (x - law.d000643) +
                  (law.d000643 - target) ^ 2)) := by
        funext x
        ring
      rw [hfun]
      exact integral_add hcenter_sq hrest
    _ = (∫ x, (x - law.d000643) ^ 2 ∂law.measure) +
          (2 * (law.d000643 - target) *
              ∫ x, (x - law.d000643) ∂law.measure +
            (law.d000643 - target) ^ 2) := by
      congr 1
      rw [integral_add
        (hcenter_linear.const_mul (2 * (law.d000643 - target)))
        (integrable_const _), integral_const_mul, integral_const]
      simp
    _ = (law.d000643 - target) ^ 2 +
          (∫ x, (x - law.d000643) ^ 2 ∂law.measure) := by
      rw [hcenter]
      ring


theorem d000651
    (law : _root_.GD.N0230.N0688.d000642) (hzero : law.d000644 = 0) :
    (id : ℝ → ℝ) =ᵐ[law.measure] fun _ => law.d000643 := by
  exact ae_eq_integral_of_variance_eq_zero law.memLp_id hzero





theorem d000652
    (law : _root_.GD.N0230.N0688.d000642) (hzero : law.d000644 = 0) :
    law.measure = Measure.dirac law.d000643 := by
  have hae := _root_.GD.N0230.N0688.d000642.d000651 law hzero
  calc
    law.measure = Measure.map id law.measure := Measure.map_id.symm
    _ = Measure.map (fun _ : ℝ => law.d000643) law.measure :=
      Measure.map_congr hae
    _ = (law.measure Set.univ) • Measure.dirac law.d000643 :=
      Measure.map_const law.measure law.d000643
    _ = Measure.dirac law.d000643 := by simp



theorem d000653
    (law : _root_.GD.N0230.N0688.d000642) (hzero : law.d000644 = 0) :
    law = _root_.GD.N0230.N0688.d000642.d000646 law.d000643 := by
  apply _root_.GD.N0230.N0688.d000642.ext
  exact _root_.GD.N0230.N0688.d000642.d000652 law hzero


theorem d000654 (law : _root_.GD.N0230.N0688.d000642) :
    law.d000644 = 0 ↔ law = _root_.GD.N0230.N0688.d000642.d000646 law.d000643 := by
  constructor
  · exact _root_.GD.N0230.N0688.d000642.d000653 law
  · intro h
    rw [h, _root_.GD.N0230.N0688.d000642.d000648]

end d000642

end

end N0688
end N0230
end GD

#print axioms _root_.GD.N0230.N0688.d000642.d000650
#print axioms _root_.GD.N0230.N0688.d000642.d000652
#print axioms _root_.GD.N0230.N0688.d000642.d000654
