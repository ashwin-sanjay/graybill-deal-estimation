import GD.Module1469
import GD.Module1680

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace GD.N0213.N0508
noncomputable section
open _root_.GD.N0213.N0509 _root_.GD.N0213.N0516 _root_.GD.N0213.N0522

variable {k : ℕ}

def d028429 (a : Fin k → ℝ) : Measure (Fin k → ℝ) :=
  (_root_.GD.N0213.N0522.d008020 (fun _ : Fin k => 1)).withDensity (fun β => ENNReal.ofReal (_root_.GD.N0213.N0509.d023108 a β ^ 2))

def d028430 (a t : Fin k → ℝ) : Measure (Fin k → ℝ) :=
  (_root_.GD.N0213.N0516.d028412 a 0 t).withDensity (fun β => ENNReal.ofReal (_root_.GD.N0213.N0509.d023108 a β ^ 2))

theorem d028431 (a : Fin k → ℝ)
    (F : (Fin k → ℝ) → (Fin k → ℝ) → ℝ≥0∞)
    (hF : Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) => F z.1 z.2)) :
    Measurable (fun β => ∫⁻ t, F β t ∂_root_.GD.N0213.N0516.d028411 a β) := by
  have heq (β : Fin k → ℝ) : (∫⁻ t, F β t ∂_root_.GD.N0213.N0516.d028411 a β) =
      ∫⁻ t, _root_.GD.N0213.N0516.d028398 a β t * F β t := by
    rw [_root_.GD.N0213.N0516.d028414, lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (_root_.GD.N0213.N0516.d028398 a β) by fun_prop)
      (show Measurable (fun t => F β t) by fun_prop)]
    rfl
  simp_rw [heq]
  fun_prop

theorem d028432 (a t : Fin k → ℝ)
    (f : (Fin k → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ β, f β ∂_root_.GD.N0213.N0508.d028430 a t) =
      ∫⁻ β, ENNReal.ofReal (_root_.GD.N0213.N0509.d023108 a β ^ 2) * f β ∂_root_.GD.N0213.N0516.d028412 a 0 t := by
  rw [_root_.GD.N0213.N0508.d028430, lintegral_withDensity_eq_lintegral_mul _
    ((_root_.GD.N0213.N0509.d023110 a).pow_const 2).ennreal_ofReal hf]
  rfl



theorem d028433 (a : Fin k → ℝ)
    (ha : ∀ i, 0 < a i)
    (F : (Fin k → ℝ) → (Fin k → ℝ) → ℝ≥0∞)
    (hF : Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) => F z.1 z.2)) :
    (∫⁻ β, ∫⁻ t, F β t ∂_root_.GD.N0213.N0516.d028411 a β ∂_root_.GD.N0213.N0508.d028429 a) =
      ∫⁻ t, ∫⁻ β, F β t ∂_root_.GD.N0213.N0508.d028430 a t ∂_root_.GD.N0213.N0516.d028413 a 0 := by
  have hleft :
      (∫⁻ β, ∫⁻ t, F β t ∂_root_.GD.N0213.N0516.d028411 a β ∂_root_.GD.N0213.N0508.d028429 a) =
        ∫⁻ β, ∫⁻ t, ENNReal.ofReal (_root_.GD.N0213.N0509.d023108 a β ^ 2) * F β t
          ∂_root_.GD.N0213.N0516.d028411 a β ∂_root_.GD.N0213.N0522.d008020 (fun _ : Fin k => 1) := by
    rw [_root_.GD.N0213.N0508.d028429, lintegral_withDensity_eq_lintegral_mul _
      ((_root_.GD.N0213.N0509.d023110 a).pow_const 2).ennreal_ofReal
      (_root_.GD.N0213.N0508.d028431 a F hF)]
    apply lintegral_congr
    intro β
    exact (lintegral_const_mul'' _
      (show Measurable (fun t => F β t) by fun_prop).aemeasurable).symm
  rw [hleft]
  have h := _root_.GD.N0213.N0516.d028416 a 0 ha (by norm_num)
    (fun β t => ENNReal.ofReal (_root_.GD.N0213.N0509.d023108 a β ^ 2) * F β t) (by fun_prop)
  simp only [zero_mul, sub_zero] at h
  rw [h]
  apply lintegral_congr
  intro t
  exact (_root_.GD.N0213.N0508.d028432 a t (fun β => F β t) (by fun_prop)).symm

theorem d028434 (a t : Fin k → ℝ) :
    _root_.GD.N0213.N0508.d028430 a t =
      (Measure.pi fun i => gammaMeasure (a i + 1) (a i * t i)).withDensity
        (fun β => ENNReal.ofReal (_root_.GD.N0213.N0509.d023108 a β ^ 2)) := by
  simp only [_root_.GD.N0213.N0508.d028430, _root_.GD.N0213.N0516.d028412,
    _root_.GD.N0213.N0523.d023144, sub_zero, mul_one]

end
end GD.N0213.N0508

#print axioms _root_.GD.N0213.N0508.d028431
#print axioms _root_.GD.N0213.N0508.d028433
#print axioms _root_.GD.N0213.N0508.d028434
