import GD.Module0410
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

set_option warningAsError true












open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal ProbabilityTheory BoundedContinuousFunction

namespace GD
namespace N0228
namespace N0547
namespace N0788

noncomputable section


def d006356 : Measure ℝ :=
  (1 / 2 : ℝ≥0) • (Measure.dirac (-1 : ℝ) + Measure.dirac (1 : ℝ))


def d006357 (p : ℝ × ℝ) : ℝ :=
  p.1 * Real.sqrt p.2

@[fun_prop]
theorem d006358 : Measurable _root_.GD.N0228.N0547.N0788.d006357 := by
  unfold _root_.GD.N0228.N0547.N0788.d006357
  fun_prop

@[fun_prop]
theorem d006359 : Continuous _root_.GD.N0228.N0547.N0788.d006357 := by
  unfold _root_.GD.N0228.N0547.N0788.d006357
  fun_prop

instance : IsProbabilityMeasure _root_.GD.N0228.N0547.N0788.d006356 := by
  refine ⟨?_⟩
  simpa [_root_.GD.N0228.N0547.N0788.d006356] using ENNReal.inv_two_add_inv_two

private instance :
    IsProbabilityMeasure (_root_.GD.N0121.d006346 1) := by
  unfold _root_.GD.N0121.d006346
  exact isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)

theorem d006360 (f : ℝ → ℝ) :
    (∫ e, f e ∂_root_.GD.N0228.N0547.N0788.d006356) = (f (-1) + f 1) / 2 := by
  have hneg : Integrable f (Measure.dirac (-1 : ℝ)) :=
    integrable_dirac (by simp)
  have hpos : Integrable f (Measure.dirac (1 : ℝ)) :=
    integrable_dirac (by simp)
  rw [_root_.GD.N0228.N0547.N0788.d006356, integral_smul_nnreal_measure,
    integral_add_measure hneg hpos, integral_dirac, integral_dirac]
  norm_num [NNReal.smul_def, div_eq_mul_inv]
  ring

private def d006361 (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  f.compContinuous ⟨Real.sqrt, Real.continuous_sqrt⟩

private def d006362 (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  f.compContinuous ⟨fun z : ℝ => |z|, continuous_abs⟩

private def d006363 (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  f.compContinuous ⟨fun z : ℝ => -|z|, continuous_abs.neg⟩

private def d006364 (f : ℝ →ᵇ ℝ) : ℝ →ᵇ ℝ :=
  f.compContinuous ⟨fun z : ℝ => -z, continuous_neg⟩




theorem d006365 (f : ℝ →ᵇ ℝ) :
    (∫ q, f (Real.sqrt q) ∂_root_.GD.N0121.d006346 1) =
      ∫ z, f |z| ∂gaussianReal 0 1 := by
  calc
    (∫ q, f (Real.sqrt q) ∂_root_.GD.N0121.d006346 1) =
        ∫ q, _root_.GD.N0228.N0547.N0788.d006361 f q ∂_root_.GD.N0121.d006346 1 := rfl
    _ = ∫ q, _root_.GD.N0228.N0547.N0788.d006361 f q
          ∂(gaussianReal 0 1).map (fun z : ℝ => z ^ 2) := by
      rw [_root_.GD.N0121.d006355]
    _ = ∫ z, _root_.GD.N0228.N0547.N0788.d006361 f (z ^ 2) ∂gaussianReal 0 1 := by
      rw [integral_map
        ((by fun_prop : Measurable (fun z : ℝ => z ^ 2)).aemeasurable)
        (_root_.GD.N0228.N0547.N0788.d006361 f).continuous.aestronglyMeasurable]
    _ = ∫ z, f |z| ∂gaussianReal 0 1 := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [_root_.GD.N0228.N0547.N0788.d006361, BoundedContinuousFunction.compContinuous_apply]
      change f (Real.sqrt (z ^ 2)) = f |z|
      rw [Real.sqrt_sq_eq_abs]


theorem d006366 (f : ℝ →ᵇ ℝ) :
    (∫ q, f (-Real.sqrt q) ∂_root_.GD.N0121.d006346 1) =
      ∫ z, f (-|z|) ∂gaussianReal 0 1 := by
  change
    (∫ q, _root_.GD.N0228.N0547.N0788.d006364 f (Real.sqrt q)
      ∂_root_.GD.N0121.d006346 1) =
      ∫ z, _root_.GD.N0228.N0547.N0788.d006364 f |z| ∂gaussianReal 0 1
  exact _root_.GD.N0228.N0547.N0788.d006365 (_root_.GD.N0228.N0547.N0788.d006364 f)

private theorem d006367 (f : ℝ → ℝ) (z : ℝ) :
    f (-|z|) + f |z| = f (-z) + f z := by
  by_cases hz : 0 ≤ z
  · rw [abs_of_nonneg hz]
  · have hz' : z ≤ 0 := le_of_not_ge hz
    simp only [abs_of_nonpos hz', neg_neg, add_comm]


theorem d006368 (f : ℝ →ᵇ ℝ) :
    (∫ z, f (-z) ∂gaussianReal 0 1) = ∫ z, f z ∂gaussianReal 0 1 := by
  calc
    (∫ z, f (-z) ∂gaussianReal 0 1) =
        ∫ z, f z ∂(gaussianReal 0 1).map (fun z : ℝ => -z) := by
      rw [integral_map measurable_neg.aemeasurable
        f.continuous.aestronglyMeasurable]
    _ = ∫ z, f z ∂gaussianReal 0 1 := by
      have hmap : (gaussianReal 0 1).map (fun z : ℝ => -z) =
          gaussianReal 0 1 := by
        simpa using (gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : ℝ≥0)))
      rw [hmap]



theorem d006369 (f : ℝ →ᵇ ℝ) :
    ((∫ z, f (-|z|) ∂gaussianReal 0 1) +
        ∫ z, f |z| ∂gaussianReal 0 1) / 2 =
      ∫ z, f z ∂gaussianReal 0 1 := by
  have hnegAbs : Integrable (_root_.GD.N0228.N0547.N0788.d006363 f) (gaussianReal 0 1) :=
    (_root_.GD.N0228.N0547.N0788.d006363 f).integrable _
  have hAbs : Integrable (_root_.GD.N0228.N0547.N0788.d006362 f) (gaussianReal 0 1) :=
    (_root_.GD.N0228.N0547.N0788.d006362 f).integrable _
  have haddAbs :
      (∫ z, _root_.GD.N0228.N0547.N0788.d006363 f z + _root_.GD.N0228.N0547.N0788.d006362 f z ∂gaussianReal 0 1) =
        (∫ z, _root_.GD.N0228.N0547.N0788.d006363 f z ∂gaussianReal 0 1) +
          ∫ z, _root_.GD.N0228.N0547.N0788.d006362 f z ∂gaussianReal 0 1 :=
    integral_add hnegAbs hAbs
  have hnegInt : Integrable (_root_.GD.N0228.N0547.N0788.d006364 f) (gaussianReal 0 1) :=
    (_root_.GD.N0228.N0547.N0788.d006364 f).integrable _
  have hfInt : Integrable f (gaussianReal 0 1) := f.integrable _
  have haddNeg :
      (∫ z, _root_.GD.N0228.N0547.N0788.d006364 f z + f z ∂gaussianReal 0 1) =
        (∫ z, _root_.GD.N0228.N0547.N0788.d006364 f z ∂gaussianReal 0 1) +
          ∫ z, f z ∂gaussianReal 0 1 :=
    integral_add hnegInt hfInt
  calc
    ((∫ z, f (-|z|) ∂gaussianReal 0 1) +
        ∫ z, f |z| ∂gaussianReal 0 1) / 2 =
        (∫ z, (f (-|z|) + f |z|) ∂gaussianReal 0 1) / 2 := by
      change
        ((∫ z, _root_.GD.N0228.N0547.N0788.d006363 f z ∂gaussianReal 0 1) +
          ∫ z, _root_.GD.N0228.N0547.N0788.d006362 f z ∂gaussianReal 0 1) / 2 =
          (∫ z, _root_.GD.N0228.N0547.N0788.d006363 f z + _root_.GD.N0228.N0547.N0788.d006362 f z
            ∂gaussianReal 0 1) / 2
      exact congrArg (fun x : ℝ => x / 2) haddAbs.symm
    _ = (∫ z, (f (-z) + f z) ∂gaussianReal 0 1) / 2 := by
      congr 1
      apply integral_congr_ae
      filter_upwards with z
      exact _root_.GD.N0228.N0547.N0788.d006367 f z
    _ = ((∫ z, f (-z) ∂gaussianReal 0 1) +
          ∫ z, f z ∂gaussianReal 0 1) / 2 := by
      change
        (∫ z, (_root_.GD.N0228.N0547.N0788.d006364 f z + f z) ∂gaussianReal 0 1) / 2 =
          ((∫ z, _root_.GD.N0228.N0547.N0788.d006364 f z ∂gaussianReal 0 1) +
            ∫ z, f z ∂gaussianReal 0 1) / 2
      exact congrArg (fun x : ℝ => x / 2) haddNeg
    _ = ∫ z, f z ∂gaussianReal 0 1 := by
      rw [_root_.GD.N0228.N0547.N0788.d006368]
      ring



theorem d006370 (f : ℝ →ᵇ ℝ) :
    (∫ p, f (_root_.GD.N0228.N0547.N0788.d006357 p)
        ∂_root_.GD.N0228.N0547.N0788.d006356.prod (_root_.GD.N0121.d006346 1)) =
      ∫ z, f z ∂gaussianReal 0 1 := by
  have hcomp : Integrable (fun p : ℝ × ℝ => f (_root_.GD.N0228.N0547.N0788.d006357 p))
      (_root_.GD.N0228.N0547.N0788.d006356.prod (_root_.GD.N0121.d006346 1)) := by
    let F : (ℝ × ℝ) →ᵇ ℝ :=
      f.compContinuous ⟨_root_.GD.N0228.N0547.N0788.d006357, _root_.GD.N0228.N0547.N0788.d006359⟩
    exact F.integrable _
  rw [integral_prod _ hcomp, _root_.GD.N0228.N0547.N0788.d006360]
  simp only [_root_.GD.N0228.N0547.N0788.d006357, neg_one_mul, one_mul]
  rw [_root_.GD.N0228.N0547.N0788.d006366 f, _root_.GD.N0228.N0547.N0788.d006365 f]
  exact _root_.GD.N0228.N0547.N0788.d006369 f



theorem d006371 :
    (_root_.GD.N0228.N0547.N0788.d006356.prod (_root_.GD.N0121.d006346 1)).map
        _root_.GD.N0228.N0547.N0788.d006357 =
      gaussianReal 0 1 := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map _root_.GD.N0228.N0547.N0788.d006358.aemeasurable
    f.continuous.aestronglyMeasurable]
  exact _root_.GD.N0228.N0547.N0788.d006370 f

end

#print axioms _root_.GD.N0228.N0547.N0788.d006356
#print axioms _root_.GD.N0228.N0547.N0788.d006360
#print axioms _root_.GD.N0228.N0547.N0788.d006370
#print axioms _root_.GD.N0228.N0547.N0788.d006371

end N0788
end N0547
end N0228
end GD
