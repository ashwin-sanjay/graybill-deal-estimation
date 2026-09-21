import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure










open scoped BigOperators
open MeasureTheory Set

namespace GD.N0232.N0720







theorem d002619
    {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → E) (hf : Integrable f μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (x : ι → α),
      (∀ i, 0 ≤ w i) ∧
      (∑ i, w i) = 1 ∧
      dist (∑ i, w i • f (x i)) (∫ a, f a ∂μ) < ε := by
  classical
  let C : Set E := closedConvexHull ℝ (Set.range f)
  have hCconvex : Convex ℝ C := convex_closedConvexHull
  have hCclosed : IsClosed C := isClosed_closedConvexHull
  have hfC : ∀ᵐ a ∂μ, f a ∈ C :=
    Filter.Eventually.of_forall fun a ↦
      subset_closedConvexHull (𝕜 := ℝ) (Set.mem_range_self a)
  have hint : (∫ a, f a ∂μ) ∈ C :=
    hCconvex.integral_mem hCclosed hfC hf
  rw [show C = closure (convexHull ℝ (Set.range f)) by
    exact closedConvexHull_eq_closure_convexHull] at hint
  obtain ⟨y, hy, hdist⟩ := (Metric.mem_closure_iff.mp hint) ε hε
  obtain ⟨ι, inst, w, z, hw0, hw1, hz, hsum⟩ :=
    (mem_convexHull_iff_exists_fintype.mp hy)
  letI : Fintype ι := inst
  have hxExists : ∀ i, ∃ a, f a = z i := by
    intro i
    exact hz i
  choose x hx using hxExists
  refine ⟨ι, inferInstance, w, x, hw0, hw1, ?_⟩
  have hpacket : (∑ i, w i • f (x i)) = y := by
    calc
      (∑ i, w i • f (x i)) = ∑ i, w i • z i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hx i]
      _ = y := hsum
  rw [hpacket, dist_comm]
  exact hdist






theorem d002620
    {α E : Type*} [Nonempty α] [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ν : FiniteMeasure α) (hν : ν ≠ 0)
    (f : α → E) (hf : Integrable f (ν : Measure α))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (x : ι → α),
      (∀ i, 0 ≤ w i) ∧
      (∑ i, w i) = (ν.mass : ℝ) ∧
      dist (∑ i, w i • f (x i)) (∫ a, f a ∂(ν : Measure α)) < ε := by
  classical
  have hmass_ne : ν.mass ≠ 0 := ν.mass_nonzero_iff.mpr hν
  have hmass : 0 < (ν.mass : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hmass_ne)
  have hfNormalize : Integrable f (ν.normalize : Measure α) := by
    rw [ν.toMeasure_normalize_eq_of_nonzero hν]
    exact hf.smul_measure_nnreal
  obtain ⟨ι, inst, w, x, hw0, hw1, hdist⟩ :=
    _root_.GD.N0232.N0720.d002619
      (ν.normalize : Measure α) f hfNormalize (div_pos hε hmass)
  letI : Fintype ι := inst
  let W : ι → ℝ := fun i ↦ (ν.mass : ℝ) * w i
  refine ⟨ι, inferInstance, W, x, ?_, ?_, ?_⟩
  · intro i
    exact mul_nonneg hmass.le (hw0 i)
  · simp [W, ← Finset.mul_sum, hw1]
  · have hmeasure : (ν : Measure α) =
        ν.mass • (ν.normalize : Measure α) := by
      have h := congrArg (fun ρ : FiniteMeasure α ↦ (ρ : Measure α))
        ν.self_eq_mass_smul_normalize
      simpa using h
    have hintegral : (∫ a, f a ∂(ν : Measure α)) =
        (ν.mass : ℝ) • (∫ a, f a ∂(ν.normalize : Measure α)) := by
      rw [hmeasure, integral_smul_nnreal_measure, NNReal.smul_def]
    have hpacket : (∑ i, W i • f (x i)) =
        (ν.mass : ℝ) • (∑ i, w i • f (x i)) := by
      simp [W, Finset.smul_sum, mul_smul]
    rw [hpacket, hintegral, dist_smul₀, Real.norm_eq_abs,
      abs_of_pos hmass]
    have := (lt_div_iff₀ hmass).mp hdist
    simpa [mul_comm] using this

end GD.N0232.N0720

#print axioms _root_.GD.N0232.N0720.d002619
#print axioms _root_.GD.N0232.N0720.d002620
