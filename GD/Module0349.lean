import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic





















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1533
noncomputable section

open MeasureTheory Set Filter Topology Complex Metric
open scoped Topology

def d005163 (d : ℝ) : Set ℂ := {z : ℂ | |z.im| < d}

def d005164 (d : ℝ) : Set ℂ := {z : ℂ | |z.im| ≤ d}

def d005165 (T : ℝ) (u : ℝ → ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Icc (-T) T, u t * f ((t : ℂ) + z)

def d005166 (T : ℝ) (u : ℝ → ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Icc (-T) T, u t * deriv f ((t : ℂ) + z)

theorem d005167 (d : ℝ) : IsOpen (_root_.GD.N0106.N0428.N0765.N1533.d005163 d) :=
  isOpen_lt Complex.continuous_im.abs continuous_const

theorem d005168 (d : ℝ) : IsClosed (_root_.GD.N0106.N0428.N0765.N1533.d005164 d) :=
  isClosed_le Complex.continuous_im.abs continuous_const

theorem d005169 (d : ℝ) :
    closure (_root_.GD.N0106.N0428.N0765.N1533.d005163 d) ⊆ _root_.GD.N0106.N0428.N0765.N1533.d005164 d := by
  apply closure_minimal _ (_root_.GD.N0106.N0428.N0765.N1533.d005168 d)
  intro z hz
  exact (show |z.im| < d from hz).le

theorem d005170 {f : ℂ → ℂ} {d : ℝ}
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d)) {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d) :
    Continuous (fun t : ℝ => f ((t : ℂ) + z)) := by
  apply hc.comp_continuous (by fun_prop : Continuous (fun t : ℝ => (t : ℂ) + z))
  intro t
  simpa only [_root_.GD.N0106.N0428.N0765.N1533.d005164, mem_setOf_eq, Complex.add_im, Complex.ofReal_im,
    zero_add] using hz

theorem d005171 {f : ℂ → ℂ} {d : ℝ}
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d)) (t : ℝ) :
    ContinuousOn (fun z : ℂ => f ((t : ℂ) + z)) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d) := by
  apply hc.comp (continuous_const.add continuous_id).continuousOn
  intro z hz
  change |((t : ℂ) + z).im| ≤ d
  simpa only [_root_.GD.N0106.N0428.N0765.N1533.d005164, mem_setOf_eq, Complex.add_im, Complex.ofReal_im,
    zero_add] using hz

theorem d005172 {f : ℂ → ℂ} {u : ℝ → ℂ} {d M : ℝ}
    (hu : ∀ t : ℝ, ‖u t‖ ≤ 1)
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d) (t : ℝ) :
    ‖u t * f ((t : ℂ) + z)‖ ≤ M := by
  have htz : (t : ℂ) + z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d := by
    simpa only [_root_.GD.N0106.N0428.N0765.N1533.d005164, mem_setOf_eq, Complex.add_im, Complex.ofReal_im,
      zero_add] using hz
  calc
    _ = ‖u t‖ * ‖f ((t : ℂ) + z)‖ := norm_mul _ _
    _ ≤ 1 * ‖f ((t : ℂ) + z)‖ :=
      mul_le_mul_of_nonneg_right (hu t) (norm_nonneg _)
    _ = ‖f ((t : ℂ) + z)‖ := one_mul _
    _ ≤ M := hM _ htz

theorem d005173 {f : ℂ → ℂ} {u : ℝ → ℂ} {d M T : ℝ}
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d)) (hu : Measurable u)
    (hunorm : ∀ t : ℝ, ‖u t‖ ≤ 1)
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d) :
    Integrable (fun t : ℝ => u t * f ((t : ℂ) + z))
      (volume.restrict (Icc (-T) T)) := by
  refine Integrable.mono' (integrable_const M)
    (hu.aestronglyMeasurable.mul (_root_.GD.N0106.N0428.N0765.N1533.d005170 hc hz).aestronglyMeasurable) ?_
  exact ae_of_all _ (_root_.GD.N0106.N0428.N0765.N1533.d005172 hunorm hM hz)


theorem d005174 {f : ℂ → ℂ} {u : ℝ → ℂ} {d M T : ℝ}
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d)) (hu : Measurable u)
    (hunorm : ∀ t : ℝ, ‖u t‖ ≤ 1)
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖f z‖ ≤ M) :
    ContinuousOn (_root_.GD.N0106.N0428.N0765.N1533.d005165 T u f) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d) := by
  apply continuousOn_of_dominated (μ := volume.restrict (Icc (-T) T))
    (bound := fun _ : ℝ => M)
  · intro z hz
    exact hu.aestronglyMeasurable.mul
      (_root_.GD.N0106.N0428.N0765.N1533.d005170 hc hz).aestronglyMeasurable
  · intro z hz
    exact ae_of_all _ (_root_.GD.N0106.N0428.N0765.N1533.d005172 hunorm hM hz)
  · exact integrable_const M
  · apply ae_of_all
    intro t
    exact continuousOn_const.mul (_root_.GD.N0106.N0428.N0765.N1533.d005171 hc t)


theorem d005175 {f : ℂ → ℂ} {u : ℝ → ℂ} {d M T : ℝ}
    (hT : 0 ≤ T) (hunorm : ∀ t : ℝ, ‖u t‖ ≤ 1)
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d) : ‖_root_.GD.N0106.N0428.N0765.N1533.d005165 T u f z‖ ≤ 2 * T * M := by
  have hb : ‖_root_.GD.N0106.N0428.N0765.N1533.d005165 T u f z‖ ≤ M * volume.real (Icc (-T) T) :=
    norm_setIntegral_le_of_norm_le_const_ae (by simp)
      (ae_of_all _ (_root_.GD.N0106.N0428.N0765.N1533.d005172 hunorm hM hz))
  rw [Real.volume_real_Icc_of_le (by linarith : -T ≤ T)] at hb
  calc
    _ ≤ M * (T - -T) := hb
    _ = 2 * T * M := by ring



theorem d005176 {f : ℂ → ℂ} {u : ℝ → ℂ} {T : ℝ}
    (hu : Measurable u) (hunorm : ∀ t : ℝ, ‖u t‖ ≤ 1)
    {z : ℂ} (hf : Integrable (fun t : ℝ => f ((t : ℂ) + z))) :
    ‖_root_.GD.N0106.N0428.N0765.N1533.d005165 T u f z‖ ≤ ∫ t : ℝ, ‖f ((t : ℂ) + z)‖ := by
  have hfr : Integrable (fun t : ℝ => f ((t : ℂ) + z))
      (volume.restrict (Icc (-T) T)) := hf.integrableOn
  have hle : ∀ t : ℝ, ‖u t * f ((t : ℂ) + z)‖ ≤ ‖f ((t : ℂ) + z)‖ := by
    intro t
    calc
      _ = ‖u t‖ * ‖f ((t : ℂ) + z)‖ := norm_mul _ _
      _ ≤ 1 * ‖f ((t : ℂ) + z)‖ :=
        mul_le_mul_of_nonneg_right (hunorm t) (norm_nonneg _)
      _ = _ := one_mul _
  have hprod : Integrable (fun t : ℝ => u t * f ((t : ℂ) + z))
      (volume.restrict (Icc (-T) T)) :=
    Integrable.mono' hfr.norm (hu.aestronglyMeasurable.mul hfr.aestronglyMeasurable)
      (ae_of_all _ hle)
  calc
    _ ≤ ∫ t : ℝ in Icc (-T) T, ‖u t * f ((t : ℂ) + z)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Icc (-T) T, ‖f ((t : ℂ) + z)‖ :=
      integral_mono_ae hprod.norm hfr.norm (ae_of_all _ hle)
    _ ≤ ∫ t : ℝ, ‖f ((t : ℂ) + z)‖ :=
      integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ (fun t => norm_nonneg (f ((t : ℂ) + z)))) hf.norm




theorem d005177 {f : ℂ → ℂ} {d T : ℝ}
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    {z₀ : ℂ} (hz₀ : z₀ ∈ _root_.GD.N0106.N0428.N0765.N1533.d005163 d) :
    ∃ r : ℝ, 0 < r ∧ closedBall z₀ r ⊆ _root_.GD.N0106.N0428.N0765.N1533.d005163 d ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (-T) T, ∀ z ∈ closedBall z₀ r,
        ‖deriv f ((t : ℂ) + z)‖ ≤ B := by
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp
    ((_root_.GD.N0106.N0428.N0765.N1533.d005167 d).mem_nhds hz₀)
  let K : Set ℂ := (fun p : ℝ × ℂ => (p.1 : ℂ) + p.2) ''
    (Icc (-T) T ×ˢ closedBall z₀ r)
  have hK : IsCompact K :=
    (isCompact_Icc.prod (isCompact_closedBall z₀ r)).image (by fun_prop)
  have hsubset : K ⊆ _root_.GD.N0106.N0428.N0765.N1533.d005163 d := by
    rintro z ⟨⟨t, w⟩, htw, rfl⟩
    have hw := hball htw.2
    simpa only [_root_.GD.N0106.N0428.N0765.N1533.d005163, mem_setOf_eq, Complex.add_im, Complex.ofReal_im,
      zero_add] using hw
  have hdc : ContinuousOn (deriv f) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d) :=
    (hf.deriv (_root_.GD.N0106.N0428.N0765.N1533.d005167 d)).continuousOn
  obtain ⟨B, hB⟩ := hK.bddAbove_image (hdc.norm.mono hsubset)
  refine ⟨r, hr, hball, max B 0, le_max_right _ _, ?_⟩
  intro t ht z hz
  have htz : (t : ℂ) + z ∈ K := ⟨(t, z), ⟨ht, hz⟩, rfl⟩
  exact (hB ⟨(t : ℂ) + z, htz, rfl⟩).trans (le_max_left _ _)

theorem d005178 {f : ℂ → ℂ} {d : ℝ}
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    {z : ℂ} (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005163 d) :
    Continuous (fun t : ℝ => deriv f ((t : ℂ) + z)) := by
  apply (hf.deriv (_root_.GD.N0106.N0428.N0765.N1533.d005167 d)).continuousOn.comp_continuous
    (by fun_prop : Continuous (fun t : ℝ => (t : ℂ) + z))
  intro t
  simpa only [_root_.GD.N0106.N0428.N0765.N1533.d005163, mem_setOf_eq, Complex.add_im, Complex.ofReal_im,
    zero_add] using hz



theorem d005179 {f : ℂ → ℂ} {u : ℝ → ℂ} {d M T : ℝ}
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hu : Measurable u) (hunorm : ∀ t : ℝ, ‖u t‖ ≤ 1)
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖f z‖ ≤ M)
    {z₀ : ℂ} (hz₀ : z₀ ∈ _root_.GD.N0106.N0428.N0765.N1533.d005163 d) :
    HasDerivAt (_root_.GD.N0106.N0428.N0765.N1533.d005165 T u f) (_root_.GD.N0106.N0428.N0765.N1533.d005166 T u f z₀) z₀ := by
  obtain ⟨r, hr, hball, B, _hB, hB⟩ := _root_.GD.N0106.N0428.N0765.N1533.d005177
    (T := T) hf hz₀
  have hzclosed : z₀ ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d := (show |z₀.im| < d from hz₀).le
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Icc (-T) T))
    (F := fun z t => u t * f ((t : ℂ) + z))
    (F' := fun z t => u t * deriv f ((t : ℂ) + z))
    (s := ball z₀ r) (bound := fun _ : ℝ => B)
    (ball_mem_nhds z₀ hr) ?_
    (_root_.GD.N0106.N0428.N0765.N1533.d005173 hc hu hunorm hM hzclosed) ?_ ?_
    (integrable_const B) ?_).2
  · filter_upwards [ball_mem_nhds z₀ hr] with z hz
    have hzstrip : z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d :=
      (show |z.im| < d from hball (ball_subset_closedBall hz)).le
    exact hu.aestronglyMeasurable.mul
      (_root_.GD.N0106.N0428.N0765.N1533.d005170 hc hzstrip).aestronglyMeasurable
  · exact hu.aestronglyMeasurable.mul
      (_root_.GD.N0106.N0428.N0765.N1533.d005178 hf hz₀).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro z hz
    calc
      _ = ‖u t‖ * ‖deriv f ((t : ℂ) + z)‖ := norm_mul _ _
      _ ≤ 1 * ‖deriv f ((t : ℂ) + z)‖ :=
        mul_le_mul_of_nonneg_right (hunorm t) (norm_nonneg _)
      _ = ‖deriv f ((t : ℂ) + z)‖ := one_mul _
      _ ≤ B := hB t ht z (ball_subset_closedBall hz)
  · apply ae_of_all
    intro t z hz
    have hzstrip : z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005163 d := hball (ball_subset_closedBall hz)
    have htz : (t : ℂ) + z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005163 d := by
      simpa only [_root_.GD.N0106.N0428.N0765.N1533.d005163, mem_setOf_eq, Complex.add_im, Complex.ofReal_im,
        zero_add] using hzstrip
    have hfd : DifferentiableAt ℂ f ((t : ℂ) + z) :=
      (hf _ htz).differentiableAt ((_root_.GD.N0106.N0428.N0765.N1533.d005167 d).mem_nhds htz)
    simpa only [mul_one, Function.comp_apply] using
      (hfd.hasDerivAt.comp z ((hasDerivAt_id z).const_add (t : ℂ))).const_mul (u t)

theorem d005180 {f : ℂ → ℂ} {u : ℝ → ℂ} {d M T : ℝ}
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hu : Measurable u) (hunorm : ∀ t : ℝ, ‖u t‖ ≤ 1)
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖f z‖ ≤ M) :
    DifferentiableOn ℂ (_root_.GD.N0106.N0428.N0765.N1533.d005165 T u f) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d) := by
  intro z hz
  exact (_root_.GD.N0106.N0428.N0765.N1533.d005179 hc hf hu hunorm hM hz).differentiableAt.differentiableWithinAt



theorem d005181 {T : ℝ} {u : ℝ → ℂ}
    (hu : ∀ t : ℝ, t ∉ Icc (-T) T → u t = 0) (f : ℂ → ℂ) (z : ℂ) :
    _root_.GD.N0106.N0428.N0765.N1533.d005165 T u f z = ∫ t : ℝ, u t * f ((t : ℂ) + z) := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  rw [hu t ht, zero_mul]



theorem d005182 {f : ℂ → ℂ} {u : ℝ → ℂ} {d M T : ℝ}
    (hT : 0 ≤ T) (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hu : Measurable u) (hunorm : ∀ t : ℝ, ‖u t‖ ≤ 1)
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖f z‖ ≤ M) :
    DiffContOnCl ℂ (_root_.GD.N0106.N0428.N0765.N1533.d005165 T u f) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d) ∧
      BddAbove ((fun z : ℂ => ‖_root_.GD.N0106.N0428.N0765.N1533.d005165 T u f z‖) '' _root_.GD.N0106.N0428.N0765.N1533.d005164 d) ∧
      ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖_root_.GD.N0106.N0428.N0765.N1533.d005165 T u f z‖ ≤ 2 * T * M := by
  have hcG := _root_.GD.N0106.N0428.N0765.N1533.d005174 (T := T) hc hu hunorm hM
  have hdG := _root_.GD.N0106.N0428.N0765.N1533.d005180 (T := T) hc hf hu hunorm hM
  refine ⟨⟨hdG, hcG.mono (_root_.GD.N0106.N0428.N0765.N1533.d005169 d)⟩, ?_, ?_⟩
  · refine ⟨2 * T * M, ?_⟩
    rintro b ⟨z, hz, rfl⟩
    exact _root_.GD.N0106.N0428.N0765.N1533.d005175 hT hunorm hM hz
  · intro z hz
    exact _root_.GD.N0106.N0428.N0765.N1533.d005175 hT hunorm hM hz

end
end GD.N0106.N0428.N0765.N1533

#print axioms _root_.GD.N0106.N0428.N0765.N1533.d005174
#print axioms _root_.GD.N0106.N0428.N0765.N1533.d005176
#print axioms _root_.GD.N0106.N0428.N0765.N1533.d005177
#print axioms _root_.GD.N0106.N0428.N0765.N1533.d005179
#print axioms _root_.GD.N0106.N0428.N0765.N1533.d005182
