import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace GD.N0004.N0241

variable {X : Type*} [MeasurableSpace X]

theorem d005268 (μ : Measure X) [IsProbabilityMeasure μ]
    {r : X → ℝ} {V : ℝ} (hr : Measurable r)
    (h0 : ∀ x, 0 ≤ r x) (hV : ∀ x, r x ≤ V) : Integrable r μ := by
  apply (integrable_const V).mono' hr.aestronglyMeasurable
  exact Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]; exact hV x

theorem d005269 (μ : Measure X) [IsProbabilityMeasure μ]
    {r : X → ℝ} {V : ℝ} (hr : Measurable r)
    (h0 : ∀ x, 0 ≤ r x) (hV : ∀ x, r x < V) :
    (∫ x, r x ∂μ) < V := by
  have hi := _root_.GD.N0004.N0241.d005268 μ hr h0 (fun x => (hV x).le)
  have hd : Integrable (fun x => V - r x) μ := (integrable_const V).sub hi
  have hp : 0 < ∫ x, V - r x ∂μ := by
    rw [integral_pos_iff_support_of_nonneg (fun x => (sub_pos.mpr (hV x)).le) hd]
    have hs : Function.support (fun x => V - r x) = univ := by
      ext x
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (sub_pos.mpr (hV x)).ne'
    rw [hs, measure_univ]
    norm_num
  rw [integral_sub (integrable_const V) hi, integral_const] at hp
  simpa using (show (∫ x, r x ∂μ) < V by simpa using (sub_pos.mp hp))

theorem d005270 (μ : Measure X) [IsProbabilityMeasure μ]
    {r : X → ℝ} {V ε : ℝ} (hr : Measurable r)
    (h0 : ∀ x, 0 ≤ r x) (hV : ∀ x, r x ≤ V) :
    ε * μ.real {x | ε ≤ V - r x} ≤ V - ∫ x, r x ∂μ := by
  have hi := _root_.GD.N0004.N0241.d005268 μ hr h0 hV
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (Eventually.of_forall fun x => sub_nonneg.mpr (hV x))
    ((integrable_const V).sub hi) ε
  simpa only [integral_sub (integrable_const V) hi, integral_const,
    probReal_univ, one_smul] using hm

theorem d005271
    (μ : ℕ → Measure X) [∀ n, IsProbabilityMeasure (μ n)]
    {r : X → ℝ} {V ε : ℝ} (hr : Measurable r)
    (h0 : ∀ x, 0 ≤ r x) (hV : ∀ x, r x ≤ V) (hε : 0 < ε)
    (hlim : Tendsto (fun n => ∫ x, r x ∂μ n) atTop (𝓝 V)) :
    Tendsto (fun n => (μ n).real {x | ε ≤ V - r x}) atTop (𝓝 0) := by
  have hb (n) : (μ n).real {x | ε ≤ V - r x} ≤
      (V - ∫ x, r x ∂μ n) / ε := by
    apply (le_div_iff₀ hε).mpr
    simpa only [mul_comm] using _root_.GD.N0004.N0241.d005270 (μ n) hr h0 hV (ε := ε)
  have hz : Tendsto (fun n => (V - ∫ x, r x ∂μ n) / ε) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := V)).sub hlim).div_const ε
  exact squeeze_zero (fun n => measureReal_nonneg) hb hz

theorem d005272
    (μ : ℕ → Measure X) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure X) [IsFiniteMeasure ν]
    (hdom : ∀ n, μ n ≤ ν)
    {r : X → ℝ} {V : ℝ} (hr : Measurable r)
    (h0 : ∀ x, 0 ≤ r x) (hV : ∀ x, r x < V) :
    ¬ Tendsto (fun n => ∫ x, r x ∂μ n) atTop (𝓝 V) := by
  intro hlim
  let A : ℕ → Set X := fun j => {x | (j + 1 : ℝ)⁻¹ ≤ V - r x}
  have hm (j) : MeasurableSet (A j) :=
    measurableSet_le measurable_const (measurable_const.sub hr)
  have hcover : (⋃ j, A j) = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr (hV x))
    refine ⟨n, ?_⟩
    dsimp [A]
    exact (by simpa using hn.le)
  have hanti : Antitone (fun j => (A j)ᶜ) := by
    intro i j hij
    apply compl_subset_compl.mpr
    intro x hx
    exact (inv_anti₀ (show (0 : ℝ) < (i : ℝ) + 1 by positivity)
      (show (i : ℝ) + 1 ≤ (j : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right hij 1)).trans hx
  have hempty : (⋂ j, (A j)ᶜ) = ∅ := by rw [← compl_iUnion, hcover, compl_univ]
  have hν : Tendsto (fun j => ν ((A j)ᶜ)) atTop (𝓝 0) := by
    simpa only [hempty, measure_empty, Function.comp_def] using
      (tendsto_measure_iInter_atTop (fun j => (hm j).compl.nullMeasurableSet) hanti
        ⟨0, measure_ne_top _ _⟩)
  obtain ⟨j, hj⟩ := ((tendsto_order.mp hν).2 (1 / 2) (by norm_num)).exists
  have hνj : ν ((A j)ᶜ) < 1 / 2 := hj
  have hμj := _root_.GD.N0004.N0241.d005271 μ hr h0 (fun x => (hV x).le)
    (show (0 : ℝ) < (j + 1 : ℝ)⁻¹ by positivity) hlim
  obtain ⟨n, hn⟩ := ((tendsto_order.mp hμj).2 (1 / 2) (by norm_num)).exists
  have hcompl : (μ n).real ((A j)ᶜ) < 1 / 2 := by
    have he : (μ n).real ((A j)ᶜ) ≤ ν.real ((A j)ᶜ) :=
      ENNReal.toReal_mono (by finiteness) (hdom n ((A j)ᶜ))
    apply he.trans_lt
    have hv := (ENNReal.toReal_lt_toReal (measure_ne_top ν _) (by norm_num :
      (1 / 2 : ℝ≥0∞) ≠ ⊤)).mpr hνj
    simpa only [measureReal_def, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_ofNat] using hv
  have hsum := measureReal_add_measureReal_compl (μ := μ n) (hm j)
  change (μ n).real (A j) < 1 / 2 at hn
  rw [probReal_univ] at hsum
  linarith

end GD.N0004.N0241

#print axioms _root_.GD.N0004.N0241.d005269
#print axioms _root_.GD.N0004.N0241.d005270
#print axioms _root_.GD.N0004.N0241.d005271
#print axioms _root_.GD.N0004.N0241.d005272
