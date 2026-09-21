import GD.Module0356

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace GD.N0153.N0441

open _root_.GD.N0004.N0241

variable {X : Type*} [MeasurableSpace X]





theorem d006787
    (μ : ℕ → Measure X) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure X) [IsProbabilityMeasure ν]
    {r : X → ℝ} {V ε : ℝ} (hr : Measurable r)
    (h0 : ∀ x, 0 ≤ r x) (hV : ∀ x, r x < V) (hε : 0 < ε)
    (hlim : Tendsto (fun n => ∫ x, r x ∂μ n) atTop (𝓝 V)) :
    ∃ A : Set X, MeasurableSet A ∧ 1 - ε < ν.real A ∧
      Tendsto (fun n => (μ n).real A) atTop (𝓝 0) := by
  let A : ℕ → Set X := fun j => {x | (j + 1 : ℝ)⁻¹ ≤ V - r x}
  have hmeas (j) : MeasurableSet (A j) :=
    measurableSet_le measurable_const (measurable_const.sub hr)
  have hcover : (⋃ j, A j) = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.mpr (hV x))
    exact ⟨j, by simpa only [A, mem_setOf_eq, one_div] using hj.le⟩
  have hmono : Monotone A := by
    intro i j hij x hx
    exact (inv_anti₀ (show (0 : ℝ) < (i : ℝ) + 1 by positivity)
      (show (i : ℝ) + 1 ≤ (j : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right hij 1)).trans hx
  have href : Tendsto (fun j => ν.real (A j)) atTop (𝓝 1) := by
    have h := (ENNReal.tendsto_toReal (measure_ne_top ν (⋃ j, A j))).comp
      (tendsto_measure_iUnion_atTop (μ := ν) hmono)
    simpa only [hcover, measure_univ, ENNReal.toReal_one, Function.comp_def,
      measureReal_def] using h
  obtain ⟨j, hj⟩ := ((tendsto_order.mp href).1 (1 - ε) (by linarith)).exists
  refine ⟨A j, hmeas j, hj, ?_⟩
  exact _root_.GD.N0004.N0241.d005271 μ hr h0 (fun x => (hV x).le)
    (show (0 : ℝ) < (j + 1 : ℝ)⁻¹ by positivity) hlim



theorem d006788
    (μ : ℕ → Measure X) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure X) [IsProbabilityMeasure ν]
    {r : X → ℝ} {V ε : ℝ} (hr : Measurable r)
    (h0 : ∀ x, 0 ≤ r x) (hV : ∀ x, r x < V) (hε : 0 < ε)
    (hlim : Tendsto (fun n => ∫ x, r x ∂μ n) atTop (𝓝 V)) :
    ∃ B : Set X, MeasurableSet B ∧ ν.real B < ε ∧
      Tendsto (fun n => (μ n).real B) atTop (𝓝 1) := by
  obtain ⟨A, hA, hνA, hμA⟩ :=
    _root_.GD.N0153.N0441.d006787 μ ν hr h0 hV hε hlim
  have hνsum := measureReal_add_measureReal_compl (μ := ν) hA
  rw [probReal_univ] at hνsum
  refine ⟨Aᶜ, hA.compl, by linarith, ?_⟩
  have heq (n) : (μ n).real Aᶜ = 1 - (μ n).real A := by
    have h := measureReal_add_measureReal_compl (μ := μ n) hA
    rw [probReal_univ] at h
    linarith
  simp_rw [heq]
  simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hμA



theorem d006789
    (μ : ℕ → Measure X) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure X) [IsProbabilityMeasure ν]
    {r : X → ℝ} {V : ℝ} (hr : Measurable r)
    (h0 : ∀ x, 0 ≤ r x) (hV : ∀ x, r x < V)
    (hlim : Tendsto (fun n => ∫ x, r x ∂μ n) atTop (𝓝 V)) :
    ¬ ∀ A : Set X, MeasurableSet A →
      Tendsto (fun n => (μ n).real A) atTop (𝓝 (ν.real A)) := by
  intro hsetwise
  obtain ⟨A, hA, hνA, hμA⟩ :=
    _root_.GD.N0153.N0441.d006787 μ ν hr h0 hV
      (show (0 : ℝ) < 1 / 2 by norm_num) hlim
  have hz : ν.real A = 0 := tendsto_nhds_unique (hsetwise A hA) hμA
  rw [hz] at hνA
  norm_num at hνA





theorem d006790
    (μ : ℕ → Measure X) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure X) [IsProbabilityMeasure ν]
    {r : X → ℝ} {V ε : ℝ} (hr : Measurable r)
    (h0 : ∀ x, 0 ≤ r x) (hV : ∀ x, r x < V) (hε : 0 < ε)
    (hlim : Tendsto (fun n => ∫ x, r x ∂μ n) atTop (𝓝 V)) :
    ∃ A : Set X, MeasurableSet A ∧
      ∀ᶠ n in atTop, 1 - ε < |(μ n).real A - ν.real A| := by
  obtain ⟨A, hA, hνA, hμA⟩ :=
    _root_.GD.N0153.N0441.d006787 μ ν hr h0 hV
      (half_pos hε) hlim
  refine ⟨A, hA, ?_⟩
  filter_upwards [(tendsto_order.mp hμA).2 (ε / 2) (half_pos hε)] with n hn
  have habs : ν.real A - (μ n).real A ≤ |(μ n).real A - ν.real A| := by
    simpa only [neg_sub] using neg_le_abs ((μ n).real A - ν.real A)
  linarith

end GD.N0153.N0441

#print axioms _root_.GD.N0153.N0441.d006787
#print axioms _root_.GD.N0153.N0441.d006788
#print axioms _root_.GD.N0153.N0441.d006789
#print axioms _root_.GD.N0153.N0441.d006790
