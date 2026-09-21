import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0005.N0245

open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {Ω E Θ : Type*} [MeasurableSpace Ω]

theorem d030050
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (events : ℕ → Set Ω) (hm : ∀ n, MeasurableSet (events n))
    (hescape : ∀ ω, ∀ᶠ n in atTop, ω ∉ events n) :
    Tendsto (fun n => μ (events n)) atTop (𝓝 0) := by
  let tails : ℕ → Set Ω := fun n => ⋃ k, ⋃ (_ : n ≤ k), events k
  have ht : ∀ n, MeasurableSet (tails n) := fun n =>
    MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => hm k
  have hanti : Antitone tails := by
    intro n m hnm ω hω
    obtain ⟨k, hk⟩ := mem_iUnion.1 hω
    obtain ⟨hmk, hωk⟩ := mem_iUnion.1 hk
    exact mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨hnm.trans hmk, hωk⟩⟩
  have hinter : (⋂ n, tails n) = ∅ := by
    apply eq_empty_iff_forall_notMem.2
    intro ω hω
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hescape ω)
    obtain ⟨k, hk⟩ := mem_iUnion.1 (mem_iInter.1 hω N)
    obtain ⟨hNk, hωk⟩ := mem_iUnion.1 hk
    exact hN k hNk hωk
  have htend : Tendsto (fun n => μ (tails n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hinter, measure_empty] using
      tendsto_measure_iInter_atTop (fun n => (ht n).nullMeasurableSet)
        hanti ⟨0, measure_ne_top μ _⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htend
    (fun _ => bot_le) ?_
  intro n
  exact measure_mono (fun ω hω => mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨le_rfl, hω⟩⟩)

theorem d030051
    [SeminormedAddCommGroup E]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (region : Ω → Set E) (target : ℕ → E)
    (hm : ∀ n, MeasurableSet {ω | target n ∈ region ω})
    (hbounded : ∀ ω, Bornology.IsBounded (region ω))
    (htarget : Tendsto (fun n => ‖target n‖) atTop atTop) :
    Tendsto (fun n => μ {ω | target n ∈ region ω}) atTop (𝓝 0) := by
  apply _root_.GD.N0005.N0245.d030050 μ _ hm
  intro ω
  obtain ⟨R, hR⟩ := (hbounded ω).exists_norm_le
  filter_upwards [htarget.eventually (eventually_gt_atTop R)] with n hn
  exact fun hmem => (not_le_of_gt hn) (hR _ hmem)

theorem d030052
    [SeminormedAddCommGroup E]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (region : Ω → Set E) (target : ℕ → E)
    (hm : ∀ n, MeasurableSet {ω | target n ∈ region ω})
    (hbounded : ∀ ω, Bornology.IsBounded (region ω))
    (htarget : Tendsto (fun n => ‖target n‖) atTop atTop)
    {p : ℝ≥0∞} (hp : 0 < p) :
    ∃ n, μ {ω | target n ∈ region ω} < p := by
  have h := _root_.GD.N0005.N0245.d030051 μ region target hm hbounded htarget
  exact (h.eventually (eventually_lt_nhds hp)).exists

theorem d030053
    [SeminormedAddCommGroup E]
    (law : Θ → Measure Ω) (θ : ℕ → Θ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hlaw : ∀ n, law (θ n) = μ)
    (truth : Θ → E) (region : Ω → Set E)
    (hm : ∀ n, MeasurableSet {ω | truth (θ n) ∈ region ω})
    (hbounded : ∀ ω, Bornology.IsBounded (region ω))
    (htarget : Tendsto (fun n => ‖truth (θ n)‖) atTop atTop)
    {p : ℝ≥0∞} (hp : 0 < p) :
    ¬ ∀ η, p ≤ law η {ω | truth η ∈ region ω} := by
  intro hcoverage
  obtain ⟨n, hn⟩ := _root_.GD.N0005.N0245.d030052 μ region (truth ∘ θ)
    hm hbounded htarget hp
  have h := hcoverage (θ n)
  rw [hlaw n] at h
  exact (not_lt_of_ge h) hn

theorem d030054
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Ω) [SFinite μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (A : Set Ω) :
    (μ.prod ν) {z : Ω × Y | z.1 ∈ A} = μ A := by
  have heq : {z : Ω × Y | z.1 ∈ A} = A ×ˢ (univ : Set Y) := by ext z; simp
  rw [heq]
  rw [Measure.prod_prod, measure_univ, mul_one]

end GD.N0005.N0245

#print axioms _root_.GD.N0005.N0245.d030050
#print axioms _root_.GD.N0005.N0245.d030051
#print axioms _root_.GD.N0005.N0245.d030053
#print axioms _root_.GD.N0005.N0245.d030054
