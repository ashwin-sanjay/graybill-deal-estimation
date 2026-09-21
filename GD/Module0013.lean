import Mathlib.MeasureTheory.Function.ConvergenceInMeasure















open Filter MeasureTheory

namespace GD
namespace N0230
namespace N0594

variable {G I Ω E : Type*}
  [MeasurableSpace Ω] [EMetricSpace E]



theorem d000112
    [TopologicalSpace G] [FrechetUrysohnSpace G]
    (label : I → G) (hlabel : DenseRange label) (g : G) :
    ∃ sequence : ℕ → I,
      Tendsto (fun n ↦ label (sequence n)) atTop (nhds g) := by
  obtain ⟨points, hpoints, hpoints_tendsto⟩ :=
    mem_closure_iff_seq_limit.mp (hlabel g)
  choose sequence hsequence using hpoints
  refine ⟨sequence, ?_⟩
  have heq : (fun n ↦ label (sequence n)) = points := by
    funext n
    exact hsequence n
  rw [heq]
  exact hpoints_tendsto









theorem d000113
    (mu : Measure Ω) [IsFiniteMeasure mu]
    (label : I → G) (orbit : G → Ω → E) (f : Ω → E)
    (hf : AEStronglyMeasurable f mu)
    (hfixed : ∀ i, orbit (label i) =ᵐ[mu] f)
    (happrox : ∀ g, ∃ sequence : ℕ → I,
      TendstoInMeasure mu
        (fun n ↦ orbit (label (sequence n))) atTop (orbit g)) :
    ∀ g, orbit g =ᵐ[mu] f := by
  intro g
  obtain ⟨sequence, hsequence⟩ := happrox g
  have hconstant :
      TendstoInMeasure mu (fun _ : ℕ ↦ f) atTop f := by
    apply tendstoInMeasure_of_tendsto_ae (fun _ ↦ hf)
    exact Filter.Eventually.of_forall (fun _ ↦ tendsto_const_nhds)
  have hskeleton :
      TendstoInMeasure mu
        (fun n ↦ orbit (label (sequence n))) atTop f := by
    exact TendstoInMeasure.congr'
      (Filter.Eventually.of_forall fun n ↦ (hfixed (sequence n)).symm)
      Filter.EventuallyEq.rfl hconstant
  exact tendstoInMeasure_ae_unique hsequence hskeleton











theorem d000114
    [TopologicalSpace G]
    (mu : Measure Ω) [IsFiniteMeasure mu]
    (label : I → G) (orbit : G → Ω → E) (f : Ω → E)
    (hf : AEStronglyMeasurable f mu)
    (hfixed : ∀ i, orbit (label i) =ᵐ[mu] f)
    (hdense : ∀ g, ∃ sequence : ℕ → I,
      Tendsto (fun n ↦ label (sequence n)) atTop (nhds g))
    (horbit : ∀ (sequence : ℕ → I) (g : G),
      Tendsto (fun n ↦ label (sequence n)) atTop (nhds g) →
        TendstoInMeasure mu
          (fun n ↦ orbit (label (sequence n))) atTop (orbit g)) :
    ∀ g, orbit g =ᵐ[mu] f := by
  apply _root_.GD.N0230.N0594.d000113
    mu label orbit f hf hfixed
  intro g
  obtain ⟨sequence, hsequence⟩ := hdense g
  exact ⟨sequence, horbit sequence g hsequence⟩






theorem d000115
    [TopologicalSpace G] [FrechetUrysohnSpace G]
    (mu : Measure Ω) [IsFiniteMeasure mu]
    (label : I → G) (hlabel : DenseRange label)
    (orbit : G → Ω → E) (f : Ω → E)
    (hf : AEStronglyMeasurable f mu)
    (hfixed : ∀ i, orbit (label i) =ᵐ[mu] f)
    (horbit : ∀ (sequence : ℕ → I) (g : G),
      Tendsto (fun n ↦ label (sequence n)) atTop (nhds g) →
        TendstoInMeasure mu
          (fun n ↦ orbit (label (sequence n))) atTop (orbit g)) :
    ∀ g, orbit g =ᵐ[mu] f := by
  apply _root_.GD.N0230.N0594.d000114
    mu label orbit f hf hfixed
  · exact _root_.GD.N0230.N0594.d000112 label hlabel
  · exact horbit

end N0594
end N0230
end GD

#print axioms _root_.GD.N0230.N0594.d000113
#print axioms _root_.GD.N0230.N0594.d000114
#print axioms _root_.GD.N0230.N0594.d000115
