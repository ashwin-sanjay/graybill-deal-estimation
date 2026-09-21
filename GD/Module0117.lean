import GD.Module0116






























open MeasureTheory Filter
open scoped RealInnerProductSpace BigOperators

namespace GD
namespace N0230
namespace N0592

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Θ : Type*}
variable (ψ : Θ → H) (m w : H)


def d001445 (w : H) : Submodule ℝ H where
  carrier := {v : H | ⟪w, v⟫ = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [inner_add_right, ha, hb]
    ring
  zero_mem' := by
    simp only [Set.mem_setOf_eq, inner_zero_right]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [real_inner_smul_right, ha]
    ring



theorem d001446 {L : Set H}
    (horthm : ⟪w, m⟫ = 0)
    (horthloc : ∀ v ∈ L, ⟪w, v⟫ = 0)
    {x : H} (hx : x ∈ Submodule.span ℝ ({m} ∪ L)) :
    ⟪w, x⟫ = 0 := by
  have hle : Submodule.span ℝ ({m} ∪ L) ≤ _root_.GD.N0230.N0592.d001445 w := by
    rw [Submodule.span_le]
    intro v hv
    rcases hv with hv | hv
    · rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact horthm
    · exact horthloc v hv
  exact hle hx



theorem d001447 {L : Set H}
    (horthm : ⟪w, m⟫ = 0)
    (horthloc : ∀ v ∈ L, ⟪w, v⟫ = 0)
    (hlowrank : ∀ θ, ψ θ - m ∈ Submodule.span ℝ ({m} ∪ L))
    {k : ℕ} (lam : Fin k → ℝ) (θs : Fin k → Θ) :
    ⟪w, ∑ i, lam i • (ψ (θs i) - m)⟫ = 0 := by
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [real_inner_smul_right,
    _root_.GD.N0230.N0592.d001446 m w horthm horthloc (hlowrank (θs i))]
  ring





theorem d001448 {L : Set H}
    (horthm : ⟪w, m⟫ = 0)
    (horthloc : ∀ v ∈ L, ⟪w, v⟫ = 0)
    (hlowrank : ∀ θ, ψ θ - m ∈ Submodule.span ℝ ({m} ∪ L))
    {v : ℕ → H}
    (hcombo : ∀ n, ∃ (k : ℕ) (lam : Fin k → ℝ) (θs : Fin k → Θ),
      v n = ∑ i, lam i • (ψ (θs i) - m))
    (hlim : Tendsto v atTop (nhds w)) :
    w = 0 := by
  have hpair : ∀ n, ⟪w, v n⟫ = 0 := by
    intro n
    obtain ⟨k, lam, θs, hvn⟩ := hcombo n
    rw [hvn]
    exact _root_.GD.N0230.N0592.d001447 ψ m w horthm horthloc hlowrank lam θs
  have hlim2 : Tendsto (fun n ↦ ⟪w, v n⟫) atTop (nhds ⟪w, w⟫) :=
    Tendsto.inner tendsto_const_nhds hlim
  have hconst : (fun n ↦ ⟪w, v n⟫) = fun _ ↦ (0 : ℝ) :=
    funext hpair
  rw [hconst] at hlim2
  have hww : ⟪w, w⟫ = 0 :=
    tendsto_nhds_unique hlim2 tendsto_const_nhds
  rw [real_inner_self_eq_norm_sq] at hww
  have : ‖w‖ = 0 := by
    nlinarith [norm_nonneg w, hww]
  exact norm_eq_zero.mp this




theorem d001449 {L : Set H}
    (horthm : ⟪w, m⟫ = 0)
    (horthloc : ∀ v ∈ L, ⟪w, v⟫ = 0)
    {θ : Θ} {u contrast : H}
    (hu : u ∈ Submodule.span ℝ ({m} ∪ L))
    (hdecomp : ψ θ - m = u + contrast) :
    ⟪w, ψ θ - m⟫ = ⟪w, contrast⟫ := by
  rw [hdecomp, inner_add_right,
    _root_.GD.N0230.N0592.d001446 m w horthm horthloc hu]
  ring

end

end N0592
end N0230
end GD

#print axioms _root_.GD.N0230.N0592.d001446
#print axioms _root_.GD.N0230.N0592.d001448
#print axioms _root_.GD.N0230.N0592.d001449
