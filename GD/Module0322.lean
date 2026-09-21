import GD.Module0295
import GD.Module0321
























open scoped BigOperators

namespace GD
namespace N0233
namespace N0734

noncomputable section

open _root_.GD.N0233.N0723
open _root_.GD.N0233.N0724

variable {E Θ : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]





theorem d004805
    (a : Θ → E →L[ℝ] ℝ)
    (hfaithful : ∀ x : E, (∀ θ, a θ x = 0) → x = 0) :
    _root_.GD.N0233.N0724.d004785 (fun θ ↦ (a θ).toLinearMap) = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hall : ∀ θ, a θ x = 0 := by
      intro θ
      have hθ :=
        (_root_.GD.N0233.N0724.d004786
          (fun θ ↦ (a θ).toLinearMap) x).mp hx θ
      exact hθ
    simpa using hfaithful x hall
  · exact bot_le





theorem d004806
    (a : Θ → E →L[ℝ] ℝ)
    (hfaithful : ∀ x : E, (∀ θ, a θ x = 0) → x = 0) :
    ∃ s : Finset Θ,
      s.card ≤ Module.finrank ℝ E ∧
      ∀ x : E, (∀ θ : ↥s, a θ.1 x = 0) → x = 0 := by
  classical
  let detector : ∀ θ : Θ, E →ₗ[ℝ] ℝ :=
    fun θ ↦ (a θ).toLinearMap
  have hcommon : _root_.GD.N0233.N0724.d004785 detector = ⊥ := by
    simpa [detector] using _root_.GD.N0233.N0734.d004805 a hfaithful
  obtain ⟨s, hcard, hker⟩ :=
    (_root_.GD.N0233.N0724.d004803
      (⊥ : Submodule ℝ E) detector bot_le).mp hcommon
  refine ⟨s, ?_, ?_⟩
  · simpa using hcard
  · intro x hx
    have hxker :
        x ∈ LinearMap.ker (_root_.GD.N0233.N0724.d004798 s detector) := by
      rw [_root_.GD.N0233.N0724.d004800]
      intro θ hθ
      exact hx ⟨θ, hθ⟩
    rw [hker] at hxker
    simpa using hxker








theorem d004807
    (a : Θ → E →L[ℝ] ℝ) (s : Finset Θ)
    (hfaithful : ∀ x : E, (∀ θ : ↥s, a θ.1 x = 0) → x = 0) :
    Module.finrank ℝ E ≤ s.card := by
  classical
  let detector : ∀ θ : Θ, E →ₗ[ℝ] ℝ :=
    fun θ ↦ (a θ).toLinearMap
  have hinjective :
      Function.Injective (_root_.GD.N0233.N0724.d004798 s detector) := by
    rw [← LinearMap.ker_eq_bot]
    apply le_antisymm
    · intro x hx
      have hall : ∀ θ : ↥s, a θ.1 x = 0 := by
        intro θ
        have hθ :=
          (_root_.GD.N0233.N0724.d004800
            s detector x).mp hx θ.1 θ.2
        exact hθ
      simpa using hfaithful x hall
    · exact bot_le
  have hdim :
      Module.finrank ℝ E ≤
        Module.finrank ℝ (∀ _ : ↥s, ℝ) :=
    LinearMap.finrank_le_finrank_of_injective hinjective
  simpa only [Module.finrank_pi, Fintype.card_coe] using hdim








theorem d004808
    (a : Θ → E →L[ℝ] ℝ)
    (hfaithful : ∀ x : E, (∀ θ, a θ x = 0) → x = 0) :
    ∃ s : Finset Θ,
      s.card = Module.finrank ℝ E ∧
      ∀ x : E, (∀ θ : ↥s, a θ.1 x = 0) → x = 0 := by
  obtain ⟨s, hcard, hsfaithful⟩ :=
    _root_.GD.N0233.N0734.d004806 a hfaithful
  refine ⟨s, le_antisymm hcard ?_, hsfaithful⟩
  exact
    _root_.GD.N0233.N0734.d004807
      a s hsfaithful







theorem d004809
    (a : Θ → E →L[ℝ] ℝ)
    (hfaithful : ∀ x : E, (∀ θ, a θ x = 0) → x = 0) :
    ∃ u : Finset Θ, ∃ δ : ℝ,
      u.card ≤ Module.finrank ℝ E ∧
      0 < δ ∧
      ∀ x : E,
        δ * ‖x‖ ^ 2 ≤ _root_.GD.N0233.N0723.d004310 a u x := by
  classical
  obtain ⟨s, hscard, hsfaithful⟩ :=
    _root_.GD.N0233.N0734.d004806 a hfaithful
  obtain ⟨t, δ, hδ, hcoercive⟩ :=
    _root_.GD.N0233.N0723.d004317
      (fun θ : ↥s ↦ a θ.1) hsfaithful
  let inclusion : ↥s ↪ Θ := Function.Embedding.subtype _
  let u : Finset Θ := t.map inclusion
  refine ⟨u, δ, ?_, hδ, ?_⟩
  · calc
      u.card = t.card := by simp [u]
      _ ≤ Fintype.card ↥s := Finset.card_le_univ t
      _ = s.card := Fintype.card_coe s
      _ ≤ Module.finrank ℝ E := hscard
  · intro x
    have henergy :
        _root_.GD.N0233.N0723.d004310 (fun θ : ↥s ↦ a θ.1) t x =
          _root_.GD.N0233.N0723.d004310 a u x := by
      simp [_root_.GD.N0233.N0723.d004310, u, inclusion]
    simpa [henergy] using hcoercive x







theorem d004810
    (a : Θ → E →L[ℝ] ℝ)
    (hfaithful : ∀ x : E, (∀ θ, a θ x = 0) → x = 0) :
    ∃ u : Finset Θ, ∃ δ : ℝ,
      u.card = Module.finrank ℝ E ∧
      0 < δ ∧
      ∀ x : E,
        δ * ‖x‖ ^ 2 ≤ _root_.GD.N0233.N0723.d004310 a u x := by
  classical
  obtain ⟨u, δ, hcard, hδ, hcoercive⟩ :=
    _root_.GD.N0233.N0734.d004809
      a hfaithful
  have hselectedFaithful :
      ∀ x : E, (∀ θ : ↥u, a θ.1 x = 0) → x = 0 := by
    intro x hx
    have henergy_zero : _root_.GD.N0233.N0723.d004310 a u x = 0 := by
      unfold _root_.GD.N0233.N0723.d004310
      apply Finset.sum_eq_zero
      intro θ hθ
      simp [hx ⟨θ, hθ⟩]
    have hlower := hcoercive x
    rw [henergy_zero] at hlower
    have hnorm_zero : ‖x‖ = 0 := by
      by_contra hne
      have hsq_pos : 0 < ‖x‖ ^ 2 :=
        sq_pos_of_ne_zero hne
      have hproduct_pos : 0 < δ * ‖x‖ ^ 2 :=
        mul_pos hδ hsq_pos
      linarith
    exact norm_eq_zero.mp hnorm_zero
  have hreverse : Module.finrank ℝ E ≤ u.card :=
    _root_.GD.N0233.N0734.d004807
      a u hselectedFaithful
  exact
    ⟨u, δ, le_antisymm hcard hreverse, hδ, hcoercive⟩






theorem d004811
    (a : Θ → E →L[ℝ] ℝ) :
    (∀ x : E, (∀ θ, a θ x = 0) → x = 0) ↔
      ∃ u : Finset Θ, ∃ δ : ℝ,
        u.card ≤ Module.finrank ℝ E ∧
        0 < δ ∧
        ∀ x : E,
          δ * ‖x‖ ^ 2 ≤ _root_.GD.N0233.N0723.d004310 a u x := by
  constructor
  · exact _root_.GD.N0233.N0734.d004809 a
  · rintro ⟨u, δ, hcard, hδ, hcoercive⟩
    exact
      _root_.GD.N0233.N0723.d004318
        a u δ hδ hcoercive








theorem d004812
    (a : Θ → E →L[ℝ] ℝ) :
    (∃ x : E, x ≠ 0 ∧ ∀ θ, a θ x = 0) ∨
      ∃ u : Finset Θ, ∃ δ : ℝ,
        u.card ≤ Module.finrank ℝ E ∧
        0 < δ ∧
        ∀ x : E,
          δ * ‖x‖ ^ 2 ≤ _root_.GD.N0233.N0723.d004310 a u x := by
  classical
  by_cases hfaithful :
      ∀ x : E, (∀ θ, a θ x = 0) → x = 0
  · exact Or.inr <|
      _root_.GD.N0233.N0734.d004809
        a hfaithful
  · left
    push Not at hfaithful
    obtain ⟨x, hall, hx⟩ := hfaithful
    exact ⟨x, hx, hall⟩

end

end N0734
end N0233
end GD
