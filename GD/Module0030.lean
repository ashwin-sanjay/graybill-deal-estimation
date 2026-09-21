import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.SpecificLimits.Basic




















open Filter Set

namespace GD
namespace N0230
namespace N0656

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyConvexSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [LocallyConvexSpace ℝ F]




theorem d000354
    (C : ProperCone ℝ E) (x : E) :
    x ∈ C ∨
      ∃ f : StrongDual ℝ E,
        (∀ y ∈ C, 0 ≤ f y) ∧ f x < 0 := by
  by_cases hx : x ∈ C
  · exact Or.inl hx
  · exact Or.inr (C.hyperplane_separation_point hx)



theorem d000355
    (C : ProperCone ℝ E) (x : E) :
    x ∈ C ↔
      ∀ f : StrongDual ℝ E,
        (∀ y ∈ C, 0 ≤ f y) → 0 ≤ f x := by
  constructor
  · intro hx f hf
    exact hf x hx
  · intro hdual
    by_contra hx
    obtain ⟨f, hfC, hfx⟩ := C.hyperplane_separation_point hx
    exact (not_lt_of_ge (hdual f hfC)) hfx





theorem d000356
    (C : ProperCone ℝ E) (T : E →L[ℝ] F) (target : F) :
    target ∈ C.map T ↔
      ∀ f : StrongDual ℝ F,
        (∀ x ∈ C, 0 ≤ f (T x)) → 0 ≤ f target := by
  constructor
  · intro htarget f hf
    have hhalf : IsClosed {y : F | 0 ≤ f y} :=
      isClosed_Ici.preimage f.continuous
    have himage :
        (C.toPointedCone.map (T : E →ₗ[ℝ] F) : Set F) ⊆
          {y : F | 0 ≤ f y} := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := PointedCone.mem_map.mp hy
      exact hf x hx
    have hclosure :
        closure (C.toPointedCone.map (T : E →ₗ[ℝ] F) : Set F) ⊆
          {y : F | 0 ≤ f y} :=
      hhalf.closure_subset_iff.mpr himage
    exact hclosure htarget
  · intro hdual
    rw [_root_.GD.N0230.N0656.d000355]
    intro f hf
    apply hdual f
    intro x hx
    apply hf (T x)
    rw [ProperCone.mem_map]
    exact subset_closure (PointedCone.mem_map.mpr ⟨x, hx, rfl⟩)





theorem d000357
    (T : E →L[ℝ] F) (signed pedestal : E) (target : F) :
    ‖T (signed + pedestal) - target‖ ≤
      ‖T signed - target‖ + ‖T pedestal‖ := by
  rw [map_add]
  calc
    ‖T signed + T pedestal - target‖ =
        ‖(T signed - target) + T pedestal‖ := by
          congr 1
          abel
    _ ≤ ‖T signed - target‖ + ‖T pedestal‖ := norm_add_le _ _





theorem d000358
    (T : E →L[ℝ] F) (target : F) (Admissible : E → Prop)
    (hsigned : ∀ ε : ℝ, 0 < ε →
      ∃ signed : E, ‖T signed - target‖ < ε)
    (hpedestal : ∀ signed : E, ∀ ε : ℝ, 0 < ε →
      ∃ pedestal : E,
        Admissible (signed + pedestal) ∧ ‖T pedestal‖ < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ positive : E,
        Admissible positive ∧ ‖T positive - target‖ < ε := by
  intro ε hε
  obtain ⟨signed, hsignedError⟩ := hsigned (ε / 2) (half_pos hε)
  obtain ⟨pedestal, hpositive, hpedestalError⟩ :=
    hpedestal signed (ε / 2) (half_pos hε)
  refine ⟨signed + pedestal, hpositive, ?_⟩
  calc
    ‖T (signed + pedestal) - target‖ ≤
        ‖T signed - target‖ + ‖T pedestal‖ :=
      _root_.GD.N0230.N0656.d000357 T signed pedestal target
    _ < ε / 2 + ε / 2 :=
      add_lt_add hsignedError hpedestalError
    _ = ε := by ring







theorem d000359
    {X : ℕ → Type*}
    (Legal : ∀ n, X n → Prop)
    (residual : ∀ n, X n → ℝ)
    (hresidual_nonneg : ∀ n x, 0 ≤ residual n x)
    (harbitrarilySmall : ∀ n, ∀ ε : ℝ, 0 < ε →
      ∃ x : X n, Legal n x ∧ residual n x < ε) :
    ∃ x : ∀ n, X n,
      (∀ n, Legal n (x n)) ∧
      Tendsto (fun n ↦ residual n (x n)) atTop (nhds 0) := by
  have hchoose : ∀ n : ℕ,
      ∃ x : X n,
        Legal n x ∧ residual n x < 1 / ((n : ℝ) + 1) := by
    intro n
    exact harbitrarilySmall n (1 / ((n : ℝ) + 1)) (by positivity)
  choose x hxLegal hxBound using hchoose
  refine ⟨x, hxLegal, ?_⟩
  exact squeeze_zero
    (fun n ↦ hresidual_nonneg n (x n))
    (fun n ↦ (hxBound n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

end

end N0656
end N0230
end GD

#print axioms _root_.GD.N0230.N0656.d000355
#print axioms _root_.GD.N0230.N0656.d000356
#print axioms _root_.GD.N0230.N0656.d000358
#print axioms _root_.GD.N0230.N0656.d000359
