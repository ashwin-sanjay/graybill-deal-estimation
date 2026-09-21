import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import GD.Module0118




























open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0575

noncomputable section

open _root_.GD.N0230.N0669
open _root_.GD.N0230.N0572
open _root_.GD.N0230.N0574

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Θ : Type*}
variable (ψ : Θ → H) (m w : H)





theorem d001454 : IsClosed (_root_.GD.N0230.N0669.d001375 ψ m) := by
  have hrw : _root_.GD.N0230.N0669.d001375 ψ m =
      ⋂ θ, {d : H | ‖d - ψ θ‖ ≤ ‖m - ψ θ‖} := by
    ext d
    simp [_root_.GD.N0230.N0669.d001375, Set.mem_iInter]
  rw [hrw]
  apply isClosed_iInter
  intro θ
  exact isClosed_le ((continuous_id.sub continuous_const).norm)
    continuous_const


theorem d001455 :
    Continuous (_root_.GD.N0230.N0572.d001400 m w) := by
  show Continuous fun d : H ↦ -2 * ⟪d - m, w⟫
  exact ((continuous_id.sub continuous_const).inner
    continuous_const).const_mul (-2)


theorem d001456 (η : ℝ) :
    IsClosed {d : H | _root_.GD.N0230.N0572.d001400 m w d ≤ -η} :=
  isClosed_le (_root_.GD.N0230.N0575.d001455 m w) continuous_const


theorem d001457 (η : ℝ) :
    IsClosed (_root_.GD.N0230.N0574.d001411 ψ m w η) :=
  (_root_.GD.N0230.N0575.d001454 ψ m).inter (_root_.GD.N0230.N0575.d001456 m w η)






theorem d001458 [CompleteSpace H]
    {S : Set H} (hne : S.Nonempty) (hconv : Convex ℝ S)
    (hclosed : IsClosed S) (u : H) :
    ∃! p, p ∈ S ∧ ∀ q ∈ S, ‖u - p‖ ≤ ‖u - q‖ := by
  haveI : Nonempty S := hne.to_subtype
  have hbdd : BddBelow (Set.range fun q : S ↦ ‖u - (q : H)‖) :=
    ⟨0, Set.forall_mem_range.2 fun _ ↦ norm_nonneg _⟩
  obtain ⟨v, hv, hmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne
      hclosed.isComplete hconv u
  have hvar := (norm_eq_iInf_iff_real_inner_le_zero hconv hv).mp hmin
  refine ⟨v, ⟨hv, ?_⟩, ?_⟩
  · intro q hq
    rw [hmin]
    exact ciInf_le hbdd ⟨q, hq⟩
  · rintro p ⟨hp, hpmin⟩
    have hpinf : ‖u - p‖ = ⨅ q : S, ‖u - (q : H)‖ := by
      apply le_antisymm
      · exact le_ciInf fun q ↦ hpmin q q.2
      · exact ciInf_le hbdd ⟨p, hp⟩
    have hvarp :=
      (norm_eq_iInf_iff_real_inner_le_zero hconv hp).mp hpinf
    have h1 := hvar p hp
    have h2 := hvarp v hv
    have hA : ⟪p - v, p - v⟫ =
        ⟪u - v, p - v⟫ - ⟪u - p, p - v⟫ := by
      nth_rewrite 1 [show p - v = (u - v) - (u - p) from by abel]
      rw [inner_sub_left]
    have hB : ⟪u - p, v - p⟫ = -⟪u - p, p - v⟫ := by
      rw [show v - p = -(p - v) from by abel, inner_neg_right]
    have hkey : ⟪p - v, p - v⟫ ≤ 0 := by
      rw [hA]
      linarith [h1, h2, hB]
    have hnorm : ‖p - v‖ ^ 2 ≤ 0 := by
      rw [← real_inner_self_eq_norm_sq]
      exact hkey
    have hzero : ‖p - v‖ = 0 := by
      nlinarith [norm_nonneg (p - v), hnorm]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)







theorem d001459 [CompleteSpace H]
    {u : H} {c γ η : ℝ} (hu : u ≠ 0)
    (hfloor : ∀ θ, c ≤ ⟪u, ψ θ - m⟫) (hc : 0 < c)
    (hslope : γ ≤ ⟪u, w⟫) (hγ : 0 < γ)
    (hη : 0 < η) (hbudget : η < 4 * γ * c / ‖u‖ ^ 2) (d : H) :
    ∃! p, p ∈ _root_.GD.N0230.N0574.d001411 ψ m w η ∧
      ∀ q ∈ _root_.GD.N0230.N0574.d001411 ψ m w η, ‖d - p‖ ≤ ‖d - q‖ := by
  obtain ⟨hconv, hne, -⟩ :=
    _root_.GD.N0230.N0574.d001414 ψ m w hu hfloor hc hslope hγ
      hη hbudget
  exact _root_.GD.N0230.N0575.d001458 hne hconv
    (_root_.GD.N0230.N0575.d001457 ψ m w η) d

end

end N0575
end N0230
end GD

#print axioms _root_.GD.N0230.N0575.d001454
#print axioms _root_.GD.N0230.N0575.d001457
#print axioms _root_.GD.N0230.N0575.d001458
#print axioms _root_.GD.N0230.N0575.d001459
