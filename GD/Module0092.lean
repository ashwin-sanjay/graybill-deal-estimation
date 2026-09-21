import GD.Module0091
import GD.Module0041


















open Set

namespace GD
namespace N0230
namespace N0613

noncomputable section

open _root_.GD.N0230.N0633 _root_.GD.N0230.N0685
open _root_.GD.N0230.N0708

variable {H Theta : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]









theorem d001202
    (C : Theta → Set H)
    (hclosed : ∀ theta, IsClosed (C theta))
    (hconvex : ∀ theta, Convex ℝ (C theta))
    (p : H) (hp : _root_.GD.N0230.N0685.d000511 (⋂ theta, C theta) 0 p)
    {a : ℝ} (ha : a < ‖p‖ ^ 2) :
    ∃ F : Finset Theta, ∀ x : H,
      (∀ theta ∈ F, x ∈ C theta) → a < ‖x‖ ^ 2 := by
  classical
  by_cases ha0 : a < 0
  · refine ⟨∅, ?_⟩
    intro x hx
    exact ha0.trans_le (sq_nonneg ‖x‖)
  · have ha_nonneg : 0 ≤ a := le_of_not_gt ha0
    let r : ℝ := Real.sqrt a
    let B : Set (WeakSpace ℝ H) :=
      toWeakSpace ℝ H '' Metric.closedBall (0 : H) r
    let U : Theta → Set (WeakSpace ℝ H) := fun theta ↦
      (toWeakSpace ℝ H '' C theta)ᶜ
    have hBcompact : IsCompact B := by
      exact _root_.GD.N0230.N0633.d001199 (H := H) r
    have hUopen : ∀ theta, IsOpen (U theta) := by
      intro theta
      exact (_root_.GD.N0230.N0708.d001175
        (hconvex theta) (hclosed theta)).isOpen_compl
    have hcover : B ⊆ ⋃ theta, U theta := by
      rintro _ ⟨x, hxball, rfl⟩
      have hx_not_full : x ∉ ⋂ theta, C theta := by
        intro hxfull
        have htax := _root_.GD.N0230.N0685.d000512 hp hxfull
        simp only [sub_zero] at htax
        have hxnorm : ‖x‖ ≤ r := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hxball
        have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg a
        have hr_sq : r ^ 2 = a := by
          exact Real.sq_sqrt ha_nonneg
        have hx_sq : ‖x‖ ^ 2 ≤ r ^ 2 := by
          nlinarith [norm_nonneg x]
        nlinarith [sq_nonneg ‖x - p‖]
      simp only [Set.mem_iInter] at hx_not_full
      push Not at hx_not_full
      obtain ⟨theta, htheta⟩ := hx_not_full
      refine Set.mem_iUnion.2 ⟨theta, ?_⟩
      change toWeakSpace ℝ H x ∉ toWeakSpace ℝ H '' C theta
      rintro ⟨y, hy, hyx⟩
      exact htheta ((toWeakSpace ℝ H).injective hyx ▸ hy)
    obtain ⟨F, hF⟩ :=
      hBcompact.elim_finite_subcover U hUopen hcover
    refine ⟨F, ?_⟩
    intro x hxF
    by_contra hax
    push Not at hax
    have hxnorm : ‖x‖ ≤ r := by
      have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg a
      have hr_sq : r ^ 2 = a := Real.sq_sqrt ha_nonneg
      nlinarith [norm_nonneg x]
    have hxball : x ∈ Metric.closedBall (0 : H) r := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxnorm
    have hxB : toWeakSpace ℝ H x ∈ B := ⟨x, hxball, rfl⟩
    have hxcover := hF hxB
    obtain ⟨theta, hthetaF, hthetaU⟩ := Set.mem_iUnion₂.mp hxcover
    exact hthetaU ⟨x, hxF theta hthetaF, rfl⟩




theorem d001203
    (C : Theta → Set H)
    (hclosed : ∀ theta, IsClosed (C theta))
    (hconvex : ∀ theta, Convex ℝ (C theta))
    (p : H) (hp : _root_.GD.N0230.N0685.d000511 (⋂ theta, C theta) 0 p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset Theta, ∀ x : H,
      (∀ theta ∈ F, x ∈ C theta) →
        ‖p‖ ^ 2 - ε < ‖x‖ ^ 2 := by
  apply _root_.GD.N0230.N0613.d001202
    C hclosed hconvex p hp
  linarith

end

end N0613
end N0230
end GD

#print axioms _root_.GD.N0230.N0613.d001202
#print axioms _root_.GD.N0230.N0613.d001203
