import GD.Module0121


































open Filter
open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0667

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]




theorem d001468 (a b p q : H) :
    (‖q - a‖ ^ 2 - ‖p - a‖ ^ 2) + (‖p - b‖ ^ 2 - ‖q - b‖ ^ 2) =
      2 * ⟪q - p, b - a⟫ := by
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right]
  ring


theorem d001469 (a b p q : H) :
    |(‖q - a‖ ^ 2 - ‖p - a‖ ^ 2) +
      (‖p - b‖ ^ 2 - ‖q - b‖ ^ 2)| ≤
      2 * (‖q - p‖ * ‖b - a‖) := by
  rw [_root_.GD.N0230.N0667.d001468, abs_mul]
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]
  exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _)
    (by norm_num)



theorem d001470 {a b p q : H}
    (hcoer : 2 * ‖q - p‖ ^ 2 ≤
      (‖q - a‖ ^ 2 - ‖p - a‖ ^ 2) +
        (‖p - b‖ ^ 2 - ‖q - b‖ ^ 2)) :
    ‖q - p‖ ≤ ‖b - a‖ := by
  rw [_root_.GD.N0230.N0667.d001468] at hcoer
  rcases eq_or_ne q p with hqp | hqp
  · rw [hqp, sub_self, norm_zero]
    exact norm_nonneg _
  · have hpos : 0 < ‖q - p‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hqp)
    have hcs : ⟪q - p, b - a⟫ ≤ ‖q - p‖ * ‖b - a‖ :=
      real_inner_le_norm _ _
    have hsq : ‖q - p‖ * ‖q - p‖ ≤ ‖q - p‖ * ‖b - a‖ := by
      nlinarith [hcoer, hcs]
    exact le_of_mul_le_mul_left hsq hpos



theorem d001471 {a p q : H}
    (hcoer : 2 * ‖q - p‖ ^ 2 ≤
      (‖q - a‖ ^ 2 - ‖p - a‖ ^ 2) +
        (‖p - a‖ ^ 2 - ‖q - a‖ ^ 2)) :
    q = p := by
  have hlip := _root_.GD.N0230.N0667.d001470 (a := a) (b := a) hcoer
  rw [sub_self, norm_zero] at hlip
  have : ‖q - p‖ = 0 :=
    le_antisymm hlip (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp this)



theorem d001472
    {τ ρ : ℕ → H}
    (htax : ∀ m n : ℕ, 2 * ‖ρ n - ρ m‖ ^ 2 ≤
      (‖ρ n - τ m‖ ^ 2 - ‖ρ m - τ m‖ ^ 2) +
        (‖ρ m - τ n‖ ^ 2 - ‖ρ n - τ n‖ ^ 2))
    (hτ : CauchySeq τ) : CauchySeq ρ := by
  rw [Metric.cauchySeq_iff] at hτ ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hτ ε hε
  refine ⟨N, fun m hm n hn ↦ ?_⟩
  have hlip := _root_.GD.N0230.N0667.d001470
    (a := τ m) (b := τ n) (p := ρ m) (q := ρ n) (htax m n)
  calc
    dist (ρ m) (ρ n) = ‖ρ m - ρ n‖ := dist_eq_norm _ _
    _ = ‖ρ n - ρ m‖ := by rw [norm_sub_rev]
    _ ≤ ‖τ n - τ m‖ := hlip
    _ = dist (τ m) (τ n) := by rw [norm_sub_rev, ← dist_eq_norm]
    _ < ε := hN m hm n hn




theorem d001473 [CompleteSpace H]
    {τ ρ : ℕ → H} {τlim : H}
    (htax : ∀ m n : ℕ, 2 * ‖ρ n - ρ m‖ ^ 2 ≤
      (‖ρ n - τ m‖ ^ 2 - ‖ρ m - τ m‖ ^ 2) +
        (‖ρ m - τ n‖ ^ 2 - ‖ρ n - τ n‖ ^ 2))
    (hτ : Tendsto τ atTop (nhds τlim)) :
    ∃ ρlim : H, Tendsto ρ atTop (nhds ρlim) :=
  cauchySeq_tendsto_of_complete
    (_root_.GD.N0230.N0667.d001472 htax hτ.cauchySeq)

end

end N0667
end N0230
end GD

#print axioms _root_.GD.N0230.N0667.d001468
#print axioms _root_.GD.N0230.N0667.d001470
#print axioms _root_.GD.N0230.N0667.d001471
#print axioms _root_.GD.N0230.N0667.d001472
#print axioms _root_.GD.N0230.N0667.d001473
