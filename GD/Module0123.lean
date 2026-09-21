import GD.Module0122








































open Filter
open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0661

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]




theorem d001474 {C : Set H} (hC : Convex ℝ C)
    {a p : H} (hp : p ∈ C)
    (hmin : ∀ r ∈ C, ‖a - p‖ ≤ ‖a - r‖)
    {q : H} (hq : q ∈ C) :
    ⟪a - p, q - p⟫ ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have hqp : q ≠ p := by
    rintro rfl
    simp at hpos
  have hs : 0 < ‖q - p‖ ^ 2 := by
    have : 0 < ‖q - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hqp)
    positivity
  set c := ⟪a - p, q - p⟫ with hc
  set s := ‖q - p‖ ^ 2 with hsdef
  set t := min 1 (c / s) with htdef
  have ht0 : 0 < t := lt_min one_pos (div_pos hpos hs)
  have ht1 : t ≤ 1 := min_le_left _ _
  have hmem : p + t • (q - p) ∈ C := by
    have hcomb := hC hp hq (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le
      (by ring : (1 - t) + t = 1)
    have hpt : (1 - t) • p + t • q = p + t • (q - p) := by
      rw [sub_smul, one_smul, smul_sub]
      abel
    rwa [hpt] at hcomb
  have hle := hmin _ hmem
  have hexp : ‖a - (p + t • (q - p))‖ ^ 2 =
      ‖a - p‖ ^ 2 - 2 * t * c + t ^ 2 * s := by
    rw [sub_add_eq_sub_sub]
    rw [show a - p - t • (q - p) = (a - p) - t • (q - p) from rfl,
      norm_sub_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs]
    rw [hc, hsdef]
    ring
  have hsq : ‖a - p‖ ^ 2 ≤ ‖a - (p + t • (q - p))‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hkey : 2 * c ≤ t * s := by
    have h1 : t * (2 * c) ≤ t * (t * s) := by nlinarith [hsq, hexp]
    exact le_of_mul_le_mul_left h1 ht0
  have hts : t * s ≤ c := by
    have htc : t ≤ c / s := min_le_right _ _
    have := mul_le_mul_of_nonneg_right htc hs.le
    calc t * s ≤ c / s * s := this
      _ = c := by field_simp
  linarith [hkey, hts, hpos]



theorem d001475 {C : Set H} (hC : Convex ℝ C)
    {a b p q : H} (hp : p ∈ C) (hq : q ∈ C)
    (hpmin : ∀ r ∈ C, ‖a - p‖ ≤ ‖a - r‖)
    (hqmin : ∀ r ∈ C, ‖b - q‖ ≤ ‖b - r‖) :
    ‖q - p‖ ^ 2 ≤ ⟪q - p, b - a⟫ := by
  have h1 := _root_.GD.N0230.N0661.d001474 hC hp hpmin hq
  have h2 := _root_.GD.N0230.N0661.d001474 hC hq hqmin hp
  have e1 : ⟪q - p, b - q⟫ = -⟪b - q, p - q⟫ := by
    rw [show q - p = -(p - q) from by abel, inner_neg_left,
      real_inner_comm]
  have e2 : ⟪q - p, a - p⟫ = ⟪a - p, q - p⟫ := real_inner_comm _ _
  have hstep : ⟪q - p, b - a⟫ - ⟪q - p, q - p⟫ =
      ⟪q - p, b - q⟫ - ⟪q - p, a - p⟫ := by
    rw [← inner_sub_right, ← inner_sub_right]
    congr 1
    abel
  have hself : ⟪q - p, q - p⟫ = ‖q - p‖ ^ 2 :=
    real_inner_self_eq_norm_sq _
  linarith [h1, h2, e1, e2, hstep, hself]




theorem d001476 {C : Set H} (hC : Convex ℝ C)
    {a b p q : H} (hp : p ∈ C) (hq : q ∈ C)
    (hpmin : ∀ r ∈ C, ‖a - p‖ ≤ ‖a - r‖)
    (hqmin : ∀ r ∈ C, ‖b - q‖ ≤ ‖b - r‖) :
    2 * ‖q - p‖ ^ 2 ≤
      (‖q - a‖ ^ 2 - ‖p - a‖ ^ 2) +
        (‖p - b‖ ^ 2 - ‖q - b‖ ^ 2) := by
  rw [_root_.GD.N0230.N0667.d001468]
  have := _root_.GD.N0230.N0661.d001475 hC hp hq hpmin hqmin
  linarith



theorem d001477 {C : Set H} (hC : Convex ℝ C)
    {a b p q : H} (hp : p ∈ C) (hq : q ∈ C)
    (hpmin : ∀ r ∈ C, ‖a - p‖ ≤ ‖a - r‖)
    (hqmin : ∀ r ∈ C, ‖b - q‖ ≤ ‖b - r‖) :
    ‖q - p‖ ≤ ‖b - a‖ :=
  _root_.GD.N0230.N0667.d001470
    (_root_.GD.N0230.N0661.d001476 hC hp hq hpmin hqmin)





theorem d001478 [CompleteSpace H]
    {C : Set H} (hC : Convex ℝ C) (hclosed : IsClosed C)
    {τ ρ : ℕ → H} {τlim : H}
    (hmem : ∀ n, ρ n ∈ C)
    (hmin : ∀ n, ∀ r ∈ C, ‖τ n - ρ n‖ ≤ ‖τ n - r‖)
    (hτ : Tendsto τ atTop (nhds τlim)) :
    ∃ ρlim ∈ C, Tendsto ρ atTop (nhds ρlim) := by
  have htax : ∀ m n : ℕ, 2 * ‖ρ n - ρ m‖ ^ 2 ≤
      (‖ρ n - τ m‖ ^ 2 - ‖ρ m - τ m‖ ^ 2) +
        (‖ρ m - τ n‖ ^ 2 - ‖ρ n - τ n‖ ^ 2) := fun m n ↦
    _root_.GD.N0230.N0661.d001476 hC (hmem m) (hmem n) (hmin m) (hmin n)
  obtain ⟨ρlim, hρ⟩ :=
    _root_.GD.N0230.N0667.d001473
      htax hτ
  exact ⟨ρlim,
    hclosed.mem_of_tendsto hρ (Eventually.of_forall hmem), hρ⟩

end

end N0661
end N0230
end GD

#print axioms _root_.GD.N0230.N0661.d001474
#print axioms _root_.GD.N0230.N0661.d001475
#print axioms _root_.GD.N0230.N0661.d001476
#print axioms _root_.GD.N0230.N0661.d001477
#print axioms _root_.GD.N0230.N0661.d001478
