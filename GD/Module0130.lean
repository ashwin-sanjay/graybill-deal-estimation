import GD.Module0129








































open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0634

noncomputable section

open _root_.GD.N0230.N0604
open _root_.GD.N0230.N0696

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Θ : Type*}




theorem d001515 [CompleteSpace H] [Nonempty Θ]
    {ψ : Θ → H} {m : H}
    (hm : m ∉ closure (convexHull ℝ (Set.range ψ))) :
    ∃ u : H, u ≠ 0 ∧ ∀ θ, ‖u‖ ^ 2 ≤ ⟪u, ψ θ - m⟫ := by
  set K : Set H := closure (convexHull ℝ (Set.range ψ)) with hK
  have hKconv : Convex ℝ K := (convex_convexHull ℝ _).closure
  have hKclosed : IsClosed K := isClosed_closure
  have hKne : K.Nonempty := by
    obtain θ₀ := Classical.arbitrary Θ
    exact ⟨ψ θ₀, subset_closure (subset_convexHull ℝ _
      (Set.mem_range_self θ₀))⟩
  obtain ⟨p, hp, hdist⟩ := exists_norm_eq_iInf_of_complete_convex
    hKne hKclosed.isComplete hKconv m
  have hmin : ∀ r ∈ K, ‖m - p‖ ≤ ‖m - r‖ := by
    intro r hr
    rw [hdist]
    haveI : Nonempty K := hKne.to_subtype
    have hbdd : BddBelow (Set.range fun w : K ↦ ‖m - (w : H)‖) :=
      ⟨0, Set.forall_mem_range.2 fun _ ↦ norm_nonneg _⟩
    exact ciInf_le hbdd ⟨r, hr⟩
  have hpm : p ≠ m := fun h ↦ hm (h ▸ hp)
  refine ⟨p - m, sub_ne_zero.mpr hpm, fun θ ↦ ?_⟩
  have hψK : ψ θ ∈ K :=
    subset_closure (subset_convexHull ℝ _ (Set.mem_range_self θ))
  have hVI := _root_.GD.N0230.N0661.d001474
    hKconv hp hmin hψK
  have hsplit : ⟪p - m, ψ θ - m⟫ =
      ⟪p - m, ψ θ - p⟫ + ‖p - m‖ ^ 2 := by
    have h1 : ψ θ - m = (ψ θ - p) + (p - m) := by abel
    rw [h1, inner_add_right, real_inner_self_eq_norm_sq]
  have hVIneg : 0 ≤ ⟪p - m, ψ θ - p⟫ := by
    have h2 : ⟪p - m, ψ θ - p⟫ = -⟪m - p, ψ θ - p⟫ := by
      rw [show p - m = -(m - p) from by abel, inner_neg_left]
    rw [h2]
    linarith [hVI]
  linarith [hsplit, hVIneg]


theorem d001516 {ψ : Θ → H} {m u : H} {c : ℝ}
    (hc : 0 < c) (hfloor : ∀ θ, c ≤ ⟪u, ψ θ - m⟫) :
    m ∉ closure (convexHull ℝ (Set.range ψ)) := by
  intro hm
  have hcont : Continuous fun x : H ↦ ⟪u, x - m⟫ := by
    have h1 : Continuous fun x : H ↦ x - m :=
      continuous_id.sub continuous_const
    exact (innerSL ℝ u).continuous.comp h1
  have hset : IsClosed {x : H | c ≤ ⟪u, x - m⟫} :=
    isClosed_le continuous_const hcont
  have hconvset : Convex ℝ {x : H | c ≤ ⟪u, x - m⟫} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have hmm : a • m + b • m = m := by
      rw [← add_smul, hab, one_smul]
    have h1 : a • x + b • y - m = a • (x - m) + b • (y - m) := by
      have h2 : a • (x - m) + b • (y - m) =
          a • x + b • y - (a • m + b • m) := by
        rw [smul_sub, smul_sub]
        abel
      rw [h2, hmm]
    have hexp : ⟪u, a • x + b • y - m⟫ =
        a * ⟪u, x - m⟫ + b * ⟪u, y - m⟫ := by
      rw [h1, inner_add_right, real_inner_smul_right,
        real_inner_smul_right]
    have k1 : a * c ≤ a * ⟪u, x - m⟫ :=
      mul_le_mul_of_nonneg_left hx ha
    have k2 : b * c ≤ b * ⟪u, y - m⟫ :=
      mul_le_mul_of_nonneg_left hy hb
    have k3 : a * c + b * c = c := by
      rw [← add_mul, hab, one_mul]
    rw [hexp]
    linarith
  have hsub : Set.range ψ ⊆ {x : H | c ≤ ⟪u, x - m⟫} := by
    rintro _ ⟨θ, rfl⟩
    exact hfloor θ
  have hhull : closure (convexHull ℝ (Set.range ψ)) ⊆
      {x : H | c ≤ ⟪u, x - m⟫} :=
    closure_minimal (convexHull_min hsub hconvset) hset
  have := hhull hm
  simp only [Set.mem_setOf_eq, sub_self, inner_zero_right] at this
  linarith





theorem d001517 {ψ : Θ → H} {m : H}
    (hm : m ∈ closure (convexHull ℝ (Set.range ψ))) :
    _root_.GD.N0230.N0604.d001486 Set.univ ψ m := by
  refine ⟨Set.mem_univ _, ?_⟩
  rintro d - ⟨hdom, θ₀, hstrict⟩
  set S₀ : Set H :=
    {x : H | 2 * ⟪m - d, x⟫ ≤ ‖m‖ ^ 2 - ‖d‖ ^ 2} with hS₀
  have hcont : Continuous fun x : H ↦ 2 * ⟪m - d, x⟫ :=
    continuous_const.mul (innerSL ℝ (m - d)).continuous
  have hclosed : IsClosed S₀ := isClosed_le hcont continuous_const
  have hconv : Convex ℝ S₀ := by
    intro x hx y hy a b ha hb hab
    simp only [hS₀, Set.mem_setOf_eq] at hx hy ⊢
    have hexp : ⟪m - d, a • x + b • y⟫ =
        a * ⟪m - d, x⟫ + b * ⟪m - d, y⟫ := by
      rw [inner_add_right, real_inner_smul_right,
        real_inner_smul_right]
    have k1 : a * (2 * ⟪m - d, x⟫) ≤ a * (‖m‖ ^ 2 - ‖d‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hx ha
    have k2 : b * (2 * ⟪m - d, y⟫) ≤ b * (‖m‖ ^ 2 - ‖d‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hy hb
    have k3 : a * (‖m‖ ^ 2 - ‖d‖ ^ 2) + b * (‖m‖ ^ 2 - ‖d‖ ^ 2) =
        ‖m‖ ^ 2 - ‖d‖ ^ 2 := by
      rw [← add_mul, hab, one_mul]
    rw [hexp]
    linarith
  have hsub : Set.range ψ ⊆ S₀ := by
    rintro _ ⟨θ, rfl⟩
    simp only [hS₀, Set.mem_setOf_eq]
    have hsq : ‖d - ψ θ‖ ^ 2 ≤ ‖m - ψ θ‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hdom θ) 2
    have e1 := norm_sub_sq_real d (ψ θ)
    have e2 := norm_sub_sq_real m (ψ θ)
    have e3 : ⟪m - d, ψ θ⟫ = ⟪m, ψ θ⟫ - ⟪d, ψ θ⟫ :=
      inner_sub_left m d (ψ θ)
    linarith
  have hmS₀ : m ∈ S₀ :=
    closure_minimal (convexHull_min hsub hconv) hclosed hm
  have hdm : d = m := by
    simp only [hS₀, Set.mem_setOf_eq] at hmS₀
    have e3 : ⟪m - d, m⟫ = ⟪m, m⟫ - ⟪d, m⟫ := inner_sub_left m d m
    have e4 : ⟪m, m⟫ = ‖m‖ ^ 2 := real_inner_self_eq_norm_sq m
    have e5 := norm_sub_sq_real m d
    have e6 : ⟪m, d⟫ = ⟪d, m⟫ := real_inner_comm d m
    have hz : ‖m - d‖ ^ 2 ≤ 0 := by linarith
    have h0 : ‖m - d‖ ^ 2 = 0 :=
      le_antisymm hz (by positivity)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
    have hmd : m - d = 0 := norm_eq_zero.mp this
    have := sub_eq_zero.mp hmd
    exact this.symm
  rw [hdm] at hstrict
  exact lt_irrefl _ hstrict





theorem d001518 [CompleteSpace H] [Nonempty Θ]
    (ψ : Θ → H) (m : H) :
    _root_.GD.N0230.N0604.d001486 Set.univ ψ m ∨
    ∃ dstar, (∀ θ, ‖dstar - ψ θ‖ < ‖m - ψ θ‖) ∧
      _root_.GD.N0230.N0604.d001486 Set.univ ψ dstar := by
  by_cases hm : m ∈ closure (convexHull ℝ (Set.range ψ))
  · exact Or.inl (_root_.GD.N0230.N0634.d001517 hm)
  · obtain ⟨u, hu, hfloor⟩ := _root_.GD.N0230.N0634.d001515 hm
    have hnorm : (0 : ℝ) < ‖u‖ ^ 2 := by
      have := norm_pos_iff.mpr hu
      positivity
    exact Or.inr
      (_root_.GD.N0230.N0687.d001514
        hu hnorm hfloor)



theorem d001519
    [CompleteSpace H] [Nonempty Θ] (ψ : Θ → H) (m : H) :
    ∃ dstar, _root_.GD.N0230.N0604.d001484 ψ dstar m ∧ _root_.GD.N0230.N0604.d001486 Set.univ ψ dstar := by
  rcases _root_.GD.N0230.N0634.d001518 ψ m with h | ⟨dstar, hstrict, hterm⟩
  · exact ⟨m, _root_.GD.N0230.N0696.d001492 ψ m, h⟩
  · exact ⟨dstar, fun θ ↦ (hstrict θ).le, hterm⟩


theorem d001520
    [CompleteSpace H] [Nonempty Θ] (ψ : Θ → H) (m : H) :
    (∃ d, ∀ θ, ‖d - ψ θ‖ < ‖m - ψ θ‖) ↔
      m ∉ closure (convexHull ℝ (Set.range ψ)) := by
  constructor
  · rintro ⟨d, hd⟩ hm
    exact (_root_.GD.N0230.N0634.d001517 hm).2 d (Set.mem_univ d)
      ⟨fun θ ↦ (hd θ).le, Classical.arbitrary Θ,
        hd (Classical.arbitrary Θ)⟩
  · intro hm
    obtain ⟨u, hu, hfloor⟩ := _root_.GD.N0230.N0634.d001515 hm
    have hnorm : (0 : ℝ) < ‖u‖ ^ 2 := by
      have := norm_pos_iff.mpr hu
      positivity
    obtain ⟨dstar, hstrict, _⟩ :=
      _root_.GD.N0230.N0687.d001514
        hu hnorm hfloor
    exact ⟨dstar, hstrict⟩

end

end N0634
end N0230
end GD

#print axioms _root_.GD.N0230.N0634.d001515
#print axioms _root_.GD.N0230.N0634.d001516
#print axioms _root_.GD.N0230.N0634.d001517
#print axioms _root_.GD.N0230.N0634.d001518
#print axioms _root_.GD.N0230.N0634.d001519
#print axioms _root_.GD.N0230.N0634.d001520
