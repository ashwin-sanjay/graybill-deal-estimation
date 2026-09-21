import GD.Module0108


































open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0679

noncomputable section

open _root_.GD.N0230.N0669

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Θ : Type*} (ψ : Θ → H) (m : H)



def d001389 : Set H :=
  {u : H | ∃ c : ℝ, 0 < c ∧ ∀ θ, c ≤ ⟪u, ψ θ - m⟫}




theorem d001390 {u v : H} {a b : ℝ}
    (hu : ∀ θ, a ≤ ⟪u, ψ θ - m⟫) (hv : ∀ θ, b ≤ ⟪v, ψ θ - m⟫)
    (θ : Θ) :
    a + b ≤ ⟪u + v, ψ θ - m⟫ := by
  rw [inner_add_left]
  exact add_le_add (hu θ) (hv θ)


theorem d001391 {u : H} {a t : ℝ} (ht : 0 ≤ t)
    (hu : ∀ θ, a ≤ ⟪u, ψ θ - m⟫) (θ : Θ) :
    t * a ≤ ⟪t • u, ψ θ - m⟫ := by
  rw [real_inner_smul_left]
  exact mul_le_mul_of_nonneg_left (hu θ) ht


theorem d001392
    {u v : H} (hu : u ∈ _root_.GD.N0230.N0679.d001389 ψ m)
    (hv : v ∈ _root_.GD.N0230.N0679.d001389 ψ m) :
    u + v ∈ _root_.GD.N0230.N0679.d001389 ψ m := by
  obtain ⟨a, ha, hfu⟩ := hu
  obtain ⟨b, hb, hfv⟩ := hv
  exact ⟨a + b, by linarith, _root_.GD.N0230.N0679.d001390 ψ m hfu hfv⟩


theorem d001393
    {u : H} {t : ℝ} (ht : 0 < t)
    (hu : u ∈ _root_.GD.N0230.N0679.d001389 ψ m) :
    t • u ∈ _root_.GD.N0230.N0679.d001389 ψ m := by
  obtain ⟨a, ha, hfu⟩ := hu
  exact ⟨t * a, mul_pos ht ha, _root_.GD.N0230.N0679.d001391 ψ m ht.le hfu⟩


theorem d001394 :
    Convex ℝ (_root_.GD.N0230.N0679.d001389 ψ m) := by
  intro u hu v hv s r hs hr hsr
  rcases eq_or_lt_of_le hs with hs0 | hs0
  · have hr1 : r = 1 := by linarith
    rw [← hs0, hr1, zero_smul, one_smul, zero_add]
    exact hv
  rcases eq_or_lt_of_le hr with hr0 | hr0
  · have hs1 : s = 1 := by linarith
    rw [← hr0, hs1, zero_smul, one_smul, add_zero]
    exact hu
  exact _root_.GD.N0230.N0679.d001392 ψ m
    (_root_.GD.N0230.N0679.d001393 ψ m hs0 hu)
    (_root_.GD.N0230.N0679.d001393 ψ m hr0 hv)






theorem d001395 {u : H} (hu : u ≠ 0) :
    (∃ t : ℝ, 0 < t ∧ m + t • u ∈ _root_.GD.N0230.N0669.d001375 ψ m) ↔
      u ∈ _root_.GD.N0230.N0679.d001389 ψ m := by
  have hn : (0 : ℝ) < ‖u‖ ^ 2 := by
    have := norm_pos_iff.mpr hu
    positivity
  constructor
  · rintro ⟨t, ht, hmem⟩
    have hrad := (_root_.GD.N0230.N0669.d001381 ψ m ht).mp hmem
    refine ⟨t * ‖u‖ ^ 2 / 2, by positivity, fun θ ↦ ?_⟩
    have := hrad θ
    linarith
  · rintro ⟨c, hc, hfloor⟩
    refine ⟨c / ‖u‖ ^ 2, by positivity, ?_⟩
    rw [_root_.GD.N0230.N0669.d001381 ψ m (by positivity)]
    intro θ
    have h1 : c / ‖u‖ ^ 2 * ‖u‖ ^ 2 = c := by
      field_simp
    rw [h1]
    have := hfloor θ
    linarith






theorem d001396 {u₀ u : H} {c R δ : ℝ}
    (hR : ∀ θ, ‖ψ θ - m‖ ≤ R)
    (hfloor : ∀ θ, c ≤ ⟪u₀, ψ θ - m⟫)
    (hclose : ‖u - u₀‖ ≤ δ) (θ : Θ) :
    c - δ * R ≤ ⟪u, ψ θ - m⟫ := by
  have hsplit : ⟪u, ψ θ - m⟫ =
      ⟪u₀, ψ θ - m⟫ + ⟪u - u₀, ψ θ - m⟫ := by
    rw [← inner_add_left]
    congr 1
    abel
  have habs : |⟪u - u₀, ψ θ - m⟫| ≤ δ * R := by
    calc
      |⟪u - u₀, ψ θ - m⟫| ≤ ‖u - u₀‖ * ‖ψ θ - m‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ δ * R := by
        have h0 : (0 : ℝ) ≤ ‖ψ θ - m‖ := norm_nonneg _
        have h1 : ‖u - u₀‖ * ‖ψ θ - m‖ ≤ δ * ‖ψ θ - m‖ :=
          mul_le_mul_of_nonneg_right hclose h0
        have h2 : δ * ‖ψ θ - m‖ ≤ δ * R := by
          have hδ0 : (0 : ℝ) ≤ δ :=
            le_trans (norm_nonneg _) hclose
          exact mul_le_mul_of_nonneg_left (hR θ) hδ0
        linarith
  have hlow : -(δ * R) ≤ ⟪u - u₀, ψ θ - m⟫ := by
    have := abs_le.mp habs
    exact this.1
  rw [hsplit]
  linarith [hfloor θ]



theorem d001397 {u₀ u : H} {c R δ : ℝ}
    (hR : ∀ θ, ‖ψ θ - m‖ ≤ R)
    (hfloor : ∀ θ, c ≤ ⟪u₀, ψ θ - m⟫)
    (hclose : ‖u - u₀‖ ≤ δ)
    (hgap : 0 < c - δ * R) :
    u ∈ _root_.GD.N0230.N0679.d001389 ψ m :=
  ⟨c - δ * R, hgap, _root_.GD.N0230.N0679.d001396 ψ m hR hfloor hclose⟩








theorem d001398 {u₀ u : H} {c R δ t : ℝ}
    (hR : ∀ θ, ‖ψ θ - m‖ ≤ R)
    (hfloor : ∀ θ, c ≤ ⟪u₀, ψ θ - m⟫)
    (hclose : ‖u - u₀‖ ≤ δ)
    (ht0 : 0 < t)
    (ht2 : t * ‖u‖ ^ 2 < 2 * (c - δ * R)) (θ : Θ) :
    0 < ‖m - ψ θ‖ ^ 2 - ‖m + t • u - ψ θ‖ ^ 2 := by
  rw [_root_.GD.N0230.N0669.d001382 ψ m u t θ]
  have hf := _root_.GD.N0230.N0679.d001396 ψ m hR hfloor hclose θ
  nlinarith [mul_le_mul_of_nonneg_left hf
    (by linarith : (0 : ℝ) ≤ 2 * t),
    mul_pos ht0 (by linarith : (0 : ℝ) < 2 * (c - δ * R) -
      t * ‖u‖ ^ 2)]



theorem d001399 {u₀ u : H} {c R δ t : ℝ}
    (hR : ∀ θ, ‖ψ θ - m‖ ≤ R)
    (hfloor : ∀ θ, c ≤ ⟪u₀, ψ θ - m⟫)
    (hclose : ‖u - u₀‖ ≤ δ)
    (ht0 : 0 < t)
    (ht2 : t * ‖u‖ ^ 2 ≤ 2 * (c - δ * R)) :
    m + t • u ∈ _root_.GD.N0230.N0669.d001375 ψ m := by
  rw [_root_.GD.N0230.N0669.d001381 ψ m ht0]
  intro θ
  have hf := _root_.GD.N0230.N0679.d001396 ψ m hR hfloor hclose θ
  linarith

end

end N0679
end N0230
end GD

#print axioms _root_.GD.N0230.N0679.d001394
#print axioms _root_.GD.N0230.N0679.d001395
#print axioms _root_.GD.N0230.N0679.d001396
#print axioms _root_.GD.N0230.N0679.d001397
#print axioms _root_.GD.N0230.N0679.d001398
#print axioms _root_.GD.N0230.N0679.d001399
