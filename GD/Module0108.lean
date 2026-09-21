import GD.Module0107












































open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0669

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Θ : Type*} (ψ : Θ → H) (m : H)


def d001375 : Set H :=
  {d : H | ∀ θ, ‖d - ψ θ‖ ≤ ‖m - ψ θ‖}


theorem d001376 : m ∈ _root_.GD.N0230.N0669.d001375 ψ m := fun _θ ↦ le_refl _



theorem d001377 :
    _root_.GD.N0230.N0669.d001375 ψ m = ⋂ θ, Metric.closedBall (ψ θ) ‖m - ψ θ‖ := by
  ext d
  simp [_root_.GD.N0230.N0669.d001375, Metric.mem_closedBall, dist_eq_norm]


theorem d001378 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ≤ b ↔ a ^ 2 ≤ b ^ 2 := by
  constructor
  · intro h
    nlinarith
  · intro h
    by_contra hab
    push Not at hab
    nlinarith [mul_pos (by linarith : (0 : ℝ) < a - b)
      (by linarith : (0 : ℝ) < a + b)]



theorem d001379 (d : H) :
    d ∈ _root_.GD.N0230.N0669.d001375 ψ m ↔
      ∀ θ, ‖d - m‖ ^ 2 ≤ 2 * ⟪d - m, ψ θ - m⟫ := by
  unfold _root_.GD.N0230.N0669.d001375
  rw [Set.mem_setOf_eq]
  apply forall_congr'
  intro θ
  rw [_root_.GD.N0230.N0669.d001378 (norm_nonneg _) (norm_nonneg _)]
  have hexpand : ‖d - ψ θ‖ ^ 2 =
      ‖d - m‖ ^ 2 + 2 * ⟪d - m, m - ψ θ⟫ + ‖m - ψ θ‖ ^ 2 := by
    have hsplit : d - ψ θ = (d - m) + (m - ψ θ) := by abel
    rw [hsplit, norm_add_sq_real]
    try ring
  have hinner : ⟪d - m, m - ψ θ⟫ = -⟪d - m, ψ θ - m⟫ := by
    rw [show m - ψ θ = -(ψ θ - m) from by abel, inner_neg_right]
  constructor <;> intro h <;> nlinarith [hexpand, hinner, h]



theorem d001380 (p : H) :
    p ∈ _root_.GD.N0230.N0669.d001375 ψ m ↔
      ∀ θ, ‖p - m‖ ^ 2 / 2 ≤ ⟪p - m, ψ θ - m⟫ := by
  rw [_root_.GD.N0230.N0669.d001379]
  apply forall_congr'
  intro θ
  constructor <;> intro h <;> linarith



theorem d001381 {u : H} {t : ℝ} (ht : 0 < t) :
    m + t • u ∈ _root_.GD.N0230.N0669.d001375 ψ m ↔
      ∀ θ, t * ‖u‖ ^ 2 ≤ 2 * ⟪u, ψ θ - m⟫ := by
  rw [_root_.GD.N0230.N0669.d001379]
  apply forall_congr'
  intro θ
  have hshift : m + t • u - m = t • u := by abel
  rw [hshift, norm_smul, real_inner_smul_left, Real.norm_eq_abs,
    mul_pow, sq_abs]
  constructor
  · intro h
    have h' : t * (t * ‖u‖ ^ 2) ≤ t * (2 * ⟪u, ψ θ - m⟫) := by
      nlinarith [h]
    exact le_of_mul_le_mul_left h' ht
  · intro h
    nlinarith [mul_le_mul_of_nonneg_left h ht.le]


theorem d001382 (u : H) (t : ℝ) (θ : Θ) :
    ‖m - ψ θ‖ ^ 2 - ‖m + t • u - ψ θ‖ ^ 2 =
      2 * t * ⟪u, ψ θ - m⟫ - t ^ 2 * ‖u‖ ^ 2 := by
  have hsplit : m + t • u - ψ θ = t • u + (m - ψ θ) := by abel
  rw [hsplit, norm_add_sq_real, real_inner_smul_left, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  have hinner : ⟪u, m - ψ θ⟫ = -⟪u, ψ θ - m⟫ := by
    rw [show m - ψ θ = -(ψ θ - m) from by abel, inner_neg_right]
  rw [hinner]
  ring



theorem d001383 {u : H} (hu : ‖u‖ = 1) {c : ℝ}
    (hc : 0 ≤ c) (hfloor : ∀ θ, c ≤ ⟪u, ψ θ - m⟫) (θ : Θ) :
    c ^ 2 ≤ ‖m - ψ θ‖ ^ 2 - ‖m + c • u - ψ θ‖ ^ 2 := by
  rw [_root_.GD.N0230.N0669.d001382, hu]
  nlinarith [mul_nonneg hc
    (by linarith [hfloor θ] : (0 : ℝ) ≤ ⟪u, ψ θ - m⟫ - c)]



theorem d001384 {u : H} (hu : ‖u‖ = 1) {c : ℝ}
    {θ₀ : Θ} (htight : ⟪u, ψ θ₀ - m⟫ = c) (t : ℝ) :
    ‖m - ψ θ₀‖ ^ 2 - ‖m + t • u - ψ θ₀‖ ^ 2 ≤ c ^ 2 := by
  rw [_root_.GD.N0230.N0669.d001382, hu, htight]
  nlinarith [sq_nonneg (t - c)]



theorem d001385 {u : H} (hu : ‖u‖ = 1) {c t : ℝ}
    (hfloor : ∀ θ, c ≤ ⟪u, ψ θ - m⟫)
    (ht0 : 0 < t) (ht2 : t < 2 * c) (θ : Θ) :
    0 < ‖m - ψ θ‖ ^ 2 - ‖m + t • u - ψ θ‖ ^ 2 := by
  rw [_root_.GD.N0230.N0669.d001382, hu]
  nlinarith [mul_le_mul_of_nonneg_left (hfloor θ)
    (by linarith : (0 : ℝ) ≤ 2 * t),
    mul_pos ht0 (by linarith : (0 : ℝ) < 2 * c - t)]





theorem d001386 {u : H} (hu : ‖u‖ = 1) {c α : ℝ}
    (hc : 0 ≤ c) (hα : 0 ≤ α)
    (hfloor : ∀ θ, c ≤ ⟪u, ψ θ - m⟫) (θ : Θ) :
    (2 * α - α ^ 2) * c ^ 2 ≤
      ‖m - ψ θ‖ ^ 2 - ‖m + (α * c) • u - ψ θ‖ ^ 2 := by
  rw [_root_.GD.N0230.N0669.d001382, hu]
  nlinarith [mul_nonneg (mul_nonneg hα hc)
    (by linarith [hfloor θ] : (0 : ℝ) ≤ ⟪u, ψ θ - m⟫ - c)]


theorem d001387 : Convex ℝ (_root_.GD.N0230.N0669.d001375 ψ m) := by
  intro d hd e he s r hs hr hsr
  intro θ
  have h1 : s • (d - ψ θ) + r • (e - ψ θ) =
      s • d + r • e - (s • ψ θ + r • ψ θ) := by
    rw [smul_sub, smul_sub]
    abel
  have h2 : s • ψ θ + r • ψ θ = ψ θ := by
    rw [← add_smul, hsr, one_smul]
  have hcomb : s • d + r • e - ψ θ =
      s • (d - ψ θ) + r • (e - ψ θ) := by
    rw [h1, h2]
  calc
    ‖s • d + r • e - ψ θ‖ = ‖s • (d - ψ θ) + r • (e - ψ θ)‖ := by
      rw [hcomb]
    _ ≤ ‖s • (d - ψ θ)‖ + ‖r • (e - ψ θ)‖ := norm_add_le _ _
    _ = s * ‖d - ψ θ‖ + r * ‖e - ψ θ‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hs, abs_of_nonneg hr]
    _ ≤ s * ‖m - ψ θ‖ + r * ‖m - ψ θ‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (hd θ) hs)
        (mul_le_mul_of_nonneg_left (he θ) hr)
    _ = ‖m - ψ θ‖ := by
      rw [← add_mul, hsr, one_mul]




theorem d001388 (d : H) :
    d ∈ _root_.GD.N0230.N0669.d001375 ψ m ↔
      ∀ θ, _root_.GD.N0230.N0673.d001333 ψ
        (fun _ ↦ m) d θ ≤ 0 := by
  unfold _root_.GD.N0230.N0669.d001375 _root_.GD.N0230.N0673.d001333
  rw [Set.mem_setOf_eq]
  apply forall_congr'
  intro θ
  rw [_root_.GD.N0230.N0669.d001378 (norm_nonneg _) (norm_nonneg _), sub_nonpos]

end

end N0669
end N0230
end GD

#print axioms _root_.GD.N0230.N0669.d001379
#print axioms _root_.GD.N0230.N0669.d001380
#print axioms _root_.GD.N0230.N0669.d001381
#print axioms _root_.GD.N0230.N0669.d001383
#print axioms _root_.GD.N0230.N0669.d001384
#print axioms _root_.GD.N0230.N0669.d001386
#print axioms _root_.GD.N0230.N0669.d001387
#print axioms _root_.GD.N0230.N0669.d001388
