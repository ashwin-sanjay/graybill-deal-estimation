import GD.Module0041

























namespace GD
namespace N0230
namespace N0652

open _root_.GD.N0230.N0685
open Filter Topology

set_option linter.unusedSectionVars false

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]





theorem d000635
    {C D : Set E} {p q r : E}
    (hCD : C ⊆ D)
    (hp : _root_.GD.N0230.N0685.d000511 D 0 p)
    (hq : _root_.GD.N0230.N0685.d000511 C 0 q)
    (hr : r ∈ C)
    (hradial : ‖r‖ ≤ ‖p‖) :
    p = q ∧ q = r := by
  have hpq : ‖q - p‖ ^ 2 + ‖p‖ ^ 2 ≤ ‖q‖ ^ 2 := by
    simpa using _root_.GD.N0230.N0685.d000512 hp (hCD hq.1)
  have hqr : ‖r - q‖ ^ 2 + ‖q‖ ^ 2 ≤ ‖r‖ ^ 2 := by
    simpa using _root_.GD.N0230.N0685.d000512 hq hr
  have hradial_sq : ‖r‖ ^ 2 ≤ ‖p‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg r) (norm_nonneg p)).2 hradial
  have hsum : ‖q - p‖ ^ 2 + ‖r - q‖ ^ 2 ≤ 0 := by
    linarith
  have hqp_sq : ‖q - p‖ ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg ‖r - q‖]
  have hrq_sq : ‖r - q‖ ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg ‖q - p‖]
  have hqp : q = p := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (q - p)]
  have hrq : r = q := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (r - q)]
  exact ⟨hqp.symm, hrq.symm⟩





theorem d000636
    {K : Set E} {x z : E} (hz : _root_.GD.N0230.N0685.d000511 K x z) :
    Metric.infDist x K = ‖x - z‖ := by
  apply le_antisymm
  · simpa [dist_eq_norm] using Metric.infDist_le_dist_of_mem hz.1
  · refine (Metric.le_infDist ⟨z, hz.1⟩).2 ?_
    intro y hy
    have htax := _root_.GD.N0230.N0685.d000512 hz hy
    have hnorm : ‖z - x‖ ≤ ‖y - x‖ := by
      apply (sq_le_sq₀ (norm_nonneg (z - x)) (norm_nonneg (y - x))).1
      nlinarith [sq_nonneg ‖y - z‖]
    simpa [dist_eq_norm, norm_sub_rev] using hnorm





theorem d000637
    {C D : Set E} {p q r c : E} {B ε δ : ℝ}
    (hCD : C ⊆ D)
    (hp : _root_.GD.N0230.N0685.d000511 D 0 p)
    (hq : _root_.GD.N0230.N0685.d000511 C 0 q)
    (hc : c ∈ C)
    (hnear : ‖r - c‖ ≤ δ)
    (hδ : 0 ≤ δ)
    (hpB : ‖p‖ ≤ B)
    (hradial : ‖r‖ ^ 2 ≤ ‖p‖ ^ 2 + ε) :
    ‖q - r‖ ≤
      δ + Real.sqrt (ε + 2 * Real.sqrt (B ^ 2 + ε) * δ + δ ^ 2) := by
  have hpq : ‖q - p‖ ^ 2 + ‖p‖ ^ 2 ≤ ‖q‖ ^ 2 := by
    simpa using _root_.GD.N0230.N0685.d000512 hp (hCD hq.1)
  have hqc : ‖c - q‖ ^ 2 + ‖q‖ ^ 2 ≤ ‖c‖ ^ 2 := by
    simpa using _root_.GD.N0230.N0685.d000512 hq hc
  have hp_sq_le_q_sq : ‖p‖ ^ 2 ≤ ‖q‖ ^ 2 := by
    nlinarith [sq_nonneg ‖q - p‖]
  have hB : 0 ≤ B := (norm_nonneg p).trans hpB
  have hp_sq_le_B_sq : ‖p‖ ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ (norm_nonneg p) hB).2 hpB
  have hr_sq_le_B_sq : ‖r‖ ^ 2 ≤ B ^ 2 + ε := by
    linarith
  have hBε : 0 ≤ B ^ 2 + ε :=
    (sq_nonneg ‖r‖).trans hr_sq_le_B_sq
  have hr_le_sqrt : ‖r‖ ≤ Real.sqrt (B ^ 2 + ε) := by
    rw [← Real.sqrt_sq (norm_nonneg r), Real.sqrt_le_sqrt_iff hBε]
    exact hr_sq_le_B_sq
  have hc_le : ‖c‖ ≤ ‖r‖ + δ := by
    calc
      ‖c‖ = ‖(c - r) + r‖ := by
        congr 1
        abel
      _ ≤ ‖c - r‖ + ‖r‖ := norm_add_le _ _
      _ ≤ δ + ‖r‖ := by
        gcongr
        simpa [norm_sub_rev] using hnear
      _ = ‖r‖ + δ := by ring
  have hc_sq_le : ‖c‖ ^ 2 ≤ (‖r‖ + δ) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg c) (add_nonneg (norm_nonneg r) hδ)).2 hc_le
  have hcross : 2 * ‖r‖ * δ ≤ 2 * Real.sqrt (B ^ 2 + ε) * δ := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hr_le_sqrt (by norm_num)) hδ
  have hrepair_sq :
      ‖c - q‖ ^ 2 ≤
        ε + 2 * Real.sqrt (B ^ 2 + ε) * δ + δ ^ 2 := by
    nlinarith
  have hradicand :
      0 ≤ ε + 2 * Real.sqrt (B ^ 2 + ε) * δ + δ ^ 2 :=
    (sq_nonneg ‖c - q‖).trans hrepair_sq
  have hrepair :
      ‖c - q‖ ≤
        Real.sqrt (ε + 2 * Real.sqrt (B ^ 2 + ε) * δ + δ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg (c - q)),
      Real.sqrt_le_sqrt_iff hradicand]
    exact hrepair_sq
  calc
    ‖q - r‖ = ‖(q - c) + (c - r)‖ := by
      congr 1
      abel
    _ ≤ ‖q - c‖ + ‖c - r‖ := norm_add_le _ _
    _ ≤
        Real.sqrt (ε + 2 * Real.sqrt (B ^ 2 + ε) * δ + δ ^ 2) + δ := by
      gcongr
      · simpa [norm_sub_rev] using hrepair
      · simpa [norm_sub_rev] using hnear
    _ = δ + Real.sqrt (ε + 2 * Real.sqrt (B ^ 2 + ε) * δ + δ ^ 2) := by
      ring







theorem d000638
    {C D : Set E} {p q r : E} {B ε δ : ℝ}
    (hCD : C ⊆ D)
    (hp : _root_.GD.N0230.N0685.d000511 D 0 p)
    (hq : _root_.GD.N0230.N0685.d000511 C 0 q)
    (hnear : Metric.infDist r C ≤ δ)
    (hδ : 0 ≤ δ)
    (hpB : ‖p‖ ≤ B)
    (hradial : ‖r‖ ^ 2 ≤ ‖p‖ ^ 2 + ε) :
    ‖q - r‖ ≤
      δ + Real.sqrt (ε + 2 * Real.sqrt (B ^ 2 + ε) * δ + δ ^ 2) := by
  let δn : ℕ → ℝ := fun n ↦ δ + 1 / ((n : ℝ) + 1)
  have hδn_pos (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  have hbounds : ∀ n,
      ‖q - r‖ ≤
        δn n + Real.sqrt
          (ε + 2 * Real.sqrt (B ^ 2 + ε) * δn n + (δn n) ^ 2) := by
    intro n
    have hinf : Metric.infDist r C < δn n := by
      dsimp [δn]
      linarith [hδn_pos n]
    obtain ⟨c, hc, hrc⟩ :=
      (Metric.infDist_lt_iff ⟨q, hq.1⟩).mp hinf
    have hrc' : ‖r - c‖ ≤ δn n := by
      simpa [dist_eq_norm] using hrc.le
    have hδn_nonneg : 0 ≤ δn n := by
      dsimp [δn]
      linarith [hδn_pos n]
    exact _root_.GD.N0230.N0652.d000637
      hCD hp hq hc hrc' hδn_nonneg hpB hradial
  have hδn : Tendsto δn atTop (nhds δ) := by
    have hzero :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [δn] using tendsto_const_nhds.add hzero
  let bound : ℝ → ℝ := fun t ↦
    t + Real.sqrt (ε + 2 * Real.sqrt (B ^ 2 + ε) * t + t ^ 2)
  have hbound_cont : Continuous bound := by
    dsimp [bound]
    fun_prop
  have hbound_lim :
      Tendsto (fun n ↦ bound (δn n)) atTop (nhds (bound δ)) :=
    (hbound_cont.tendsto δ).comp hδn
  have hfinal : ‖q - r‖ ≤ bound δ :=
    ge_of_tendsto' hbound_lim hbounds
  simpa [bound] using hfinal




theorem d000639
    [CompleteSpace E]
    {C D : Set E} {p q r : E} {B ε δ : ℝ}
    (hCD : C ⊆ D)
    (hp : _root_.GD.N0230.N0685.d000511 D 0 p)
    (hq : _root_.GD.N0230.N0685.d000511 C 0 q)
    (hCclosed : IsClosed C)
    (hCconvex : Convex ℝ C)
    (hnear : Metric.infDist r C ≤ δ)
    (hδ : 0 ≤ δ)
    (hpB : ‖p‖ ≤ B)
    (hradial : ‖r‖ ^ 2 ≤ ‖p‖ ^ 2 + ε) :
    ‖q - r‖ ≤
      δ + Real.sqrt (ε + 2 * Real.sqrt (B ^ 2 + ε) * δ + δ ^ 2) := by
  obtain ⟨c, hc⟩ :=
    _root_.GD.N0230.N0685.d000521 ⟨q, hq.1⟩ hCclosed.isComplete hCconvex r
  have hrc : ‖r - c‖ ≤ δ := by
    rw [← _root_.GD.N0230.N0652.d000636 hc]
    exact hnear
  exact _root_.GD.N0230.N0652.d000637
    hCD hp hq hc.1 hrc hδ hpB hradial





theorem d000640
    (T : E → E) (hT : Isometry T) (q r : E) :
    ‖T q - q‖ ≤ ‖T r - r‖ + 2 * ‖q - r‖ := by
  have hdecomp :
      T q - q = (T q - T r) + ((T r - r) + (r - q)) := by
    abel
  calc
    ‖T q - q‖ = ‖(T q - T r) + ((T r - r) + (r - q))‖ := by rw [hdecomp]
    _ ≤ ‖T q - T r‖ + ‖(T r - r) + (r - q)‖ := norm_add_le _ _
    _ ≤ ‖T q - T r‖ + (‖T r - r‖ + ‖r - q‖) := by
      gcongr
      exact norm_add_le _ _
    _ = ‖q - r‖ + (‖T r - r‖ + ‖q - r‖) := by
      have hdist : ‖T q - T r‖ = ‖q - r‖ := by
        simpa [dist_eq_norm] using hT.dist_eq q r
      rw [hdist, norm_sub_rev]
    _ = ‖T r - r‖ + 2 * ‖q - r‖ := by ring


theorem d000641
    (T : E → E) (hT : Isometry T)
    {C D : Set E} {p q r c : E} {B ε δ : ℝ}
    (hCD : C ⊆ D)
    (hp : _root_.GD.N0230.N0685.d000511 D 0 p)
    (hq : _root_.GD.N0230.N0685.d000511 C 0 q)
    (hc : c ∈ C)
    (hnear : ‖r - c‖ ≤ δ)
    (hδ : 0 ≤ δ)
    (hpB : ‖p‖ ≤ B)
    (hradial : ‖r‖ ^ 2 ≤ ‖p‖ ^ 2 + ε) :
    ‖T q - q‖ ≤
      ‖T r - r‖ +
        2 * (δ + Real.sqrt
          (ε + 2 * Real.sqrt (B ^ 2 + ε) * δ + δ ^ 2)) := by
  calc
    ‖T q - q‖ ≤ ‖T r - r‖ + 2 * ‖q - r‖ :=
      _root_.GD.N0230.N0652.d000640 T hT q r
    _ ≤
        ‖T r - r‖ +
          2 * (δ + Real.sqrt
            (ε + 2 * Real.sqrt (B ^ 2 + ε) * δ + δ ^ 2)) := by
      gcongr
      exact _root_.GD.N0230.N0652.d000637
        hCD hp hq hc hnear hδ hpB hradial

end N0652
end N0230
end GD

#print axioms _root_.GD.N0230.N0652.d000635
#print axioms _root_.GD.N0230.N0652.d000637
#print axioms _root_.GD.N0230.N0652.d000638
#print axioms _root_.GD.N0230.N0652.d000639
#print axioms _root_.GD.N0230.N0652.d000641
