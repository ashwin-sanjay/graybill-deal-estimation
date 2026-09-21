import GD.Module0123












































open Filter
open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0650

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]




theorem d001479 {C : ℕ → Set H} (hconv : ∀ n, Convex ℝ (C n))
    (hanti : Antitone C) {d : H} {p : ℕ → H}
    (hmem : ∀ n, p n ∈ C n)
    (hmin : ∀ n, ∀ r ∈ C n, ‖d - p n‖ ≤ ‖d - r‖)
    {m n : ℕ} (hmn : m ≤ n) :
    ‖p n - p m‖ ^ 2 ≤ 2 * ‖d - p n‖ ^ 2 - 2 * ‖d - p m‖ ^ 2 := by
  have hw : (1 / 2 : ℝ) • p m + (1 / 2 : ℝ) • p n ∈ C m :=
    hconv m (hmem m) (hanti hmn (hmem n))
      (by norm_num) (by norm_num) (by norm_num)
  have hmid := hmin m _ hw
  have hab : (d - p m) + (d - p n) =
      (2 : ℝ) • (d - ((1 / 2 : ℝ) • p m + (1 / 2 : ℝ) • p n)) := by
    rw [smul_sub, smul_add, smul_smul, smul_smul]
    norm_num
    rw [two_smul]
    abel
  have hnorm_ab : ‖(d - p m) + (d - p n)‖ ^ 2 =
      4 * ‖d - ((1 / 2 : ℝ) • p m + (1 / 2 : ℝ) • p n)‖ ^ 2 := by
    rw [hab, norm_smul, Real.norm_eq_abs,
      show |(2 : ℝ)| = 2 by norm_num]
    ring
  have hab2 : (d - p m) - (d - p n) = p n - p m := by abel
  have hpar : ‖(d - p m) - (d - p n)‖ ^ 2 +
      ‖(d - p m) + (d - p n)‖ ^ 2 =
      2 * ‖d - p m‖ ^ 2 + 2 * ‖d - p n‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_add_sq_real]
    ring
  have hmid_sq : ‖d - p m‖ ^ 2 ≤
      ‖d - ((1 / 2 : ℝ) • p m + (1 / 2 : ℝ) • p n)‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hmid 2
  rw [hab2] at hpar
  linarith [hpar, hnorm_ab, hmid_sq]





theorem d001480
    {C : ℕ → Set H} (hconv : ∀ n, Convex ℝ (C n)) (hanti : Antitone C)
    {z : H} (hz : ∀ n, z ∈ C n) (d : H)
    {p : ℕ → H} (hmem : ∀ n, p n ∈ C n)
    (hmin : ∀ n, ∀ r ∈ C n, ‖d - p n‖ ≤ ‖d - r‖) :
    CauchySeq p := by
  have hmono : Monotone (fun n ↦ ‖d - p n‖ ^ 2) := by
    intro a b hab
    exact pow_le_pow_left₀ (norm_nonneg _)
      (hmin a _ (hanti hab (hmem b))) 2
  have hbdd : BddAbove (Set.range fun n ↦ ‖d - p n‖ ^ 2) :=
    ⟨‖d - z‖ ^ 2, Set.forall_mem_range.2 fun n ↦
      pow_le_pow_left₀ (norm_nonneg _) (hmin n z (hz n)) 2⟩
  have hRC : CauchySeq (fun n ↦ ‖d - p n‖ ^ 2) :=
    (tendsto_atTop_ciSup hmono hbdd).cauchySeq
  rw [Metric.cauchySeq_iff] at hRC ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hRC (ε ^ 2 / 2) (by positivity)
  refine ⟨N, fun m hm n hn ↦ ?_⟩
  have habs : |‖d - p n‖ ^ 2 - ‖d - p m‖ ^ 2| < ε ^ 2 / 2 := by
    have := hN m hm n hn
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this
  have hkey : ‖p n - p m‖ ^ 2 ≤
      2 * |‖d - p n‖ ^ 2 - ‖d - p m‖ ^ 2| := by
    rcases le_total m n with h | h
    · have h1 := _root_.GD.N0230.N0650.d001479 hconv hanti hmem hmin h
      have h2 := le_abs_self (‖d - p n‖ ^ 2 - ‖d - p m‖ ^ 2)
      linarith
    · have h1 := _root_.GD.N0230.N0650.d001479 hconv hanti hmem hmin h
      have h2 := neg_abs_le (‖d - p n‖ ^ 2 - ‖d - p m‖ ^ 2)
      have h3 : ‖p n - p m‖ = ‖p m - p n‖ := norm_sub_rev _ _
      rw [h3]
      linarith
  have hsq : ‖p n - p m‖ ^ 2 < ε ^ 2 := by linarith
  rw [dist_eq_norm,
    show ‖p m - p n‖ = ‖p n - p m‖ from norm_sub_rev _ _]
  by_contra hcon
  push Not at hcon
  exact absurd hsq (not_lt.mpr (pow_le_pow_left₀ hε.le hcon 2))




theorem d001481 [CompleteSpace H]
    {C : ℕ → Set H} (hconv : ∀ n, Convex ℝ (C n))
    (hclosed : ∀ n, IsClosed (C n)) (hanti : Antitone C)
    {z : H} (hz : ∀ n, z ∈ C n) (d : H)
    {p : ℕ → H} (hmem : ∀ n, p n ∈ C n)
    (hmin : ∀ n, ∀ r ∈ C n, ‖d - p n‖ ≤ ‖d - r‖) :
    ∃ plim, (∀ n, plim ∈ C n) ∧ Tendsto p atTop (nhds plim) ∧
      ∀ w, (∀ n, w ∈ C n) → ‖d - plim‖ ≤ ‖d - w‖ := by
  obtain ⟨plim, hplim⟩ := cauchySeq_tendsto_of_complete
    (_root_.GD.N0230.N0650.d001480 hconv hanti hz d hmem hmin)
  refine ⟨plim, fun m ↦ ?_, hplim, fun w hw ↦ ?_⟩
  · apply (hclosed m).mem_of_tendsto hplim
    filter_upwards [eventually_ge_atTop m] with n hn
    exact hanti hn (hmem n)
  · have hcont : Tendsto (fun n ↦ ‖d - p n‖) atTop
        (nhds ‖d - plim‖) := (tendsto_const_nhds.sub hplim).norm
    exact le_of_tendsto hcont
      (Eventually.of_forall fun n ↦ hmin n w (hw n))



theorem d001482 {C : Set H} (hC : Convex ℝ C)
    {a b p q : H} (hp : p ∈ C) (hq : q ∈ C)
    (hpmin : ∀ r ∈ C, ‖a - p‖ ≤ ‖a - r‖)
    (hqmin : ∀ r ∈ C, ‖b - q‖ ≤ ‖b - r‖) :
    ‖q - p‖ ^ 2 + ‖(b - a) - (q - p)‖ ^ 2 ≤ ‖b - a‖ ^ 2 := by
  have htax := _root_.GD.N0230.N0661.d001475
    hC hp hq hpmin hqmin
  have hexp : ‖(b - a) - (q - p)‖ ^ 2 =
      ‖b - a‖ ^ 2 - 2 * ⟪q - p, b - a⟫ + ‖q - p‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm]
    try ring
  rw [hexp]
  linarith







theorem d001483 [CompleteSpace H]
    {C : ℕ → Set H} (hconv : ∀ n, Convex ℝ (C n))
    (hclosed : ∀ n, IsClosed (C n)) (hanti : Antitone C)
    {z : H} (hz : ∀ n, z ∈ C n)
    {τ ρ : ℕ → H} {τlim : H}
    (hmem : ∀ n, ρ n ∈ C n)
    (hmin : ∀ n, ∀ r ∈ C n, ‖τ n - ρ n‖ ≤ ‖τ n - r‖)
    (hτ : Tendsto τ atTop (nhds τlim)) :
    ∃ ρlim, (∀ n, ρlim ∈ C n) ∧ Tendsto ρ atTop (nhds ρlim) ∧
      ∀ w, (∀ n, w ∈ C n) → ‖τlim - ρlim‖ ≤ ‖τlim - w‖ := by

  have hproj : ∀ n, ∃ q, q ∈ C n ∧
      ∀ r ∈ C n, ‖τlim - q‖ ≤ ‖τlim - r‖ := by
    intro n
    have hne : (C n).Nonempty := ⟨z, hz n⟩
    obtain ⟨q, hqmem, hq⟩ := exists_norm_eq_iInf_of_complete_convex
      hne ((hclosed n).isComplete) (hconv n) τlim
    refine ⟨q, hqmem, fun r hr ↦ ?_⟩
    rw [hq]
    haveI : Nonempty (C n) := hne.to_subtype
    have hbdd : BddBelow (Set.range fun w : C n ↦ ‖τlim - (w : H)‖) :=
      ⟨0, Set.forall_mem_range.2 fun _ ↦ norm_nonneg _⟩
    exact ciInf_le hbdd ⟨r, hr⟩
  choose q hqmem hqmin using hproj
  obtain ⟨qlim, hqlimmem, hqtend, hqlimmin⟩ :=
    _root_.GD.N0230.N0650.d001481 hconv hclosed hanti hz τlim hqmem hqmin
  refine ⟨qlim, hqlimmem, ?_, hqlimmin⟩


  have hlip : ∀ n, ‖q n - ρ n‖ ≤ ‖τlim - τ n‖ := fun n ↦
    _root_.GD.N0230.N0661.d001477
      (hconv n) (hmem n) (hqmem n) (hmin n) (hqmin n)
  rw [tendsto_iff_dist_tendsto_zero]
  have hτ0 : Tendsto (fun n ↦ ‖τlim - τ n‖) atTop (nhds 0) := by
    have h1 : Tendsto (fun n ↦ τlim - τ n) atTop
        (nhds (τlim - τlim)) := tendsto_const_nhds.sub hτ
    rw [sub_self] at h1
    simpa using h1.norm
  have hq0 : Tendsto (fun n ↦ dist (q n) qlim) atTop (nhds 0) :=
    tendsto_iff_dist_tendsto_zero.mp hqtend
  have hsum : Tendsto (fun n ↦ ‖τlim - τ n‖ + dist (q n) qlim)
      atTop (nhds 0) := by
    simpa using hτ0.add hq0
  refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_) hsum
  calc dist (ρ n) qlim ≤ dist (ρ n) (q n) + dist (q n) qlim :=
        dist_triangle _ _ _
    _ ≤ ‖τlim - τ n‖ + dist (q n) qlim := by
        have h1 : dist (ρ n) (q n) = ‖q n - ρ n‖ := by
          rw [dist_eq_norm, norm_sub_rev]
        linarith [hlip n, h1.le, h1.ge]

end

end N0650
end N0230
end GD

#print axioms _root_.GD.N0230.N0650.d001479
#print axioms _root_.GD.N0230.N0650.d001480
#print axioms _root_.GD.N0230.N0650.d001481
#print axioms _root_.GD.N0230.N0650.d001482
#print axioms _root_.GD.N0230.N0650.d001483
