import GD.Module0127






































open Filter
open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0612

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]



def d001502 (C : Set H) (x : ℕ → H) : Prop :=
  ∀ z ∈ C, ∀ n, ‖x (n + 1) - z‖ ≤ ‖x n - z‖


theorem d001503 {C : Set H} {F : H → H}
    (hnonexp : ∀ x y : H, ‖F x - F y‖ ≤ ‖x - y‖)
    (hfix : ∀ z ∈ C, F z = z) (x₀ : H) :
    _root_.GD.N0230.N0612.d001502 C (fun n ↦ F^[n] x₀) := by
  intro z hz n
  have h1 : F^[n + 1] x₀ = F (F^[n] x₀) :=
    Function.iterate_succ_apply' F n x₀
  calc ‖F^[n + 1] x₀ - z‖ = ‖F (F^[n] x₀) - F z‖ := by
        rw [h1, hfix z hz]
    _ ≤ ‖F^[n] x₀ - z‖ := hnonexp _ _



theorem d001504 {C : Set H} {x : ℕ → H}
    (hFej : _root_.GD.N0230.N0612.d001502 C x) {z : H} (hz : z ∈ C) :
    Antitone fun n ↦ ‖x n - z‖ :=
  antitone_nat_of_succ_le fun n ↦ hFej z hz n




theorem d001505 {C : Set H} (hC : Convex ℝ C)
    {x p : ℕ → H} (hFej : _root_.GD.N0230.N0612.d001502 C x)
    (hmem : ∀ n, p n ∈ C)
    (hmin : ∀ n, ∀ r ∈ C, ‖x n - p n‖ ≤ ‖x n - r‖)
    {m n : ℕ} (hmn : m ≤ n) :
    ‖p n - p m‖ ^ 2 ≤ 2 * ‖x m - p m‖ ^ 2 - 2 * ‖x n - p n‖ ^ 2 := by
  have hw : (1 / 2 : ℝ) • p m + (1 / 2 : ℝ) • p n ∈ C :=
    hC (hmem m) (hmem n) (by norm_num) (by norm_num) (by norm_num)
  have hmid := hmin n _ hw
  have hab : (x n - p m) + (x n - p n) =
      (2 : ℝ) • (x n - ((1 / 2 : ℝ) • p m + (1 / 2 : ℝ) • p n)) := by
    rw [smul_sub, smul_add, smul_smul, smul_smul]
    norm_num
    rw [two_smul]
    abel
  have hnorm_ab : ‖(x n - p m) + (x n - p n)‖ ^ 2 =
      4 * ‖x n - ((1 / 2 : ℝ) • p m + (1 / 2 : ℝ) • p n)‖ ^ 2 := by
    rw [hab, norm_smul, Real.norm_eq_abs,
      show |(2 : ℝ)| = 2 by norm_num]
    ring
  have hab2 : (x n - p m) - (x n - p n) = p n - p m := by abel
  have hadd := norm_add_sq_real (x n - p m) (x n - p n)
  have hsub := norm_sub_sq_real (x n - p m) (x n - p n)
  have hpar : ‖(x n - p m) - (x n - p n)‖ ^ 2 +
      ‖(x n - p m) + (x n - p n)‖ ^ 2 =
      2 * ‖x n - p m‖ ^ 2 + 2 * ‖x n - p n‖ ^ 2 := by
    linarith [hadd, hsub]
  rw [hab2] at hpar
  have hmid_sq : ‖x n - p n‖ ^ 2 ≤
      ‖x n - ((1 / 2 : ℝ) • p m + (1 / 2 : ℝ) • p n)‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hmid 2
  have hfej_sq : ‖x n - p m‖ ^ 2 ≤ ‖x m - p m‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _)
      (_root_.GD.N0230.N0612.d001504 hFej (hmem m) hmn) 2
  linarith [hpar, hnorm_ab, hmid_sq, hfej_sq]




theorem d001506 {C : Set H} (hC : Convex ℝ C)
    {x p : ℕ → H} (hFej : _root_.GD.N0230.N0612.d001502 C x)
    (hmem : ∀ n, p n ∈ C)
    (hmin : ∀ n, ∀ r ∈ C, ‖x n - p n‖ ≤ ‖x n - r‖) :
    CauchySeq p := by
  have hdmono : ∀ n, ‖x (n + 1) - p (n + 1)‖ ≤ ‖x n - p n‖ :=
    fun n ↦ le_trans (hmin (n + 1) (p n) (hmem n))
      (hFej (p n) (hmem n) n)
  have hdanti : Antitone (fun n : ℕ ↦ ‖x n - p n‖) :=
    antitone_nat_of_succ_le (f := fun n : ℕ ↦ ‖x n - p n‖) hdmono
  have hRanti : Antitone (fun n ↦ ‖x n - p n‖ ^ 2) := by
    intro a b hab
    exact pow_le_pow_left₀ (norm_nonneg _) (hdanti hab) 2
  have hbdd : BddBelow (Set.range fun n ↦ ‖x n - p n‖ ^ 2) :=
    ⟨0, Set.forall_mem_range.2 fun n ↦ by positivity⟩
  have hRC : CauchySeq (fun n ↦ ‖x n - p n‖ ^ 2) :=
    (tendsto_atTop_ciInf hRanti hbdd).cauchySeq
  rw [Metric.cauchySeq_iff] at hRC ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hRC (ε ^ 2 / 2) (by positivity)
  refine ⟨N, fun m hm n hn ↦ ?_⟩
  have habs : |‖x m - p m‖ ^ 2 - ‖x n - p n‖ ^ 2| < ε ^ 2 / 2 := by
    have := hN m hm n hn
    rwa [Real.dist_eq] at this
  have hkey : ‖p n - p m‖ ^ 2 ≤
      2 * |‖x m - p m‖ ^ 2 - ‖x n - p n‖ ^ 2| := by
    rcases le_total m n with h | h
    · have h1 := _root_.GD.N0230.N0612.d001505 hC hFej hmem hmin h
      have h2 := le_abs_self (‖x m - p m‖ ^ 2 - ‖x n - p n‖ ^ 2)
      linarith
    · have h1 := _root_.GD.N0230.N0612.d001505 hC hFej hmem hmin h
      have h2 := neg_abs_le (‖x m - p m‖ ^ 2 - ‖x n - p n‖ ^ 2)
      have h3 : ‖p n - p m‖ = ‖p m - p n‖ := norm_sub_rev _ _
      rw [h3]
      linarith
  have hsq : ‖p n - p m‖ ^ 2 < ε ^ 2 := by linarith
  rw [dist_eq_norm,
    show ‖p m - p n‖ = ‖p n - p m‖ from norm_sub_rev _ _]
  by_contra hcon
  push Not at hcon
  exact absurd hsq (not_lt.mpr (pow_le_pow_left₀ hε.le hcon 2))


theorem d001507 [CompleteSpace H] {C : Set H}
    (hC : Convex ℝ C) (hclosed : IsClosed C)
    {x p : ℕ → H} (hFej : _root_.GD.N0230.N0612.d001502 C x)
    (hmem : ∀ n, p n ∈ C)
    (hmin : ∀ n, ∀ r ∈ C, ‖x n - p n‖ ≤ ‖x n - r‖) :
    ∃ plim ∈ C, Tendsto p atTop (nhds plim) := by
  obtain ⟨plim, hplim⟩ := cauchySeq_tendsto_of_complete
    (_root_.GD.N0230.N0612.d001506 hC hFej hmem hmin)
  exact ⟨plim, hclosed.mem_of_tendsto hplim
    (Eventually.of_forall hmem), hplim⟩




theorem d001508 [CompleteSpace H]
    {C : Set H} (hC : Convex ℝ C) (hclosed : IsClosed C)
    (hne : C.Nonempty) {F : H → H}
    (hnonexp : ∀ x y : H, ‖F x - F y‖ ≤ ‖x - y‖)
    (hfix : ∀ z ∈ C, F z = z) (x₀ : H) :
    ∃ p : ℕ → H, (∀ n, p n ∈ C) ∧
      (∀ n, ∀ r ∈ C, ‖F^[n] x₀ - p n‖ ≤ ‖F^[n] x₀ - r‖) ∧
      ∃ plim ∈ C, Tendsto p atTop (nhds plim) := by
  have hproj : ∀ n : ℕ, ∃ q, q ∈ C ∧
      ∀ r ∈ C, ‖F^[n] x₀ - q‖ ≤ ‖F^[n] x₀ - r‖ := by
    intro n
    obtain ⟨q, hqmem, hq⟩ := exists_norm_eq_iInf_of_complete_convex
      hne hclosed.isComplete hC (F^[n] x₀)
    refine ⟨q, hqmem, fun r hr ↦ ?_⟩
    rw [hq]
    haveI : Nonempty C := hne.to_subtype
    have hbdd : BddBelow (Set.range
        fun w : C ↦ ‖F^[n] x₀ - (w : H)‖) :=
      ⟨0, Set.forall_mem_range.2 fun _ ↦ norm_nonneg _⟩
    exact ciInf_le hbdd ⟨r, hr⟩
  choose p hpmem hpmin using hproj
  exact ⟨p, hpmem, hpmin,
    _root_.GD.N0230.N0612.d001507 hC hclosed
      (_root_.GD.N0230.N0612.d001503 hnonexp hfix x₀) hpmem hpmin⟩

end

end N0612
end N0230
end GD

#print axioms _root_.GD.N0230.N0612.d001503
#print axioms _root_.GD.N0230.N0612.d001505
#print axioms _root_.GD.N0230.N0612.d001506
#print axioms _root_.GD.N0230.N0612.d001507
#print axioms _root_.GD.N0230.N0612.d001508
