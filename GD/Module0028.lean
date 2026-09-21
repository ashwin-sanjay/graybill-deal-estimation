import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.Order.IsLUB
import Mathlib.Tactic














open Filter Topology

namespace GD
namespace N0230
namespace N0647

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]


theorem d000344 {K : Set E} (hne : K.Nonempty) (hcl : IsClosed K)
    (hcv : Convex ℝ K) :
    ∃ v ∈ K, ∀ w ∈ K, ‖v‖ ≤ ‖w‖ := by
  obtain ⟨v, hv, hmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hcv (0 : E)
  refine ⟨v, hv, fun w hw => ?_⟩
  have hbdd : BddBelow (Set.range fun w : K => ‖(0 : E) - (w : E)‖) :=
    ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
  have h1 := ciInf_le hbdd ⟨w, hw⟩
  rw [← hmin] at h1
  simpa using h1

omit [CompleteSpace E] in


theorem d000345 {K : Set E} (hcv : Convex ℝ K)
    {v : E} (hv : v ∈ K) (hmin : ∀ w ∈ K, ‖v‖ ≤ ‖w‖) {x : E} (hx : x ∈ K) :
    ‖x - v‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 - 2 * ‖v‖ ^ 2 := by
  have hmid : (2 : ℝ)⁻¹ • (x + v) ∈ K := by
    have := hcv hx hv (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num)
    simpa [smul_add] using this
  have h1 : ‖v‖ ≤ ‖(2 : ℝ)⁻¹ • (x + v)‖ := hmin _ hmid
  have h2 : ‖(2 : ℝ)⁻¹ • (x + v)‖ = 2⁻¹ * ‖x + v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
  rw [h2] at h1
  have h3 : 2 * ‖v‖ ≤ ‖x + v‖ := by linarith
  have h4 : 4 * ‖v‖ ^ 2 ≤ ‖x + v‖ ^ 2 := by
    nlinarith [norm_nonneg v, norm_nonneg (x + v)]
  have hpar := parallelogram_law_with_norm ℝ x v
  nlinarith [hpar, h4]





theorem d000346
    {ι : Type*} [Nonempty ι] (S : ι → Set E)
    (hne : ∀ i, (S i).Nonempty) (hcl : ∀ i, IsClosed (S i))
    (hcv : ∀ i, Convex ℝ (S i))
    (R : ℝ) (hbd : ∀ i, ∀ x ∈ S i, ‖x‖ ≤ R)
    (hdir : ∀ i j, ∃ k, S k ⊆ S i ∧ S k ⊆ S j)
    (m : ι → E) (hm : ∀ i, m i ∈ S i) (hmin : ∀ i, ∀ w ∈ S i, ‖m i‖ ≤ ‖w‖) :
    ∃ x ∈ ⋂ i, S i, (∀ w ∈ ⋂ i, S i, ‖x‖ ≤ ‖w‖) ∧
      ‖x‖ ^ 2 = sSup (Set.range fun i => ‖m i‖ ^ 2) := by
  have key : ∀ i k, S k ⊆ S i →
      ‖m k - m i‖ ^ 2 ≤ 2 * ‖m k‖ ^ 2 - 2 * ‖m i‖ ^ 2 :=
    fun i k hsub => _root_.GD.N0230.N0647.d000345 (hcv i) (hm i) (hmin i) (hsub (hm k))
  have hTne : (Set.range fun i => ‖m i‖ ^ 2).Nonempty := Set.range_nonempty _
  have hTbdd : BddAbove (Set.range fun i => ‖m i‖ ^ 2) :=
    ⟨R ^ 2, by
      rintro _ ⟨i, rfl⟩
      exact pow_le_pow_left₀ (norm_nonneg _) (hbd i _ (hm i)) 2⟩
  have hleL : ∀ i, ‖m i‖ ^ 2 ≤ sSup (Set.range fun i => ‖m i‖ ^ 2) :=
    fun i => le_csSup hTbdd ⟨i, rfl⟩
  obtain ⟨u, hu_mono, hu_lim, hu_mem⟩ := exists_seq_tendsto_sSup hTne hTbdd
  have hu_mem' : ∀ n, ∃ i, ‖m i‖ ^ 2 = u n := fun n => hu_mem n
  choose idx hidx using hu_mem'
  choose meet hmeet1 hmeet2 using hdir
  set L := sSup (Set.range fun i => ‖m i‖ ^ 2) with hL
  have hgap : Tendsto (fun n => L - u n) atTop (𝓝 0) := by
    have := hu_lim.const_sub L
    simpa using this
  have hbound : ∀ i k, S k ⊆ S i → ‖m k - m i‖ ^ 2 ≤ 2 * (L - ‖m i‖ ^ 2) := by
    intro i k h
    have := key i k h
    have := hleL k
    nlinarith

  have hcauchy : CauchySeq (fun n => m (idx n)) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hgap) (ε ^ 2 / 8) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have hN' : L - u N < ε ^ 2 / 8 := by
      have := hN N le_rfl
      rw [Real.dist_eq, sub_zero] at this
      exact lt_of_abs_lt this
    have hn' : L - u n < ε ^ 2 / 8 := by
      have := hu_mono hn
      linarith
    have h1 : ‖m (meet (idx n) (idx N)) - m (idx n)‖ ^ 2 ≤ 2 * (L - u n) := by
      rw [← hidx n]; exact hbound _ _ (hmeet1 _ _)
    have h2 : ‖m (meet (idx n) (idx N)) - m (idx N)‖ ^ 2 ≤ 2 * (L - u N) := by
      rw [← hidx N]; exact hbound _ _ (hmeet2 _ _)
    have h1' : ‖m (meet (idx n) (idx N)) - m (idx n)‖ < ε / 2 := by
      by_contra hcon
      push Not at hcon
      nlinarith [norm_nonneg (m (meet (idx n) (idx N)) - m (idx n))]
    have h2' : ‖m (meet (idx n) (idx N)) - m (idx N)‖ < ε / 2 := by
      by_contra hcon
      push Not at hcon
      nlinarith [norm_nonneg (m (meet (idx n) (idx N)) - m (idx N))]
    rw [dist_eq_norm]
    have htri : ‖m (idx n) - m (idx N)‖ ≤
        ‖m (idx n) - m (meet (idx n) (idx N))‖ +
          ‖m (meet (idx n) (idx N)) - m (idx N)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have hrev : ‖m (idx n) - m (meet (idx n) (idx N))‖ =
        ‖m (meet (idx n) (idx N)) - m (idx n)‖ := norm_sub_rev _ _
    linarith
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy

  have hxmem : ∀ i, x ∈ S i := by
    intro i
    have hdist : Tendsto (fun n => ‖m (meet i (idx n)) - m (idx n)‖) atTop (𝓝 0) := by
      have hsq : Tendsto (fun n => ‖m (meet i (idx n)) - m (idx n)‖ ^ 2) atTop (𝓝 0) := by
        refine squeeze_zero (g := fun n => 2 * (L - u n)) (fun n => sq_nonneg _)
          (fun n => ?_) ?_
        · rw [← hidx n]; exact hbound _ _ (hmeet2 _ _)
        · have := hgap.const_mul 2
          simpa using this
      have := hsq.sqrt
      simpa [Real.sqrt_sq (norm_nonneg _)] using this
    have hx' : Tendsto (fun n => ‖m (idx n) - x‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hx
    have hconv : Tendsto (fun n => m (meet i (idx n))) atTop (𝓝 x) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (g := fun n => ‖m (meet i (idx n)) - m (idx n)‖ + ‖m (idx n) - x‖)
        (fun n => norm_nonneg _) (fun n => ?_) ?_
      · exact norm_sub_le_norm_sub_add_norm_sub _ _ _
      · have := hdist.add hx'
        simpa using this
    exact (hcl i).mem_of_tendsto hconv (Eventually.of_forall fun n => hmeet1 _ _ (hm _))

  have hxnorm : ‖x‖ ^ 2 = L := by
    have h1 : Tendsto (fun n => ‖m (idx n)‖ ^ 2) atTop (𝓝 (‖x‖ ^ 2)) :=
      (hx.norm).pow 2
    have h2 : Tendsto (fun n => ‖m (idx n)‖ ^ 2) atTop (𝓝 L) := by
      simpa [hidx] using hu_lim
    exact tendsto_nhds_unique h1 h2
  refine ⟨x, Set.mem_iInter.2 hxmem, fun w hw => ?_, hxnorm⟩
  have hLw : L ≤ ‖w‖ ^ 2 := by
    refine csSup_le hTne ?_
    rintro _ ⟨i, rfl⟩
    exact pow_le_pow_left₀ (norm_nonneg _) (hmin i w (Set.mem_iInter.1 hw i)) 2
  have h3 : ‖x‖ ^ 2 ≤ ‖w‖ ^ 2 := by rw [hxnorm]; exact hLw
  have h4 := Real.sqrt_le_sqrt h3
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h4



theorem d000347 {ι : Type*} (S : ι → Set E)
    (hcv : ∀ i, Convex ℝ (S i))
    (m : ι → E) (hm : ∀ i, m i ∈ S i) (hmin : ∀ i, ∀ w ∈ S i, ‖m i‖ ≤ ‖w‖)
    (x : E) (hx : ∀ i, x ∈ S i) (i : ι) :
    ‖x - m i‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 - 2 * ‖m i‖ ^ 2 :=
  _root_.GD.N0230.N0647.d000345 (hcv i) (hm i) (hmin i) (hx i)



theorem d000348
    {ι : Type*} [Nonempty ι] (S : ι → Set E)
    (hne : ∀ i, (S i).Nonempty) (hcl : ∀ i, IsClosed (S i))
    (hcv : ∀ i, Convex ℝ (S i))
    (R : ℝ) (hbd : ∀ i, ∀ x ∈ S i, ‖x‖ ≤ R)
    (hdir : ∀ i j, ∃ k, S k ⊆ S i ∧ S k ⊆ S j) :
    (⋂ i, S i).Nonempty := by
  choose m hm hmin using fun i => _root_.GD.N0230.N0647.d000344 (hne i) (hcl i) (hcv i)
  obtain ⟨x, hx, -, -⟩ :=
    _root_.GD.N0230.N0647.d000346 S hne hcl hcv R hbd hdir m hm hmin
  exact ⟨x, hx⟩

end N0647
end N0230
end GD
