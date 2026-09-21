import GD.Module0045
















namespace GD
namespace N0230
namespace N0649

open Filter Topology
open _root_.GD.N0230.N0685 _root_.GD.N0230.N0648

set_option linter.unusedSectionVars false

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]



theorem d000580
    (C : ℕ → Set E) (p : ℕ → E)
    (hanti : Antitone C)
    (hp : ∀ n, _root_.GD.N0230.N0685.d000511 (C n) 0 (p n)) :
    Monotone (fun n ↦ ‖p n‖ ^ 2) := by
  intro n m hnm
  have h := _root_.GD.N0230.N0648.d000574 C p hanti hp hnm
  nlinarith [sq_nonneg ‖p m - p n‖]



theorem d000581
    (C : ℕ → Set E) (p : ℕ → E) (e : E)
    (hp : ∀ n, _root_.GD.N0230.N0685.d000511 (C n) 0 (p n))
    (he : e ∈ ⋂ n, C n) :
    BddAbove (Set.range (fun n ↦ ‖p n‖ ^ 2)) := by
  refine ⟨‖e‖ ^ 2, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hn : e ∈ C n := Set.mem_iInter.mp he n
  have h := _root_.GD.N0230.N0685.d000512 (hp n) hn
  simp only [sub_zero] at h
  nlinarith [sq_nonneg ‖e - p n‖]



theorem d000582
    (C : ℕ → Set E) (p : ℕ → E) (e : E)
    (hanti : Antitone C)
    (hp : ∀ n, _root_.GD.N0230.N0685.d000511 (C n) 0 (p n))
    (he : e ∈ ⋂ n, C n) :
    CauchySeq p := by
  let a : ℕ → ℝ := fun n ↦ ‖p n‖ ^ 2
  have hmono : Monotone a := _root_.GD.N0230.N0649.d000580 C p hanti hp
  have hbdd : BddAbove (Set.range a) := _root_.GD.N0230.N0649.d000581 C p e hp he
  have ha : Tendsto a atTop (nhds (⨆ n, a n)) :=
    tendsto_atTop_ciSup hmono hbdd
  have hca : CauchySeq a := ha.cauchySeq
  rw [Metric.cauchySeq_iff] at hca ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hca (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, ?_⟩
  intro m hm n hn
  rcases le_total n m with hnm | hmn
  · have htax := _root_.GD.N0230.N0648.d000574 C p hanti hp hnm
    have hscalar := hN m hm n hn
    rw [Real.dist_eq] at hscalar
    have hdiff : 0 ≤ a m - a n := sub_nonneg.mpr (hmono hnm)
    have hsquare : ‖p m - p n‖ ^ 2 < ε ^ 2 := by
      dsimp [a] at htax hscalar ⊢
      rw [abs_of_nonneg hdiff] at hscalar
      nlinarith
    rw [dist_eq_norm]
    have hnonneg := norm_nonneg (p m - p n)
    nlinarith
  · have htax := _root_.GD.N0230.N0648.d000574 C p hanti hp hmn
    have hscalar := hN n hn m hm
    rw [Real.dist_eq] at hscalar
    have hdiff : 0 ≤ a n - a m := sub_nonneg.mpr (hmono hmn)
    have hsquare : ‖p n - p m‖ ^ 2 < ε ^ 2 := by
      dsimp [a] at htax hscalar ⊢
      rw [abs_of_nonneg hdiff] at hscalar
      nlinarith
    rw [dist_eq_norm, norm_sub_rev]
    have hnonneg := norm_nonneg (p n - p m)
    nlinarith






theorem d000583
    [CompleteSpace E]
    (C : ℕ → Set E) (p : ℕ → E) (plim : E)
    (hanti : Antitone C)
    (hclosed : ∀ n, IsClosed (C n))
    (hp : ∀ n, _root_.GD.N0230.N0685.d000511 (C n) 0 (p n))
    (hplim : _root_.GD.N0230.N0685.d000511 (⋂ n, C n) 0 plim) :
    Tendsto p atTop (nhds plim) := by
  have hcauchy : CauchySeq p :=
    _root_.GD.N0230.N0649.d000582 C p plim hanti hp hplim.1
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hqmem : q ∈ ⋂ n, C n := by
    refine Set.mem_iInter.mpr fun n ↦ ?_
    apply (hclosed n).mem_of_tendsto hq
    filter_upwards [eventually_ge_atTop n] with m hm
    exact hanti hm (hp m).1
  have hqnorm : ‖q‖ ≤ ‖plim‖ := by
    have hnorm : Tendsto (fun n ↦ ‖p n‖) atTop (nhds ‖q‖) :=
      continuous_norm.tendsto q |>.comp hq
    apply le_of_tendsto' hnorm
    intro n
    have h := _root_.GD.N0230.N0648.d000575 C p plim hp hplim n
    nlinarith [norm_nonneg (p n), norm_nonneg plim,
      sq_nonneg ‖plim - p n‖]
  have htax := _root_.GD.N0230.N0685.d000512 hplim hqmem
  simp only [sub_zero] at htax
  have hzero : ‖q - plim‖ = 0 := by
    nlinarith [sq_nonneg ‖q - plim‖, norm_nonneg q, norm_nonneg plim]
  have hqeq : q = plim := sub_eq_zero.mp (norm_eq_zero.mp hzero)
  simpa [hqeq] using hq



theorem d000584
    [CompleteSpace E]
    (C : ℕ → Set E) (p : ℕ → E) (plim : E)
    (hanti : Antitone C)
    (hclosed : ∀ n, IsClosed (C n))
    (hp : ∀ n, _root_.GD.N0230.N0685.d000511 (C n) 0 (p n))
    (hplim : _root_.GD.N0230.N0685.d000511 (⋂ n, C n) 0 plim) :
    Tendsto (fun n ↦ ‖p n‖ ^ 2) atTop (nhds (‖plim‖ ^ 2)) := by
  have hpconv := _root_.GD.N0230.N0649.d000583 C p plim hanti hclosed hp hplim
  exact ((continuous_norm.comp continuous_id).pow 2).tendsto plim |>.comp hpconv



theorem d000585
    [CompleteSpace E]
    (C : ℕ → Set E) (p : ℕ → E) (plim : E)
    (hanti : Antitone C)
    (hclosed : ∀ n, IsClosed (C n))
    (hp : ∀ n, _root_.GD.N0230.N0685.d000511 (C n) 0 (p n))
    (hplim : _root_.GD.N0230.N0685.d000511 (⋂ n, C n) 0 plim) :
    (⨆ n, ‖p n‖ ^ 2) = ‖plim‖ ^ 2 := by
  have hmono := _root_.GD.N0230.N0649.d000580 C p hanti hp
  have hbdd := _root_.GD.N0230.N0649.d000581 C p plim hp hplim.1
  have hsup : Tendsto (fun n ↦ ‖p n‖ ^ 2) atTop
      (nhds (⨆ n, ‖p n‖ ^ 2)) := tendsto_atTop_ciSup hmono hbdd
  exact tendsto_nhds_unique hsup
    (_root_.GD.N0230.N0649.d000584 C p plim hanti hclosed hp hplim)

end N0649
end N0230
end GD

#print axioms _root_.GD.N0230.N0649.d000580
#print axioms _root_.GD.N0230.N0649.d000581
#print axioms _root_.GD.N0230.N0649.d000582
#print axioms _root_.GD.N0230.N0649.d000583
#print axioms _root_.GD.N0230.N0649.d000584
#print axioms _root_.GD.N0230.N0649.d000585
