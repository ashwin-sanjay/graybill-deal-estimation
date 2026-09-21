import GD.Module0041















namespace GD
namespace N0230
namespace N0648

open Filter Topology
open _root_.GD.N0230.N0685

set_option linter.unusedSectionVars false

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]



theorem d000574
    (C : ℕ → Set E) (p : ℕ → E)
    (hanti : Antitone C)
    (hp : ∀ n, _root_.GD.N0230.N0685.d000511 (C n) 0 (p n))
    {n m : ℕ} (hnm : n ≤ m) :
    ‖p m - p n‖ ^ 2 + ‖p n‖ ^ 2 ≤ ‖p m‖ ^ 2 := by
  have hmem : p m ∈ C n := hanti hnm (hp m).1
  simpa using (_root_.GD.N0230.N0685.d000512 (hp n) hmem)



theorem d000575
    (C : ℕ → Set E) (p : ℕ → E) (plim : E)
    (hp : ∀ n, _root_.GD.N0230.N0685.d000511 (C n) 0 (p n))
    (hplim : _root_.GD.N0230.N0685.d000511 (⋂ n, C n) 0 plim)
    (n : ℕ) :
    ‖plim - p n‖ ^ 2 + ‖p n‖ ^ 2 ≤ ‖plim‖ ^ 2 := by
  have hmem : plim ∈ C n := Set.mem_iInter.mp hplim.1 n
  simpa using (_root_.GD.N0230.N0685.d000512 (hp n) hmem)


theorem d000576
    (C : ℕ → Set E) (p : ℕ → E) (plim : E)
    (hp : ∀ n, _root_.GD.N0230.N0685.d000511 (C n) 0 (p n))
    (hplim : _root_.GD.N0230.N0685.d000511 (⋂ n, C n) 0 plim)
    (n : ℕ) :
    ‖plim - p n‖ ^ 2 ≤ ‖plim‖ ^ 2 - ‖p n‖ ^ 2 := by
  have h := _root_.GD.N0230.N0648.d000575 C p plim hp hplim n
  linarith



theorem d000577
    (C : ℕ → Set E) (p : ℕ → E) (plim e : E)
    (hp : ∀ n, _root_.GD.N0230.N0685.d000511 (C n) 0 (p n))
    (hplim : _root_.GD.N0230.N0685.d000511 (⋂ n, C n) 0 plim)
    (he : e ∈ ⋂ n, C n)
    (n : ℕ) :
    ‖plim - p n‖ ^ 2 ≤ ‖e‖ ^ 2 - ‖p n‖ ^ 2 := by
  have hfinite := _root_.GD.N0230.N0648.d000575 C p plim hp hplim n
  have hfull := _root_.GD.N0230.N0685.d000512 hplim he
  simp only [sub_zero] at hfull
  nlinarith [sq_nonneg ‖e - plim‖]


theorem d000578
    (C : ℕ → Set E) (p : ℕ → E) (plim e : E)
    (hp : ∀ n, _root_.GD.N0230.N0685.d000511 (C n) 0 (p n))
    (hplim : _root_.GD.N0230.N0685.d000511 (⋂ n, C n) 0 plim)
    (he : e ∈ ⋂ n, C n)
    (n : ℕ) :
    ‖plim - p n‖ ≤ Real.sqrt (‖e‖ ^ 2 - ‖p n‖ ^ 2) := by
  have hsq := _root_.GD.N0230.N0648.d000577 C p plim e hp hplim he n
  have hgap : 0 ≤ ‖e‖ ^ 2 - ‖p n‖ ^ 2 :=
    (sq_nonneg ‖plim - p n‖).trans hsq
  rw [← Real.sqrt_sq (norm_nonneg (plim - p n)),
    Real.sqrt_le_sqrt_iff hgap]
  exact hsq




theorem d000579
    (C : ℕ → Set E) (p : ℕ → E) (plim : E)
    (hp : ∀ n, _root_.GD.N0230.N0685.d000511 (C n) 0 (p n))
    (hplim : _root_.GD.N0230.N0685.d000511 (⋂ n, C n) 0 plim)
    (hobj : Tendsto (fun n ↦ ‖p n‖ ^ 2) atTop (𝓝 (‖plim‖ ^ 2))) :
    Tendsto p atTop (𝓝 plim) := by
  have hgap :
      Tendsto (fun n ↦ ‖plim‖ ^ 2 - ‖p n‖ ^ 2) atTop (𝓝 0) := by
    have hconst :
        Tendsto (fun _ : ℕ ↦ ‖plim‖ ^ 2) atTop (𝓝 (‖plim‖ ^ 2)) :=
      tendsto_const_nhds
    simpa only [sub_self] using hconst.sub hobj
  have hsq :
      Tendsto (fun n ↦ ‖plim - p n‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero
      (g := fun n ↦ ‖plim‖ ^ 2 - ‖p n‖ ^ 2) ?_ ?_ hgap
    · intro n
      exact sq_nonneg ‖plim - p n‖
    · intro n
      exact _root_.GD.N0230.N0648.d000576 C p plim hp hplim n
  have hnorm : Tendsto (fun n ↦ ‖plim - p n‖) atTop (𝓝 0) := by
    have hsqrt := hsq.sqrt
    simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg] using hsqrt
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa [norm_sub_rev] using hnorm

end N0648
end N0230
end GD

#print axioms _root_.GD.N0230.N0648.d000574
#print axioms _root_.GD.N0230.N0648.d000575
#print axioms _root_.GD.N0230.N0648.d000576
#print axioms _root_.GD.N0230.N0648.d000577
#print axioms _root_.GD.N0230.N0648.d000578
#print axioms _root_.GD.N0230.N0648.d000579
