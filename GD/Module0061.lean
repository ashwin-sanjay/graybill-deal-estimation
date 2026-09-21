import GD.Module0060


















namespace GD
namespace N0230
namespace N0565

open Filter
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0616
open _root_.GD.N0230.N0596

variable {G Theta D : Type*}



def d000737
    (risk : Theta → D → ENNReal) (objective : D → ℝ) : Prop :=
  ∀ ⦃e d : D⦄, _root_.GD.N0230.N0608.d000672 risk e d → objective e ≤ objective d


def d000738 [Group G] [MulAction G D]
    (objective : D → ℝ) : Prop :=
  ∀ (g : G) (d : D), objective (g • d) = objective d



theorem d000739
    (risk : Theta → D → ENNReal)
    (profile : D → ℝ) (center scale : ℝ)
    (hprofile : _root_.GD.N0230.N0565.d000737 risk profile)
    (hscale : 0 < scale) :
    _root_.GD.N0230.N0565.d000737 risk (fun d ↦ (profile d - center) / scale) := by
  intro e d hed
  exact (div_le_div_iff_of_pos_right hscale).2 (sub_le_sub_right (hprofile hed) center)


theorem d000740
    [Group G] [MulAction G D]
    (profile : D → ℝ) (center scale : ℝ)
    (hprofile : _root_.GD.N0230.N0565.d000738 (G := G) profile) :
    _root_.GD.N0230.N0565.d000738 (G := G) (fun d ↦ (profile d - center) / scale) := by
  intro g d
  dsimp only
  rw [hprofile g d]



theorem d000741
    (risk : Theta → D → ENNReal)
    (approx : ℕ → D → ℝ) (jet : D → ℝ)
    (hmono : ∀ n, _root_.GD.N0230.N0565.d000737 risk (approx n))
    (hlim : ∀ d, Tendsto (fun n ↦ approx n d) atTop (nhds (jet d))) :
    _root_.GD.N0230.N0565.d000737 risk jet := by
  intro e d hed
  have hpair :
      Tendsto (fun n ↦ (approx n e, approx n d)) atTop (nhds (jet e, jet d)) :=
    (hlim e).prodMk_nhds (hlim d)
  have hclosed : IsClosed {z : ℝ × ℝ | z.1 ≤ z.2} :=
    isClosed_le continuous_fst continuous_snd
  exact hclosed.mem_of_tendsto hpair
    (Filter.Eventually.of_forall (fun n ↦ hmono n hed))



theorem d000742
    [Group G] [MulAction G D]
    (approx : ℕ → D → ℝ) (jet : D → ℝ)
    (hinvariant : ∀ n, _root_.GD.N0230.N0565.d000738 (G := G) (approx n))
    (hlim : ∀ d, Tendsto (fun n ↦ approx n d) atTop (nhds (jet d))) :
    _root_.GD.N0230.N0565.d000738 (G := G) jet := by
  intro g d
  apply tendsto_nhds_unique (hlim (g • d))
  exact (hlim d).congr'
    (Filter.Eventually.of_forall (fun n ↦ (hinvariant n g d).symm))





theorem d000743
    [Group G] [MulAction G D]
    {n : ℕ}
    (risk : Theta → D → ENNReal)
    (approx : Fin n → ℕ → D → ℝ)
    (jet : Fin n → D → ℝ)
    (C : Set D) (p : D)
    (happroxMono : ∀ i m, _root_.GD.N0230.N0565.d000737 risk (approx i m))
    (happroxInvariant : ∀ i m, _root_.GD.N0230.N0565.d000738 (G := G) (approx i m))
    (hlim : ∀ i d, Tendsto (fun m ↦ approx i m d) atTop (nhds (jet i d)))
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hlex : _root_.GD.N0230.N0616.d000722 jet C p)
    (hfaithful : _root_.GD.N0230.N0616.d000723 jet C p) :
    (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  apply _root_.GD.N0230.N0616.d000729
    risk jet C p hhereditary
  · intro i e d hed
    exact _root_.GD.N0230.N0565.d000741
      risk (approx i) (jet i) (happroxMono i) (hlim i) hed
  · exact hC
  · intro i g d
    exact _root_.GD.N0230.N0565.d000742
      (approx i) (jet i) (happroxInvariant i) (hlim i) g d
  · exact hlex
  · exact hfaithful






theorem d000744
    [Group G] [MulAction G D]
    (risk : Theta → D → ENNReal)
    (approx : ℕ → ℕ → D → ℝ)
    (jet : ℕ → D → ℝ)
    (C : Set D) (p : D)
    (happroxMono : ∀ i m, _root_.GD.N0230.N0565.d000737 risk (approx i m))
    (happroxInvariant : ∀ i m, _root_.GD.N0230.N0565.d000738 (G := G) (approx i m))
    (hlim : ∀ i d, Tendsto (fun m ↦ approx i m d) atTop (nhds (jet i d)))
    (hhereditary : _root_.GD.N0230.N0616.d000721 risk C)
    (hC : _root_.GD.N0230.N0616.d000726 (G := G) C)
    (hlex : _root_.GD.N0230.N0596.d000730 jet C p)
    (hfaithful : _root_.GD.N0230.N0596.d000731 jet C p) :
    (∀ g : G, g • p = p) ∧ _root_.GD.N0230.N0608.d000674 risk p := by
  apply _root_.GD.N0230.N0596.d000736
    risk jet C p hhereditary
  · intro i e d hed
    exact _root_.GD.N0230.N0565.d000741
      risk (approx i) (jet i) (happroxMono i) (hlim i) hed
  · exact hC
  · intro i g d
    exact _root_.GD.N0230.N0565.d000742
      (approx i) (jet i) (happroxInvariant i) (hlim i) g d
  · exact hlex
  · exact hfaithful

end N0565
end N0230
end GD

#print axioms _root_.GD.N0230.N0565.d000739
#print axioms _root_.GD.N0230.N0565.d000741
#print axioms _root_.GD.N0230.N0565.d000742
#print axioms _root_.GD.N0230.N0565.d000743
#print axioms _root_.GD.N0230.N0565.d000744
