import GD.Module0232
























open Filter

namespace GD
namespace N0230
namespace N0653

noncomputable section

variable {G X : Type*} [Nonempty G] [PseudoMetricSpace X]



def d003537 (act : G → X → X) (x y : X) : Prop :=
  ∃ g : ℕ → G,
    Tendsto (fun n ↦ dist (act (g n) x) (act (g n) y))
      atTop (nhds 0)


def d003538 (act : G → X → X) (x y : X) : Prop :=
  ∃ epsilon : ℝ, 0 < epsilon ∧
    ∀ g : G, epsilon ≤ dist (act g x) (act g y)



theorem d003539
    (act : G → X → X) (x y : X)
    (hnot : ¬ _root_.GD.N0230.N0653.d003538 act x y) :
    _root_.GD.N0230.N0653.d003537 act x y := by
  unfold _root_.GD.N0230.N0653.d003538 at hnot
  push Not at hnot
  have hchoice : ∀ n : ℕ, ∃ g : G,
      dist (act g x) (act g y) < 1 / ((n : ℝ) + 1) := by
    intro n
    exact hnot (1 / ((n : ℝ) + 1)) (by positivity)
  choose g hg using hchoice
  refine ⟨g, squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ (hg n).le) ?_⟩
  exact tendsto_one_div_add_atTop_nhds_zero_nat


theorem d003540
    (act : G → X → X) (x y : X)
    (hsep : _root_.GD.N0230.N0653.d003538 act x y) :
    ¬ _root_.GD.N0230.N0653.d003537 act x y := by
  rintro ⟨g, hzero⟩
  obtain ⟨epsilon, hepsilon, hlower⟩ := hsep
  have hsmall : ∀ᶠ n in atTop,
      dist (act (g n) x) (act (g n) y) < epsilon :=
    (tendsto_order.1 hzero).2 epsilon hepsilon
  obtain ⟨n, hn⟩ := hsmall.exists
  exact (not_lt_of_ge (hlower (g n))) hn


theorem d003541
    (act : G → X → X) (x y : X) :
    ¬ _root_.GD.N0230.N0653.d003537 act x y ↔ _root_.GD.N0230.N0653.d003538 act x y := by
  constructor
  · intro hno
    by_contra hnot
    exact hno (_root_.GD.N0230.N0653.d003539 act x y hnot)
  · exact _root_.GD.N0230.N0653.d003540 act x y


theorem d003542
    (act : G → X → X) (x y : X) :
    _root_.GD.N0230.N0653.d003538 act x y ∨ _root_.GD.N0230.N0653.d003537 act x y := by
  by_cases hsep : _root_.GD.N0230.N0653.d003538 act x y
  · exact Or.inl hsep
  · exact Or.inr (_root_.GD.N0230.N0653.d003539 act x y hsep)



theorem d003543
    (act : G → X → X) (x y : X) (hxy : 0 < dist x y)
    (hisometry : ∀ g : G,
      dist (act g x) (act g y) = dist x y) :
    _root_.GD.N0230.N0653.d003538 act x y := by
  refine ⟨dist x y, hxy, ?_⟩
  intro g
  rw [hisometry g]

end

end N0653
end N0230
end GD

#print axioms _root_.GD.N0230.N0653.d003539
#print axioms _root_.GD.N0230.N0653.d003541
#print axioms _root_.GD.N0230.N0653.d003543
