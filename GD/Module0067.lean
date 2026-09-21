import GD.Module0066
import Mathlib.Algebra.BigOperators.Group.Finset.Basic



























open scoped BigOperators
open Set

namespace GD
namespace N0230
namespace N0625

open _root_.GD.N0230.N0556
open _root_.GD.N0230.N0630

variable {G Θ Rule : Type*}


def d000798
    [Group G] [MulAction G Θ] [MulAction G Rule]
    (risk : Θ → Rule → ℝ) : Prop :=
  ∀ (g : G) (θ : Θ) (d : Rule),
    risk (g • θ) (g • d) = risk θ d


def d000799
    [Group G] [MulAction G Rule]
    (objective : Rule → ℝ) : Prop :=
  ∀ (g : G) (d : Rule), objective (g • d) = objective d


def d000800
    [Group G] [MulAction G Rule]
    (C : Set Rule) : Prop :=
  ∀ (g : G) (d : Rule), d ∈ C → g • d ∈ C







def d000801
    (objective : Rule → ℝ) (C : Set Rule) (star : Rule) : Prop :=
  star ∈ C ∧
    (∀ d, d ∈ C → objective star ≤ objective d) ∧
    (∀ d, d ∈ C → objective d = objective star → d = star)





def d000802
    (risk : Θ → Rule → ℝ) (objective : Rule → ℝ) : Prop :=
  ∀ ⦃e d⦄, _root_.GD.N0230.N0556.d000028 risk e d → objective e ≤ objective d

variable [Group G] [MulAction G Θ] [MulAction G Rule]


theorem d000803
    (risk : Θ → Rule → ℝ)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    (g : G) (θ : Θ) (d : Rule) :
    risk θ (g • d) = risk (g⁻¹ • θ) d := by
  simpa using hRisk g (g⁻¹ • θ) d


theorem d000804
    (risk : Θ → Rule → ℝ)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    {e d : Rule}
    (hed : _root_.GD.N0230.N0556.d000028 risk e d)
    (g : G) :
    _root_.GD.N0230.N0556.d000028 risk (g • e) (g • d) := by
  intro θ
  rw [_root_.GD.N0230.N0625.d000803 risk hRisk g θ e,
      _root_.GD.N0230.N0625.d000803 risk hRisk g θ d]
  exact hed (g⁻¹ • θ)


theorem d000805
    (risk : Θ → Rule → ℝ)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    {e d : Rule}
    (hed : _root_.GD.N0230.N0556.d000029 risk e d)
    (g : G) :
    _root_.GD.N0230.N0556.d000029 risk (g • e) (g • d) := by
  refine ⟨_root_.GD.N0230.N0625.d000804 risk hRisk hed.1 g, ?_⟩
  obtain ⟨θ, hθ⟩ := hed.2
  refine ⟨g • θ, ?_⟩
  rw [hRisk g θ e, hRisk g θ d]
  exact hθ





theorem d000806
    (risk : Θ → Rule → ℝ)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    (bar : Rule)
    (hbar : ∀ g : G, g • bar = bar)
    {d : Rule}
    (hd : _root_.GD.N0230.N0556.d000030 risk bar d)
    (g : G) :
    _root_.GD.N0230.N0556.d000030 risk bar (g • d) := by
  intro θ
  rw [_root_.GD.N0230.N0625.d000803 risk hRisk g θ d]
  calc
    risk (g⁻¹ • θ) d ≤ risk (g⁻¹ • θ) bar := hd (g⁻¹ • θ)
    _ = risk θ (g • bar) :=
      (_root_.GD.N0230.N0625.d000803 risk hRisk g θ bar).symm
    _ = risk θ bar := by rw [hbar g]


theorem d000807
    (risk : Θ → Rule → ℝ)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    (bar : Rule)
    (hbar : ∀ g : G, g • bar = bar) :
    _root_.GD.N0230.N0625.d000800 (G := G) {d : Rule | _root_.GD.N0230.N0556.d000030 risk bar d} := by
  intro g d hd
  exact _root_.GD.N0230.N0625.d000806 risk hRisk bar hbar hd g







theorem d000808
    (objective : Rule → ℝ)
    (C : Set Rule)
    (star : Rule)
    (hC : _root_.GD.N0230.N0625.d000800 (G := G) C)
    (hobjective : _root_.GD.N0230.N0625.d000799 (G := G) objective)
    (hstar : _root_.GD.N0230.N0625.d000801 objective C star) :
    ∀ g : G, g • star = star := by
  intro g
  exact hstar.2.2 (g • star) (hC g star hstar.1)
    (hobjective g star)





theorem d000809
    (risk : Θ → Rule → ℝ)
    (objective : Rule → ℝ)
    (bar star : Rule)
    (hobjective : _root_.GD.N0230.N0625.d000802 risk objective)
    (hstar :
      _root_.GD.N0230.N0625.d000801 objective
        {d : Rule | _root_.GD.N0230.N0556.d000030 risk bar d} star) :
    _root_.GD.N0230.N0630.d000786 risk star := by
  intro e he
  have heBelow : _root_.GD.N0230.N0556.d000030 risk bar e :=
    _root_.GD.N0230.N0556.d000034 risk hstar.1 he
  have hstarLe : objective star ≤ objective e :=
    hstar.2.1 e heBelow
  have heLe : objective e ≤ objective star :=
    hobjective he
  exact hstar.2.2 e heBelow (le_antisymm heLe hstarLe)





theorem d000810
    (risk : Θ → Rule → ℝ)
    (objective : Rule → ℝ)
    (bar star : Rule)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    (hbar : ∀ g : G, g • bar = bar)
    (hobjectiveInv : _root_.GD.N0230.N0625.d000799 (G := G) objective)
    (hobjectiveMono : _root_.GD.N0230.N0625.d000802 risk objective)
    (hstar :
      _root_.GD.N0230.N0625.d000801 objective
        {d : Rule | _root_.GD.N0230.N0556.d000030 risk bar d} star) :
    (∀ g : G, g • star = star) ∧
      _root_.GD.N0230.N0630.d000786 risk star ∧
      _root_.GD.N0230.N0556.d000031 risk star := by
  have hfixed : ∀ g : G, g • star = star :=
    _root_.GD.N0230.N0625.d000808 objective
      {d : Rule | _root_.GD.N0230.N0556.d000030 risk bar d} star
      (_root_.GD.N0230.N0625.d000807 risk hRisk bar hbar)
      hobjectiveInv hstar
  have hunbeatable : _root_.GD.N0230.N0630.d000786 risk star :=
    _root_.GD.N0230.N0625.d000809
      risk objective bar star hobjectiveMono hstar
  exact
    ⟨hfixed, hunbeatable,
      _root_.GD.N0230.N0630.d000788 risk hunbeatable⟩

section FiniteOrbit

variable [Fintype G]


def d000811 (d : Rule) : Prop :=
  ∀ g : G, g • d = d







def d000812
    (risk : Θ → Rule → ℝ) (d : Rule) : Prop :=
  ¬ ∃ e, _root_.GD.N0230.N0625.d000811 (G := G) e ∧ _root_.GD.N0230.N0556.d000029 risk e d








def d000813
    (risk : Θ → Rule → ℝ)
    (average : Rule → Rule) : Prop :=
  ∀ θ d,
    (Fintype.card G : ℝ) * risk θ (average d) ≤
      ∑ g : G, risk θ (g • d)









theorem d000814
    (risk : Θ → Rule → ℝ)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    (average : Rule → Rule)
    (hJensen : _root_.GD.N0230.N0625.d000813 (G := G) risk average)
    {e star : Rule}
    (hstar : _root_.GD.N0230.N0625.d000811 (G := G) star)
    (he : _root_.GD.N0230.N0556.d000029 risk e star) :
    _root_.GD.N0230.N0556.d000029 risk (average e) star := by
  have hcard : (0 : ℝ) < Fintype.card G := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hsum_le :
      ∀ θ,
        (∑ g : G, risk θ (g • e)) ≤
          (Fintype.card G : ℝ) * risk θ star := by
    intro θ
    calc
      (∑ g : G, risk θ (g • e)) ≤
          ∑ _g : G, risk θ star := by
        apply Finset.sum_le_sum
        intro g _
        have hg :=
          _root_.GD.N0230.N0625.d000804 risk hRisk he.1 g
        simpa [hstar g] using hg θ
      _ = (Fintype.card G : ℝ) * risk θ star := by
        simp
  refine ⟨?_, ?_⟩
  · intro θ
    have hjensen := hJensen θ e
    have hsum := hsum_le θ
    nlinarith
  · obtain ⟨θ, hθ⟩ := he.2
    refine ⟨θ, ?_⟩
    have hsum_lt :
        (∑ g : G, risk θ (g • e)) <
          (Fintype.card G : ℝ) * risk θ star := by
      calc
        (∑ g : G, risk θ (g • e)) <
            ∑ _g : G, risk θ star := by
          apply Finset.sum_lt_sum
          · intro g _
            have hg :=
              _root_.GD.N0230.N0625.d000804 risk hRisk he.1 g
            simpa [hstar g] using hg θ
          · exact
              ⟨1, Finset.mem_univ 1, by simpa using hθ⟩
        _ = (Fintype.card G : ℝ) * risk θ star := by
          simp
    have hjensen := hJensen θ e
    nlinarith








theorem d000815
    (risk : Θ → Rule → ℝ)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    (average : Rule → Rule)
    (hJensen : _root_.GD.N0230.N0625.d000813 (G := G) risk average)
    {e star : Rule}
    (hstar : _root_.GD.N0230.N0625.d000811 (G := G) star)
    (he : _root_.GD.N0230.N0630.d000785 risk e star) :
    _root_.GD.N0230.N0630.d000785 risk (average e) star := by
  have hcard : (0 : ℝ) < Fintype.card G := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  intro θ
  have hsum_lt :
      (∑ g : G, risk θ (g • e)) <
        (Fintype.card G : ℝ) * risk θ star := by
    calc
      (∑ g : G, risk θ (g • e)) <
          ∑ _g : G, risk θ star := by
        apply Finset.sum_lt_sum
        · intro g _
          have hglt : risk θ (g • e) < risk θ star := by
            rw [_root_.GD.N0230.N0625.d000803 risk hRisk g θ e]
            calc
              risk (g⁻¹ • θ) e < risk (g⁻¹ • θ) star :=
                he (g⁻¹ • θ)
              _ = risk θ (g • star) :=
                (_root_.GD.N0230.N0625.d000803 risk hRisk g θ star).symm
              _ = risk θ star := by rw [hstar g]
          exact hglt.le
        · refine ⟨(1 : G), Finset.mem_univ _, ?_⟩
          simpa using he θ
      _ = (Fintype.card G : ℝ) * risk θ star := by simp
  have hjensen := hJensen θ e
  nlinarith






theorem d000816
    (risk : Θ → Rule → ℝ)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    (average : Rule → Rule)
    (hAverageFixed : ∀ d, _root_.GD.N0230.N0625.d000811 (G := G) (average d))
    (hJensen : _root_.GD.N0230.N0625.d000813 (G := G) risk average)
    {e star : Rule}
    (hstar : _root_.GD.N0230.N0625.d000811 (G := G) star)
    (he : _root_.GD.N0230.N0630.d000785 risk e star) :
    _root_.GD.N0230.N0625.d000811 (G := G) (average e) ∧
      _root_.GD.N0230.N0630.d000785 risk (average e) star :=
  ⟨hAverageFixed e,
    _root_.GD.N0230.N0625.d000815
      risk hRisk average hJensen hstar he⟩









theorem d000817
    (risk : Θ → Rule → ℝ)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    (average : Rule → Rule)
    (hAverageFixed : ∀ d, _root_.GD.N0230.N0625.d000811 (G := G) (average d))
    (hJensen : _root_.GD.N0230.N0625.d000813 (G := G) risk average)
    {star : Rule}
    (hstarFixed : _root_.GD.N0230.N0625.d000811 (G := G) star)
    (hstarAdmissible : _root_.GD.N0230.N0625.d000812 (G := G) risk star) :
    _root_.GD.N0230.N0556.d000031 risk star := by
  rintro ⟨e, he⟩
  apply hstarAdmissible
  exact
    ⟨average e, hAverageFixed e,
      _root_.GD.N0230.N0625.d000814
        risk hRisk average hJensen hstarFixed he⟩


def d000818
    (risk : Θ → Rule → ℝ) (θ₀ : Θ) (d : Rule) : ℝ :=
  ∑ g : G, risk (g • θ₀) d


theorem d000819
    (risk : Θ → Rule → ℝ)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    (θ₀ : Θ) :
    _root_.GD.N0230.N0625.d000799 (G := G) (_root_.GD.N0230.N0625.d000818 (G := G) risk θ₀) := by
  intro h d
  unfold _root_.GD.N0230.N0625.d000818
  calc
    (∑ g : G, risk (g • θ₀) (h • d)) =
        ∑ g : G, risk ((h⁻¹ * g) • θ₀) d := by
      apply Finset.sum_congr rfl
      intro g _
      rw [_root_.GD.N0230.N0625.d000803 risk hRisk h (g • θ₀) d]
      simp only [smul_smul]
    _ = ∑ g : G, risk (g • θ₀) d := by
      simpa [Equiv.coe_mulLeft] using
        (Equiv.sum_comp (Equiv.mulLeft h⁻¹)
          (fun g : G => risk (g • θ₀) d))

omit [MulAction G Rule] in

theorem d000820
    (risk : Θ → Rule → ℝ)
    (θ₀ : Θ) :
    _root_.GD.N0230.N0625.d000802 risk (_root_.GD.N0230.N0625.d000818 (G := G) risk θ₀) := by
  intro e d hed
  unfold _root_.GD.N0230.N0625.d000818
  exact Finset.sum_le_sum fun g _ => hed (g • θ₀)









theorem d000821
    (risk : Θ → Rule → ℝ)
    (θ₀ : Θ)
    (bar star : Rule)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    (hbar : ∀ g : G, g • bar = bar)
    (hstar :
      _root_.GD.N0230.N0625.d000801
        (_root_.GD.N0230.N0625.d000818 (G := G) risk θ₀)
        {d : Rule | _root_.GD.N0230.N0556.d000030 risk bar d} star) :
    (∀ g : G, g • star = star) ∧
      _root_.GD.N0230.N0630.d000786 risk star ∧
      _root_.GD.N0230.N0556.d000031 risk star := by
  exact _root_.GD.N0230.N0625.d000810
    risk (_root_.GD.N0230.N0625.d000818 (G := G) risk θ₀) bar star
    hRisk hbar
    (_root_.GD.N0230.N0625.d000819 risk hRisk θ₀)
    (_root_.GD.N0230.N0625.d000820 risk θ₀)
    hstar





theorem d000822
    (risk : Θ → Rule → ℝ)
    (θ₀ : Θ)
    (base bar star : Rule)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    (hbarFixed : ∀ g : G, g • bar = bar)
    (hbarStrict : _root_.GD.N0230.N0630.d000785 risk bar base)
    (hstar :
      _root_.GD.N0230.N0625.d000801
        (_root_.GD.N0230.N0625.d000818 (G := G) risk θ₀)
        {d : Rule | _root_.GD.N0230.N0556.d000030 risk bar d} star) :
    (∀ g : G, g • star = star) ∧
      _root_.GD.N0230.N0630.d000786 risk star ∧
      _root_.GD.N0230.N0556.d000031 risk star ∧
      _root_.GD.N0230.N0630.d000785 risk star base := by
  obtain ⟨hfixed, hunbeatable, hadmissible⟩ :=
    _root_.GD.N0230.N0625.d000821
      risk θ₀ bar star hRisk hbarFixed hstar
  exact
    ⟨hfixed, hunbeatable, hadmissible,
      _root_.GD.N0230.N0630.d000790
        risk hstar.1 hbarStrict⟩

end FiniteOrbit

end N0625
end N0230
end GD
