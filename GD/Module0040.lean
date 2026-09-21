import GD.Module0004


















namespace GD
namespace N0230
namespace N0682

open _root_.GD.N0230.N0556

variable {Θ Rule : Type*}


def d000500
    (risk : Θ → Rule → ℝ) (property : Rule → Prop) : Prop :=
  ∀ ⦃d e⦄, property d → _root_.GD.N0230.N0556.d000028 risk e d → property e


def d000501
    (risk : Θ → Rule → ℝ) (objective : Rule → ℝ) : Prop :=
  ∀ ⦃d e⦄, _root_.GD.N0230.N0556.d000028 risk e d → objective e ≤ objective d


theorem d000502
    (risk : Θ → Rule → ℝ) (property : Rule → Prop)
    {bar star : Rule}
    (hproperty : _root_.GD.N0230.N0682.d000500 risk property)
    (hbar : property bar)
    (hstar : _root_.GD.N0230.N0556.d000028 risk star bar) :
    property star :=
  hproperty hbar hstar


theorem d000503
    (risk : Θ → Rule → ℝ) (objective : Rule → ℝ)
    {bar star : Rule}
    (hobjective : _root_.GD.N0230.N0682.d000501 risk objective)
    (hstar : _root_.GD.N0230.N0556.d000028 risk star bar) :
    objective star ≤ objective bar :=
  hobjective hstar





theorem d000504
    (risk : Θ → Rule → ℝ)
    (feasible : Rule → Prop)
    (objective : Rule → ℝ)
    {bar star : Rule}
    (hobjective : _root_.GD.N0230.N0682.d000501 risk objective)
    (hbarOptimal : ∀ d, feasible d → objective bar ≤ objective d)
    (hstarFeasible : feasible star)
    (hstar : _root_.GD.N0230.N0556.d000028 risk star bar) :
    feasible star ∧
      ∀ d, feasible d → objective star ≤ objective d := by
  have hstarLeBar : objective star ≤ objective bar :=
    hobjective hstar
  refine ⟨hstarFeasible, ?_⟩
  intro d hd
  exact hstarLeBar.trans (hbarOptimal d hd)





theorem d000505
    (risk : Θ → Rule → ℝ)
    (weight : Θ → ℝ)
    {base bar star : Rule}
    (ε : ℝ)
    (hbarMargin :
      ∀ θ, ε * weight θ ≤ risk θ base - risk θ bar)
    (hstar : _root_.GD.N0230.N0556.d000028 risk star bar) :
    ∀ θ, ε * weight θ ≤ risk θ base - risk θ star := by
  intro θ
  have hdiff :
      risk θ base - risk θ bar ≤
        risk θ base - risk θ star := by
    exact sub_le_sub_left (hstar θ) (risk θ base)
  exact (hbarMargin θ).trans hdiff


theorem d000506
    (risk : Θ → Rule → ℝ)
    {base d : Rule}
    (hd : _root_.GD.N0230.N0556.d000028 risk d base) :
    ∀ θ, 0 ≤ risk θ base - risk θ d := by
  intro θ
  exact sub_nonneg.mpr (hd θ)





theorem d000507
    (risk : Θ → Rule → ℝ)
    {base d : Rule}
    (hdNonnegative : ∀ θ, 0 ≤ risk θ d)
    (hbaseArbitrarilySmall :
      ∀ ε : ℝ, 0 < ε → ∃ θ, risk θ base < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ θ, risk θ base - risk θ d < ε := by
  intro ε hε
  obtain ⟨θ, hsmall⟩ := hbaseArbitrarilySmall ε hε
  exact ⟨θ, (sub_le_self _ (hdNonnegative θ)).trans_lt hsmall⟩







theorem d000508
    (risk : Θ → Rule → ℝ)
    {base d : Rule}
    (hd : _root_.GD.N0230.N0556.d000028 risk d base)
    (hdNonnegative : ∀ θ, 0 ≤ risk θ d)
    (hbaseArbitrarilySmall :
      ∀ ε : ℝ, 0 < ε → ∃ θ, risk θ base < ε) :
    IsGLB (Set.range (fun θ => risk θ base - risk θ d)) 0 := by
  constructor
  · rintro _ ⟨θ, rfl⟩
    exact _root_.GD.N0230.N0682.d000506 risk hd θ
  · intro b hb
    by_contra hnot
    have hbpos : 0 < b := lt_of_not_ge hnot
    obtain ⟨θ, hsmall⟩ :=
      _root_.GD.N0230.N0682.d000507
        risk hdNonnegative hbaseArbitrarilySmall b hbpos
    exact (not_lt_of_ge (hb ⟨θ, rfl⟩)) hsmall






theorem d000509
    (risk : Θ → Rule → ℝ)
    {base d : Rule}
    (hdNonnegative : ∀ θ, 0 ≤ risk θ d)
    (hbaseArbitrarilySmall :
      ∀ ε : ℝ, 0 < ε → ∃ θ, risk θ base < ε) :
    ¬ ∃ ε : ℝ, 0 < ε ∧
      ∀ θ, ε ≤ risk θ base - risk θ d := by
  rintro ⟨ε, hε, hgap⟩
  obtain ⟨θ, hgap_lt⟩ :=
    _root_.GD.N0230.N0682.d000507
      risk hdNonnegative hbaseArbitrarilySmall ε hε
  exact (not_lt_of_ge (hgap θ)) hgap_lt






theorem d000510
    (risk : Θ → Rule → ℝ)
    {base d : Rule}
    (hd : _root_.GD.N0230.N0556.d000028 risk d base)
    (hdNonnegative : ∀ θ, 0 ≤ risk θ d)
    (hbaseArbitrarilySmall :
      ∀ ε : ℝ, 0 < ε → ∃ θ, risk θ base < ε) :
    (∀ θ, 0 ≤ risk θ base - risk θ d) ∧
      ¬ ∃ ε : ℝ, 0 < ε ∧
        ∀ θ, ε ≤ risk θ base - risk θ d :=
  ⟨_root_.GD.N0230.N0682.d000506 risk hd,
    _root_.GD.N0230.N0682.d000509
      risk hdNonnegative hbaseArbitrarilySmall⟩

end N0682
end N0230
end GD
