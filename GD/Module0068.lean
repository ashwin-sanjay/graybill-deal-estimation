import GD.Module0066
















open Set

namespace GD
namespace N0230
namespace N0631

open _root_.GD.N0230.N0556
open _root_.GD.N0230.N0630

variable {Θ H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]








theorem d000823
    (risk : Θ → H → ℝ)
    (θ₀ : Θ) (target bar e : H)
    (hcomplete : IsComplete {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (href : ∀ d, risk θ₀ d = ‖target - d‖ ^ 2)
    (he : _root_.GD.N0230.N0556.d000030 risk bar e) :
    ‖e - _root_.GD.N0230.N0630.d000793
          risk θ₀ target bar hcomplete hconvex href‖ ^ 2 ≤
      risk θ₀ e -
        risk θ₀
          (_root_.GD.N0230.N0630.d000793
            risk θ₀ target bar hcomplete hconvex href) := by
  let C : Set H := {d : H | _root_.GD.N0230.N0556.d000030 risk bar d}
  let star : H :=
    _root_.GD.N0230.N0630.d000793 risk θ₀ target bar hcomplete hconvex href
  have hstarC : star ∈ C :=
    (_root_.GD.N0230.N0630.d000794
      risk θ₀ target bar hcomplete hconvex href).1
  letI : Nonempty C := ⟨⟨star, hstarC⟩⟩
  have heC : e ∈ C := he
  have hriskMin :
      risk θ₀ star ≤ risk θ₀ e :=
    (_root_.GD.N0230.N0630.d000794
      risk θ₀ target bar hcomplete hconvex href).2.2.2 e he
  have hdistLe : ‖target - star‖ ≤ ‖target - e‖ := by
    rw [href star, href e] at hriskMin
    nlinarith [norm_nonneg (target - star), norm_nonneg (target - e)]
  have hnormMin :
      ‖target - star‖ =
        ⨅ w : C, ‖target - (w : H)‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro w
      have hwRisk :
          risk θ₀ star ≤ risk θ₀ (w : H) :=
        (_root_.GD.N0230.N0630.d000794
          risk θ₀ target bar hcomplete hconvex href).2.2.2
            (w : H) w.property
      rw [href star, href (w : H)] at hwRisk
      nlinarith [norm_nonneg (target - star),
        norm_nonneg (target - (w : H))]
    · have hbdd :
          BddBelow
            (Set.range (fun w : C ↦ ‖target - (w : H)‖)) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨w, rfl⟩
        exact norm_nonneg (target - (w : H))
      exact ciInf_le hbdd ⟨star, hstarC⟩
  have hprojection :
      inner ℝ (target - star) (e - star) ≤ 0 :=
    ((norm_eq_iInf_iff_real_inner_le_zero hconvex hstarC).1
      hnormMin) e heC
  have hgap :
      ‖e - star‖ ^ 2 ≤
        _root_.GD.N0230.N0693.d000667 target star e :=
    _root_.GD.N0230.N0693.d000669
      target star e hprojection
  change ‖e - star‖ ^ 2 ≤ risk θ₀ e - risk θ₀ star
  rw [href e, href star]
  exact hgap






theorem d000824
    (risk : Θ → H → ℝ)
    (θ₀ : Θ) (target bar e : H)
    (hcomplete : IsComplete {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (href : ∀ d, risk θ₀ d = ‖target - d‖ ^ 2)
    (he : ¬ _root_.GD.N0230.N0556.d000030 risk bar e) :
    ∃ θ,
      risk θ
          (_root_.GD.N0230.N0630.d000793
            risk θ₀ target bar hcomplete hconvex href) ≤
        risk θ bar ∧
      risk θ bar < risk θ e := by
  have hstar :
      _root_.GD.N0230.N0556.d000030 risk bar
        (_root_.GD.N0230.N0630.d000793
          risk θ₀ target bar hcomplete hconvex href) :=
    (_root_.GD.N0230.N0630.d000794
      risk θ₀ target bar hcomplete hconvex href).1
  rw [_root_.GD.N0230.N0556.d000030, _root_.GD.N0230.N0556.d000028] at he
  push Not at he
  obtain ⟨θ, hθ⟩ := he
  exact ⟨θ, hstar θ, hθ⟩







theorem d000825
    (risk : Θ → H → ℝ)
    (θ₀ : Θ) (target bar e : H)
    (hcomplete : IsComplete {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (href : ∀ d, risk θ₀ d = ‖target - d‖ ^ 2) :
    (∃ θ,
      risk θ
          (_root_.GD.N0230.N0630.d000793
            risk θ₀ target bar hcomplete hconvex href) ≤
        risk θ bar ∧
      risk θ bar < risk θ e) ∨
    (_root_.GD.N0230.N0556.d000030 risk bar e ∧
      ‖e - _root_.GD.N0230.N0630.d000793
            risk θ₀ target bar hcomplete hconvex href‖ ^ 2 ≤
        risk θ₀ e -
          risk θ₀
            (_root_.GD.N0230.N0630.d000793
              risk θ₀ target bar hcomplete hconvex href)) := by
  by_cases he : _root_.GD.N0230.N0556.d000030 risk bar e
  · exact Or.inr
      ⟨he, _root_.GD.N0230.N0631.d000823
        risk θ₀ target bar e hcomplete hconvex href he⟩
  · exact Or.inl
      (_root_.GD.N0230.N0631.d000824
        risk θ₀ target bar e hcomplete hconvex href he)





theorem d000826
    (risk : Θ → H → ℝ)
    (θ₀ : Θ) (target bar : H)
    (hcomplete : IsComplete {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (href : ∀ d, risk θ₀ d = ‖target - d‖ ^ 2) :
    _root_.GD.N0230.N0630.d000793 risk θ₀ target bar hcomplete hconvex href = bar ↔
      _root_.GD.N0230.N0630.d000786 risk bar := by
  constructor
  · intro h
    have hstrong :
        _root_.GD.N0230.N0630.d000786 risk
          (_root_.GD.N0230.N0630.d000793
            risk θ₀ target bar hcomplete hconvex href) :=
      (_root_.GD.N0230.N0630.d000794
        risk θ₀ target bar hcomplete hconvex href).2.1
    rw [h] at hstrong
    exact hstrong
  · intro hstrong
    exact hstrong _
      ((_root_.GD.N0230.N0630.d000794
        risk θ₀ target bar hcomplete hconvex href).1)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in




theorem d000827
    (risk : Θ → H → ℝ) (d : H)
    (hstrong : _root_.GD.N0230.N0630.d000786 risk d) :
    {e : H | _root_.GD.N0230.N0556.d000030 risk d e} = {d} := by
  ext e
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · exact fun he ↦ hstrong e he
  · intro he
    subst e
    exact _root_.GD.N0230.N0556.d000032 risk d

omit [InnerProductSpace ℝ H] in

theorem d000828
    (risk : Θ → H → ℝ) (d : H)
    (hstrong : _root_.GD.N0230.N0630.d000786 risk d) :
    IsComplete {e : H | _root_.GD.N0230.N0556.d000030 risk d e} := by
  rw [_root_.GD.N0230.N0631.d000827 risk d hstrong]
  exact isCompact_singleton.isComplete


theorem d000829
    (risk : Θ → H → ℝ) (d : H)
    (hstrong : _root_.GD.N0230.N0630.d000786 risk d) :
    Convex ℝ {e : H | _root_.GD.N0230.N0556.d000030 risk d e} := by
  rw [_root_.GD.N0230.N0631.d000827 risk d hstrong]
  exact convex_singleton d








theorem d000830
    (risk : Θ → H → ℝ)
    (θ₀ : Θ) (target bar : H)
    (hcomplete : IsComplete {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (href : ∀ d, risk θ₀ d = ‖target - d‖ ^ 2)
    (hcompleteStar :
      IsComplete
        {d : H |
          _root_.GD.N0230.N0556.d000030 risk
            (_root_.GD.N0230.N0630.d000793
              risk θ₀ target bar hcomplete hconvex href) d})
    (hconvexStar :
      Convex ℝ
        {d : H |
          _root_.GD.N0230.N0556.d000030 risk
            (_root_.GD.N0230.N0630.d000793
              risk θ₀ target bar hcomplete hconvex href) d}) :
    _root_.GD.N0230.N0630.d000793 risk θ₀ target
        (_root_.GD.N0230.N0630.d000793
          risk θ₀ target bar hcomplete hconvex href)
        hcompleteStar hconvexStar href =
      _root_.GD.N0230.N0630.d000793
        risk θ₀ target bar hcomplete hconvex href := by
  apply
    (_root_.GD.N0230.N0631.d000826
      risk θ₀ target
        (_root_.GD.N0230.N0630.d000793
          risk θ₀ target bar hcomplete hconvex href)
        hcompleteStar hconvexStar href).2
  exact
    (_root_.GD.N0230.N0630.d000794
      risk θ₀ target bar hcomplete hconvex href).2.1





theorem d000831
    (risk : Θ → H → ℝ)
    (θ₀ : Θ) (target bar : H)
    (hcomplete : IsComplete {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (href : ∀ d, risk θ₀ d = ‖target - d‖ ^ 2) :
    let star :=
      _root_.GD.N0230.N0630.d000793 risk θ₀ target bar hcomplete hconvex href
    let hstrong : _root_.GD.N0230.N0630.d000786 risk star :=
      (_root_.GD.N0230.N0630.d000794
        risk θ₀ target bar hcomplete hconvex href).2.1
    _root_.GD.N0230.N0630.d000793 risk θ₀ target star
        (_root_.GD.N0230.N0631.d000828 risk star hstrong)
        (_root_.GD.N0230.N0631.d000829 risk star hstrong)
        href =
      star := by
  dsimp only
  apply
    (_root_.GD.N0230.N0631.d000826
      risk θ₀ target
        (_root_.GD.N0230.N0630.d000793
          risk θ₀ target bar hcomplete hconvex href)
        (_root_.GD.N0230.N0631.d000828 risk _
          ((_root_.GD.N0230.N0630.d000794
            risk θ₀ target bar hcomplete hconvex href).2.1))
        (_root_.GD.N0230.N0631.d000829 risk _
          ((_root_.GD.N0230.N0630.d000794
            risk θ₀ target bar hcomplete hconvex href).2.1))
        href).2
  exact
    (_root_.GD.N0230.N0630.d000794
      risk θ₀ target bar hcomplete hconvex href).2.1

end N0631
end N0230
end GD
