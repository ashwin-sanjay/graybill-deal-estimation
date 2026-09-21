import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import GD.Module0004
import GD.Module0054























open Set

namespace GD
namespace N0230
namespace N0630

open _root_.GD.N0230.N0556

variable {Θ H : Type*}


def d000785
    (risk : Θ → H → ℝ) (e d : H) : Prop :=
  ∀ θ, risk θ e < risk θ d








def d000786
    (risk : Θ → H → ℝ) (d : H) : Prop :=
  ∀ e, _root_.GD.N0230.N0556.d000028 risk e d → e = d





theorem d000787
    (risk : Θ → H → ℝ) (d : H) :
    _root_.GD.N0230.N0630.d000786 risk d ↔
      ∀ e, e ≠ d → ∃ θ, risk θ d < risk θ e := by
  constructor
  · intro h e hed
    by_contra hno
    have heWeak : _root_.GD.N0230.N0556.d000028 risk e d := by
      intro θ
      exact not_lt.mp (by
        intro hlt
        exact hno ⟨θ, hlt⟩)
    exact hed (h e heWeak)
  · intro h e heWeak
    by_contra hed
    obtain ⟨θ, hθ⟩ := h e hed
    exact (not_lt_of_ge (heWeak θ)) hθ


theorem d000788
    (risk : Θ → H → ℝ) {d : H}
    (h : _root_.GD.N0230.N0630.d000786 risk d) :
    _root_.GD.N0230.N0556.d000031 risk d := by
  rintro ⟨e, heWeak, θ, heStrict⟩
  have hed : e = d := h e heWeak
  subst e
  exact (lt_irrefl (risk θ d)) heStrict







theorem d000789
    (risk : Θ → H → ℝ) {d : H}
    (h : _root_.GD.N0230.N0630.d000786 risk d)
    (Q : H → H)
    (hQ : ∀ θ, risk θ (Q d) ≤ risk θ d) :
    Q d = d :=
  h (Q d) hQ





theorem d000790
    (risk : Θ → H → ℝ) {star bar base : H}
    (hstar : _root_.GD.N0230.N0556.d000028 risk star bar)
    (hbar : _root_.GD.N0230.N0630.d000785 risk bar base) :
    _root_.GD.N0230.N0630.d000785 risk star base := by
  intro θ
  exact lt_of_le_of_lt (hstar θ) (hbar θ)





theorem d000791
    [Nonempty Θ] (risk : Θ → H → ℝ) :
    ¬ ∃ d, ∀ e, _root_.GD.N0230.N0630.d000785 risk d e := by
  rintro ⟨d, hd⟩
  exact (lt_irrefl (risk (Classical.choice inferInstance) d)) (hd d _)

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]













theorem d000792
    (risk : Θ → H → ℝ)
    (θ₀ : Θ) (target bar : H)
    (hcomplete : IsComplete {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (href : ∀ d, risk θ₀ d = ‖target - d‖ ^ 2) :
    ∃ star,
      _root_.GD.N0230.N0556.d000030 risk bar star ∧
      _root_.GD.N0230.N0630.d000786 risk star ∧
      _root_.GD.N0230.N0556.d000031 risk star ∧
      (∀ d, _root_.GD.N0230.N0556.d000030 risk bar d → risk θ₀ star ≤ risk θ₀ d) := by
  let C : Set H := {d : H | _root_.GD.N0230.N0556.d000030 risk bar d}
  have hbarC : bar ∈ C := by
    exact _root_.GD.N0230.N0556.d000032 risk bar
  have hCnonempty : C.Nonempty := ⟨bar, hbarC⟩
  obtain ⟨star, hstarC, hstarMin⟩ :=
    exists_norm_eq_iInf_of_complete_convex
      hCnonempty hcomplete hconvex target

  have hdist_le :
      ∀ d, d ∈ C → ‖target - star‖ ≤ ‖target - d‖ := by
    intro d hd
    rw [hstarMin]
    have hbdd :
        BddBelow (Set.range (fun w : C => ‖target - (w : H)‖)) := by
      refine ⟨(0 : ℝ), ?_⟩
      rintro _ ⟨w, rfl⟩
      exact norm_nonneg (target - (w : H))
    exact ciInf_le hbdd ⟨d, hd⟩

  have hriskMin :
      ∀ d, _root_.GD.N0230.N0556.d000030 risk bar d → risk θ₀ star ≤ risk θ₀ d := by
    intro d hd
    rw [href star, href d]
    have hnorm := hdist_le d hd
    nlinarith [norm_nonneg (target - star), norm_nonneg (target - d)]

  have hunbeatable : _root_.GD.N0230.N0630.d000786 risk star := by
    intro e heWeak
    have heC : e ∈ C :=
      _root_.GD.N0230.N0556.d000034 risk hstarC heWeak
    have hdistStarLe : ‖target - star‖ ≤ ‖target - e‖ :=
      hdist_le e heC
    have hriskWeak := heWeak θ₀
    rw [href e, href star] at hriskWeak
    have hdistEq : ‖target - e‖ = ‖target - star‖ := by
      have hstarNonneg := norm_nonneg (target - star)
      have heNonneg := norm_nonneg (target - e)
      nlinarith
    have hprojection :
        inner ℝ (target - star) (e - star) ≤ 0 :=
      ((norm_eq_iInf_iff_real_inner_le_zero hconvex hstarC).1
        hstarMin) e heC
    have hgapBound :
        ‖e - star‖ ^ 2 ≤
          _root_.GD.N0230.N0693.d000667 target star e :=
      _root_.GD.N0230.N0693.d000669
        target star e hprojection
    have hgapZero :
        _root_.GD.N0230.N0693.d000667 target star e = 0 := by
      rw [_root_.GD.N0230.N0693.d000667, hdistEq]
      exact sub_self _
    rw [hgapZero] at hgapBound
    have hnormZero : ‖e - star‖ = 0 := by
      nlinarith [norm_nonneg (e - star)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnormZero)

  have hadmissible : _root_.GD.N0230.N0556.d000031 risk star :=
    _root_.GD.N0230.N0630.d000788 risk hunbeatable

  exact ⟨star, hstarC, hunbeatable, hadmissible, hriskMin⟩








noncomputable def d000793
    (risk : Θ → H → ℝ)
    (θ₀ : Θ) (target bar : H)
    (hcomplete : IsComplete {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (href : ∀ d, risk θ₀ d = ‖target - d‖ ^ 2) : H :=
  Classical.choose
    (_root_.GD.N0230.N0630.d000792
      risk θ₀ target bar hcomplete hconvex href)


theorem d000794
    (risk : Θ → H → ℝ)
    (θ₀ : Θ) (target bar : H)
    (hcomplete : IsComplete {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (href : ∀ d, risk θ₀ d = ‖target - d‖ ^ 2) :
    _root_.GD.N0230.N0556.d000030 risk bar
        (_root_.GD.N0230.N0630.d000793 risk θ₀ target bar hcomplete hconvex href) ∧
      _root_.GD.N0230.N0630.d000786 risk
        (_root_.GD.N0230.N0630.d000793 risk θ₀ target bar hcomplete hconvex href) ∧
      _root_.GD.N0230.N0556.d000031 risk
        (_root_.GD.N0230.N0630.d000793 risk θ₀ target bar hcomplete hconvex href) ∧
      (∀ d, _root_.GD.N0230.N0556.d000030 risk bar d →
        risk θ₀
            (_root_.GD.N0230.N0630.d000793 risk θ₀ target bar hcomplete hconvex href) ≤
          risk θ₀ d) :=
  Classical.choose_spec
    (_root_.GD.N0230.N0630.d000792
      risk θ₀ target bar hcomplete hconvex href)







theorem d000795
    (risk : Θ → H → ℝ)
    (θ₀ : Θ) (target bar : H)
    (hcomplete : IsComplete {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (href : ∀ d, risk θ₀ d = ‖target - d‖ ^ 2)
    (Q : H → H)
    (hQ : ∀ θ d, risk θ (Q d) ≤ risk θ d) :
    Q (_root_.GD.N0230.N0630.d000793 risk θ₀ target bar hcomplete hconvex href) =
      _root_.GD.N0230.N0630.d000793 risk θ₀ target bar hcomplete hconvex href := by
  apply _root_.GD.N0230.N0630.d000789 risk
      ((_root_.GD.N0230.N0630.d000794
        risk θ₀ target bar hcomplete hconvex href).2.1)
  intro θ
  exact hQ θ _





theorem d000796
    (risk : Θ → H → ℝ)
    (θ₀ : Θ) (target base bar : H)
    (hcomplete : IsComplete {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (href : ∀ d, risk θ₀ d = ‖target - d‖ ^ 2)
    (hbar : _root_.GD.N0230.N0630.d000785 risk bar base) :
    _root_.GD.N0230.N0630.d000785 risk
      (_root_.GD.N0230.N0630.d000793 risk θ₀ target bar hcomplete hconvex href) base :=
  _root_.GD.N0230.N0630.d000790 risk
    ((_root_.GD.N0230.N0630.d000794
      risk θ₀ target bar hcomplete hconvex href).1)
    hbar












theorem d000797
    (risk : Θ → H → ℝ)
    (θ₀ : Θ) (target base bar : H)
    (hcomplete : IsComplete {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (href : ∀ d, risk θ₀ d = ‖target - d‖ ^ 2)
    (hbar : _root_.GD.N0230.N0630.d000785 risk bar base) :
    ∃ star,
      _root_.GD.N0230.N0556.d000030 risk bar star ∧
      _root_.GD.N0230.N0630.d000786 risk star ∧
      _root_.GD.N0230.N0556.d000031 risk star ∧
      _root_.GD.N0230.N0630.d000785 risk star base ∧
      (∀ d, _root_.GD.N0230.N0556.d000030 risk bar d → risk θ₀ star ≤ risk θ₀ d) := by
  obtain ⟨star, hstar, hunbeatable, hadmissible, hmin⟩ :=
    _root_.GD.N0230.N0630.d000792
      risk θ₀ target bar hcomplete hconvex href
  exact
    ⟨star, hstar, hunbeatable, hadmissible,
      _root_.GD.N0230.N0630.d000790 risk hstar hbar,
      hmin⟩

end N0630
end N0230
end GD
