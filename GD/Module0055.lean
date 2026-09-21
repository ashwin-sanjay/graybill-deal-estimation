import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Data.ENNReal.Real
import GD.Module0054






















open Set

namespace GD
namespace N0230
namespace N0608

variable {Θ H : Type*}


def d000672
    (risk : Θ → H → ENNReal) (e d : H) : Prop :=
  ∀ θ, risk θ e ≤ risk θ d


def d000673
    (risk : Θ → H → ENNReal) (bar d : H) : Prop :=
  _root_.GD.N0230.N0608.d000672 risk d bar


def d000674
    (risk : Θ → H → ENNReal) (d : H) : Prop :=
  ∀ e, _root_.GD.N0230.N0608.d000672 risk e d → e = d


def d000675
    (risk : Θ → H → ENNReal) (e d : H) : Prop :=
  ∀ θ, risk θ e < risk θ d

theorem d000676
    (risk : Θ → H → ENNReal) (d : H) :
    _root_.GD.N0230.N0608.d000672 risk d d := by
  intro θ
  exact le_rfl

theorem d000677
    (risk : Θ → H → ENNReal) {d₁ d₂ d₃ : H}
    (h₁₂ : _root_.GD.N0230.N0608.d000672 risk d₁ d₂)
    (h₂₃ : _root_.GD.N0230.N0608.d000672 risk d₂ d₃) :
    _root_.GD.N0230.N0608.d000672 risk d₁ d₃ := by
  intro θ
  exact le_trans (h₁₂ θ) (h₂₃ θ)

theorem d000678
    (risk : Θ → H → ENNReal) {bar d e : H}
    (hd : _root_.GD.N0230.N0608.d000673 risk bar d)
    (hed : _root_.GD.N0230.N0608.d000672 risk e d) :
    _root_.GD.N0230.N0608.d000673 risk bar e :=
  _root_.GD.N0230.N0608.d000677 risk hed hd

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]







theorem d000679
    (risk : Θ → H → ENNReal)
    (θ₀ : Θ) (target bar : H)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (href :
      ∀ d, risk θ₀ d = ENNReal.ofReal (‖target - d‖ ^ 2)) :
    ∃ star,
      _root_.GD.N0230.N0608.d000673 risk bar star ∧
      _root_.GD.N0230.N0608.d000674 risk star ∧
      (∀ d, _root_.GD.N0230.N0608.d000673 risk bar d →
        risk θ₀ star ≤ risk θ₀ d) := by
  let C : Set H := {d : H | _root_.GD.N0230.N0608.d000673 risk bar d}
  have hbarC : bar ∈ C :=
    _root_.GD.N0230.N0608.d000676 risk bar
  have hCnonempty : C.Nonempty := ⟨bar, hbarC⟩
  obtain ⟨star, hstarC, hstarMin⟩ :=
    exists_norm_eq_iInf_of_complete_convex
      hCnonempty hclosed.isComplete hconvex target

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
      ∀ d, _root_.GD.N0230.N0608.d000673 risk bar d → risk θ₀ star ≤ risk θ₀ d := by
    intro d hd
    rw [href star, href d]
    have hsquare :
        ‖target - star‖ ^ 2 ≤ ‖target - d‖ ^ 2 := by
      nlinarith [hdist_le d hd, norm_nonneg (target - star),
        norm_nonneg (target - d)]
    exact ENNReal.ofReal_le_ofReal hsquare

  have hunbeatable : _root_.GD.N0230.N0608.d000674 risk star := by
    intro e heWeak
    have heC : e ∈ C :=
      _root_.GD.N0230.N0608.d000678 risk hstarC heWeak
    have hdistStarLe : ‖target - star‖ ≤ ‖target - e‖ :=
      hdist_le e heC
    have hriskWeak := heWeak θ₀
    rw [href e, href star] at hriskWeak
    have hsqWeak :
        ‖target - e‖ ^ 2 ≤ ‖target - star‖ ^ 2 :=
      (ENNReal.ofReal_le_ofReal_iff
        (sq_nonneg ‖target - star‖)).mp hriskWeak
    have hdistEq : ‖target - e‖ = ‖target - star‖ := by
      nlinarith [norm_nonneg (target - star), norm_nonneg (target - e)]
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

  exact ⟨star, hstarC, hunbeatable, hriskMin⟩











theorem d000680
    (risk : Θ → H → ENNReal)
    (θ₀ : Θ) (target bar : H)
    (hcapClosed :
      ∀ θ, IsClosed {d : H | risk θ d ≤ risk θ bar})
    (hcapConvex :
      ∀ θ, Convex ℝ {d : H | risk θ d ≤ risk θ bar})
    (href :
      ∀ d, risk θ₀ d = ENNReal.ofReal (‖target - d‖ ^ 2)) :
    ∃ star,
      _root_.GD.N0230.N0608.d000673 risk bar star ∧
      _root_.GD.N0230.N0608.d000674 risk star ∧
      (∀ d, _root_.GD.N0230.N0608.d000673 risk bar d →
        risk θ₀ star ≤ risk θ₀ d) := by
  apply
    _root_.GD.N0230.N0608.d000679
      risk θ₀ target bar
  · simpa only [_root_.GD.N0230.N0608.d000673, _root_.GD.N0230.N0608.d000672, Set.setOf_forall] using
      isClosed_iInter hcapClosed
  · simpa only [_root_.GD.N0230.N0608.d000673, _root_.GD.N0230.N0608.d000672, Set.setOf_forall] using
      convex_iInter hcapConvex
  · exact href


noncomputable def d000681
    (risk : Θ → H → ENNReal)
    (θ₀ : Θ) (target bar : H)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (href :
      ∀ d, risk θ₀ d = ENNReal.ofReal (‖target - d‖ ^ 2)) : H :=
  Classical.choose
    (_root_.GD.N0230.N0608.d000679
      risk θ₀ target bar hclosed hconvex href)

theorem d000682
    (risk : Θ → H → ENNReal)
    (θ₀ : Θ) (target bar : H)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (href :
      ∀ d, risk θ₀ d = ENNReal.ofReal (‖target - d‖ ^ 2)) :
    _root_.GD.N0230.N0608.d000673 risk bar
        (_root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href) ∧
      _root_.GD.N0230.N0608.d000674 risk
        (_root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href) ∧
      (∀ d, _root_.GD.N0230.N0608.d000673 risk bar d →
        risk θ₀
            (_root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href) ≤
          risk θ₀ d) :=
  Classical.choose_spec
    (_root_.GD.N0230.N0608.d000679
      risk θ₀ target bar hclosed hconvex href)


theorem d000683
    (risk : Θ → H → ENNReal)
    (θ₀ : Θ) (target base bar : H)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (href :
      ∀ d, risk θ₀ d = ENNReal.ofReal (‖target - d‖ ^ 2))
    (hbar : _root_.GD.N0230.N0608.d000675 risk bar base) :
    _root_.GD.N0230.N0608.d000675 risk
      (_root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href) base := by
  intro θ
  exact lt_of_le_of_lt
    ((_root_.GD.N0230.N0608.d000682
      risk θ₀ target bar hclosed hconvex href).1 θ)
    (hbar θ)

end N0608
end N0230
end GD
