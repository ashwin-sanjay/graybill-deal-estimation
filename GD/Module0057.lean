import GD.Module0055

















open Set

namespace GD
namespace N0230
namespace N0609

open _root_.GD.N0230.N0608

variable {Θ H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]







theorem d000701
    (risk : Θ → H → ENNReal)
    (θ₀ : Θ) (target bar e : H)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (href :
      ∀ d, risk θ₀ d = ENNReal.ofReal (‖target - d‖ ^ 2))
    (he : _root_.GD.N0230.N0608.d000673 risk bar e) :
    let star :=
      _root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href
    ‖e - star‖ ^ 2 ≤
      ‖target - e‖ ^ 2 - ‖target - star‖ ^ 2 := by
  dsimp only
  let C : Set H := {d : H | _root_.GD.N0230.N0608.d000673 risk bar d}
  let star : H :=
    _root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href
  have hstarC : star ∈ C :=
    (_root_.GD.N0230.N0608.d000682
      risk θ₀ target bar hclosed hconvex href).1
  letI : Nonempty C := ⟨⟨star, hstarC⟩⟩
  have heC : e ∈ C := he
  have hriskMin : risk θ₀ star ≤ risk θ₀ e :=
    (_root_.GD.N0230.N0608.d000682
      risk θ₀ target bar hclosed hconvex href).2.2 e he
  have hdistLe : ‖target - star‖ ≤ ‖target - e‖ := by
    rw [href star, href e] at hriskMin
    have hsq :
        ‖target - star‖ ^ 2 ≤ ‖target - e‖ ^ 2 :=
      (ENNReal.ofReal_le_ofReal_iff
        (sq_nonneg ‖target - e‖)).mp hriskMin
    nlinarith [norm_nonneg (target - star), norm_nonneg (target - e)]
  have hnormMin :
      ‖target - star‖ =
        ⨅ w : C, ‖target - (w : H)‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro w
      have hwRisk : risk θ₀ star ≤ risk θ₀ (w : H) :=
        (_root_.GD.N0230.N0608.d000682
          risk θ₀ target bar hclosed hconvex href).2.2
            (w : H) w.property
      rw [href star, href (w : H)] at hwRisk
      have hsq :
          ‖target - star‖ ^ 2 ≤ ‖target - (w : H)‖ ^ 2 :=
        (ENNReal.ofReal_le_ofReal_iff
          (sq_nonneg ‖target - (w : H)‖)).mp hwRisk
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
    _root_.GD.N0230.N0693.d000669 target star e hprojection
  simpa [star, _root_.GD.N0230.N0693.d000667] using hgap








theorem d000702
    (risk : Θ → H → ENNReal)
    (θ₀ : Θ) (target bar e : H)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (href :
      ∀ d, risk θ₀ d = ENNReal.ofReal (‖target - d‖ ^ 2))
    (he : _root_.GD.N0230.N0608.d000673 risk bar e) :
    let star :=
      _root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href
    risk θ₀ star + ENNReal.ofReal (‖e - star‖ ^ 2) ≤ risk θ₀ e := by
  dsimp only
  let star : H :=
    _root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href
  have htax :=
    _root_.GD.N0230.N0609.d000701
      risk θ₀ target bar e hclosed hconvex href he
  have hadd :
      ‖target - star‖ ^ 2 + ‖e - star‖ ^ 2 ≤
        ‖target - e‖ ^ 2 := by
    nlinarith
  rw [href star, href e]
  rw [← ENNReal.ofReal_add
    (sq_nonneg ‖target - star‖) (sq_nonneg ‖e - star‖)]
  exact ENNReal.ofReal_le_ofReal hadd





theorem d000703
    (risk : Θ → H → ENNReal)
    (θ₀ : Θ) (target bar e : H)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (href :
      ∀ d, risk θ₀ d = ENNReal.ofReal (‖target - d‖ ^ 2))
    (he : _root_.GD.N0230.N0608.d000673 risk bar e)
    {η : ℝ}
    (hgap :
      ‖target - e‖ ^ 2 -
          ‖target - _root_.GD.N0230.N0608.d000681
            risk θ₀ target bar hclosed hconvex href‖ ^ 2 ≤ η) :
    ‖e - _root_.GD.N0230.N0608.d000681
          risk θ₀ target bar hclosed hconvex href‖ ^ 2 ≤ η := by
  exact
    (_root_.GD.N0230.N0609.d000701
      risk θ₀ target bar e hclosed hconvex href he).trans hgap




theorem d000704
    (risk : Θ → H → ENNReal)
    (θ₀ : Θ) (target bar e : H)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (href :
      ∀ d, risk θ₀ d = ENNReal.ofReal (‖target - d‖ ^ 2))
    (he : _root_.GD.N0230.N0608.d000673 risk bar e)
    {η : ℝ} (hη : 0 ≤ η)
    (hgap :
      ‖target - e‖ ^ 2 -
          ‖target - _root_.GD.N0230.N0608.d000681
            risk θ₀ target bar hclosed hconvex href‖ ^ 2 ≤ η) :
    ‖e - _root_.GD.N0230.N0608.d000681
          risk θ₀ target bar hclosed hconvex href‖ ≤ Real.sqrt η := by
  have hsq :=
    _root_.GD.N0230.N0609.d000703
      risk θ₀ target bar e hclosed hconvex href he hgap
  have hsqrtSq : (Real.sqrt η) ^ 2 = η := Real.sq_sqrt hη
  nlinarith [norm_nonneg
    (e - _root_.GD.N0230.N0608.d000681
      risk θ₀ target bar hclosed hconvex href), Real.sqrt_nonneg η]










theorem d000705
    (risk : Θ → H → ENNReal)
    (θ₀ : Θ) (target bar e q : H)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (href :
      ∀ d, risk θ₀ d = ENNReal.ofReal (‖target - d‖ ^ 2))
    (he : _root_.GD.N0230.N0608.d000673 risk bar e)
    (relaxed : Set H)
    (hcontains : ∀ d, _root_.GD.N0230.N0608.d000673 risk bar d → d ∈ relaxed)
    (hqmin : ∀ d, d ∈ relaxed → ‖target - q‖ ≤ ‖target - d‖) :
    ‖e - _root_.GD.N0230.N0608.d000681
          risk θ₀ target bar hclosed hconvex href‖ ^ 2 ≤
      ‖target - e‖ ^ 2 - ‖target - q‖ ^ 2 := by
  let star :=
    _root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href
  have hstar : _root_.GD.N0230.N0608.d000673 risk bar star :=
    (_root_.GD.N0230.N0608.d000682
      risk θ₀ target bar hclosed hconvex href).1
  have hqstar : ‖target - q‖ ≤ ‖target - star‖ :=
    hqmin star (hcontains star hstar)
  have hqstarSq :
      ‖target - q‖ ^ 2 ≤ ‖target - star‖ ^ 2 := by
    nlinarith [norm_nonneg (target - q), norm_nonneg (target - star)]
  have htax :=
    _root_.GD.N0230.N0609.d000701
      risk θ₀ target bar e hclosed hconvex href he
  dsimp only [star] at hqstarSq
  nlinarith





theorem d000706
    (risk : Θ → H → ENNReal)
    (θ₀ : Θ) (target bar e q : H)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (href :
      ∀ d, risk θ₀ d = ENNReal.ofReal (‖target - d‖ ^ 2))
    (he : _root_.GD.N0230.N0608.d000673 risk bar e)
    (relaxed : Set H)
    (hcontains : ∀ d, _root_.GD.N0230.N0608.d000673 risk bar d → d ∈ relaxed)
    (hqmin : ∀ d, d ∈ relaxed → ‖target - q‖ ≤ ‖target - d‖)
    {η : ℝ} (hη : 0 ≤ η)
    (hgap : ‖target - e‖ ^ 2 - ‖target - q‖ ^ 2 ≤ η) :
    ‖e - _root_.GD.N0230.N0608.d000681
          risk θ₀ target bar hclosed hconvex href‖ ≤ Real.sqrt η := by
  have hsq :=
    _root_.GD.N0230.N0609.d000705
      risk θ₀ target bar e q hclosed hconvex href he
      relaxed hcontains hqmin
  have hsqrtSq : (Real.sqrt η) ^ 2 = η := Real.sq_sqrt hη
  nlinarith [norm_nonneg
    (e - _root_.GD.N0230.N0608.d000681
      risk θ₀ target bar hclosed hconvex href), Real.sqrt_nonneg η]

end N0609
end N0230
end GD
