import GD.Module0057




























open Set

namespace GD
namespace N0230
namespace N0610

open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0609

variable {G Θ H : Type*}


def d000707
    [Group G] [MulAction G Θ] [MulAction G H]
    (risk : Θ → H → ENNReal) : Prop :=
  ∀ (g : G) (θ : Θ) (d : H),
    risk (g • θ) (g • d) = risk θ d


def d000708
    [Group G] [MulAction G H]
    (C : Set H) : Prop :=
  ∀ (g : G) (d : H), d ∈ C → g • d ∈ C

variable [Group G] [MulAction G Θ] [MulAction G H]


theorem d000709
    (risk : Θ → H → ENNReal)
    (hRisk : _root_.GD.N0230.N0610.d000707 (G := G) risk)
    (g : G) (θ : Θ) (d : H) :
    risk θ (g • d) = risk (g⁻¹ • θ) d := by
  simpa using hRisk g (g⁻¹ • θ) d


theorem d000710
    (risk : Θ → H → ENNReal)
    (hRisk : _root_.GD.N0230.N0610.d000707 (G := G) risk)
    {e d : H}
    (hed : _root_.GD.N0230.N0608.d000672 risk e d)
    (g : G) :
    _root_.GD.N0230.N0608.d000672 risk (g • e) (g • d) := by
  intro θ
  rw [_root_.GD.N0230.N0610.d000709 risk hRisk g θ e,
      _root_.GD.N0230.N0610.d000709 risk hRisk g θ d]
  exact hed (g⁻¹ • θ)


theorem d000711
    (risk : Θ → H → ENNReal)
    (hRisk : _root_.GD.N0230.N0610.d000707 (G := G) risk)
    {e d : H}
    (hed : _root_.GD.N0230.N0608.d000675 risk e d)
    (g : G) :
    _root_.GD.N0230.N0608.d000675 risk (g • e) (g • d) := by
  intro θ
  rw [_root_.GD.N0230.N0610.d000709 risk hRisk g θ e,
      _root_.GD.N0230.N0610.d000709 risk hRisk g θ d]
  exact hed (g⁻¹ • θ)


theorem d000712
    (risk : Θ → H → ENNReal)
    (hRisk : _root_.GD.N0230.N0610.d000707 (G := G) risk)
    (bar : H)
    (hbar : ∀ g : G, g • bar = bar)
    {d : H}
    (hd : _root_.GD.N0230.N0608.d000673 risk bar d)
    (g : G) :
    _root_.GD.N0230.N0608.d000673 risk bar (g • d) := by
  intro θ
  rw [_root_.GD.N0230.N0610.d000709 risk hRisk g θ d]
  calc
    risk (g⁻¹ • θ) d ≤ risk (g⁻¹ • θ) bar := hd (g⁻¹ • θ)
    _ = risk θ (g • bar) :=
      (_root_.GD.N0230.N0610.d000709 risk hRisk g θ bar).symm
    _ = risk θ bar := by rw [hbar g]


theorem d000713
    (risk : Θ → H → ENNReal)
    (hRisk : _root_.GD.N0230.N0610.d000707 (G := G) risk)
    (bar : H)
    (hbar : ∀ g : G, g • bar = bar) :
    _root_.GD.N0230.N0610.d000708 (G := G) {d : H | _root_.GD.N0230.N0608.d000673 risk bar d} := by
  intro g d hd
  exact _root_.GD.N0230.N0610.d000712 risk hRisk bar hbar hd g

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section MinimalProjectionGate

omit [MulAction G Θ] in






theorem d000714
    (risk : Θ → H → ENNReal)
    (θ₀ : Θ) (target bar : H)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (href :
      ∀ d, risk θ₀ d = ENNReal.ofReal (‖target - d‖ ^ 2))
    (hcone : _root_.GD.N0230.N0610.d000708 (G := G) {d : H | _root_.GD.N0230.N0608.d000673 risk bar d}) :
    ∀ g : G,
      let star :=
        _root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href
      ‖g • star - star‖ ^ 2 ≤
        ‖target - g • star‖ ^ 2 - ‖target - star‖ ^ 2 := by
  intro g
  dsimp only
  let star : H :=
    _root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href
  have hstar : _root_.GD.N0230.N0608.d000673 risk bar star :=
    (_root_.GD.N0230.N0608.d000682
      risk θ₀ target bar hclosed hconvex href).1
  exact _root_.GD.N0230.N0609.d000701
    risk θ₀ target bar (g • star)
    hclosed hconvex href (hcone g star hstar)

omit [MulAction G Θ] in





theorem d000715
    (risk : Θ → H → ENNReal)
    (θ₀ : Θ) (target bar : H)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (href :
      ∀ d, risk θ₀ d = ENNReal.ofReal (‖target - d‖ ^ 2))
    (hcone : _root_.GD.N0230.N0610.d000708 (G := G) {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (g : G) {η : ℝ}
    (hgap :
      ‖target - g • _root_.GD.N0230.N0608.d000681
          risk θ₀ target bar hclosed hconvex href‖ ^ 2 -
        ‖target - _root_.GD.N0230.N0608.d000681
          risk θ₀ target bar hclosed hconvex href‖ ^ 2 ≤ η) :
    ‖g • _root_.GD.N0230.N0608.d000681
          risk θ₀ target bar hclosed hconvex href -
        _root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href‖ ^ 2 ≤ η := by
  exact (_root_.GD.N0230.N0610.d000714
    risk θ₀ target bar hclosed hconvex href hcone g).trans hgap

omit [MulAction G Θ] in








theorem d000716
    (risk : Θ → H → ENNReal)
    (θ₀ : Θ) (target bar : H)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (href :
      ∀ d, risk θ₀ d = ENNReal.ofReal (‖target - d‖ ^ 2))
    (hcone : _root_.GD.N0230.N0610.d000708 (G := G) {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (hdistance : ∀ (g : G) (d : H),
      ‖target - g • d‖ = ‖target - d‖) :
    ∀ g : G,
      g • _root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href =
        _root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href := by
  intro g
  let star : H :=
    _root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href
  have hstar : _root_.GD.N0230.N0608.d000673 risk bar star :=
    (_root_.GD.N0230.N0608.d000682
      risk θ₀ target bar hclosed hconvex href).1
  have hgstar : _root_.GD.N0230.N0608.d000673 risk bar (g • star) :=
    hcone g star hstar
  have htax :=
    _root_.GD.N0230.N0609.d000701
      risk θ₀ target bar (g • star)
      hclosed hconvex href hgstar
  have hnonpos : ‖g • star - star‖ ^ 2 ≤ 0 := by
    simpa [star, hdistance g star] using htax
  have hzero : ‖g • star - star‖ = 0 := by
    nlinarith [norm_nonneg (g • star - star)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

end MinimalProjectionGate








theorem d000717
    (risk : Θ → H → ENNReal)
    (θ₀ : Θ) (target bar : H)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (href :
      ∀ d, risk θ₀ d = ENNReal.ofReal (‖target - d‖ ^ 2))
    (hRisk : _root_.GD.N0230.N0610.d000707 (G := G) risk)
    (hbar : ∀ g : G, g • bar = bar)
    (hdistance : ∀ (g : G) (d : H),
      ‖target - g • d‖ = ‖target - d‖) :
    ∀ g : G,
      g • _root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href =
        _root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href := by
  exact _root_.GD.N0230.N0610.d000716
    risk θ₀ target bar hclosed hconvex href
    (_root_.GD.N0230.N0610.d000713 risk hRisk bar hbar) hdistance









theorem d000718
    (K : Subgroup G)
    (risk : Θ → H → ENNReal)
    (θ₀ : Θ) (target bar : H)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (href :
      ∀ d, risk θ₀ d = ENNReal.ofReal (‖target - d‖ ^ 2))
    (hRisk : _root_.GD.N0230.N0610.d000707 (G := G) risk)
    (hbar : ∀ g : K, (g : G) • bar = bar)
    (hdistance : ∀ (g : K) (d : H),
      ‖target - (g : G) • d‖ = ‖target - d‖) :
    ∀ g : K,
      (g : G) • _root_.GD.N0230.N0608.d000681
          risk θ₀ target bar hclosed hconvex href =
        _root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href := by
  have hRiskK : _root_.GD.N0230.N0610.d000707 (G := K) risk := by
    intro g θ d
    exact hRisk (g : G) θ d
  have hbarK : ∀ g : K, g • bar = bar := by
    intro g
    exact hbar g
  have hdistanceK : ∀ (g : K) (d : H),
      ‖target - g • d‖ = ‖target - d‖ := by
    intro g d
    exact hdistance g d
  exact _root_.GD.N0230.N0610.d000717 (G := K)
    risk θ₀ target bar hclosed hconvex href
    hRiskK hbarK hdistanceK










theorem d000719
    (risk : Θ → H → ENNReal)
    (θ₀ : Θ) (target bar : H)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (href :
      ∀ d, risk θ₀ d = ENNReal.ofReal (‖target - d‖ ^ 2))
    (hRisk : _root_.GD.N0230.N0610.d000707 (G := G) risk)
    (hbar : ∀ g : G, g • bar = bar)
    (htarget : ∀ g : G, g • target = target)
    (hsub : ∀ (g : G) (x y : H), g • (x - y) = g • x - g • y)
    (hnorm : ∀ (g : G) (d : H), ‖g • d‖ = ‖d‖) :
    ∀ g : G,
      g • _root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href =
        _root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href := by
  apply _root_.GD.N0230.N0610.d000717
    risk θ₀ target bar hclosed hconvex href hRisk hbar
  intro g d
  calc
    ‖target - g • d‖ = ‖g • target - g • d‖ := by rw [htarget g]
    _ = ‖g • (target - d)‖ := by rw [hsub]
    _ = ‖target - d‖ := hnorm g (target - d)









theorem d000720
    (risk : Θ → H → ENNReal)
    (θ₀ : Θ) (target base bar : H)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (hconvex : Convex ℝ {d : H | _root_.GD.N0230.N0608.d000673 risk bar d})
    (href :
      ∀ d, risk θ₀ d = ENNReal.ofReal (‖target - d‖ ^ 2))
    (hRisk : _root_.GD.N0230.N0610.d000707 (G := G) risk)
    (hbar : ∀ g : G, g • bar = bar)
    (hdistance : ∀ (g : G) (d : H),
      ‖target - g • d‖ = ‖target - d‖)
    (hstrict : _root_.GD.N0230.N0608.d000675 risk bar base) :
    let star :=
      _root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href
    (∀ g : G, g • star = star) ∧
      _root_.GD.N0230.N0608.d000674 risk star ∧
      _root_.GD.N0230.N0608.d000675 risk star base := by
  dsimp only
  let star : H :=
    _root_.GD.N0230.N0608.d000681 risk θ₀ target bar hclosed hconvex href
  have hspec :=
    _root_.GD.N0230.N0608.d000682
      risk θ₀ target bar hclosed hconvex href
  refine ⟨?_, hspec.2.1, ?_⟩
  · exact _root_.GD.N0230.N0610.d000717
      risk θ₀ target bar hclosed hconvex href
      hRisk hbar hdistance
  · intro θ
    exact lt_of_le_of_lt (hspec.1 θ) (hstrict θ)

end N0610
end N0230
end GD
