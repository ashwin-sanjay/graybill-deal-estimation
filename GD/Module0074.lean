import GD.Module0069






















open Filter Set

namespace GD
namespace N0230
namespace N0678

noncomputable section

open _root_.GD.N0230.N0556
open _root_.GD.N0230.N0630
open _root_.GD.N0230.N0573

variable {Theta Rule : Type*}


theorem d000924
    (scale : ℕ → ℝ) (finiteDeficit : ℕ → Rule → ℝ)
    {e d : Rule}
    (hscale : ∀ n, 0 ≤ scale n)
    (hmono : ∀ n, finiteDeficit n e ≤ finiteDeficit n d) :
    ∀ n,
      scale n * finiteDeficit n e ≤ scale n * finiteDeficit n d := by
  intro n
  exact mul_le_mul_of_nonneg_left (hmono n) (hscale n)



theorem d000925
    (scale : ℕ → ℝ) (finiteDeficit : ℕ → Rule → ℝ)
    {e d : Rule} {chargeE chargeD : ℝ}
    (hscale : ∀ n, 0 ≤ scale n)
    (hmono : ∀ n, finiteDeficit n e ≤ finiteDeficit n d)
    (he : Tendsto
      (fun n ↦ scale n * finiteDeficit n e) atTop (nhds chargeE))
    (hd : Tendsto
      (fun n ↦ scale n * finiteDeficit n d) atTop (nhds chargeD)) :
    chargeE ≤ chargeD := by
  exact le_of_tendsto_of_tendsto' he hd
    (_root_.GD.N0230.N0678.d000924 scale finiteDeficit hscale hmono)




theorem d000926
    (risk : Theta → Rule → ℝ)
    (scale : ℕ → ℝ) (finiteDeficit : ℕ → Rule → ℝ)
    (charge : Rule → ℝ)
    (hscale : ∀ n, 0 ≤ scale n)
    (hfiniteMono : ∀ {e d : Rule},
      _root_.GD.N0230.N0556.d000028 risk e d →
        ∀ n, finiteDeficit n e ≤ finiteDeficit n d)
    (hlimit : ∀ d,
      Tendsto (fun n ↦ scale n * finiteDeficit n d)
        atTop (nhds (charge d))) :
    ∀ {e d : Rule}, _root_.GD.N0230.N0556.d000028 risk e d → charge e ≤ charge d := by
  intro e d hed
  exact _root_.GD.N0230.N0678.d000925
    scale finiteDeficit hscale (hfiniteMono hed)
    (hlimit e) (hlimit d)

variable {H : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]


theorem d000927
    (risk : Theta → H → ℝ)
    (scale : ℕ → ℝ) (finiteDeficit : ℕ → H → ℝ)
    (charge : H →L[ℝ] ℝ) (eta : ℝ)
    (hscale : ∀ n, 0 ≤ scale n)
    (hfiniteMono : ∀ {e d : H},
      _root_.GD.N0230.N0556.d000028 risk e d →
        ∀ n, finiteDeficit n e ≤ finiteDeficit n d)
    (hlimit : ∀ d,
      Tendsto (fun n ↦ scale n * finiteDeficit n d)
        atTop (nhds (charge d))) :
    _root_.GD.N0230.N0573.d000834 risk charge eta := by
  apply _root_.GD.N0230.N0573.d000843
  exact _root_.GD.N0230.N0678.d000926
    risk scale finiteDeficit charge hscale hfiniteMono hlimit


theorem d000928
    (scale : ℕ → ℝ) (finiteDeficit : ℕ → H → ℝ)
    (charge : H → ℝ)
    (hconvex : ∀ n,
      ConvexOn ℝ Set.univ (fun d ↦ scale n * finiteDeficit n d))
    (hlimit : ∀ d,
      Tendsto (fun n ↦ scale n * finiteDeficit n d)
        atTop (nhds (charge d))) :
    ConvexOn ℝ Set.univ charge := by
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy a b ha hb hab
  have hright : Tendsto
      (fun n ↦
        a * (scale n * finiteDeficit n x) +
          b * (scale n * finiteDeficit n y))
      atTop (nhds (a * charge x + b * charge y)) :=
    (tendsto_const_nhds.mul (hlimit x)).add
      (tendsto_const_nhds.mul (hlimit y))
  have hle : ∀ n,
      scale n * finiteDeficit n (a • x + b • y) ≤
        a * (scale n * finiteDeficit n x) +
          b * (scale n * finiteDeficit n y) := by
    intro n
    simpa only [smul_eq_mul] using
      (hconvex n).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  exact le_of_tendsto_of_tendsto'
    (hlimit (a • x + b • y)) hright hle


theorem d000929
    (scale : ℕ → ℝ) (finiteDeficit : ℕ → H → ℝ)
    (charge : H → ℝ) (threshold : ℝ)
    (hconvex : ∀ n,
      ConvexOn ℝ Set.univ (fun d ↦ scale n * finiteDeficit n d))
    (hlimit : ∀ d,
      Tendsto (fun n ↦ scale n * finiteDeficit n d)
        atTop (nhds (charge d))) :
    Convex ℝ {d : H | charge d ≤ threshold} := by
  have h := (_root_.GD.N0230.N0678.d000928
    scale finiteDeficit charge hconvex hlimit).convex_le threshold
  simpa using h

variable {K : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]





theorem d000930
    (risk : Theta → K → ℝ)
    (theta0 : Theta) (target base bar : K)
    (scale : ℕ → ℝ) (finiteDeficit : ℕ → K → ℝ)
    (charge : K → ℝ) (eta : ℝ)
    (hclosed : IsClosed {d : K | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hconvex : Convex ℝ {d : K | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hchargeClosed : IsClosed {d : K | charge d ≤ -eta})
    (hchargeConvex : Convex ℝ {d : K | charge d ≤ -eta})
    (hbarCharge : charge bar ≤ -eta)
    (hscale : ∀ n, 0 ≤ scale n)
    (hfiniteMono : ∀ {e d : K},
      _root_.GD.N0230.N0556.d000028 risk e d →
        ∀ n, finiteDeficit n e ≤ finiteDeficit n d)
    (hlimit : ∀ d,
      Tendsto (fun n ↦ scale n * finiteDeficit n d)
        atTop (nhds (charge d)))
    (href : ∀ d, risk theta0 d = ‖target - d‖ ^ 2)
    (hbarStrict : _root_.GD.N0230.N0630.d000785 risk bar base) :
    ∃ star,
      _root_.GD.N0230.N0556.d000030 risk bar star ∧
      _root_.GD.N0230.N0630.d000785 risk star base ∧
      charge star ≤ -eta ∧
      _root_.GD.N0230.N0630.d000786 risk star ∧
      _root_.GD.N0230.N0556.d000031 risk star ∧
      (∀ d, _root_.GD.N0230.N0556.d000030 risk bar d → charge d ≤ -eta →
        ‖d - star‖ ^ 2 ≤ risk theta0 d - risk theta0 star) := by
  apply _root_.GD.N0230.N0573.d000845
    risk theta0 target base bar charge eta hclosed hconvex
    hchargeClosed hchargeConvex hbarCharge
  · intro e d hed hdc
    exact (_root_.GD.N0230.N0678.d000926
      risk scale finiteDeficit charge hscale hfiniteMono hlimit hed).trans hdc
  · exact href
  · exact hbarStrict



theorem d000931
    (risk : Theta → K → ℝ)
    (theta0 : Theta) (target base bar : K)
    (scale : ℕ → ℝ) (finiteDeficit : ℕ → K → ℝ)
    (charge : K → ℝ) (eta : ℝ)
    (hclosed : IsClosed {d : K | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hconvexCone : Convex ℝ {d : K | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hchargeContinuous : Continuous charge)
    (hbarCharge : charge bar ≤ -eta)
    (hscale : ∀ n, 0 ≤ scale n)
    (hfiniteConvex : ∀ n,
      ConvexOn ℝ Set.univ (fun d ↦ scale n * finiteDeficit n d))
    (hfiniteMono : ∀ {e d : K},
      _root_.GD.N0230.N0556.d000028 risk e d →
        ∀ n, finiteDeficit n e ≤ finiteDeficit n d)
    (hlimit : ∀ d,
      Tendsto (fun n ↦ scale n * finiteDeficit n d)
        atTop (nhds (charge d)))
    (href : ∀ d, risk theta0 d = ‖target - d‖ ^ 2)
    (hbarStrict : _root_.GD.N0230.N0630.d000785 risk bar base) :
    ∃ star,
      _root_.GD.N0230.N0556.d000030 risk bar star ∧
      _root_.GD.N0230.N0630.d000785 risk star base ∧
      charge star ≤ -eta ∧
      _root_.GD.N0230.N0630.d000786 risk star ∧
      _root_.GD.N0230.N0556.d000031 risk star ∧
      (∀ d, _root_.GD.N0230.N0556.d000030 risk bar d → charge d ≤ -eta →
        ‖d - star‖ ^ 2 ≤ risk theta0 d - risk theta0 star) := by
  apply _root_.GD.N0230.N0678.d000930
    risk theta0 target base bar scale finiteDeficit charge eta
    hclosed hconvexCone
  · exact isClosed_le hchargeContinuous continuous_const
  · exact _root_.GD.N0230.N0678.d000929
      scale finiteDeficit charge (-eta) hfiniteConvex hlimit
  · exact hbarCharge
  · exact hscale
  · exact hfiniteMono
  · exact hlimit
  · exact href
  · exact hbarStrict





theorem d000932
    (risk : Theta → K → ℝ)
    (theta0 : Theta) (target base bar : K)
    (scale : ℕ → ℝ) (finiteDeficit : ℕ → K → ℝ)
    (charge : K →L[ℝ] ℝ) (eta : ℝ)
    (heta : 0 < eta)
    (hclosed : IsClosed {d : K | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hconvex : Convex ℝ {d : K | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hbarCharge : charge bar ≤ -eta)
    (hscale : ∀ n, 0 ≤ scale n)
    (hfiniteMono : ∀ {e d : K},
      _root_.GD.N0230.N0556.d000028 risk e d →
        ∀ n, finiteDeficit n e ≤ finiteDeficit n d)
    (hlimit : ∀ d,
      Tendsto (fun n ↦ scale n * finiteDeficit n d)
        atTop (nhds (charge d)))
    (href : ∀ d, risk theta0 d = ‖target - d‖ ^ 2)
    (hbarStrict : _root_.GD.N0230.N0630.d000785 risk bar base) :
    ∃ star,
      _root_.GD.N0230.N0556.d000030 risk bar star ∧
      _root_.GD.N0230.N0630.d000785 risk star base ∧
      charge star ≤ -eta ∧
      eta ≤ |charge star| ∧
      eta ≤ ‖charge‖ * ‖star‖ ∧
      star ≠ 0 ∧
      _root_.GD.N0230.N0630.d000786 risk star ∧
      _root_.GD.N0230.N0556.d000031 risk star := by
  apply _root_.GD.N0230.N0573.d000847
    risk theta0 target base bar charge eta heta hclosed hconvex hbarCharge
  · exact _root_.GD.N0230.N0678.d000927
      risk scale finiteDeficit charge eta hscale hfiniteMono hlimit
  · exact href
  · exact hbarStrict

end

end N0678
end N0230
end GD

#print axioms _root_.GD.N0230.N0678.d000925
#print axioms _root_.GD.N0230.N0678.d000927
#print axioms _root_.GD.N0230.N0678.d000928
#print axioms _root_.GD.N0230.N0678.d000930
#print axioms _root_.GD.N0230.N0678.d000931
#print axioms _root_.GD.N0230.N0678.d000932
