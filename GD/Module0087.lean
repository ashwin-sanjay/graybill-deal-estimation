import GD.Module0074























open Filter Set

namespace GD
namespace N0230
namespace N0704

noncomputable section

open _root_.GD.N0230.N0556
open _root_.GD.N0230.N0630
open _root_.GD.N0230.N0573
open _root_.GD.N0230.N0678

variable {X Y : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace Y]


theorem d001154
    (f : ℕ → X → Y) (limit : X → Y) (C : NNReal)
    (hlip : ∀ n, LipschitzWith C (f n))
    (hlimit : ∀ x, Tendsto (fun n ↦ f n x) atTop (nhds (limit x))) :
    LipschitzWith C limit := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact le_of_tendsto_of_tendsto'
    ((hlimit x).dist (hlimit y)) tendsto_const_nhds
    (fun n ↦ (hlip n).dist_le_mul x y)


theorem d001155
    (f : ℕ → X → Y) (limit : X → Y) (C : NNReal)
    (hlip : ∀ n, LipschitzWith C (f n))
    (hlimit : ∀ x, Tendsto (fun n ↦ f n x) atTop (nhds (limit x))) :
    Continuous limit :=
  (_root_.GD.N0230.N0704.d001154 f limit C hlip hlimit).continuous

section NormedLayer

variable {H : Type*} [NormedAddCommGroup H]



theorem d001156
    (f : ℕ → H → ℝ) (charge : H → ℝ) (error : ℕ → ℝ)
    (herrorZero : Tendsto error atTop (nhds 0))
    (hbound : ∀ n d,
      |f n d - charge d| ≤ error n * (1 + ‖d‖)) :
    ∀ d, Tendsto (fun n ↦ f n d) atTop (nhds (charge d)) := by
  intro d
  apply tendsto_iff_norm_sub_tendsto_zero.2
  refine squeeze_zero'
    (f := fun n ↦ ‖f n d - charge d‖)
    (g := fun n ↦ error n * (1 + ‖d‖))
    (Eventually.of_forall fun n ↦ norm_nonneg _)
    (Eventually.of_forall fun n ↦ ?_) ?_
  · simpa [Real.norm_eq_abs] using hbound n d
  · have hconst :
        Tendsto (fun _ : ℕ ↦ 1 + ‖d‖) atTop (nhds (1 + ‖d‖)) :=
      tendsto_const_nhds
    simpa using herrorZero.mul hconst


theorem d001157
    (f : ℕ → H → ℝ) (charge : H → ℝ) (error : ℕ → ℝ)
    (herrorNonneg : ∀ n, 0 ≤ error n)
    (hbound : ∀ n d,
      |f n d - charge d| ≤ error n * (1 + ‖d‖))
    {R : ℝ} {n : ℕ} {d : H} (hd : ‖d‖ ≤ R) :
    |f n d - charge d| ≤ error n * (1 + R) := by
  exact (hbound n d).trans
    (mul_le_mul_of_nonneg_left (by linarith) (herrorNonneg n))



theorem d001158
    (f : ℕ → H → ℝ) (charge : H → ℝ) (error : ℕ → ℝ)
    (herrorNonneg : ∀ n, 0 ≤ error n)
    (herrorZero : Tendsto error atTop (nhds 0))
    (hbound : ∀ n d,
      |f n d - charge d| ≤ error n * (1 + ‖d‖))
    {R epsilon : ℝ} (hR : 0 ≤ R) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ d, ‖d‖ ≤ R →
      |f n d - charge d| < epsilon := by
  have hden : 0 < 1 + R := by linarith
  have hevent :
      ∀ᶠ n in atTop, error n < epsilon / (1 + R) :=
    (tendsto_order.1 herrorZero).2 _ (div_pos hepsilon hden)
  filter_upwards [hevent] with n hn
  intro d hd
  exact (_root_.GD.N0230.N0704.d001157
    f charge error herrorNonneg hbound hd).trans_lt
      ((lt_div_iff₀ hden).mp hn)



theorem d001159
    {finite charge eta delta : ℝ}
    (herror : |finite - charge| ≤ delta)
    (hcharge : charge ≤ -eta) :
    finite ≤ -(eta - delta) := by
  have hupper := (abs_le.mp herror).2
  linarith



theorem d001160
    {finite charge eta delta : ℝ}
    (herror : |finite - charge| ≤ delta)
    (hfinite : finite ≤ -eta) :
    charge ≤ -(eta - delta) := by
  have hlower := (abs_le.mp herror).1
  linarith


theorem d001161
    {finiteE finiteD chargeE chargeD errorE errorD : ℝ}
    (hmono : finiteE ≤ finiteD)
    (herrorE : |finiteE - chargeE| ≤ errorE)
    (herrorD : |finiteD - chargeD| ≤ errorD) :
    chargeE ≤ chargeD + errorE + errorD := by
  have heLower := (abs_le.mp herrorE).1
  have hdUpper := (abs_le.mp herrorD).2
  linarith



theorem d001162
    {finiteE finiteD chargeE chargeD eta errorE errorD : ℝ}
    (hmono : finiteE ≤ finiteD)
    (herrorE : |finiteE - chargeE| ≤ errorE)
    (herrorD : |finiteD - chargeD| ≤ errorD)
    (hchargeD : chargeD ≤ -eta) :
    chargeE ≤ -(eta - (errorE + errorD)) := by
  have h := _root_.GD.N0230.N0704.d001161
    hmono herrorE herrorD
  linarith



theorem d001163
    (f : ℕ → H → ℝ) (charge : H → ℝ) (error : ℕ → ℝ)
    (herrorNonneg : ∀ n, 0 ≤ error n)
    (hbound : ∀ n d,
      |f n d - charge d| ≤ error n * (1 + ‖d‖))
    {n : ℕ} {e d : H} {R eta : ℝ}
    (heR : ‖e‖ ≤ R) (hdR : ‖d‖ ≤ R)
    (hmono : f n e ≤ f n d) (hdCharge : charge d ≤ -eta) :
    charge e ≤ -(eta - 2 * (error n * (1 + R))) := by
  have heError := _root_.GD.N0230.N0704.d001157
    f charge error herrorNonneg hbound heR (n := n)
  have hdError := _root_.GD.N0230.N0704.d001157
    f charge error herrorNonneg hbound hdR (n := n)
  have h := _root_.GD.N0230.N0704.d001162
    hmono heError hdError hdCharge
  nlinarith

variable {G : Type*} [Monoid G] [MulAction G H]

omit [NormedAddCommGroup H] in





theorem d001164
    (f : ℕ → H → ℝ) (charge : H → ℝ) (character : G → ℝ)
    (hlimit : ∀ d,
      Tendsto (fun n ↦ f n d) atTop (nhds (charge d)))
    (hdefect : ∀ g d,
      Tendsto
        (fun n ↦ f n (g • d) - character g * f n d)
        atTop (nhds 0)) :
    ∀ g d, charge (g • d) = character g * charge d := by
  intro g d
  have hleft : Tendsto
      (fun n ↦ f n (g • d) - character g * f n d)
      atTop (nhds (charge (g • d) - character g * charge d)) :=
    (hlimit (g • d)).sub (tendsto_const_nhds.mul (hlimit d))
  have hzero : charge (g • d) - character g * charge d = 0 :=
    tendsto_nhds_unique hleft (hdefect g d)
  linarith

omit [NormedAddCommGroup H] in


theorem d001165
    (f : ℕ → H → ℝ) (charge : H → ℝ) (character : G → ℝ)
    (hlimit : ∀ d,
      Tendsto (fun n ↦ f n d) atTop (nhds (charge d)))
    (hcharacter : ∀ n g d,
      f n (g • d) = character g * f n d) :
    ∀ g d, charge (g • d) = character g * charge d := by
  apply _root_.GD.N0230.N0704.d001164
    f charge character hlimit
  intro g d
  simpa only [hcharacter, sub_self] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (nhds 0))

omit [NormedAddCommGroup H] in

theorem d001166
    (f : ℕ → H → ℝ) (charge : H → ℝ) (character : G → ℝ)
    (error : ℕ → H → ℝ)
    (herror : ∀ n d, |f n d - charge d| ≤ error n d)
    (n : ℕ) (g : G) (d : H) :
    |charge (g • d) - character g * charge d| ≤
      error n (g • d) +
        |f n (g • d) - character g * f n d| +
        |character g| * error n d := by
  have hdecomp :
      charge (g • d) - character g * charge d =
        (charge (g • d) - f n (g • d)) +
          (f n (g • d) - character g * f n d) +
          character g * (f n d - charge d) := by
    ring
  rw [hdecomp]
  calc
    |(charge (g • d) - f n (g • d)) +
        (f n (g • d) - character g * f n d) +
        character g * (f n d - charge d)| ≤
        |charge (g • d) - f n (g • d)| +
          |f n (g • d) - character g * f n d| +
          |character g * (f n d - charge d)| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ error n (g • d) +
          |f n (g • d) - character g * f n d| +
          |character g| * error n d := by
      rw [abs_mul]
      exact add_le_add
        (add_le_add
          (by simpa [abs_sub_comm] using herror n (g • d)) le_rfl)
        (mul_le_mul_of_nonneg_left (herror n d) (abs_nonneg _))

variable [NormedSpace ℝ H]






theorem d001167
    {Theta : Type*}
    (risk : Theta → H → ℝ)
    (scale : ℕ → ℝ) (finiteDeficit : ℕ → H → ℝ)
    (charge : H → ℝ) (character : G → ℝ)
    (eta : ℝ) (C : NNReal)
    (hscale : ∀ n, 0 ≤ scale n)
    (hfiniteLip : ∀ n,
      LipschitzWith C (fun d ↦ scale n * finiteDeficit n d))
    (hfiniteConvex : ∀ n,
      ConvexOn ℝ Set.univ (fun d ↦ scale n * finiteDeficit n d))
    (hfiniteMono : ∀ {e d : H},
      _root_.GD.N0230.N0556.d000028 risk e d →
        ∀ n, finiteDeficit n e ≤ finiteDeficit n d)
    (hlimit : ∀ d,
      Tendsto (fun n ↦ scale n * finiteDeficit n d)
        atTop (nhds (charge d)))
    (hcharacterDefect : ∀ g d,
      Tendsto
        (fun n ↦
          scale n * finiteDeficit n (g • d) -
            character g * (scale n * finiteDeficit n d))
        atTop (nhds 0)) :
    Continuous charge ∧
      IsClosed {d : H | charge d ≤ -eta} ∧
      Convex ℝ {d : H | charge d ≤ -eta} ∧
      (∀ {e d : H}, _root_.GD.N0230.N0556.d000028 risk e d →
        charge d ≤ -eta → charge e ≤ -eta) ∧
      (∀ g d, charge (g • d) = character g * charge d) := by
  let f : ℕ → H → ℝ :=
    fun n d ↦ scale n * finiteDeficit n d
  have hcontinuous : Continuous charge :=
    (_root_.GD.N0230.N0704.d001154
      f charge C hfiniteLip hlimit).continuous
  refine ⟨hcontinuous, isClosed_le hcontinuous continuous_const,
    _root_.GD.N0230.N0678.d000929
      scale finiteDeficit charge (-eta) hfiniteConvex hlimit,
    ?_, ?_⟩
  · intro e d hed hd
    exact (_root_.GD.N0230.N0678.d000926
      risk scale finiteDeficit charge hscale hfiniteMono hlimit hed).trans hd
  · exact _root_.GD.N0230.N0704.d001164
      f charge character hlimit hcharacterDefect

end NormedLayer

variable {Theta H G : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [Monoid G] [MulAction G H]










theorem d001168
    (risk : Theta → H → ℝ)
    (theta0 : Theta) (target base bar : H)
    (scale : ℕ → ℝ) (finiteDeficit : ℕ → H → ℝ)
    (charge : H → ℝ) (character : G → ℝ)
    (eta : ℝ) (C : NNReal)
    (heta : 0 < eta)
    (hclosed : IsClosed {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hconvexCone : Convex ℝ {d : H | _root_.GD.N0230.N0556.d000030 risk bar d})
    (hbarCharge : charge bar ≤ -eta)
    (hchargeZero : charge 0 = 0)
    (hscale : ∀ n, 0 ≤ scale n)
    (hfiniteLip : ∀ n,
      LipschitzWith C (fun d ↦ scale n * finiteDeficit n d))
    (hfiniteConvex : ∀ n,
      ConvexOn ℝ Set.univ (fun d ↦ scale n * finiteDeficit n d))
    (hfiniteMono : ∀ {e d : H},
      _root_.GD.N0230.N0556.d000028 risk e d →
        ∀ n, finiteDeficit n e ≤ finiteDeficit n d)
    (hlimit : ∀ d,
      Tendsto (fun n ↦ scale n * finiteDeficit n d)
        atTop (nhds (charge d)))
    (hcharacterDefect : ∀ g d,
      Tendsto
        (fun n ↦
          scale n * finiteDeficit n (g • d) -
            character g * (scale n * finiteDeficit n d))
        atTop (nhds 0))
    (href : ∀ d, risk theta0 d = ‖target - d‖ ^ 2)
    (hbarStrict : _root_.GD.N0230.N0630.d000785 risk bar base) :
    (∀ g d, charge (g • d) = character g * charge d) ∧
      ∃ star,
        _root_.GD.N0230.N0556.d000030 risk bar star ∧
        _root_.GD.N0230.N0630.d000785 risk star base ∧
        charge star ≤ -eta ∧
        eta ≤ |charge star| ∧
        eta ≤ (C : ℝ) * ‖star‖ ∧
        star ≠ 0 ∧
        _root_.GD.N0230.N0630.d000786 risk star ∧
        _root_.GD.N0230.N0556.d000031 risk star ∧
        (∀ d, _root_.GD.N0230.N0556.d000030 risk bar d → charge d ≤ -eta →
          ‖d - star‖ ^ 2 ≤ risk theta0 d - risk theta0 star) := by
  let f : ℕ → H → ℝ :=
    fun n d ↦ scale n * finiteDeficit n d
  have hchargeLip : LipschitzWith C charge :=
    _root_.GD.N0230.N0704.d001154 f charge C hfiniteLip hlimit
  have hchargeContinuous : Continuous charge := hchargeLip.continuous
  have hchar : ∀ g d, charge (g • d) = character g * charge d :=
    _root_.GD.N0230.N0704.d001164
      f charge character hlimit hcharacterDefect
  refine ⟨hchar, ?_⟩
  obtain ⟨star, hstar, hstarStrict, hstarCharge, hterminal,
      hadmissible, htax⟩ :=
    _root_.GD.N0230.N0678.d000931
      risk theta0 target base bar scale finiteDeficit charge eta
      hclosed hconvexCone hchargeContinuous hbarCharge hscale
      hfiniteConvex hfiniteMono hlimit href hbarStrict
  have hchargeNonpos : charge star ≤ 0 := by linarith
  have habs : eta ≤ |charge star| := by
    rw [abs_of_nonpos hchargeNonpos]
    linarith
  have hlip0 := hchargeLip.dist_le_mul star 0
  have hnormFloor : eta ≤ (C : ℝ) * ‖star‖ := by
    have hdist : |charge star| ≤ (C : ℝ) * ‖star‖ := by
      simpa [Real.dist_eq, hchargeZero] using hlip0
    exact habs.trans hdist
  have hstarNe : star ≠ 0 := by
    intro hzero
    subst star
    have hbad : 0 ≤ -eta := by simpa [hchargeZero] using hstarCharge
    linarith
  exact ⟨star, hstar, hstarStrict, hstarCharge, habs, hnormFloor,
    hstarNe, hterminal, hadmissible, htax⟩

end

end N0704
end N0230
end GD

#print axioms _root_.GD.N0230.N0704.d001154
#print axioms _root_.GD.N0230.N0704.d001156
#print axioms _root_.GD.N0230.N0704.d001158
#print axioms _root_.GD.N0230.N0704.d001163
#print axioms _root_.GD.N0230.N0704.d001164
#print axioms _root_.GD.N0230.N0704.d001166
#print axioms _root_.GD.N0230.N0704.d001167
#print axioms _root_.GD.N0230.N0704.d001168
