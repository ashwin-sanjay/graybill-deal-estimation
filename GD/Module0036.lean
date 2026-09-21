import Mathlib.Tactic



















open scoped BigOperators

namespace GD
namespace N0230
namespace N0666

noncomputable section

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I]



theorem d000423
    (mass x f : ℝ) (hmass : 0 < mass) :
    2 * f * x - mass * f ^ 2 ≤ x ^ 2 / mass := by
  apply (le_div_iff₀ hmass).2
  nlinarith [sq_nonneg (x - mass * f)]



theorem d000424
    (weight benefit lower : I → ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hatom : ∀ i, lower i ≤ benefit i) :
    ∑ i, weight i * lower i ≤ ∑ i, weight i * benefit i := by
  exact Finset.sum_le_sum fun i _ ↦
    mul_le_mul_of_nonneg_left (hatom i) (hweight i)







theorem d000425
    (weight benefit contact : I → ℝ)
    (capacity epsilon correlation atomCost packetMass : ℝ)
    (hweight : ∀ i, 0 ≤ weight i)
    (hatom : ∀ i,
      -(epsilon ^ 2 * atomCost * contact i) ≤ benefit i)
    (hmass : ∑ i, weight i * contact i = packetMass)
    (hcapacity :
      2 * epsilon * correlation - epsilon ^ 2 +
          ∑ i, weight i * benefit i ≤ capacity) :
    2 * epsilon * correlation -
        epsilon ^ 2 * (1 + atomCost * packetMass) ≤ capacity := by
  have hsum := _root_.GD.N0230.N0666.d000424 weight benefit
    (fun i ↦ -(epsilon ^ 2 * atomCost * contact i)) hweight hatom
  rw [← hmass]
  have hsumIdentity :
      (∑ i, weight i *
        (-(epsilon ^ 2 * atomCost * contact i))) =
        -(epsilon ^ 2 * atomCost) *
          ∑ i, weight i * contact i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    2 * epsilon * correlation -
          epsilon ^ 2 * (1 + atomCost * ∑ i, weight i * contact i) =
        2 * epsilon * correlation - epsilon ^ 2 +
          ∑ i, weight i *
            (-(epsilon ^ 2 * atomCost * contact i)) := by
      rw [hsumIdentity]
      ring
    _ ≤ 2 * epsilon * correlation - epsilon ^ 2 +
          ∑ i, weight i * benefit i := by linarith
    _ ≤ capacity := hcapacity


theorem d000426
    (correlation atomCost packetMass : ℝ)
    (hdenom : 1 + atomCost * packetMass ≠ 0) :
    2 * (correlation / (1 + atomCost * packetMass)) * correlation -
        (correlation / (1 + atomCost * packetMass)) ^ 2 *
          (1 + atomCost * packetMass) =
      correlation ^ 2 / (1 + atomCost * packetMass) := by
  field_simp [hdenom]
  ring



theorem d000427
    (capacity correlation atomCost packetMass : ℝ)
    (hcorrelation : 0 ≤ correlation)
    (hatomCost : 0 ≤ atomCost)
    (hpacketMass : 0 ≤ packetMass)
    (hcapacity : ∀ epsilon, 0 ≤ epsilon →
      2 * epsilon * correlation -
          epsilon ^ 2 * (1 + atomCost * packetMass) ≤ capacity) :
    correlation ^ 2 / (1 + atomCost * packetMass) ≤ capacity := by
  have hdenom : 0 < 1 + atomCost * packetMass := by positivity
  let epsilon := correlation / (1 + atomCost * packetMass)
  have hepsilon : 0 ≤ epsilon := div_nonneg hcorrelation hdenom.le
  have h := hcapacity epsilon hepsilon
  rw [_root_.GD.N0230.N0666.d000426
    correlation atomCost packetMass hdenom.ne'] at h
  exact h



theorem d000428
    (correlation atomCost mass massCap : ℝ)
    (hatomCost : 0 ≤ atomCost)
    (hmass : 0 ≤ mass)
    (hmassCap : mass ≤ massCap) :
    correlation ^ 2 / (1 + atomCost * massCap) ≤
      correlation ^ 2 / (1 + atomCost * mass) := by
  have hdenom : 0 < 1 + atomCost * mass := by positivity
  exact div_le_div_of_nonneg_left (sq_nonneg correlation)
    hdenom (by nlinarith)


theorem d000429
    (packetMass defect budget kappa threshold : ℝ)
    (hkappa : 0 < kappa)
    (hmass : kappa * packetMass ≤ defect + budget)
    (hdefect : defect < threshold) :
    packetMass ≤ (threshold + budget) / kappa := by
  apply (le_div_iff₀ hkappa).2
  linarith








theorem d000430
    (xi capacity defect packetMass correlation atomCost
      coefficient kappa budget threshold : ℝ)
    (hxi : capacity + coefficient * defect ≤ xi)
    (hcapacity :
      correlation ^ 2 / (1 + atomCost * packetMass) ≤ capacity)
    (hmassControl : kappa * packetMass ≤ defect + budget)
    (hcapacity_nonneg : 0 ≤ capacity)
    (hdefect_nonneg : 0 ≤ defect)
    (hpacketMass_nonneg : 0 ≤ packetMass)
    (_hcorrelation : 0 ≤ correlation)
    (hatomCost : 0 ≤ atomCost)
    (hcoefficient : 0 ≤ coefficient)
    (hkappa : 0 < kappa)
    (_hbudget : 0 ≤ budget)
    (_hthreshold : 0 < threshold) :
    min (coefficient * threshold)
        (correlation ^ 2 /
          (1 + atomCost * ((threshold + budget) / kappa))) ≤ xi := by
  by_cases hlarge : threshold ≤ defect
  · have hpay : coefficient * threshold ≤ coefficient * defect :=
      mul_le_mul_of_nonneg_left hlarge hcoefficient
    have hcapDefect : coefficient * defect ≤
        capacity + coefficient * defect := by linarith
    exact (min_le_left _ _).trans (hpay.trans (hcapDefect.trans hxi))
  · have hsmall : defect < threshold := lt_of_not_ge hlarge
    have hmassCap : packetMass ≤ (threshold + budget) / kappa :=
      _root_.GD.N0230.N0666.d000429 packetMass defect budget kappa threshold
        hkappa hmassControl hsmall
    have hfloorMass := _root_.GD.N0230.N0666.d000428
      correlation atomCost packetMass ((threshold + budget) / kappa)
      hatomCost hpacketMass_nonneg hmassCap
    have hfloorCapacity := hfloorMass.trans hcapacity
    have hcapacityXi : capacity ≤ xi := by
      have hterm : 0 ≤ coefficient * defect :=
        mul_nonneg hcoefficient hdefect_nonneg
      linarith
    exact (min_le_right _ _).trans (hfloorCapacity.trans hcapacityXi)


theorem d000431
    (correlation atomCost coefficient kappa budget threshold : ℝ)
    (hcorrelation : 0 < correlation)
    (hatomCost : 0 ≤ atomCost)
    (hcoefficient : 0 < coefficient)
    (hkappa : 0 < kappa)
    (hbudget : 0 ≤ budget)
    (hthreshold : 0 < threshold) :
    0 < min (coefficient * threshold)
        (correlation ^ 2 /
          (1 + atomCost * ((threshold + budget) / kappa))) := by
  have hmassCap : 0 ≤ (threshold + budget) / kappa := by positivity
  have hdenom :
      0 < 1 + atomCost * ((threshold + budget) / kappa) := by positivity
  exact lt_min (mul_pos hcoefficient hthreshold)
    (div_pos (sq_pos_of_pos hcorrelation) hdenom)





def d000432
    (amplitude rate lower displacement : ℝ) : ℝ :=
  rate * displacement + amplitude / (lower + displacement)


def d000433
    (amplitude rate lower : ℝ) : ℝ :=
  if amplitude ≤ rate * lower ^ 2 then
    amplitude / lower
  else
    2 * Real.sqrt (amplitude * rate) - rate * lower


theorem d000434
    (amplitude rate lower displacement : ℝ)
    (hamplitude : 0 < amplitude)
    (hrate : 0 < rate)
    (hlower : 0 < lower)
    (hdisplacement : 0 ≤ displacement) :
    _root_.GD.N0230.N0666.d000433 amplitude rate lower ≤
      _root_.GD.N0230.N0666.d000432 amplitude rate lower displacement := by
  let u := lower + displacement
  have hu : 0 < u := by dsimp [u]; linarith
  by_cases hboundary : amplitude ≤ rate * lower ^ 2
  · rw [_root_.GD.N0230.N0666.d000433, if_pos hboundary]
    have hfactorOne : 0 ≤ u - lower := by
      dsimp [u]
      linarith
    have hfactorTwo : 0 ≤ rate * u * lower - amplitude := by
      have hlu : lower ≤ u := by dsimp [u]; linarith
      have hmul : rate * lower ^ 2 ≤ rate * u * lower := by
        nlinarith
      exact sub_nonneg.2 (hboundary.trans hmul)
    have hidentity :
        _root_.GD.N0230.N0666.d000432 amplitude rate lower displacement -
            amplitude / lower =
          (u - lower) * (rate * u * lower - amplitude) /
            (u * lower) := by
      unfold _root_.GD.N0230.N0666.d000432
      dsimp [u]
      field_simp [hu.ne', hlower.ne']
      ring
    rw [← sub_nonneg]
    rw [hidentity]
    exact div_nonneg (mul_nonneg hfactorOne hfactorTwo)
      (mul_nonneg hu.le hlower.le)
  · rw [_root_.GD.N0230.N0666.d000433, if_neg hboundary]
    let x := Real.sqrt (amplitude * rate)
    have hproduct : 0 ≤ amplitude * rate :=
      mul_nonneg hamplitude.le hrate.le
    have hxSq : x ^ 2 = amplitude * rate := by
      exact Real.sq_sqrt hproduct
    have hquad :
        0 ≤ rate * u ^ 2 - 2 * x * u + amplitude := by
      have hsquare : 0 ≤ (rate * u - x) ^ 2 := sq_nonneg _
      nlinarith
    have hAMGM : 2 * x ≤ rate * u + amplitude / u := by
      have hrhs :
          rate * u + amplitude / u =
            (rate * u ^ 2 + amplitude) / u := by
        field_simp [hu.ne']
      rw [hrhs]
      exact (le_div_iff₀ hu).2 (by nlinarith)
    unfold _root_.GD.N0230.N0666.d000432
    dsimp [u] at hAMGM ⊢
    linarith



theorem d000435
    (amplitude rate lower : ℝ)
    (hamplitude : 0 < amplitude)
    (hrate : 0 < rate)
    (hlower : 0 < lower) :
    ∃ displacement : ℝ, 0 ≤ displacement ∧
      _root_.GD.N0230.N0666.d000432 amplitude rate lower displacement =
        _root_.GD.N0230.N0666.d000433 amplitude rate lower := by
  by_cases hboundary : amplitude ≤ rate * lower ^ 2
  · refine ⟨0, le_rfl, ?_⟩
    simp [_root_.GD.N0230.N0666.d000432, _root_.GD.N0230.N0666.d000433,
      hboundary]
  · let x := Real.sqrt (amplitude * rate)
    let displacement := x / rate - lower
    have hproduct : 0 < amplitude * rate := mul_pos hamplitude hrate
    have hxPos : 0 < x := Real.sqrt_pos.2 hproduct
    have hxSq : x ^ 2 = amplitude * rate :=
      Real.sq_sqrt hproduct.le
    have hcondition : rate * lower ^ 2 < amplitude :=
      lt_of_not_ge hboundary
    have hconditionScaled :
        rate ^ 2 * lower ^ 2 < x ^ 2 := by
      nlinarith
    have hxLower : rate * lower < x := by
      have hrateLower : 0 < rate * lower := mul_pos hrate hlower
      nlinarith
    have hdisplacement : 0 ≤ displacement := by
      dsimp [displacement]
      exact sub_nonneg.2 ((le_div_iff₀ hrate).2 (by
        simpa [mul_comm] using hxLower.le))
    refine ⟨displacement, hdisplacement, ?_⟩
    rw [_root_.GD.N0230.N0666.d000433, if_neg hboundary]
    unfold _root_.GD.N0230.N0666.d000432
    dsimp [displacement]
    have hdenom : lower + (x / rate - lower) = x / rate := by ring
    rw [hdenom]
    change rate * (x / rate - lower) + amplitude / (x / rate) =
      2 * x - rate * lower
    field_simp [hrate.ne', hxPos.ne']
    nlinarith


theorem d000436
    (amplitude rate lower : ℝ)
    (hamplitude : 0 < amplitude)
    (hrate : 0 < rate)
    (hlower : 0 < lower) :
    0 < _root_.GD.N0230.N0666.d000433 amplitude rate lower := by
  obtain ⟨displacement, hdisplacement, heq⟩ :=
    _root_.GD.N0230.N0666.d000435
      amplitude rate lower hamplitude hrate hlower
  rw [← heq]
  unfold _root_.GD.N0230.N0666.d000432
  have hdenom : 0 < lower + displacement := by linarith
  have hlinear : 0 ≤ rate * displacement :=
    mul_nonneg hrate.le hdisplacement
  have hreciprocal : 0 < amplitude / (lower + displacement) :=
    div_pos hamplitude hdenom
  linarith


def d000437
    (amplitude coefficient endpointRate budget defect : ℝ) : ℝ :=
  coefficient * defect +
    amplitude / (1 + endpointRate * (budget + defect))



def d000438
    (amplitude coefficient endpointRate budget : ℝ) : ℝ :=
  if amplitude * endpointRate ≤
      coefficient * (1 + endpointRate * budget) ^ 2 then
    amplitude / (1 + endpointRate * budget)
  else
    2 * Real.sqrt (amplitude * coefficient / endpointRate) -
      coefficient / endpointRate - coefficient * budget

private theorem d000439
    (amplitude coefficient endpointRate budget : ℝ)
    (hendpointRate : 0 < endpointRate) :
    amplitude ≤ (coefficient / endpointRate) *
        (1 + endpointRate * budget) ^ 2 ↔
      amplitude * endpointRate ≤
        coefficient * (1 + endpointRate * budget) ^ 2 := by
  have hrearrange :
      (coefficient / endpointRate) *
          (1 + endpointRate * budget) ^ 2 =
        (coefficient * (1 + endpointRate * budget) ^ 2) /
          endpointRate := by ring
  rw [hrearrange]
  exact le_div_iff₀ hendpointRate

private theorem d000440
    (amplitude coefficient endpointRate budget defect : ℝ)
    (hendpointRate : 0 < endpointRate) :
    _root_.GD.N0230.N0666.d000437
        amplitude coefficient endpointRate budget defect =
      _root_.GD.N0230.N0666.d000432 amplitude (coefficient / endpointRate)
        (1 + endpointRate * budget) (endpointRate * defect) := by
  unfold _root_.GD.N0230.N0666.d000437 _root_.GD.N0230.N0666.d000432
  field_simp [hendpointRate.ne']
  ring

private theorem d000441
    (amplitude coefficient endpointRate budget : ℝ)
    (hendpointRate : 0 < endpointRate) :
    _root_.GD.N0230.N0666.d000438
        amplitude coefficient endpointRate budget =
      _root_.GD.N0230.N0666.d000433 amplitude
        (coefficient / endpointRate)
        (1 + endpointRate * budget) := by
  unfold _root_.GD.N0230.N0666.d000438 _root_.GD.N0230.N0666.d000433
  by_cases hcondition :
      amplitude * endpointRate ≤
        coefficient * (1 + endpointRate * budget) ^ 2
  · have hcondition' :
        amplitude ≤ (coefficient / endpointRate) *
          (1 + endpointRate * budget) ^ 2 :=
      (_root_.GD.N0230.N0666.d000439 amplitude coefficient endpointRate budget
        hendpointRate).2 hcondition
    simp [hcondition, hcondition']
  · have hcondition' :
        ¬ amplitude ≤ (coefficient / endpointRate) *
          (1 + endpointRate * budget) ^ 2 := by
      intro hcontra
      exact hcondition
        ((_root_.GD.N0230.N0666.d000439 amplitude coefficient endpointRate budget
          hendpointRate).1 hcontra)
    simp only [hcondition, hcondition', ↓reduceIte]
    have hsqrtArgument :
        amplitude * (coefficient / endpointRate) =
          amplitude * coefficient / endpointRate := by ring
    rw [hsqrtArgument]
    field_simp [hendpointRate.ne']
    ring



theorem d000442
    (amplitude coefficient endpointRate budget defect : ℝ)
    (hamplitude : 0 < amplitude)
    (hcoefficient : 0 < coefficient)
    (hendpointRate : 0 < endpointRate)
    (hbudget : 0 ≤ budget)
    (hdefect : 0 ≤ defect) :
    _root_.GD.N0230.N0666.d000438
        amplitude coefficient endpointRate budget ≤
      _root_.GD.N0230.N0666.d000437
        amplitude coefficient endpointRate budget defect := by
  have hrate : 0 < coefficient / endpointRate :=
    div_pos hcoefficient hendpointRate
  have hlower : 0 < 1 + endpointRate * budget := by positivity
  have hdisplacement : 0 ≤ endpointRate * defect :=
    mul_nonneg hendpointRate.le hdefect
  have hbound := _root_.GD.N0230.N0666.d000434
    amplitude (coefficient / endpointRate)
      (1 + endpointRate * budget) (endpointRate * defect)
      hamplitude hrate hlower hdisplacement
  rw [← _root_.GD.N0230.N0666.d000441
      amplitude coefficient endpointRate budget hendpointRate,
    ← _root_.GD.N0230.N0666.d000440
      amplitude coefficient endpointRate budget defect hendpointRate] at hbound
  exact hbound


theorem d000443
    (amplitude coefficient endpointRate budget : ℝ)
    (hamplitude : 0 < amplitude)
    (hcoefficient : 0 < coefficient)
    (hendpointRate : 0 < endpointRate)
    (hbudget : 0 ≤ budget) :
    ∃ defect : ℝ, 0 ≤ defect ∧
      _root_.GD.N0230.N0666.d000437
          amplitude coefficient endpointRate budget defect =
        _root_.GD.N0230.N0666.d000438
          amplitude coefficient endpointRate budget := by
  have hrate : 0 < coefficient / endpointRate :=
    div_pos hcoefficient hendpointRate
  have hlower : 0 < 1 + endpointRate * budget := by positivity
  obtain ⟨displacement, hdisplacement, heq⟩ :=
    _root_.GD.N0230.N0666.d000435
      amplitude (coefficient / endpointRate)
        (1 + endpointRate * budget) hamplitude hrate hlower
  let defect := displacement / endpointRate
  have hdefect : 0 ≤ defect := div_nonneg hdisplacement hendpointRate.le
  refine ⟨defect, hdefect, ?_⟩
  rw [_root_.GD.N0230.N0666.d000440
      amplitude coefficient endpointRate budget defect hendpointRate,
    _root_.GD.N0230.N0666.d000441
      amplitude coefficient endpointRate budget hendpointRate]
  have hcoordinate : endpointRate * defect = displacement := by
    dsimp [defect]
    field_simp [hendpointRate.ne']
  rw [hcoordinate]
  exact heq


theorem d000444
    (amplitude coefficient endpointRate budget : ℝ)
    (hamplitude : 0 < amplitude)
    (hcoefficient : 0 < coefficient)
    (hendpointRate : 0 < endpointRate)
    (hbudget : 0 ≤ budget) :
    0 < _root_.GD.N0230.N0666.d000438
      amplitude coefficient endpointRate budget := by
  rw [_root_.GD.N0230.N0666.d000441
    amplitude coefficient endpointRate budget hendpointRate]
  exact _root_.GD.N0230.N0666.d000436 amplitude
    (coefficient / endpointRate) (1 + endpointRate * budget)
    hamplitude (div_pos hcoefficient hendpointRate) (by positivity)

end

end N0666
end N0230
end GD

#print axioms _root_.GD.N0230.N0666.d000423
#print axioms _root_.GD.N0230.N0666.d000425
#print axioms _root_.GD.N0230.N0666.d000427
#print axioms _root_.GD.N0230.N0666.d000430
#print axioms _root_.GD.N0230.N0666.d000431
#print axioms _root_.GD.N0230.N0666.d000434
#print axioms _root_.GD.N0230.N0666.d000435
#print axioms _root_.GD.N0230.N0666.d000436
#print axioms _root_.GD.N0230.N0666.d000442
#print axioms _root_.GD.N0230.N0666.d000443
#print axioms _root_.GD.N0230.N0666.d000444
