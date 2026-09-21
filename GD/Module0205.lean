import GD.Module0204
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
















open Filter MeasureTheory Topology

namespace GD.N0232.N0720.N1347

noncomputable section







def d002831 (evidence current : ℝ) : ℝ :=
  if evidence = 0 then 0 else current ^ 2 / evidence

@[simp]
theorem d002832 (current : ℝ) :
    _root_.GD.N0232.N0720.N1347.d002831 0 current = 0 := by
  simp [_root_.GD.N0232.N0720.N1347.d002831]

theorem d002833
    {evidence current : ℝ} (hevidence : evidence ≠ 0) :
    _root_.GD.N0232.N0720.N1347.d002831 evidence current = current ^ 2 / evidence := by
  simp [_root_.GD.N0232.N0720.N1347.d002831, hevidence]

theorem d002834
    {evidence current : ℝ} (hevidence : 0 < evidence) :
    _root_.GD.N0232.N0720.N1347.d002831 evidence current = current ^ 2 / evidence :=
  _root_.GD.N0232.N0720.N1347.d002833 hevidence.ne'

theorem d002835
    {evidence current : ℝ} (hevidence : 0 ≤ evidence) :
    0 ≤ _root_.GD.N0232.N0720.N1347.d002831 evidence current := by
  by_cases hzero : evidence = 0
  · simp [hzero]
  · rw [_root_.GD.N0232.N0720.N1347.d002833 hzero]
    exact div_nonneg (sq_nonneg _) hevidence


theorem d002836 :
    Measurable (fun z : ℝ × ℝ ↦
      _root_.GD.N0232.N0720.N1347.d002831 z.1 z.2) := by
  unfold _root_.GD.N0232.N0720.N1347.d002831
  exact Measurable.ite
    (measurableSet_eq_fun measurable_fst measurable_const)
    measurable_const ((measurable_snd.pow_const 2).div measurable_fst)


def d002837
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (evidence current : X → ℝ) : ℝ :=
  ∫ x, _root_.GD.N0232.N0720.N1347.d002831 (evidence x) (current x) ∂mu



theorem d002838
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (evidence current : X → ℝ)
    (hevidence : ∀ᵐ x ∂mu, 0 < evidence x) :
    _root_.GD.N0232.N0720.N1347.d002837 mu evidence current =
      _root_.GD.N0232.N0720.d002827 mu evidence current := by
  unfold _root_.GD.N0232.N0720.N1347.d002837 _root_.GD.N0232.N0720.d002827
  apply integral_congr_ae
  filter_upwards [hevidence] with x hx
  exact _root_.GD.N0232.N0720.N1347.d002834 hx






theorem d002839
    {Theta : Type*} [MeasurableSpace Theta]
    (pi : Measure Theta) (weight response : Theta → ℝ)
    (hweightNonneg : 0 ≤ᵐ[pi] weight)
    (hweight : Integrable weight pi)
    (hcurrentMeasurable : AEStronglyMeasurable
      (fun theta ↦ weight theta * response theta) pi)
    (henergy : Integrable
      (fun theta ↦ weight theta * response theta ^ 2) pi) :
    Integrable (fun theta ↦ weight theta * response theta) pi := by
  have hmajor : Integrable
      (fun theta ↦ weight theta + weight theta * response theta ^ 2) pi :=
    hweight.add henergy
  apply hmajor.mono hcurrentMeasurable
  filter_upwards [hweightNonneg] with theta htheta
  have hresponse : |response theta| ≤ 1 + response theta ^ 2 := by
    exact abs_le.2 ⟨
      by nlinarith [sq_nonneg (response theta + 1 / 2)],
      by nlinarith [sq_nonneg (response theta - 1 / 2)]⟩
  have hmajorNonneg :
      0 ≤ weight theta + weight theta * response theta ^ 2 := by
    exact add_nonneg htheta (mul_nonneg htheta (sq_nonneg _))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg htheta,
    Real.norm_eq_abs, abs_of_nonneg hmajorNonneg]
  calc
    weight theta * |response theta| ≤
        weight theta * (1 + response theta ^ 2) :=
      mul_le_mul_of_nonneg_left hresponse htheta
    _ = weight theta + weight theta * response theta ^ 2 := by ring


theorem d002840
    {Theta : Type*} [MeasurableSpace Theta]
    (pi : Measure Theta) (weight response : Theta → ℝ)
    (hweightNonneg : 0 ≤ᵐ[pi] weight)
    (hweight : Integrable weight pi)
    (hmassZero : (∫ theta, weight theta ∂pi) = 0) :
    (∫ theta, weight theta * response theta ∂pi) = 0 := by
  have hweightZero : weight =ᵐ[pi] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hweightNonneg hweight).mp hmassZero
  calc
    (∫ theta, weight theta * response theta ∂pi) =
        ∫ _theta : Theta, (0 : ℝ) ∂pi := by
      apply integral_congr_ae
      filter_upwards [hweightZero] with theta htheta
      simp [htheta]
    _ = 0 := by simp







theorem d002841
    {Theta : Type*} [MeasurableSpace Theta]
    (pi : Measure Theta) (weight response : Theta → ℝ)
    (hweightNonneg : 0 ≤ᵐ[pi] weight)
    (hweight : Integrable weight pi)
    (hcurrent : Integrable (fun theta ↦ weight theta * response theta) pi)
    (henergy : Integrable
      (fun theta ↦ weight theta * response theta ^ 2) pi) :
    (∫ theta, weight theta * response theta ∂pi) ^ 2 ≤
      (∫ theta, weight theta ∂pi) *
        ∫ theta, weight theta * response theta ^ 2 ∂pi := by
  let mass : ℝ := ∫ theta, weight theta ∂pi
  let current : ℝ := ∫ theta, weight theta * response theta ∂pi
  let energy : ℝ := ∫ theta, weight theta * response theta ^ 2 ∂pi
  change current ^ 2 ≤ mass * energy
  have hmassNonneg : 0 ≤ mass := integral_nonneg_of_ae hweightNonneg
  by_cases hmassZero : mass = 0
  · have hcurrentZero : current = 0 := by
      exact _root_.GD.N0232.N0720.N1347.d002840
        pi weight response hweightNonneg hweight hmassZero
    simp [hmassZero, hcurrentZero]
  · have hmassPos : 0 < mass := lt_of_le_of_ne hmassNonneg (Ne.symm hmassZero)
    let center : ℝ := current / mass
    have hcenterIntegrable : Integrable
        (fun theta ↦ weight theta * (response theta - center) ^ 2) pi := by
      have hcross : Integrable
          (fun theta ↦ (2 * center) * (weight theta * response theta)) pi :=
        hcurrent.const_mul _
      have hconstant : Integrable
          (fun theta ↦ center ^ 2 * weight theta) pi :=
        hweight.const_mul _
      refine ((henergy.sub hcross).add hconstant).congr
        (ae_of_all pi fun theta ↦ ?_)
      change
        weight theta * response theta ^ 2 -
              (2 * center) * (weight theta * response theta) +
            center ^ 2 * weight theta =
          weight theta * (response theta - center) ^ 2
      ring
    have hcenterNonneg :
        0 ≤ ∫ theta, weight theta * (response theta - center) ^ 2 ∂pi := by
      apply integral_nonneg_of_ae
      filter_upwards [hweightNonneg] with theta htheta
      exact mul_nonneg htheta (sq_nonneg _)
    have hcenterExpansion :
        (∫ theta, weight theta * (response theta - center) ^ 2 ∂pi) =
          energy - (2 * center) * current + center ^ 2 * mass := by
      calc
        (∫ theta, weight theta * (response theta - center) ^ 2 ∂pi) =
            ∫ theta,
              (weight theta * response theta ^ 2 -
                  (2 * center) * (weight theta * response theta)) +
                center ^ 2 * weight theta ∂pi := by
          apply integral_congr_ae
          filter_upwards with theta
          ring
        _ =
            (∫ theta,
              weight theta * response theta ^ 2 -
                (2 * center) * (weight theta * response theta) ∂pi) +
              ∫ theta, center ^ 2 * weight theta ∂pi :=
          integral_add (henergy.sub (hcurrent.const_mul _))
            (hweight.const_mul _)
        _ = energy - (2 * center) * current + center ^ 2 * mass := by
          rw [integral_sub henergy (hcurrent.const_mul _),
            integral_const_mul, integral_const_mul]
    rw [hcenterExpansion] at hcenterNonneg
    have hcurrentEq : current = center * mass := by
      dsimp [center]
      field_simp [hmassZero]
    have hscaled := mul_nonneg hmassNonneg hcenterNonneg
    nlinarith



theorem d002842
    {Theta : Type*} [MeasurableSpace Theta]
    (pi : Measure Theta) (weight response : Theta → ℝ)
    (hweightNonneg : 0 ≤ᵐ[pi] weight)
    (hweight : Integrable weight pi)
    (hcurrentMeasurable : AEStronglyMeasurable
      (fun theta ↦ weight theta * response theta) pi)
    (henergy : Integrable
      (fun theta ↦ weight theta * response theta ^ 2) pi) :
    (∫ theta, weight theta * response theta ∂pi) ^ 2 ≤
      (∫ theta, weight theta ∂pi) *
        ∫ theta, weight theta * response theta ^ 2 ∂pi := by
  exact _root_.GD.N0232.N0720.N1347.d002841 pi weight response
    hweightNonneg hweight
    (_root_.GD.N0232.N0720.N1347.d002839
      pi weight response hweightNonneg hweight hcurrentMeasurable henergy)
    henergy



theorem d002843
    {Theta : Type*} [MeasurableSpace Theta]
    (pi : Measure Theta) (weight response : Theta → ℝ)
    (hweightNonneg : 0 ≤ᵐ[pi] weight)
    (hweight : Integrable weight pi)
    (hcurrent : Integrable (fun theta ↦ weight theta * response theta) pi)
    (henergy : Integrable
      (fun theta ↦ weight theta * response theta ^ 2) pi)
    (hmassPos : 0 < ∫ theta, weight theta ∂pi) :
    (∫ theta, weight theta * response theta ∂pi) ^ 2 /
        (∫ theta, weight theta ∂pi) ≤
      ∫ theta, weight theta * response theta ^ 2 ∂pi := by
  apply (div_le_iff₀ hmassPos).2
  simpa [mul_comm] using
    (_root_.GD.N0232.N0720.N1347.d002841 pi weight response
      hweightNonneg hweight hcurrent henergy)



theorem d002844
    {Theta : Type*} [MeasurableSpace Theta]
    (pi : Measure Theta) (weight response : Theta → ℝ)
    (hweightNonneg : 0 ≤ᵐ[pi] weight)
    (hweight : Integrable weight pi)
    (hcurrent : Integrable (fun theta ↦ weight theta * response theta) pi)
    (henergy : Integrable
      (fun theta ↦ weight theta * response theta ^ 2) pi) :
    _root_.GD.N0232.N0720.N1347.d002831
        (∫ theta, weight theta ∂pi)
        (∫ theta, weight theta * response theta ∂pi) ≤
      ∫ theta, weight theta * response theta ^ 2 ∂pi := by
  have hmassNonneg : 0 ≤ ∫ theta, weight theta ∂pi :=
    integral_nonneg_of_ae hweightNonneg
  by_cases hmassZero : (∫ theta, weight theta ∂pi) = 0
  · have hcurrentZero :
        (∫ theta, weight theta * response theta ∂pi) = 0 :=
      _root_.GD.N0232.N0720.N1347.d002840
        pi weight response hweightNonneg hweight hmassZero
    have henergyNonneg :
        0 ≤ ∫ theta, weight theta * response theta ^ 2 ∂pi := by
      apply integral_nonneg_of_ae
      filter_upwards [hweightNonneg] with theta htheta
      exact mul_nonneg htheta (sq_nonneg _)
    simpa [_root_.GD.N0232.N0720.N1347.d002831, hmassZero, hcurrentZero] using
      henergyNonneg
  · have hmassPos : 0 < ∫ theta, weight theta ∂pi :=
      lt_of_le_of_ne hmassNonneg (Ne.symm hmassZero)
    rw [_root_.GD.N0232.N0720.N1347.d002834 hmassPos]
    exact _root_.GD.N0232.N0720.N1347.d002843 pi weight response
      hweightNonneg hweight hcurrent henergy hmassPos



theorem d002845
    {Theta : Type*} [MeasurableSpace Theta]
    (pi : Measure Theta) (weight response : Theta → ℝ)
    (hweightNonneg : 0 ≤ᵐ[pi] weight)
    (hweight : Integrable weight pi)
    (hcurrentMeasurable : AEStronglyMeasurable
      (fun theta ↦ weight theta * response theta) pi)
    (henergy : Integrable
      (fun theta ↦ weight theta * response theta ^ 2) pi) :
    _root_.GD.N0232.N0720.N1347.d002831
        (∫ theta, weight theta ∂pi)
        (∫ theta, weight theta * response theta ∂pi) ≤
      ∫ theta, weight theta * response theta ^ 2 ∂pi := by
  exact _root_.GD.N0232.N0720.N1347.d002844 pi weight response
    hweightNonneg hweight
    (_root_.GD.N0232.N0720.N1347.d002839
      pi weight response hweightNonneg hweight hcurrentMeasurable henergy)
    henergy












theorem d002846
    {Theta X : Type*} [MeasurableSpace Theta] [MeasurableSpace X]
    (pi : Measure Theta) (mu : Measure X) [SFinite pi] [SFinite mu]
    (weight response : Theta → X → ℝ)
    (hweightNonneg : ∀ theta x, 0 ≤ weight theta x)
    (hweight : Integrable weight.uncurry (pi.prod mu))
    (hcurrentMeasurable : AEStronglyMeasurable
      (fun z : Theta × X ↦ weight z.1 z.2 * response z.1 z.2)
      (pi.prod mu))
    (henergy : Integrable
      (fun z : Theta × X ↦
        weight z.1 z.2 * response z.1 z.2 ^ 2) (pi.prod mu)) :
    Integrable
        (fun x ↦ _root_.GD.N0232.N0720.N1347.d002831
          (∫ theta, weight theta x ∂pi)
          (∫ theta, weight theta x * response theta x ∂pi)) mu ∧
      _root_.GD.N0232.N0720.N1347.d002837 mu
          (fun x ↦ ∫ theta, weight theta x ∂pi)
          (fun x ↦ ∫ theta, weight theta x * response theta x ∂pi) ≤
        ∫ x, ∫ theta, weight theta x * response theta x ^ 2 ∂pi ∂mu := by
  let currentKernel : Theta × X → ℝ := fun z ↦
    weight z.1 z.2 * response z.1 z.2
  let energyKernel : Theta × X → ℝ := fun z ↦
    weight z.1 z.2 * response z.1 z.2 ^ 2
  let mass : X → ℝ := fun x ↦ ∫ theta, weight theta x ∂pi
  let current : X → ℝ := fun x ↦ ∫ theta, currentKernel (theta, x) ∂pi
  let energy : X → ℝ := fun x ↦ ∫ theta, energyKernel (theta, x) ∂pi
  let perspective : X → ℝ := fun x ↦
    _root_.GD.N0232.N0720.N1347.d002831 (mass x) (current x)
  have hcurrent : Integrable currentKernel (pi.prod mu) := by
    apply _root_.GD.N0232.N0720.N1347.d002839
      (pi.prod mu) (fun z ↦ weight z.1 z.2) (fun z ↦ response z.1 z.2)
    · exact ae_of_all _ fun z ↦ hweightNonneg z.1 z.2
    · change Integrable weight.uncurry (pi.prod mu)
      exact hweight
    · simpa only [currentKernel] using hcurrentMeasurable
    · simpa only [energyKernel] using henergy
  have hmassOuter : Integrable mass mu := by
    simpa [mass] using hweight.integral_prod_right
  have hcurrentOuter : Integrable current mu := by
    simpa [current] using hcurrent.integral_prod_right
  have henergyOuter : Integrable energy mu := by
    simpa [energy] using henergy.integral_prod_right
  have hperspectiveMeasurable : AEStronglyMeasurable perspective mu := by
    have hpair : AEStronglyMeasurable (fun x ↦ (mass x, current x)) mu :=
      hmassOuter.aestronglyMeasurable.prodMk hcurrentOuter.aestronglyMeasurable
    exact (_root_.GD.N0232.N0720.N1347.d002836.comp_aemeasurable
      hpair.aemeasurable).aestronglyMeasurable
  have hsectionBound : ∀ᵐ x ∂mu, perspective x ≤ energy x := by
    filter_upwards [hweight.prod_left_ae, hcurrent.prod_left_ae,
      henergy.prod_left_ae] with x hwx hcx hex
    exact _root_.GD.N0232.N0720.N1347.d002844 pi
      (fun theta ↦ weight theta x) (fun theta ↦ response theta x)
      (ae_of_all pi fun theta ↦ hweightNonneg theta x)
      hwx (by simpa [currentKernel] using hcx)
      (by simpa [energyKernel] using hex)
  have hperspectiveNonneg : ∀ᵐ x ∂mu, 0 ≤ perspective x := by
    filter_upwards with x
    apply _root_.GD.N0232.N0720.N1347.d002835
    exact integral_nonneg fun theta ↦ hweightNonneg theta x
  have hperspectiveIntegrable : Integrable perspective mu :=
    henergyOuter.mono_nonneg hperspectiveMeasurable
      hperspectiveNonneg hsectionBound
  refine ⟨by simpa [perspective, mass, current, currentKernel] using
      hperspectiveIntegrable, ?_⟩
  unfold _root_.GD.N0232.N0720.N1347.d002837
  change (∫ x, perspective x ∂mu) ≤ ∫ x, energy x ∂mu
  exact integral_mono_ae hperspectiveIntegrable henergyOuter hsectionBound






theorem d002847
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (central : ℕ → X → ℝ)
    (added current : X → ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable
      (fun x ↦ current x ^ 2 / (central n x + added x)) mu)
    (hcentral : ∀ n, ∀ᵐ x ∂mu, 0 ≤ central n x)
    (hadded : ∀ᵐ x ∂mu, 0 < added x)
    (hgrowth : ∀ᵐ x ∂mu,
      Tendsto (fun n ↦ central n x) atTop atTop)
    (hintrinsic : Integrable (fun x ↦ current x ^ 2 / added x) mu) :
    Tendsto
      (fun n ↦ ∫ x, current x ^ 2 / (central n x + added x) ∂mu)
      atTop (𝓝 0) := by
  have hlim : ∀ᵐ x ∂mu, Tendsto
      (fun n ↦ current x ^ 2 / (central n x + added x)) atTop (𝓝 0) := by
    filter_upwards [hgrowth] with x hx
    exact (tendsto_atTop_add_const_right atTop (added x) hx).const_div_atTop
      (current x ^ 2)
  have hdom : ∀ n, ∀ᵐ x ∂mu,
      ‖current x ^ 2 / (central n x + added x)‖ ≤
        current x ^ 2 / added x := by
    intro n
    filter_upwards [hcentral n, hadded] with x hcx hax
    have hsum : 0 < central n x + added x := add_pos_of_nonneg_of_pos hcx hax
    rw [Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (sq_nonneg _) hsum.le)]
    exact div_le_div_of_nonneg_left (sq_nonneg _) hax
      (le_add_of_nonneg_left hcx)
  simpa using tendsto_integral_of_dominated_convergence
    (fun x ↦ current x ^ 2 / added x) hmeas hintrinsic hdom hlim







theorem d002848
    {m0 m1 j0 j1 : ℝ} (hm0 : 0 < m0) (hm1 : 0 ≤ m1) :
    (j0 + j1) ^ 2 / (m0 + m1) ≤
      2 * (j0 ^ 2 / m0) + 2 * (j1 ^ 2 / (m0 + m1)) := by
  have hsum : 0 < m0 + m1 := add_pos_of_pos_of_nonneg hm0 hm1
  have hsq : (j0 + j1) ^ 2 ≤ 2 * j0 ^ 2 + 2 * j1 ^ 2 := by
    nlinarith [sq_nonneg (j0 - j1)]
  calc
    (j0 + j1) ^ 2 / (m0 + m1) ≤
        (2 * j0 ^ 2 + 2 * j1 ^ 2) / (m0 + m1) :=
      div_le_div_of_nonneg_right hsq hsum.le
    _ = 2 * (j0 ^ 2 / (m0 + m1)) +
        2 * (j1 ^ 2 / (m0 + m1)) := by ring
    _ ≤ 2 * (j0 ^ 2 / m0) +
        2 * (j1 ^ 2 / (m0 + m1)) := by
      have hj : j0 ^ 2 / (m0 + m1) ≤ j0 ^ 2 / m0 :=
        div_le_div_of_nonneg_left (sq_nonneg _) hm0
          (le_add_of_nonneg_right hm1)
      exact add_le_add
        (mul_le_mul_of_nonneg_left hj (by norm_num : (0 : ℝ) ≤ 2)) le_rfl







theorem d002849
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X)
    (centralEvidence addedEvidence centralCurrent addedCurrent : X → ℝ)
    (hcentralEvidence : ∀ᵐ x ∂mu, 0 < centralEvidence x)
    (haddedEvidence : ∀ᵐ x ∂mu, 0 ≤ addedEvidence x)
    (hcentralIntegrable : Integrable
      (fun x ↦ centralCurrent x ^ 2 / centralEvidence x) mu)
    (hshieldIntegrable : Integrable
      (fun x ↦ addedCurrent x ^ 2 /
        (centralEvidence x + addedEvidence x)) mu)
    (hmixedMeasurable : AEStronglyMeasurable
      (fun x ↦ (centralCurrent x + addedCurrent x) ^ 2 /
        (centralEvidence x + addedEvidence x)) mu) :
    Integrable
        (fun x ↦ (centralCurrent x + addedCurrent x) ^ 2 /
          (centralEvidence x + addedEvidence x)) mu ∧
      _root_.GD.N0232.N0720.d002827 mu
          (fun x ↦ centralEvidence x + addedEvidence x)
          (fun x ↦ centralCurrent x + addedCurrent x) ≤
        2 * _root_.GD.N0232.N0720.d002827 mu centralEvidence centralCurrent +
          2 * ∫ x, addedCurrent x ^ 2 /
            (centralEvidence x + addedEvidence x) ∂mu := by
  let mixed : X → ℝ := fun x ↦
    (centralCurrent x + addedCurrent x) ^ 2 /
      (centralEvidence x + addedEvidence x)
  let upper : X → ℝ := fun x ↦
    2 * (centralCurrent x ^ 2 / centralEvidence x) +
      2 * (addedCurrent x ^ 2 /
        (centralEvidence x + addedEvidence x))
  have hupperIntegrable : Integrable upper mu :=
    (hcentralIntegrable.const_mul 2).add (hshieldIntegrable.const_mul 2)
  have hmixedNonneg : ∀ᵐ x ∂mu, 0 ≤ mixed x := by
    filter_upwards [hcentralEvidence, haddedEvidence] with x hcx hax
    exact div_nonneg (sq_nonneg _) (add_pos_of_pos_of_nonneg hcx hax).le
  have hupperNonneg : ∀ᵐ x ∂mu, 0 ≤ upper x := by
    filter_upwards [hcentralEvidence, haddedEvidence] with x hcx hax
    exact add_nonneg
      (mul_nonneg (by norm_num) (div_nonneg (sq_nonneg _) hcx.le))
      (mul_nonneg (by norm_num)
        (div_nonneg (sq_nonneg _) (add_pos_of_pos_of_nonneg hcx hax).le))
  have hmixedLe : ∀ᵐ x ∂mu, mixed x ≤ upper x := by
    filter_upwards [hcentralEvidence, haddedEvidence] with x hcx hax
    exact _root_.GD.N0232.N0720.N1347.d002848
      hcx hax
  have hmixedNormLe : ∀ᵐ x ∂mu, ‖mixed x‖ ≤ ‖upper x‖ := by
    filter_upwards [hmixedNonneg, hupperNonneg, hmixedLe] with x hmx hux hle
    simpa [Real.norm_eq_abs, abs_of_nonneg hmx, abs_of_nonneg hux]
  have hmixedIntegrable : Integrable mixed mu :=
    hupperIntegrable.mono hmixedMeasurable hmixedNormLe
  refine ⟨hmixedIntegrable, ?_⟩
  unfold _root_.GD.N0232.N0720.d002827
  change (∫ x, mixed x ∂mu) ≤
    2 * (∫ x, centralCurrent x ^ 2 / centralEvidence x ∂mu) +
      2 * ∫ x, addedCurrent x ^ 2 /
        (centralEvidence x + addedEvidence x) ∂mu
  calc
    (∫ x, mixed x ∂mu) ≤ ∫ x, upper x ∂mu :=
      integral_mono_ae hmixedIntegrable hupperIntegrable hmixedLe
    _ = 2 * (∫ x, centralCurrent x ^ 2 / centralEvidence x ∂mu) +
        2 * ∫ x, addedCurrent x ^ 2 /
          (centralEvidence x + addedEvidence x) ∂mu := by
      dsimp [upper]
      rw [integral_add (hcentralIntegrable.const_mul 2)
        (hshieldIntegrable.const_mul 2), integral_const_mul,
        integral_const_mul]



theorem d002850
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X)
    (centralEvidence addedEvidence centralCurrent addedCurrent : X → ℝ)
    (hcentralEvidence : ∀ᵐ x ∂mu, 0 < centralEvidence x)
    (haddedEvidence : ∀ᵐ x ∂mu, 0 ≤ addedEvidence x)
    (hcentralIntegrable : Integrable
      (fun x ↦ centralCurrent x ^ 2 / centralEvidence x) mu)
    (hshieldIntegrable : Integrable
      (fun x ↦ addedCurrent x ^ 2 /
        (centralEvidence x + addedEvidence x)) mu)
    (hmixedMeasurable : AEStronglyMeasurable
      (fun x ↦ (centralCurrent x + addedCurrent x) ^ 2 /
        (centralEvidence x + addedEvidence x)) mu) :
    _root_.GD.N0232.N0720.d002827 mu
        (fun x ↦ centralEvidence x + addedEvidence x)
        (fun x ↦ centralCurrent x + addedCurrent x) ≤
      2 * _root_.GD.N0232.N0720.d002827 mu centralEvidence centralCurrent +
        2 * ∫ x, addedCurrent x ^ 2 /
          (centralEvidence x + addedEvidence x) ∂mu :=
  (_root_.GD.N0232.N0720.N1347.d002849 mu
    centralEvidence addedEvidence centralCurrent addedCurrent
    hcentralEvidence haddedEvidence hcentralIntegrable hshieldIntegrable
    hmixedMeasurable).2

end

end GD.N0232.N0720.N1347

#print axioms _root_.GD.N0232.N0720.N1347.d002841
#print axioms _root_.GD.N0232.N0720.N1347.d002844
#print axioms _root_.GD.N0232.N0720.N1347.d002846
#print axioms _root_.GD.N0232.N0720.N1347.d002847
#print axioms _root_.GD.N0232.N0720.N1347.d002848
#print axioms _root_.GD.N0232.N0720.N1347.d002849
#print axioms _root_.GD.N0232.N0720.N1347.d002850
