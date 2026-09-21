import GD.Module0025
import GD.Module0043
import Mathlib.MeasureTheory.Function.L2Space















open Filter MeasureTheory Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace GD
namespace N0230
namespace N0639

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0638
open _root_.GD.N0230.N0640
open _root_.GD.N0230.N0646


def d000562
    {Omega : Type*} [MeasurableSpace Omega]
    (base : Measure Omega) (density : Omega → ℝ)
    (h : _root_.GD.N0230.N0602.d000116 base) (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ omega, ENNReal.ofReal
    (_root_.GD.N0230.N0638.d000278 (density omega) u * h omega ^ 2) ∂base



theorem d000563
    {Omega : Type*} [MeasurableSpace Omega]
    (base : Measure Omega) (density : Omega → ℝ)
    (hdensity : Measurable density) (hnonneg : ∀ omega, 0 ≤ density omega)
    (h : _root_.GD.N0230.N0602.d000116 base) {u : ℝ} (hu : 0 < u) :
    MemLp
      (fun omega ↦ _root_.GD.N0230.N0638.d000278 (density omega) u * h omega)
      2 base := by
  have hmeas : AEStronglyMeasurable
      (fun omega ↦ _root_.GD.N0230.N0638.d000278 (density omega) u) base := by
    apply Measurable.aestronglyMeasurable
    unfold _root_.GD.N0230.N0638.d000278
    fun_prop
  have htop : MemLp
      (fun omega ↦ _root_.GD.N0230.N0638.d000278 (density omega) u) ∞ base := by
    apply memLp_top_of_bound hmeas (1 / 4)
    filter_upwards [] with omega
    rw [Real.norm_of_nonneg
      (_root_.GD.N0230.N0638.d000281 (hnonneg omega) hu.le)]
    exact _root_.GD.N0230.N0638.d000282 (hnonneg omega) hu
  exact (Lp.memLp h).mul' htop


def d000564
    {Omega : Type*} [MeasurableSpace Omega]
    (base : Measure Omega) (density : Omega → ℝ)
    (hdensity : Measurable density) (hnonneg : ∀ omega, 0 ≤ density omega)
    (h : _root_.GD.N0230.N0602.d000116 base) (u : ℝ) (hu : 0 < u) : _root_.GD.N0230.N0602.d000116 base :=
  (_root_.GD.N0230.N0639.d000563 base density hdensity hnonneg h hu).toLp
    (fun omega ↦ _root_.GD.N0230.N0638.d000278 (density omega) u * h omega)


theorem d000565
    {Omega : Type*} [MeasurableSpace Omega]
    (base : Measure Omega) (density : Omega → ℝ)
    (hdensity : Measurable density) (hnonneg : ∀ omega, 0 ≤ density omega)
    (h z : _root_.GD.N0230.N0602.d000116 base) (u : ℝ) (hu : 0 < u) :
    ⟪ _root_.GD.N0230.N0639.d000564 base density hdensity hnonneg h u hu, z ⟫_ℝ =
      ⟪ h, _root_.GD.N0230.N0639.d000564 base density hdensity hnonneg z u hu ⟫_ℝ := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    (_root_.GD.N0230.N0639.d000563 base density hdensity hnonneg h hu).coeFn_toLp,
    (_root_.GD.N0230.N0639.d000563 base density hdensity hnonneg z hu).coeFn_toLp]
      with omega hh hz
  change _root_.GD.N0230.N0639.d000564 base density hdensity hnonneg h u hu omega =
    _root_.GD.N0230.N0638.d000278 (density omega) u * h omega at hh
  change _root_.GD.N0230.N0639.d000564 base density hdensity hnonneg z u hu omega =
    _root_.GD.N0230.N0638.d000278 (density omega) u * z omega at hz
  rw [hh, hz]
  simp only [RCLike.inner_apply, conj_trivial]
  ring



theorem d000566
    {Omega : Type*} [MeasurableSpace Omega]
    (base : Measure Omega) (density : Omega → ℝ)
    (hdensity : Measurable density) (hnonneg : ∀ omega, 0 ≤ density omega)
    (h : _root_.GD.N0230.N0602.d000116 base) (u : ℝ) (hu : 0 < u) :
    _root_.GD.N0230.N0602.d000117 base 0
        (_root_.GD.N0230.N0639.d000564 base density hdensity hnonneg h u hu) ≤
      _root_.GD.N0230.N0639.d000562 base density h u := by
  unfold _root_.GD.N0230.N0602.d000117 _root_.GD.N0230.N0639.d000562 _root_.GD.N0230.N0639.d000564
  apply lintegral_mono_ae
  filter_upwards [
    (_root_.GD.N0230.N0639.d000563 base density hdensity hnonneg h hu).coeFn_toLp]
      with omega homega
  rw [homega]
  simp only [sub_zero]
  apply ENNReal.ofReal_le_ofReal
  let b := _root_.GD.N0230.N0638.d000278 (density omega) u
  have hb₀ : 0 ≤ b := _root_.GD.N0230.N0638.d000281 (hnonneg omega) hu.le
  have hb₁ : b ≤ 1 :=
    (_root_.GD.N0230.N0638.d000282 (hnonneg omega) hu).trans (by norm_num)
  dsimp [b] at hb₀ hb₁ ⊢
  nlinarith [sq_nonneg (h omega), mul_nonneg hb₀ (sq_nonneg (h omega))]


theorem d000567
    {Omega : Type*} [MeasurableSpace Omega]
    (base : Measure Omega) (density : Omega → ℝ)
    (hdensity : Measurable density) (hnonneg : ∀ omega, 0 ≤ density omega)
    (h : _root_.GD.N0230.N0602.d000116 base) (u : ℝ) (hu : 0 < u) :
    _root_.GD.N0230.N0639.d000562 base density h u ≤
      ENNReal.ofReal (1 / u) *
        _root_.GD.N0230.N0640.d000272 base density h := by
  unfold _root_.GD.N0230.N0639.d000562 _root_.GD.N0230.N0640.d000272
  calc
    (∫⁻ omega, ENNReal.ofReal
        (_root_.GD.N0230.N0638.d000278 (density omega) u * h omega ^ 2) ∂base) ≤
        ∫⁻ omega, ENNReal.ofReal (1 / u) *
          ENNReal.ofReal (density omega * h omega ^ 2) ∂base := by
      apply lintegral_mono
      intro omega
      change ENNReal.ofReal
          (_root_.GD.N0230.N0638.d000278 (density omega) u * h omega ^ 2) ≤
        ENNReal.ofReal (1 / u) *
          ENNReal.ofReal (density omega * h omega ^ 2)
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / u)]
      apply ENNReal.ofReal_le_ofReal
      have hband := _root_.GD.N0230.N0638.d000283
        (hnonneg omega) hu
      have hsquare : 0 ≤ h omega ^ 2 := sq_nonneg _
      have hdiv : _root_.GD.N0230.N0638.d000278 (density omega) u ≤ density omega / u :=
        (le_div_iff₀ hu).2 (by simpa [mul_comm] using hband)
      calc
        _root_.GD.N0230.N0638.d000278 (density omega) u * h omega ^ 2 ≤
            (density omega / u) * h omega ^ 2 :=
          mul_le_mul_of_nonneg_right hdiv hsquare
        _ = (1 / u) * (density omega * h omega ^ 2) := by ring
    _ = ENNReal.ofReal (1 / u) *
        ∫⁻ omega, ENNReal.ofReal (density omega * h omega ^ 2) ∂base := by
      rw [lintegral_const_mul'']
      exact ((hdensity.aemeasurable.mul
        ((Lp.aestronglyMeasurable h).aemeasurable.pow_const 2)).ennreal_ofReal)




theorem d000568
    {Omega : Type*} [MeasurableSpace Omega]
    (base : Measure Omega) (densitySeq : ℕ → Omega → ℝ)
    (hdensity : ∀ j, Measurable (densitySeq j))
    (hnonneg : ∀ j omega, 0 ≤ densitySeq j omega)
    (hSeq : ℕ → _root_.GD.N0230.N0602.d000116 base) (u : ℝ) (hu : 0 < u)
    (henergy : Tendsto
      (fun j ↦ _root_.GD.N0230.N0640.d000272 base (densitySeq j) (hSeq j))
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ _root_.GD.N0230.N0639.d000564 base (densitySeq j)
        (hdensity j) (hnonneg j) (hSeq j) u hu)
      atTop (nhds 0) := by
  let bandEnergy : ℕ → ℝ≥0∞ := fun j ↦
    _root_.GD.N0230.N0639.d000562 base (densitySeq j) (hSeq j) u
  have hscaled : Tendsto
      (fun j ↦ ENNReal.ofReal (1 / u) *
        _root_.GD.N0230.N0640.d000272 base (densitySeq j) (hSeq j))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul henergy (Or.inr ENNReal.ofReal_ne_top))
  have hband : Tendsto bandEnergy atTop (nhds 0) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      exact (not_lt_of_ge bot_le ha).elim
    · intro b hb
      filter_upwards [(tendsto_order.1 hscaled).2 b hb] with j hj
      exact (_root_.GD.N0230.N0639.d000567
        base (densitySeq j) (hdensity j) (hnonneg j) (hSeq j) u hu).trans_lt hj
  let current : ℕ → _root_.GD.N0230.N0602.d000116 base := fun j ↦
    _root_.GD.N0230.N0639.d000564 base (densitySeq j)
      (hdensity j) (hnonneg j) (hSeq j) u hu
  have hrisk : Tendsto
      (fun j ↦ _root_.GD.N0230.N0602.d000117 base 0 (current j)) atTop (nhds 0) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      exact (not_lt_of_ge bot_le ha).elim
    · intro b hb
      filter_upwards [(tendsto_order.1 hband).2 b hb] with j hj
      exact (_root_.GD.N0230.N0639.d000566
        base (densitySeq j) (hdensity j) (hnonneg j)
          (hSeq j) u hu).trans_lt hj
  have hsq : Tendsto (fun j ↦ ‖current j‖ ^ 2) atTop (nhds 0) := by
    have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hrisk
    change Tendsto
      (fun j ↦ (_root_.GD.N0230.N0602.d000117 base 0 (current j)).toReal)
      atTop (nhds (0 : ℝ)) at hreal
    simpa only [_root_.GD.N0230.N0602.d000124, ENNReal.toReal_ofReal
      (sq_nonneg _), ENNReal.toReal_zero, zero_sub, norm_neg] using hreal
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hnorm : Tendsto (fun j ↦ ‖current j‖) atTop (nhds 0) := by
    change Tendsto (fun j ↦ Real.sqrt (‖current j‖ ^ 2))
      atTop (nhds (Real.sqrt 0)) at hsqrt
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
      Real.sqrt_zero] using hsqrt
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa only [sub_zero] using hnorm



theorem d000569
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {xSeq ySeq : ℕ → H} {x y : H}
    (hx : _root_.GD.N0230.N0646.d000537 xSeq x)
    (hy : Tendsto ySeq atTop (nhds y))
    (hbounded : ∃ C : ℝ, ∀ j, ‖xSeq j‖ ≤ C) :
    Tendsto (fun j ↦ ⟪xSeq j, ySeq j⟫_ℝ) atTop (nhds ⟪x, y⟫_ℝ) := by
  obtain ⟨C, hC⟩ := hbounded
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg (xSeq 0)) (hC 0)
  have hdiff : Tendsto (fun j ↦ ySeq j - y) atTop (nhds 0) := by
    have hyconst : Tendsto (fun _ : ℕ ↦ y) atTop (nhds y) :=
      tendsto_const_nhds
    simpa only [sub_self] using hy.sub hyconst
  have hnormDiff : Tendsto (fun j ↦ ‖ySeq j - y‖) atTop (nhds 0) := by
    exact tendsto_zero_iff_norm_tendsto_zero.mp hdiff
  have herrorAbs : Tendsto
      (fun j ↦ |⟪xSeq j, ySeq j - y⟫_ℝ|) atTop (nhds 0) := by
    refine squeeze_zero'
      (g := fun j ↦ C * ‖ySeq j - y‖)
      (Filter.Eventually.of_forall fun j ↦ abs_nonneg _)
      (Filter.Eventually.of_forall fun j ↦ ?_) ?_
    · exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hC j) (norm_nonneg _))
    · simpa only [mul_zero] using hnormDiff.const_mul C
  have herror : Tendsto
      (fun j ↦ ⟪xSeq j, ySeq j - y⟫_ℝ) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using herrorAbs
  have hsum := (hx y).add herror
  convert hsum using 1 <;>
    simp only [inner_sub_right, add_zero] <;> ring_nf



def d000570
    {Omega : Type*} [MeasurableSpace Omega]
    (base : Measure Omega) (densitySeq : ℕ → Omega → ℝ)
    (density : Omega → ℝ)
    (hdensitySeq : ∀ j, Measurable (densitySeq j))
    (hnonnegSeq : ∀ j omega, 0 ≤ densitySeq j omega)
    (hdensity : Measurable density) (hnonneg : ∀ omega, 0 ≤ density omega)
    (u : ℝ) (hu : 0 < u) : Prop :=
  ∀ z : _root_.GD.N0230.N0602.d000116 base,
    Tendsto
      (fun j ↦ _root_.GD.N0230.N0639.d000564 base (densitySeq j)
        (hdensitySeq j) (hnonnegSeq j) z u hu)
      atTop
      (nhds (_root_.GD.N0230.N0639.d000564 base density
        hdensity hnonneg z u hu))








theorem d000571
    {Omega : Type*} [MeasurableSpace Omega]
    (base : Measure Omega) (densitySeq : ℕ → Omega → ℝ)
    (density : Omega → ℝ)
    (hdensitySeq : ∀ j, Measurable (densitySeq j))
    (hnonnegSeq : ∀ j omega, 0 ≤ densitySeq j omega)
    (hdensity : Measurable density) (hnonneg : ∀ omega, 0 ≤ density omega)
    (u : ℝ) (hu : 0 < u)
    (hpointwise : ∀ᵐ omega ∂base,
      Tendsto (fun j ↦ densitySeq j omega) atTop (nhds (density omega))) :
    _root_.GD.N0230.N0639.d000570 base densitySeq density
      hdensitySeq hnonnegSeq hdensity hnonneg u hu := by
  intro z
  let bandSeq : ℕ → Omega → ℝ := fun j omega ↦
    _root_.GD.N0230.N0638.d000278 (densitySeq j omega) u
  let band : Omega → ℝ := fun omega ↦
    _root_.GD.N0230.N0638.d000278 (density omega) u
  let currentSeq : ℕ → _root_.GD.N0230.N0602.d000116 base := fun j ↦
    _root_.GD.N0230.N0639.d000564 base (densitySeq j)
      (hdensitySeq j) (hnonnegSeq j) z u hu
  let current : _root_.GD.N0230.N0602.d000116 base :=
    _root_.GD.N0230.N0639.d000564 base density hdensity hnonneg z u hu
  have hbandMeasSeq : ∀ j, Measurable (bandSeq j) := by
    intro j
    unfold bandSeq _root_.GD.N0230.N0638.d000278
    fun_prop
  have hbandMeas : Measurable band := by
    unfold band _root_.GD.N0230.N0638.d000278
    fun_prop
  have hfinite :
      (∫⁻ omega, ENNReal.ofReal (z omega ^ 2) ∂base) ≠ ∞ := by
    have hzfinite : _root_.GD.N0230.N0602.d000117 base 0 z ≠ ∞ := by
      rw [_root_.GD.N0230.N0602.d000124]
      exact ENNReal.ofReal_ne_top
    simpa only [_root_.GD.N0230.N0602.d000117, sub_zero] using hzfinite
  have hintegral : Tendsto
      (fun j ↦ ∫⁻ omega, ENNReal.ofReal
        (((bandSeq j omega - band omega) * z omega) ^ 2) ∂base)
      atTop (nhds 0) := by
    have hdominated := tendsto_lintegral_of_dominated_convergence'
      (μ := base)
      (F := fun j omega ↦ ENNReal.ofReal
        (((bandSeq j omega - band omega) * z omega) ^ 2))
      (f := fun _ ↦ 0)
      (fun omega ↦ ENNReal.ofReal (z omega ^ 2))
      (fun j ↦ by
        exact (((hbandMeasSeq j).aemeasurable.sub
          hbandMeas.aemeasurable).mul
          (Lp.aestronglyMeasurable z).aemeasurable).pow_const 2 |>.ennreal_ofReal)
      (fun j ↦ Filter.Eventually.of_forall fun omega ↦ by
        apply ENNReal.ofReal_le_ofReal
        have hj₀ : 0 ≤ bandSeq j omega :=
          _root_.GD.N0230.N0638.d000281 (hnonnegSeq j omega) hu.le
        have hj₁ : bandSeq j omega ≤ 1 / 4 :=
          _root_.GD.N0230.N0638.d000282 (hnonnegSeq j omega) hu
        have h₀ : 0 ≤ band omega :=
          _root_.GD.N0230.N0638.d000281 (hnonneg omega) hu.le
        have h₁ : band omega ≤ 1 / 4 :=
          _root_.GD.N0230.N0638.d000282 (hnonneg omega) hu
        have hlower : -1 ≤ bandSeq j omega - band omega := by
          linarith
        have hupper : bandSeq j omega - band omega ≤ 1 := by
          linarith
        have hdiffSq : (bandSeq j omega - band omega) ^ 2 ≤ 1 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hupper)
            (by linarith : 0 ≤ 1 + (bandSeq j omega - band omega))]
        calc
          ((bandSeq j omega - band omega) * z omega) ^ 2 =
              (bandSeq j omega - band omega) ^ 2 * z omega ^ 2 := by ring
          _ ≤ 1 * z omega ^ 2 :=
            mul_le_mul_of_nonneg_right hdiffSq (sq_nonneg _)
          _ = z omega ^ 2 := one_mul _)
      hfinite
      (hpointwise.mono fun omega homega ↦ by
        have hbandTendsto : Tendsto
            (fun j ↦ bandSeq j omega) atTop (nhds (band omega)) := by
          unfold bandSeq band _root_.GD.N0230.N0638.d000278
          apply Tendsto.div
          · exact tendsto_const_nhds.mul homega
          · exact (homega.add tendsto_const_nhds).pow 2
          · have : 0 < density omega + u :=
              add_pos_of_nonneg_of_pos (hnonneg omega) hu
            positivity
        have hreal : Tendsto
            (fun j ↦ ((bandSeq j omega - band omega) * z omega) ^ 2)
            atTop (nhds 0) := by
          convert ((hbandTendsto.sub tendsto_const_nhds).mul
            tendsto_const_nhds).pow 2 using 1 <;> simp
        have hofReal :=
          (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
        have hofReal' : Tendsto
            (fun j ↦ ENNReal.ofReal
              (((bandSeq j omega - band omega) * z omega) ^ 2))
            atTop (nhds (ENNReal.ofReal 0)) := hofReal
        simpa only [ENNReal.ofReal_zero] using hofReal')
    simpa only [lintegral_zero] using hdominated
  have hriskEq : ∀ j,
      _root_.GD.N0230.N0602.d000117 base 0 (currentSeq j - current) =
        ∫⁻ omega, ENNReal.ofReal
          (((bandSeq j omega - band omega) * z omega) ^ 2) ∂base := by
    intro j
    unfold _root_.GD.N0230.N0602.d000117
    apply lintegral_congr_ae
    filter_upwards [
      Lp.coeFn_sub (currentSeq j) current,
      (_root_.GD.N0230.N0639.d000563 base (densitySeq j) (hdensitySeq j)
        (hnonnegSeq j) z hu).coeFn_toLp,
      (_root_.GD.N0230.N0639.d000563 base density hdensity hnonneg z hu).coeFn_toLp]
        with omega hsub hseq hlim
    change currentSeq j omega =
      _root_.GD.N0230.N0638.d000278 (densitySeq j omega) u * z omega at hseq
    change current omega =
      _root_.GD.N0230.N0638.d000278 (density omega) u * z omega at hlim
    rw [hsub]
    change ENNReal.ofReal
      (((currentSeq j omega - current omega) - 0) ^ 2) = _
    rw [hseq, hlim]
    simp only [sub_zero, bandSeq, band]
    congr 1
    ring
  have hrisk : Tendsto
      (fun j ↦ _root_.GD.N0230.N0602.d000117 base 0 (currentSeq j - current))
      atTop (nhds 0) := by
    exact hintegral.congr' (Filter.Eventually.of_forall fun j ↦ (hriskEq j).symm)
  have hsq : Tendsto (fun j ↦ ‖currentSeq j - current‖ ^ 2)
      atTop (nhds 0) := by
    have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hrisk
    change Tendsto
      (fun j ↦ (_root_.GD.N0230.N0602.d000117 base 0 (currentSeq j - current)).toReal)
      atTop (nhds (0 : ℝ)) at hreal
    simpa only [_root_.GD.N0230.N0602.d000124, ENNReal.toReal_ofReal
      (sq_nonneg _), ENNReal.toReal_zero, zero_sub, norm_neg] using hreal
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hnorm : Tendsto (fun j ↦ ‖currentSeq j - current‖)
      atTop (nhds 0) := by
    change Tendsto (fun j ↦ Real.sqrt (‖currentSeq j - current‖ ^ 2))
      atTop (nhds (Real.sqrt 0)) at hsqrt
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
      Real.sqrt_zero] using hsqrt
  exact tendsto_iff_norm_sub_tendsto_zero.2 hnorm



theorem d000572
    {Omega : Type*} [MeasurableSpace Omega]
    (base : Measure Omega) (densitySeq : ℕ → Omega → ℝ)
    (density : Omega → ℝ)
    (hdensitySeq : ∀ j, Measurable (densitySeq j))
    (hnonnegSeq : ∀ j omega, 0 ≤ densitySeq j omega)
    (hdensity : Measurable density) (hnonneg : ∀ omega, 0 ≤ density omega)
    (u : ℝ) (hu : 0 < u)
    (hpointwise : ∀ omega,
      Tendsto (fun j ↦ densitySeq j omega) atTop (nhds (density omega))) :
    _root_.GD.N0230.N0639.d000570 base densitySeq density
      hdensitySeq hnonnegSeq hdensity hnonneg u hu :=
  _root_.GD.N0230.N0639.d000571 base densitySeq density
    hdensitySeq hnonnegSeq hdensity hnonneg u hu
    (Filter.Eventually.of_forall hpointwise)







theorem d000573
    {Omega : Type*} [MeasurableSpace Omega]
    (base : Measure Omega) (densitySeq : ℕ → Omega → ℝ)
    (density : Omega → ℝ)
    (hdensitySeq : ∀ j, Measurable (densitySeq j))
    (hnonnegSeq : ∀ j omega, 0 ≤ densitySeq j omega)
    (hdensity : Measurable density) (hnonneg : ∀ omega, 0 ≤ density omega)
    (hpositive : ∀ᵐ omega ∂base, 0 < density omega)
    (hSeq : ℕ → _root_.GD.N0230.N0602.d000116 base) (h : _root_.GD.N0230.N0602.d000116 base)
    (hweak : _root_.GD.N0230.N0646.d000537 hSeq h)
    (hbounded : ∃ C : ℝ, ∀ j, ‖hSeq j‖ ≤ C)
    (u : ℝ) (hu : 0 < u)
    (htests : _root_.GD.N0230.N0639.d000570 base densitySeq density
      hdensitySeq hnonnegSeq hdensity hnonneg u hu)
    (henergy : Tendsto
      (fun j ↦ _root_.GD.N0230.N0640.d000272 base (densitySeq j) (hSeq j))
      atTop (nhds 0)) :
    h = 0 := by
  let currentSeq : ℕ → _root_.GD.N0230.N0602.d000116 base := fun j ↦
    _root_.GD.N0230.N0639.d000564 base (densitySeq j)
      (hdensitySeq j) (hnonnegSeq j) (hSeq j) u hu
  let currentLimit : _root_.GD.N0230.N0602.d000116 base :=
    _root_.GD.N0230.N0639.d000564 base density hdensity hnonneg h u hu
  have hcurrentZero : Tendsto currentSeq atTop (nhds 0) :=
    _root_.GD.N0230.N0639.d000568 base densitySeq hdensitySeq
      hnonnegSeq hSeq u hu henergy
  have hinnerLimit : ∀ z : _root_.GD.N0230.N0602.d000116 base,
      Tendsto (fun j ↦ ⟪currentSeq j, z⟫_ℝ) atTop
        (nhds ⟪currentLimit, z⟫_ℝ) := by
    intro z
    have hvary := _root_.GD.N0230.N0639.d000569
      hweak (htests z) hbounded
    simpa only [currentSeq, currentLimit,
      _root_.GD.N0230.N0639.d000565] using hvary
  have hcurrentLimitZero : currentLimit = 0 := by
    apply ext_inner_right ℝ
    intro z
    have hzero : Tendsto (fun j ↦ ⟪currentSeq j, z⟫_ℝ)
        atTop (nhds 0) := by
      simpa only [inner_zero_left] using _root_.GD.N0230.N0646.d000539 hcurrentZero z
    have heq : ⟪currentLimit, z⟫_ℝ = 0 :=
      tendsto_nhds_unique (hinnerLimit z) hzero
    simpa [heq]
  apply Lp.ext
  have hcurrentCoe :=
    (_root_.GD.N0230.N0639.d000563 base density hdensity hnonneg h hu).coeFn_toLp
  have hzeroCoe :
      (fun omega ↦ currentLimit omega) =ᵐ[base] fun _ ↦ 0 := by
    rw [hcurrentLimitZero]
    exact Lp.coeFn_zero ℝ 2 base
  have hlpZero :
      (fun omega ↦ (0 : _root_.GD.N0230.N0602.d000116 base) omega) =ᵐ[base] fun _ ↦ 0 :=
    Lp.coeFn_zero ℝ 2 base
  filter_upwards [hcurrentCoe, hzeroCoe, hpositive, hlpZero]
      with omega hcoe hzero hpos hLpZero
  have hbandPos : 0 < _root_.GD.N0230.N0638.d000278 (density omega) u := by
    unfold _root_.GD.N0230.N0638.d000278
    positivity
  have hhzero : h omega = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hbandPos.ne'
    simpa only [currentLimit] using hcoe.symm.trans hzero
  exact hhzero.trans hLpZero.symm

end

end N0639
end N0230
end GD

#print axioms _root_.GD.N0230.N0639.d000568
#print axioms _root_.GD.N0230.N0639.d000573
