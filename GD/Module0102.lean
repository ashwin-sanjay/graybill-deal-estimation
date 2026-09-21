import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Lebesgue.Add










open MeasureTheory Set Filter

namespace GD
namespace N0230
namespace N0716

noncomputable section

variable {α : Type*} {m m0 : MeasurableSpace α} {μ : Measure α}

private theorem d001316 (a : ℝ) :
    Tendsto (fun n : ℕ => min a (n : ℝ)) atTop (nhds a) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_atTop.2
    ⟨Nat.ceil a, fun n hn => Nat.le_ceil a |>.trans (by
      show (Nat.ceil a : ℝ) ≤ (n : ℝ)
      exact_mod_cast hn)⟩] with n hn
  exact (min_eq_left hn).symm



theorem d001317
    (hm : m ≤ m0) [IsFiniteMeasure μ] [SigmaFinite (μ.trim hm)]
    {f : α → ℝ} (c : ℝ) (hf : MemLp f 2 μ) :
    (fun x => (μ[f | m] x - c) ^ 2) ≤ᵐ[μ]
      μ[(fun x => (f x - c) ^ 2) | m] := by
  have hf_int : Integrable f μ := hf.integrable (by norm_num)
  have hg_lp : MemLp (fun x => f x - c) 2 μ :=
    hf.sub (memLp_const c)
  have hg_int : Integrable (fun x => f x - c) μ :=
    hg_lp.integrable (by norm_num)
  have hg_sq : Integrable (fun x => (f x - c) ^ 2) μ :=
    hg_lp.integrable_sq
  have hj :
      (fun x => (μ[(fun y => f y - c) | m] x) ^ 2) ≤ᵐ[μ]
        μ[(fun x => (f x - c) ^ 2) | m] := by
    have hj0 :=
      even_two.convexOn_pow.map_condExp_le_of_finiteDimensional
        (f := fun x => f x - c) hm hg_int hg_sq
    have hr :
        μ[((fun z : ℝ => z ^ 2) ∘ fun x => f x - c) | m] =ᵐ[μ]
          μ[(fun x => (f x - c) ^ 2) | m] := by
      apply condExp_congr_ae
      filter_upwards with x
      rfl
    filter_upwards [hj0, hr] with x hx hrx
    rw [← hrx]
    simpa only [Function.comp_apply] using hx
  have hcenter :
      μ[(fun x => f x - c) | m] =ᵐ[μ]
        fun x => μ[f | m] x - c := by
    have hsub := condExp_sub hf_int (integrable_const c) m
    have hleft :
        μ[(fun x => f x - c) | m] =ᵐ[μ]
          μ[(f - fun _ => c) | m] := by
      apply condExp_congr_ae
      filter_upwards with x
      rfl
    filter_upwards [hleft, hsub] with x hleftx hx
    rw [hleftx, hx]
    simp [condExp_const hm]
  filter_upwards [hj, hcenter] with x hx hcx
  simpa [hcx] using hx



theorem d001318
    (hm : m ≤ m0) [IsFiniteMeasure μ] [SigmaFinite (μ.trim hm)]
    {f w : α → ℝ} (c C : ℝ) (hf : MemLp f 2 μ)
    (hw : StronglyMeasurable[m] w)
    (hw_nonneg : 0 ≤ᵐ[μ] w)
    (hw_bound : ∀ᵐ x ∂μ, ‖w x‖ ≤ C) :
    (∫ x, w x * (μ[f | m] x - c) ^ 2 ∂μ) ≤
      ∫ x, w x * (f x - c) ^ 2 ∂μ := by
  have hf_int : Integrable f μ := hf.integrable (by norm_num)
  have hg_lp : MemLp (fun x => f x - c) 2 μ :=
    hf.sub (memLp_const c)
  have hg_sq : Integrable (fun x => (f x - c) ^ 2) μ :=
    hg_lp.integrable_sq
  have hq_lp : MemLp (fun x => μ[f | m] x - c) 2 μ :=
    hf.condExp.sub (memLp_const c)
  have hq_sq : Integrable (fun x => (μ[f | m] x - c) ^ 2) μ :=
    hq_lp.integrable_sq
  have hw_ae : AEStronglyMeasurable w μ :=
    (hw.mono hm).aestronglyMeasurable
  have hleft_int :
      Integrable (fun x => w x * (μ[f | m] x - c) ^ 2) μ :=
    hq_sq.bdd_mul hw_ae hw_bound
  have hright_int :
      Integrable (fun x => w x * (f x - c) ^ 2) μ :=
    hg_sq.bdd_mul hw_ae hw_bound
  have hcond_sq_int :
      Integrable (μ[(fun x => (f x - c) ^ 2) | m]) μ :=
    integrable_condExp
  have hweighted_cond_sq_int :
      Integrable
        (fun x => w x * μ[(fun y => (f y - c) ^ 2) | m] x) μ :=
    hcond_sq_int.bdd_mul hw_ae hw_bound
  have hj := _root_.GD.N0230.N0716.d001317 hm c hf
  have hfirst :
      (∫ x, w x * (μ[f | m] x - c) ^ 2 ∂μ) ≤
        ∫ x, w x * μ[(fun y => (f y - c) ^ 2) | m] x ∂μ := by
    apply integral_mono_ae hleft_int hweighted_cond_sq_int
    filter_upwards [hw_nonneg, hj] with x hwx hjx
    exact mul_le_mul_of_nonneg_left hjx hwx
  have hpull :
      μ[(fun x => w x * (f x - c) ^ 2) | m] =ᵐ[μ]
        fun x => w x * μ[(fun y => (f y - c) ^ 2) | m] x := by
    have hp := condExp_mul_of_stronglyMeasurable_left
      hw hright_int hg_sq
    exact hp
  calc
    (∫ x, w x * (μ[f | m] x - c) ^ 2 ∂μ) ≤
        ∫ x, w x * μ[(fun y => (f y - c) ^ 2) | m] x ∂μ := hfirst
    _ = ∫ x, μ[(fun y => w y * (f y - c) ^ 2) | m] x ∂μ := by
      exact integral_congr_ae hpull.symm
    _ = ∫ x, w x * (f x - c) ^ 2 ∂μ :=
      integral_condExp hm





theorem d001319
    (hm : m ≤ m0) [IsFiniteMeasure μ] [SigmaFinite (μ.trim hm)]
    {f w : α → ℝ} (c : ℝ) (hf : MemLp f 2 μ)
    (hw : StronglyMeasurable[m] w)
    (hw_nonneg : 0 ≤ᵐ[μ] w) :
    (∫⁻ x, ENNReal.ofReal (w x * (μ[f | m] x - c) ^ 2) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (w x * (f x - c) ^ 2) ∂μ := by
  let wt : ℕ → α → ℝ := fun n x => min (w x) (n : ℝ)
  have hwt_strong (n : ℕ) : StronglyMeasurable[m] (wt n) := by
    exact (hw.measurable.min measurable_const).stronglyMeasurable
  have hwt_nonneg (n : ℕ) : 0 ≤ᵐ[μ] wt n := by
    filter_upwards [hw_nonneg] with x hx
    exact le_min hx (Nat.cast_nonneg n)
  have hwt_bound (n : ℕ) : ∀ᵐ x ∂μ, ‖wt n x‖ ≤ (n : ℝ) := by
    filter_upwards [hw_nonneg] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hx (Nat.cast_nonneg n))]
    exact min_le_right _ _
  have hq_lp : MemLp (fun x => μ[f | m] x - c) 2 μ :=
    hf.condExp.sub (memLp_const c)
  have hq_sq : Integrable (fun x => (μ[f | m] x - c) ^ 2) μ :=
    hq_lp.integrable_sq
  have hg_lp : MemLp (fun x => f x - c) 2 μ :=
    hf.sub (memLp_const c)
  have hg_sq : Integrable (fun x => (f x - c) ^ 2) μ :=
    hg_lp.integrable_sq
  have hwt_ae (n : ℕ) : AEStronglyMeasurable (wt n) μ :=
    ((hwt_strong n).mono hm).aestronglyMeasurable
  have hleft_int (n : ℕ) :
      Integrable (fun x => wt n x * (μ[f | m] x - c) ^ 2) μ :=
    hq_sq.bdd_mul (hwt_ae n) (hwt_bound n)
  have hright_int (n : ℕ) :
      Integrable (fun x => wt n x * (f x - c) ^ 2) μ :=
    hg_sq.bdd_mul (hwt_ae n) (hwt_bound n)
  have hleft_nonneg (n : ℕ) :
      0 ≤ᵐ[μ] fun x => wt n x * (μ[f | m] x - c) ^ 2 := by
    filter_upwards [hwt_nonneg n] with x hx
    exact mul_nonneg hx (sq_nonneg _)
  have hright_nonneg (n : ℕ) :
      0 ≤ᵐ[μ] fun x => wt n x * (f x - c) ^ 2 := by
    filter_upwards [hwt_nonneg n] with x hx
    exact mul_nonneg hx (sq_nonneg _)
  have htruncated (n : ℕ) :
      (∫⁻ x, ENNReal.ofReal (wt n x * (μ[f | m] x - c) ^ 2) ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal (wt n x * (f x - c) ^ 2) ∂μ := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hleft_int n) (hleft_nonneg n),
      ← ofReal_integral_eq_lintegral_ofReal (hright_int n) (hright_nonneg n)]
    exact ENNReal.ofReal_le_ofReal
      (_root_.GD.N0230.N0716.d001318
        hm c (n : ℝ) hf (hwt_strong n) (hwt_nonneg n) (hwt_bound n))
  have hleft_meas (n : ℕ) :
      AEMeasurable
        (fun x => ENNReal.ofReal (wt n x * (μ[f | m] x - c) ^ 2)) μ :=
    (hleft_int n).aemeasurable.ennreal_ofReal
  have hright_meas (n : ℕ) :
      AEMeasurable (fun x => ENNReal.ofReal (wt n x * (f x - c) ^ 2)) μ :=
    (hright_int n).aemeasurable.ennreal_ofReal
  have hleft_mono : ∀ᵐ x ∂μ, Monotone fun n =>
      ENNReal.ofReal (wt n x * (μ[f | m] x - c) ^ 2) := by
    filter_upwards with x n k hnk
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (min_le_min_left (w x) (by exact_mod_cast hnk)) (sq_nonneg _)
  have hright_mono : ∀ᵐ x ∂μ, Monotone fun n =>
      ENNReal.ofReal (wt n x * (f x - c) ^ 2) := by
    filter_upwards with x n k hnk
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (min_le_min_left (w x) (by exact_mod_cast hnk)) (sq_nonneg _)
  have hleft_tendsto : ∀ᵐ x ∂μ, Tendsto
      (fun n => ENNReal.ofReal (wt n x * (μ[f | m] x - c) ^ 2)) atTop
      (nhds (ENNReal.ofReal (w x * (μ[f | m] x - c) ^ 2))) := by
    filter_upwards with x
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((_root_.GD.N0230.N0716.d001316 (w x)).mul_const _)
  have hright_tendsto : ∀ᵐ x ∂μ, Tendsto
      (fun n => ENNReal.ofReal (wt n x * (f x - c) ^ 2)) atTop
      (nhds (ENNReal.ofReal (w x * (f x - c) ^ 2))) := by
    filter_upwards with x
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((_root_.GD.N0230.N0716.d001316 (w x)).mul_const _)
  have hleft_limit := lintegral_tendsto_of_tendsto_of_monotone
    hleft_meas hleft_mono hleft_tendsto
  have hright_limit := lintegral_tendsto_of_tendsto_of_monotone
    hright_meas hright_mono hright_tendsto
  exact le_of_tendsto_of_tendsto' hleft_limit hright_limit htruncated




theorem d001320
    (hm : m ≤ m0) [IsFiniteMeasure μ] [SigmaFinite (μ.trim hm)]
    {f w : α → ℝ} (c : ℝ) (hf : MemLp f 2 μ)
    (hw : StronglyMeasurable[m] w)
    (hw_nonneg : 0 ≤ᵐ[μ] w)
    (hright : Integrable (fun x => w x * (f x - c) ^ 2) μ) :
    Integrable (fun x => w x * (μ[f | m] x - c) ^ 2) μ ∧
      (∫ x, w x * (μ[f | m] x - c) ^ 2 ∂μ) ≤
        ∫ x, w x * (f x - c) ^ 2 ∂μ := by
  have hq_lp : MemLp (fun x => μ[f | m] x - c) 2 μ :=
    hf.condExp.sub (memLp_const c)
  have hleft_ae :
      AEStronglyMeasurable (fun x => w x * (μ[f | m] x - c) ^ 2) μ :=
    ((hw.mono hm).aestronglyMeasurable.mul hq_lp.integrable_sq.aestronglyMeasurable)
  have hleft_nonneg :
      0 ≤ᵐ[μ] fun x => w x * (μ[f | m] x - c) ^ 2 := by
    filter_upwards [hw_nonneg] with x hx
    exact mul_nonneg hx (sq_nonneg _)
  have hright_nonneg : 0 ≤ᵐ[μ] fun x => w x * (f x - c) ^ 2 := by
    filter_upwards [hw_nonneg] with x hx
    exact mul_nonneg hx (sq_nonneg _)
  have hlin := _root_.GD.N0230.N0716.d001319
    hm c hf hw hw_nonneg
  have hright_ne :
      (∫⁻ x, ENNReal.ofReal (w x * (f x - c) ^ 2) ∂μ) ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable
      hright.aestronglyMeasurable hright_nonneg).2 hright
  have hleft_ne :
      (∫⁻ x, ENNReal.ofReal (w x * (μ[f | m] x - c) ^ 2) ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top hright_ne hlin
  have hleft :
      Integrable (fun x => w x * (μ[f | m] x - c) ^ 2) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hleft_ae hleft_nonneg).1 hleft_ne
  refine ⟨hleft, ?_⟩
  rw [← ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hright_nonneg),
    ofReal_integral_eq_lintegral_ofReal hleft hleft_nonneg,
    ofReal_integral_eq_lintegral_ofReal hright hright_nonneg]
  exact hlin







theorem d001321
    (hm : m ≤ m0) [IsFiniteMeasure μ] [SigmaFinite (μ.trim hm)]
    {f w : α → ℝ} (c C : ℝ) (hf : MemLp f 2 μ)
    (hw : StronglyMeasurable[m] w)
    (hw_nonneg : 0 ≤ᵐ[μ] w)
    (hw_bound : ∀ᵐ x ∂μ, ‖w x‖ ≤ C) :
    (∫ x, w x * (f x - c) ^ 2 ∂μ) =
      (∫ x, w x * (μ[f | m] x - c) ^ 2 ∂μ) +
        ∫ x, w x * (f x - μ[f | m] x) ^ 2 ∂μ := by
  let q : α → ℝ := μ[f | m]
  let r : α → ℝ := f - q
  have hf_int : Integrable f μ := hf.integrable (by norm_num)
  have hq_lp : MemLp q 2 μ := by
    exact hf.condExp
  have hr_lp : MemLp r 2 μ := by
    exact hf.sub hq_lp
  have hcenter_lp : MemLp (fun x ↦ q x - c) 2 μ :=
    hq_lp.sub (memLp_const c)
  have hfull_lp : MemLp (fun x ↦ f x - c) 2 μ :=
    hf.sub (memLp_const c)
  have hw_ae : AEStronglyMeasurable w μ :=
    (hw.mono hm).aestronglyMeasurable
  have hfull_int : Integrable (fun x ↦ w x * (f x - c) ^ 2) μ :=
    hfull_lp.integrable_sq.bdd_mul hw_ae hw_bound
  have hcenter_int : Integrable (fun x ↦ w x * (q x - c) ^ 2) μ :=
    hcenter_lp.integrable_sq.bdd_mul hw_ae hw_bound
  have hresidual_int : Integrable (fun x ↦ w x * r x ^ 2) μ :=
    hr_lp.integrable_sq.bdd_mul hw_ae hw_bound
  have hcross_int : Integrable (fun x ↦ w x * ((q x - c) * r x)) μ := by
    have hcross0 : Integrable (fun x ↦ (q x - c) * r x) μ := by
      change Integrable ((fun x ↦ q x - c) * r) μ
      exact MemLp.integrable_mul (p := 2) (q := 2) hcenter_lp hr_lp
    exact hcross0.bdd_mul hw_ae hw_bound
  have hresidual_condExp : μ[r | m] =ᵐ[μ] 0 := by
    have hsub := condExp_sub hf_int
      (integrable_condExp (f := f) (m := m)) m
    have hqfixed : μ[q | m] =ᵐ[μ] q :=
      condExp_of_aestronglyMeasurable' hm
        stronglyMeasurable_condExp.aestronglyMeasurable
        (integrable_condExp (f := f) (m := m))
    filter_upwards [hsub, hqfixed] with x hsubx hfixedx
    simp only [r, q, Pi.zero_apply]
    rw [hsubx]
    simp only [Pi.sub_apply]
    rw [hfixedx]
    ring
  have hweightedCenter : StronglyMeasurable[m]
      (fun x ↦ w x * (q x - c)) :=
    hw.mul (stronglyMeasurable_condExp.sub stronglyMeasurable_const)
  have hcross_zero : (∫ x, w x * ((q x - c) * r x) ∂μ) = 0 := by
    let a : α → ℝ := fun x ↦ w x * (q x - c)
    have hpull : μ[a * r | m] =ᵐ[μ] a * μ[r | m] :=
      condExp_mul_of_stronglyMeasurable_left hweightedCenter
        (by
          exact hcross_int.congr (Filter.Eventually.of_forall fun x ↦ by
            simp only [a, Pi.mul_apply]
            ring))
        (hr_lp.integrable (by norm_num))
    calc
      (∫ x, w x * ((q x - c) * r x) ∂μ) =
          ∫ x, (a * r) x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [a, Pi.mul_apply]
        ring
      _ = ∫ x, μ[a * r | m] x ∂μ := by
        rw [integral_condExp hm]
      _ = ∫ x, (a * μ[r | m]) x ∂μ :=
        integral_congr_ae hpull
      _ = 0 := by
        rw [integral_congr_ae (EventuallyEq.mul (EventuallyEq.rfl) hresidual_condExp)]
        simp
  calc
    (∫ x, w x * (f x - c) ^ 2 ∂μ) =
        ∫ x, w x * ((q x - c) ^ 2 + r x ^ 2 +
          2 * ((q x - c) * r x)) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [q, r, Pi.sub_apply]
      ring
    _ = (∫ x, w x * (q x - c) ^ 2 ∂μ) +
          (∫ x, w x * r x ^ 2 ∂μ) +
            2 * ∫ x, w x * ((q x - c) * r x) ∂μ := by
      have htwoCross : Integrable
          (fun x ↦ 2 * (w x * ((q x - c) * r x))) μ :=
        hcross_int.const_mul 2
      calc
        (∫ x, w x * ((q x - c) ^ 2 + r x ^ 2 +
            2 * ((q x - c) * r x)) ∂μ) =
            ∫ x, (w x * (q x - c) ^ 2 + w x * r x ^ 2) +
              2 * (w x * ((q x - c) * r x)) ∂μ := by
          apply integral_congr_ae
          filter_upwards with x
          ring
        _ = (∫ x, w x * (q x - c) ^ 2 + w x * r x ^ 2 ∂μ) +
              ∫ x, 2 * (w x * ((q x - c) * r x)) ∂μ := by
          simpa only [Pi.add_apply] using
            integral_add (hcenter_int.add hresidual_int) htwoCross
        _ = ((∫ x, w x * (q x - c) ^ 2 ∂μ) +
              ∫ x, w x * r x ^ 2 ∂μ) +
            2 * ∫ x, w x * ((q x - c) * r x) ∂μ := by
          rw [integral_add hcenter_int hresidual_int, integral_const_mul]
    _ = (∫ x, w x * (q x - c) ^ 2 ∂μ) +
        ∫ x, w x * r x ^ 2 ∂μ := by
      rw [hcross_zero]
      ring
    _ = (∫ x, w x * (μ[f | m] x - c) ^ 2 ∂μ) +
        ∫ x, w x * (f x - μ[f | m] x) ^ 2 ∂μ := rfl








theorem d001322
    (hm : m ≤ m0) [IsFiniteMeasure μ] [SigmaFinite (μ.trim hm)]
    {f w : α → ℝ} (c : ℝ) (hf : MemLp f 2 μ)
    (hw : StronglyMeasurable[m] w)
    (hw_nonneg : 0 ≤ᵐ[μ] w)
    (hfull : Integrable (fun x ↦ w x * (f x - c) ^ 2) μ) :
    Integrable (fun x ↦ w x * (f x - μ[f | m] x) ^ 2) μ ∧
      (∫ x, w x * (f x - c) ^ 2 ∂μ) =
        (∫ x, w x * (μ[f | m] x - c) ^ 2 ∂μ) +
          ∫ x, w x * (f x - μ[f | m] x) ^ 2 ∂μ := by
  let q : α → ℝ := μ[f | m]
  let r : α → ℝ := f - q
  have hf_int : Integrable f μ := hf.integrable (by norm_num)
  have hq_lp : MemLp q 2 μ := hf.condExp
  have hr_lp : MemLp r 2 μ := hf.sub hq_lp
  have hcenter_lp : MemLp (fun x ↦ q x - c) 2 μ :=
    hq_lp.sub (memLp_const c)
  have hcenter_int : Integrable (fun x ↦ w x * (q x - c) ^ 2) μ := by
    exact (_root_.GD.N0230.N0716.d001320
      hm c hf hw hw_nonneg hfull).1
  have hw_ae : AEStronglyMeasurable w μ :=
    (hw.mono hm).aestronglyMeasurable
  have hresidualMeas : AEStronglyMeasurable
      (fun x ↦ w x * r x ^ 2) μ :=
    hw_ae.mul hr_lp.integrable_sq.aestronglyMeasurable
  have hresidual_int : Integrable (fun x ↦ w x * r x ^ 2) μ := by
    refine Integrable.mono'
      ((hfull.const_mul 2).add (hcenter_int.const_mul 2))
      hresidualMeas ?_
    filter_upwards [hw_nonneg] with x hwx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hwx (sq_nonneg _))]
    have hsq : r x ^ 2 ≤
        2 * (f x - c) ^ 2 + 2 * (q x - c) ^ 2 := by
      simp only [r, Pi.sub_apply]
      nlinarith [sq_nonneg ((f x - c) + (q x - c))]
    calc
      w x * r x ^ 2 ≤
          w x * (2 * (f x - c) ^ 2 + 2 * (q x - c) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hwx
      _ = 2 * (w x * (f x - c) ^ 2) +
          2 * (w x * (q x - c) ^ 2) := by ring
  have hcrossMeas : AEStronglyMeasurable
      (fun x ↦ w x * ((q x - c) * r x)) μ :=
    hw_ae.mul (hcenter_lp.aestronglyMeasurable.mul hr_lp.aestronglyMeasurable)
  have hcross_int : Integrable (fun x ↦ w x * ((q x - c) * r x)) μ := by
    let majorant : α → ℝ := fun x ↦
      (1 / 2 : ℝ) * (w x * (q x - c) ^ 2) +
        (1 / 2 : ℝ) * (w x * r x ^ 2)
    have hmajorant : Integrable majorant μ :=
      (hcenter_int.const_mul (1 / 2 : ℝ)).add
        (hresidual_int.const_mul (1 / 2 : ℝ))
    refine Integrable.mono' hmajorant hcrossMeas ?_
    filter_upwards [hw_nonneg] with x hwx
    have habs : |q x - c| * |r x| ≤
        ((q x - c) ^ 2 + r x ^ 2) / 2 := by
      have hsquare : 0 ≤ (|q x - c| - |r x|) ^ 2 := sq_nonneg _
      have hqabs : |q x - c| ^ 2 = (q x - c) ^ 2 := sq_abs _
      have hrabs : |r x| ^ 2 = r x ^ 2 := sq_abs _
      nlinarith
    calc
      ‖w x * ((q x - c) * r x)‖ =
          w x * (|q x - c| * |r x|) := by
        simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hwx]
      _ ≤ w x * (((q x - c) ^ 2 + r x ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left habs hwx
      _ = majorant x := by
        dsimp only [majorant]
        ring
  have hresidual_condExp : μ[r | m] =ᵐ[μ] 0 := by
    have hsub := condExp_sub hf_int
      (integrable_condExp (f := f) (m := m)) m
    have hqfixed : μ[q | m] =ᵐ[μ] q :=
      condExp_of_aestronglyMeasurable' hm
        stronglyMeasurable_condExp.aestronglyMeasurable
        (integrable_condExp (f := f) (m := m))
    filter_upwards [hsub, hqfixed] with x hsubx hfixedx
    simp only [r, q, Pi.zero_apply]
    rw [hsubx]
    simp only [Pi.sub_apply]
    rw [hfixedx]
    ring
  have hweightedCenter : StronglyMeasurable[m]
      (fun x ↦ w x * (q x - c)) :=
    hw.mul (stronglyMeasurable_condExp.sub stronglyMeasurable_const)
  have hcross_zero : (∫ x, w x * ((q x - c) * r x) ∂μ) = 0 := by
    let a : α → ℝ := fun x ↦ w x * (q x - c)
    have hpull : μ[a * r | m] =ᵐ[μ] a * μ[r | m] :=
      condExp_mul_of_stronglyMeasurable_left hweightedCenter
        (by
          exact hcross_int.congr (Filter.Eventually.of_forall fun x ↦ by
            simp only [a, Pi.mul_apply]
            ring))
        (hr_lp.integrable (by norm_num))
    calc
      (∫ x, w x * ((q x - c) * r x) ∂μ) =
          ∫ x, (a * r) x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [a, Pi.mul_apply]
        ring
      _ = ∫ x, μ[a * r | m] x ∂μ := by
        rw [integral_condExp hm]
      _ = ∫ x, (a * μ[r | m]) x ∂μ := integral_congr_ae hpull
      _ = 0 := by
        rw [integral_congr_ae
          (EventuallyEq.mul (EventuallyEq.rfl) hresidual_condExp)]
        simp
  refine ⟨?_, ?_⟩
  · simpa only [r, q, Pi.sub_apply] using hresidual_int
  · calc
      (∫ x, w x * (f x - c) ^ 2 ∂μ) =
          ∫ x, w x * ((q x - c) ^ 2 + r x ^ 2 +
            2 * ((q x - c) * r x)) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [q, r, Pi.sub_apply]
        ring
      _ = (∫ x, w x * (q x - c) ^ 2 ∂μ) +
            (∫ x, w x * r x ^ 2 ∂μ) +
              2 * ∫ x, w x * ((q x - c) * r x) ∂μ := by
        have htwoCross : Integrable
            (fun x ↦ 2 * (w x * ((q x - c) * r x))) μ :=
          hcross_int.const_mul 2
        calc
          (∫ x, w x * ((q x - c) ^ 2 + r x ^ 2 +
              2 * ((q x - c) * r x)) ∂μ) =
              ∫ x, (w x * (q x - c) ^ 2 + w x * r x ^ 2) +
                2 * (w x * ((q x - c) * r x)) ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            ring
          _ = (∫ x, w x * (q x - c) ^ 2 + w x * r x ^ 2 ∂μ) +
                ∫ x, 2 * (w x * ((q x - c) * r x)) ∂μ := by
            simpa only [Pi.add_apply] using
              integral_add (hcenter_int.add hresidual_int) htwoCross
          _ = ((∫ x, w x * (q x - c) ^ 2 ∂μ) +
                ∫ x, w x * r x ^ 2 ∂μ) +
              2 * ∫ x, w x * ((q x - c) * r x) ∂μ := by
            rw [integral_add hcenter_int hresidual_int, integral_const_mul]
      _ = (∫ x, w x * (q x - c) ^ 2 ∂μ) +
          ∫ x, w x * r x ^ 2 ∂μ := by
        rw [hcross_zero]
        ring
      _ = (∫ x, w x * (μ[f | m] x - c) ^ 2 ∂μ) +
          ∫ x, w x * (f x - μ[f | m] x) ^ 2 ∂μ := rfl



theorem d001323
    (hm : m ≤ m0) [IsFiniteMeasure μ] [SigmaFinite (μ.trim hm)]
    {f w : α → ℝ} (c : ℝ) (hf : MemLp f 2 μ)
    (hw : StronglyMeasurable[m] w)
    (hw_nonneg : 0 ≤ᵐ[μ] w)
    (hfull : Integrable (fun x ↦ w x * (f x - c) ^ 2) μ) :
    (∫ x, w x * (f x - c) ^ 2 ∂μ) =
      (∫ x, w x * (μ[f | m] x - c) ^ 2 ∂μ) +
        ∫ x, w x * (f x - μ[f | m] x) ^ 2 ∂μ :=
  (_root_.GD.N0230.N0716.d001322
    hm c hf hw hw_nonneg hfull).2

end

end N0716
end N0230
end GD

#print axioms _root_.GD.N0230.N0716.d001317
#print axioms _root_.GD.N0230.N0716.d001318
#print axioms _root_.GD.N0230.N0716.d001319
#print axioms _root_.GD.N0230.N0716.d001320
#print axioms _root_.GD.N0230.N0716.d001322
#print axioms _root_.GD.N0230.N0716.d001323
