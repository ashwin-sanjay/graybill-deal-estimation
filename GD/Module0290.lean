import GD.Module0289
import Mathlib.MeasureTheory.Integral.Bochner.Basic














open MeasureTheory

namespace GD
namespace N0237
namespace N0746

open _root_.GD.N0237.N0747


noncomputable def d004280
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (residual correction : Ω → ℝ) : ℝ :=
  ∫ ω, residual ω * correction ω ∂μ


noncomputable def d004281
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (correction : Ω → ℝ) : ℝ :=
  ∫ ω, (correction ω) ^ 2 ∂μ


noncomputable def d004282
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ε : ℝ)
    (residual correction : Ω → ℝ) : ℝ :=
  ∫ ω, _root_.GD.N0237.N0747.d004276 ε residual correction ω ∂μ






theorem d004283
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ε : ℝ)
    (residual correction : Ω → ℝ)
    (henergy : Integrable (fun ω ↦ (correction ω) ^ 2) μ)
    (hgain : Integrable (fun ω ↦ residual ω * correction ω) μ) :
    Integrable (_root_.GD.N0237.N0747.d004276 ε residual correction) μ := by
  have hfun :
      _root_.GD.N0237.N0747.d004276 ε residual correction =
        fun ω ↦
          ε ^ 2 * (correction ω) ^ 2 -
            (2 * ε) * (residual ω * correction ω) := by
    funext ω
    exact _root_.GD.N0237.N0747.d004277 ε residual correction ω
  rw [hfun]
  exact
    (henergy.const_mul (ε ^ 2)).sub
      (hgain.const_mul (2 * ε))





theorem d004284
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ε : ℝ)
    (residual correction : Ω → ℝ)
    (hresidual :
      Integrable (fun ω ↦ (residual ω) ^ 2) μ)
    (henergy : Integrable (fun ω ↦ (correction ω) ^ 2) μ)
    (hgain : Integrable (fun ω ↦ residual ω * correction ω) μ) :
    Integrable
      (fun ω ↦ (residual ω - ε * correction ω) ^ 2) μ := by
  have hfun :
      (fun ω ↦ (residual ω - ε * correction ω) ^ 2) =
        fun ω ↦
          (residual ω) ^ 2 +
            (ε ^ 2 * (correction ω) ^ 2 -
              (2 * ε) * (residual ω * correction ω)) := by
    funext ω
    ring
  rw [hfun]
  exact
    hresidual.add
      ((henergy.const_mul (ε ^ 2)).sub
        (hgain.const_mul (2 * ε)))






theorem d004285
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ε : ℝ)
    (residual correction : Ω → ℝ)
    (henergy : Integrable (fun ω ↦ (correction ω) ^ 2) μ)
    (hgain : Integrable (fun ω ↦ residual ω * correction ω) μ) :
    _root_.GD.N0237.N0746.d004282 μ ε residual correction =
      ε ^ 2 * _root_.GD.N0237.N0746.d004281 μ correction -
        2 * ε * _root_.GD.N0237.N0746.d004280 μ residual correction := by
  have henergyScaled :
      Integrable (fun ω ↦ ε ^ 2 * (correction ω) ^ 2) μ :=
    henergy.const_mul (ε ^ 2)
  have hgainScaled :
      Integrable
        (fun ω ↦ (2 * ε) * (residual ω * correction ω)) μ :=
    hgain.const_mul (2 * ε)
  have hfun :
      _root_.GD.N0237.N0747.d004276 ε residual correction =
        fun ω ↦
          ε ^ 2 * (correction ω) ^ 2 -
            (2 * ε) * (residual ω * correction ω) := by
    funext ω
    exact _root_.GD.N0237.N0747.d004277 ε residual correction ω
  rw [_root_.GD.N0237.N0746.d004282, hfun,
    integral_sub henergyScaled hgainScaled]
  simp only [integral_const_mul, _root_.GD.N0237.N0746.d004281, _root_.GD.N0237.N0746.d004280]





theorem d004286
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ε : ℝ)
    (residual correction : Ω → ℝ)
    (hresidual :
      Integrable (fun ω ↦ (residual ω) ^ 2) μ)
    (henergy : Integrable (fun ω ↦ (correction ω) ^ 2) μ)
    (hgain : Integrable (fun ω ↦ residual ω * correction ω) μ) :
    (∫ ω, (residual ω - ε * correction ω) ^ 2 ∂μ) -
        ∫ ω, (residual ω) ^ 2 ∂μ =
      ε ^ 2 * _root_.GD.N0237.N0746.d004281 μ correction -
        2 * ε * _root_.GD.N0237.N0746.d004280 μ residual correction := by
  rw [← integral_sub
    (_root_.GD.N0237.N0746.d004284
      μ ε residual correction hresidual henergy hgain)
    hresidual]
  exact _root_.GD.N0237.N0746.d004285 μ ε residual correction henergy hgain





theorem d004287
    {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : ι → Measure Ω)
    (residual correction : ι → Ω → ℝ)
    (δ M ε : ℝ)
    (henergyIntegrable :
      ∀ i, Integrable (fun ω ↦ (correction i ω) ^ 2) (μ i))
    (hgainIntegrable :
      ∀ i,
        Integrable
          (fun ω ↦ residual i ω * correction i ω) (μ i))
    (hε : 0 < ε)
    (hgain :
      ∀ i, δ ≤ _root_.GD.N0237.N0746.d004280 (μ i) (residual i) (correction i))
    (henergy :
      ∀ i, _root_.GD.N0237.N0746.d004281 (μ i) (correction i) ≤ M)
    (hstep : ε * M < 2 * δ) :
    ∀ i,
      _root_.GD.N0237.N0746.d004282
        (μ i) ε (residual i) (correction i) < 0 := by
  intro i
  rw [_root_.GD.N0237.N0746.d004285
    (μ i) ε (residual i) (correction i)
    (henergyIntegrable i) (hgainIntegrable i)]
  exact
    _root_.GD.N0229.N0552.d000025
      ε
      (_root_.GD.N0237.N0746.d004281 (μ i) (correction i))
      (_root_.GD.N0237.N0746.d004280 (μ i) (residual i) (correction i))
      δ M hε (hgain i) (henergy i) hstep





theorem d004288
    {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : ι → Measure Ω)
    (residual correction : ι → Ω → ℝ)
    (δ M ε : ℝ)
    (hresidual :
      ∀ i, Integrable (fun ω ↦ (residual i ω) ^ 2) (μ i))
    (henergyIntegrable :
      ∀ i, Integrable (fun ω ↦ (correction i ω) ^ 2) (μ i))
    (hgainIntegrable :
      ∀ i,
        Integrable
          (fun ω ↦ residual i ω * correction i ω) (μ i))
    (hε : 0 < ε)
    (hgain :
      ∀ i, δ ≤ _root_.GD.N0237.N0746.d004280 (μ i) (residual i) (correction i))
    (henergy :
      ∀ i, _root_.GD.N0237.N0746.d004281 (μ i) (correction i) ≤ M)
    (hstep : ε * M < 2 * δ) :
    ∀ i,
      (∫ ω,
          (residual i ω - ε * correction i ω) ^ 2 ∂μ i) <
        ∫ ω, (residual i ω) ^ 2 ∂μ i := by
  intro i
  have hrisk :
      (∫ ω,
          (residual i ω - ε * correction i ω) ^ 2 ∂μ i) -
          ∫ ω, (residual i ω) ^ 2 ∂μ i =
        _root_.GD.N0237.N0746.d004282
          (μ i) ε (residual i) (correction i) := by
    rw [_root_.GD.N0237.N0746.d004282, ← integral_sub
      (_root_.GD.N0237.N0746.d004284
        (μ i) ε (residual i) (correction i)
        (hresidual i) (henergyIntegrable i) (hgainIntegrable i))
      (hresidual i)]
    rfl
  have hnegative :
      _root_.GD.N0237.N0746.d004282
        (μ i) ε (residual i) (correction i) < 0 :=
    _root_.GD.N0237.N0746.d004287
      μ residual correction δ M ε
      henergyIntegrable hgainIntegrable hε hgain henergy hstep i
  linarith

end N0746
end N0237
end GD
