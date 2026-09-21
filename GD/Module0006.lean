



























import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

namespace GD
namespace N0230
namespace N0564

open MeasureTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {Θ : Type*} [MeasurableSpace Θ]


noncomputable def d000051 (base : Measure Ω) (p : Θ → Ω → ℝ≥0) (θ : Θ) : Measure Ω :=
  base.withDensity fun ω => (p θ ω : ℝ≥0∞)


noncomputable def d000052 (base : Measure Ω) (p : Θ → Ω → ℝ≥0) (t : Θ → ℝ)
    (θ : Θ) (d : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal ((d ω - t θ) ^ 2) ∂(_root_.GD.N0230.N0564.d000051 base p θ)


theorem d000053 (a b : ℝ) : |a * b| ≤ a ^ 2 + b ^ 2 := by
  rcases abs_cases (a * b) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

variable {base : Measure Ω} {π : Measure Θ} {p : Θ → Ω → ℝ≥0} {t : Θ → ℝ} {s e : Ω → ℝ}


theorem d000054 (hp : Measurable (Function.uncurry p)) {d : Ω → ℝ}
    (hd : Measurable d) (θ : Θ) :
    _root_.GD.N0230.N0564.d000052 base p t θ d
      = ∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((d ω - t θ) ^ 2) ∂base := by
  have hpθ : Measurable fun ω => (p θ ω : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp (hp.comp measurable_prodMk_left)
  have hg : Measurable fun ω => ENNReal.ofReal ((d ω - t θ) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((hd.sub measurable_const).pow_const 2)
  rw [_root_.GD.N0230.N0564.d000052, _root_.GD.N0230.N0564.d000051, lintegral_withDensity_eq_lintegral_mul base hpθ hg]
  rfl

section Slice

variable {w : Ω → ℝ≥0} {c : ℝ}




theorem d000055 (hw : Measurable w) (hs : Measurable s) (he : Measurable e) (c : ℝ)
    (hfin : (∫⁻ ω, (w ω : ℝ≥0∞) * ENNReal.ofReal ((s ω - c) ^ 2) ∂base) ≠ ∞)
    (hdom : (∫⁻ ω, (w ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - c) ^ 2) ∂base)
        ≤ ∫⁻ ω, (w ω : ℝ≥0∞) * ENNReal.ofReal ((s ω - c) ^ 2) ∂base) :
    (∫⁻ ω, (w ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base).toReal
        ≤ (-2) * ∫ ω, (e ω - s ω) * ((s ω - c) * (w ω : ℝ)) ∂base
      ∧ |∫ ω, (e ω - s ω) * ((s ω - c) * (w ω : ℝ)) ∂base|
        ≤ (∫⁻ ω, (w ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base).toReal
          + (∫⁻ ω, (w ω : ℝ≥0∞) * ENNReal.ofReal ((s ω - c) ^ 2) ∂base).toReal := by
  have hWr : Measurable fun ω => (w ω : ℝ) := measurable_coe_nnreal_real.comp hw
  have hconv : ∀ f : Ω → ℝ, (∫⁻ ω, (w ω : ℝ≥0∞) * ENNReal.ofReal (f ω ^ 2) ∂base)
      = ∫⁻ ω, ENNReal.ofReal (f ω ^ 2 * (w ω : ℝ)) ∂base := by
    intro f; refine lintegral_congr fun ω => ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal, mul_comm]

  have hEq_s : ∫ ω, (s ω - c) ^ 2 * (w ω : ℝ) ∂base
      = (∫⁻ ω, (w ω : ℝ≥0∞) * ENNReal.ofReal ((s ω - c) ^ 2) ∂base).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => by positivity)
      (((hs.sub measurable_const).pow_const 2).mul hWr).aestronglyMeasurable, hconv]
  have hEq_e : ∫ ω, (e ω - c) ^ 2 * (w ω : ℝ) ∂base
      = (∫⁻ ω, (w ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - c) ^ 2) ∂base).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => by positivity)
      (((he.sub measurable_const).pow_const 2).mul hWr).aestronglyMeasurable, hconv]
  have hEq_d : ∫ ω, (e ω - s ω) ^ 2 * (w ω : ℝ) ∂base
      = (∫⁻ ω, (w ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => by positivity)
      (((he.sub hs).pow_const 2).mul hWr).aestronglyMeasurable, hconv]
  have hefin : (∫⁻ ω, (w ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - c) ^ 2) ∂base) ≠ ∞ :=
    (lt_of_le_of_lt hdom hfin.lt_top).ne

  have hIs : Integrable (fun ω => (s ω - c) ^ 2 * (w ω : ℝ)) base := by
    refine ⟨(((hs.sub measurable_const).pow_const 2).mul hWr).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => by positivity),
      ← hconv]
    exact hfin.lt_top
  have hIe : Integrable (fun ω => (e ω - c) ^ 2 * (w ω : ℝ)) base := by
    refine ⟨(((he.sub measurable_const).pow_const 2).mul hWr).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => by positivity),
      ← hconv]
    exact hefin.lt_top
  have hIes : Integrable (fun ω => (e ω - s ω) ^ 2 * (w ω : ℝ)) base := by
    refine Integrable.mono' ((hIe.const_mul 2).add (hIs.const_mul 2))
      (((he.sub hs).pow_const 2).mul hWr).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : (e ω - s ω) ^ 2 ≤ 2 * (e ω - c) ^ 2 + 2 * (s ω - c) ^ 2 := by
      nlinarith [sq_nonneg ((e ω - c) + (s ω - c))]
    calc (e ω - s ω) ^ 2 * (w ω : ℝ)
        ≤ (2 * (e ω - c) ^ 2 + 2 * (s ω - c) ^ 2) * (w ω : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (w ω).coe_nonneg
      _ = 2 * ((e ω - c) ^ 2 * (w ω : ℝ)) + 2 * ((s ω - c) ^ 2 * (w ω : ℝ)) := by ring
  have hIx : Integrable (fun ω => (e ω - s ω) * ((s ω - c) * (w ω : ℝ))) base := by
    refine Integrable.mono' (hIes.add hIs)
      (((he.sub hs).mul ((hs.sub measurable_const).mul hWr)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs,
      show (e ω - s ω) * ((s ω - c) * (w ω : ℝ)) = ((e ω - s ω) * (s ω - c)) * (w ω : ℝ) from
        by ring,
      abs_mul, abs_of_nonneg (w ω).coe_nonneg]
    calc |(e ω - s ω) * (s ω - c)| * (w ω : ℝ)
        ≤ ((e ω - s ω) ^ 2 + (s ω - c) ^ 2) * (w ω : ℝ) :=
          mul_le_mul_of_nonneg_right (_root_.GD.N0230.N0564.d000053 _ _) (w ω).coe_nonneg
      _ = (e ω - s ω) ^ 2 * (w ω : ℝ) + (s ω - c) ^ 2 * (w ω : ℝ) := by ring

  have hdomR : ∫ ω, (e ω - c) ^ 2 * (w ω : ℝ) ∂base
      ≤ ∫ ω, (s ω - c) ^ 2 * (w ω : ℝ) ∂base := by
    rw [hEq_e, hEq_s]
    exact ENNReal.toReal_le_toReal hefin hfin |>.mpr hdom

  have hptid : (fun ω => (e ω - c) ^ 2 * (w ω : ℝ))
      = fun ω => (e ω - s ω) ^ 2 * (w ω : ℝ)
          + (2 * ((e ω - s ω) * ((s ω - c) * (w ω : ℝ)))
            + (s ω - c) ^ 2 * (w ω : ℝ)) := by
    funext ω; ring
  have hsplit : ∫ ω, (e ω - c) ^ 2 * (w ω : ℝ) ∂base
      = ∫ ω, (e ω - s ω) ^ 2 * (w ω : ℝ) ∂base
        + (2 * ∫ ω, (e ω - s ω) * ((s ω - c) * (w ω : ℝ)) ∂base
          + ∫ ω, (s ω - c) ^ 2 * (w ω : ℝ) ∂base) := by
    have hadd1 : ∫ ω, ((e ω - s ω) ^ 2 * (w ω : ℝ)
        + (2 * ((e ω - s ω) * ((s ω - c) * (w ω : ℝ))) + (s ω - c) ^ 2 * (w ω : ℝ))) ∂base
        = ∫ ω, (e ω - s ω) ^ 2 * (w ω : ℝ) ∂base
          + ∫ ω, (2 * ((e ω - s ω) * ((s ω - c) * (w ω : ℝ)))
            + (s ω - c) ^ 2 * (w ω : ℝ)) ∂base :=
      integral_add hIes ((hIx.const_mul 2).add hIs)
    have hadd2 : ∫ ω, (2 * ((e ω - s ω) * ((s ω - c) * (w ω : ℝ)))
        + (s ω - c) ^ 2 * (w ω : ℝ)) ∂base
        = ∫ ω, 2 * ((e ω - s ω) * ((s ω - c) * (w ω : ℝ))) ∂base
          + ∫ ω, (s ω - c) ^ 2 * (w ω : ℝ) ∂base :=
      integral_add (hIx.const_mul 2) hIs
    have hmul2 : ∫ ω, 2 * ((e ω - s ω) * ((s ω - c) * (w ω : ℝ))) ∂base
        = 2 * ∫ ω, (e ω - s ω) * ((s ω - c) * (w ω : ℝ)) ∂base :=
      integral_const_mul _ _
    rw [hptid, hadd1, hadd2, hmul2]
  have hcore : ∫ ω, (e ω - s ω) ^ 2 * (w ω : ℝ) ∂base
      ≤ (-2) * ∫ ω, (e ω - s ω) * ((s ω - c) * (w ω : ℝ)) ∂base := by
    have := hdomR; rw [hsplit] at this; linarith
  constructor
  · rw [← hEq_d]; exact hcore
  · have habs : |∫ ω, (e ω - s ω) * ((s ω - c) * (w ω : ℝ)) ∂base|
        ≤ ∫ ω, (e ω - s ω) ^ 2 * (w ω : ℝ) ∂base
          + ∫ ω, (s ω - c) ^ 2 * (w ω : ℝ) ∂base := by
      calc |∫ ω, (e ω - s ω) * ((s ω - c) * (w ω : ℝ)) ∂base|
          ≤ ∫ ω, |(e ω - s ω) * ((s ω - c) * (w ω : ℝ))| ∂base := by
            simpa [Real.norm_eq_abs] using
              norm_integral_le_integral_norm (fun ω => (e ω - s ω) * ((s ω - c) * (w ω : ℝ)))
              (μ := base)
        _ ≤ ∫ ω, ((e ω - s ω) ^ 2 * (w ω : ℝ) + (s ω - c) ^ 2 * (w ω : ℝ)) ∂base := by
            refine integral_mono hIx.abs (hIes.add hIs)
              (fun ω => ?_)
            rw [show (e ω - s ω) * ((s ω - c) * (w ω : ℝ))
                = ((e ω - s ω) * (s ω - c)) * (w ω : ℝ) from by ring,
              abs_mul, abs_of_nonneg (w ω).coe_nonneg]
            calc |(e ω - s ω) * (s ω - c)| * (w ω : ℝ)
                ≤ ((e ω - s ω) ^ 2 + (s ω - c) ^ 2) * (w ω : ℝ) :=
                  mul_le_mul_of_nonneg_right (_root_.GD.N0230.N0564.d000053 _ _) (w ω).coe_nonneg
              _ = (e ω - s ω) ^ 2 * (w ω : ℝ) + (s ω - c) ^ 2 * (w ω : ℝ) := by ring
        _ = ∫ ω, (e ω - s ω) ^ 2 * (w ω : ℝ) ∂base
              + ∫ ω, (s ω - c) ^ 2 * (w ω : ℝ) ∂base := integral_add hIes hIs
    rw [← hEq_d, ← hEq_s]; exact habs

end Slice




theorem d000056
    [SFinite base] [SFinite π]
    (hp : Measurable (Function.uncurry p)) (ht : Measurable t)
    (hs : Measurable s) (he : Measurable e)
    (hbal : ∀ᵐ ω ∂base, ∫ θ, (s ω - t θ) * (p θ ω : ℝ) ∂π = 0)
    (hfin : ∫⁻ θ, _root_.GD.N0230.N0564.d000052 base p t θ s ∂π ≠ ∞)
    (hpos : ∀ᵐ ω ∂base, 0 < ∫⁻ θ, (p θ ω : ℝ≥0∞) ∂π)
    (hdom : ∀ θ, _root_.GD.N0230.N0564.d000052 base p t θ e ≤ _root_.GD.N0230.N0564.d000052 base p t θ s) :
    e =ᵐ[base] s := by

  have hpE : Measurable fun q : Θ × Ω => (p q.1 q.2 : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp hp
  have hpR : Measurable fun q : Θ × Ω => (p q.1 q.2 : ℝ) :=
    measurable_coe_nnreal_real.comp hp
  have hSb_joint : Measurable fun q : Θ × Ω =>
      (p q.1 q.2 : ℝ≥0∞) * ENNReal.ofReal ((s q.2 - t q.1) ^ 2) :=
    hpE.mul (ENNReal.measurable_ofReal.comp
      (((hs.comp measurable_snd).sub (ht.comp measurable_fst)).pow_const 2))
  have hAe_joint : Measurable fun q : Θ × Ω =>
      (p q.1 q.2 : ℝ≥0∞) * ENNReal.ofReal ((e q.2 - s q.2) ^ 2) :=
    hpE.mul (ENNReal.measurable_ofReal.comp
      (((he.comp measurable_snd).sub (hs.comp measurable_snd)).pow_const 2))
  have hG_joint : Measurable fun q : Θ × Ω =>
      (e q.2 - s q.2) * ((s q.2 - t q.1) * (p q.1 q.2 : ℝ)) :=
    ((he.comp measurable_snd).sub (hs.comp measurable_snd)).mul
      (((hs.comp measurable_snd).sub (ht.comp measurable_fst)).mul hpR)

  have hSb : ∀ θ, _root_.GD.N0230.N0564.d000052 base p t θ s
      = ∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((s ω - t θ) ^ 2) ∂base :=
    _root_.GD.N0230.N0564.d000054 hp hs
  have hEb : ∀ θ, _root_.GD.N0230.N0564.d000052 base p t θ e
      = ∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - t θ) ^ 2) ∂base :=
    _root_.GD.N0230.N0564.d000054 hp he
  have hmS : Measurable fun θ => _root_.GD.N0230.N0564.d000052 base p t θ s := by
    simp only [hSb]; exact hSb_joint.lintegral_prod_right'
  have hae_fin : ∀ᵐ θ ∂π, _root_.GD.N0230.N0564.d000052 base p t θ s < ∞ := ae_lt_top' hmS.aemeasurable hfin

  have hslice : ∀ᵐ θ ∂π,
      (∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base).toReal
          ≤ (-2) * ∫ ω, (e ω - s ω) * ((s ω - t θ) * (p θ ω : ℝ)) ∂base
        ∧ |∫ ω, (e ω - s ω) * ((s ω - t θ) * (p θ ω : ℝ)) ∂base|
          ≤ (∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base).toReal
            + (∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((s ω - t θ) ^ 2) ∂base).toReal := by
    refine hae_fin.mono fun θ hθ => ?_
    have hwθ : Measurable fun ω => p θ ω := hp.comp measurable_prodMk_left
    have hfinθ : (∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((s ω - t θ) ^ 2) ∂base) ≠ ∞ := by
      rw [← hSb θ]; exact hθ.ne
    have hdomθ : (∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - t θ) ^ 2) ∂base)
        ≤ ∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((s ω - t θ) ^ 2) ∂base := by
      rw [← hSb θ, ← hEb θ]; exact hdom θ
    exact _root_.GD.N0230.N0564.d000055 hwθ hs he (t θ) hfinθ hdomθ

  have hmAe : Measurable fun θ =>
      ∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base :=
    hAe_joint.lintegral_prod_right'
  have hAe_le : ∀ θ, (∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base)
      ≤ 4 * _root_.GD.N0230.N0564.d000052 base p t θ s := by
    intro θ
    have hpt : ∀ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - s ω) ^ 2)
        ≤ 2 * ((p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - t θ) ^ 2))
          + 2 * ((p θ ω : ℝ≥0∞) * ENNReal.ofReal ((s ω - t θ) ^ 2)) := by
      intro ω
      have h1 : ENNReal.ofReal ((e ω - s ω) ^ 2)
          ≤ 2 * ENNReal.ofReal ((e ω - t θ) ^ 2) + 2 * ENNReal.ofReal ((s ω - t θ) ^ 2) := by
        calc ENNReal.ofReal ((e ω - s ω) ^ 2)
            ≤ ENNReal.ofReal (2 * (e ω - t θ) ^ 2 + 2 * (s ω - t θ) ^ 2) :=
              ENNReal.ofReal_le_ofReal
                (by nlinarith [sq_nonneg ((e ω - t θ) + (s ω - t θ))])
          _ = 2 * ENNReal.ofReal ((e ω - t θ) ^ 2) + 2 * ENNReal.ofReal ((s ω - t θ) ^ 2) := by
              rw [ENNReal.ofReal_add (by positivity) (by positivity),
                ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num),
                ENNReal.ofReal_ofNat]
      calc (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - s ω) ^ 2)
          ≤ (p θ ω : ℝ≥0∞) * (2 * ENNReal.ofReal ((e ω - t θ) ^ 2)
              + 2 * ENNReal.ofReal ((s ω - t θ) ^ 2)) := mul_le_mul_left' h1 _
        _ = 2 * ((p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - t θ) ^ 2))
              + 2 * ((p θ ω : ℝ≥0∞) * ENNReal.ofReal ((s ω - t θ) ^ 2)) := by ring
    have hpθE : Measurable fun ω => (p θ ω : ℝ≥0∞) :=
      measurable_coe_nnreal_ennreal.comp (hp.comp measurable_prodMk_left)
    have hme : Measurable fun ω =>
        (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - t θ) ^ 2) :=
      hpθE.mul (ENNReal.measurable_ofReal.comp ((he.sub measurable_const).pow_const 2))
    have hms : Measurable fun ω =>
        (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((s ω - t θ) ^ 2) :=
      hpθE.mul (ENNReal.measurable_ofReal.comp ((hs.sub measurable_const).pow_const 2))
    calc (∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base)
        ≤ ∫⁻ ω, 2 * ((p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - t θ) ^ 2))
            + 2 * ((p θ ω : ℝ≥0∞) * ENNReal.ofReal ((s ω - t θ) ^ 2)) ∂base :=
          lintegral_mono hpt
      _ = 2 * (∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - t θ) ^ 2) ∂base)
            + 2 * ∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((s ω - t θ) ^ 2) ∂base := by
          rw [lintegral_add_left (hme.const_mul 2), lintegral_const_mul 2 hme,
            lintegral_const_mul 2 hms]
      _ ≤ 2 * _root_.GD.N0230.N0564.d000052 base p t θ s + 2 * _root_.GD.N0230.N0564.d000052 base p t θ s := by
          rw [← hSb θ, ← hEb θ]
          exact add_le_add (mul_le_mul_left' (hdom θ) 2) le_rfl
      _ = 4 * _root_.GD.N0230.N0564.d000052 base p t θ s := by ring
  have hAefin : (∫⁻ θ, (∫⁻ ω, (p θ ω : ℝ≥0∞)
      * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base) ∂π) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hAe_le)
    rw [lintegral_const_mul 4 hmS]
    exact ENNReal.mul_ne_top (by norm_num) hfin
  have hInt_Ae : Integrable (fun θ =>
      (∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base).toReal) π :=
    integrable_toReal_of_lintegral_ne_top hmAe.aemeasurable hAefin
  have hInt_S : Integrable (fun θ => (_root_.GD.N0230.N0564.d000052 base p t θ s).toReal) π :=
    integrable_toReal_of_lintegral_ne_top hmS.aemeasurable hfin
  have hSM_B : AEStronglyMeasurable
      (fun θ => ∫ ω, (e ω - s ω) * ((s ω - t θ) * (p θ ω : ℝ)) ∂base) π :=
    (hG_joint.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
  have hInt_B : Integrable
      (fun θ => ∫ ω, (e ω - s ω) * ((s ω - t θ) * (p θ ω : ℝ)) ∂base) π := by
    refine Integrable.mono' (hInt_Ae.add hInt_S) hSM_B ?_
    refine hslice.mono fun θ hθ => ?_
    rw [Real.norm_eq_abs]
    calc |∫ ω, (e ω - s ω) * ((s ω - t θ) * (p θ ω : ℝ)) ∂base|
        ≤ (∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base).toReal
            + (∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((s ω - t θ) ^ 2) ∂base).toReal :=
          hθ.2
      _ = (∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base).toReal
            + (_root_.GD.N0230.N0564.d000052 base p t θ s).toReal := by rw [← hSb θ]

  have hIneq : ∫ θ, (∫⁻ ω, (p θ ω : ℝ≥0∞)
        * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base).toReal ∂π
      ≤ ∫ θ, (-2) * ∫ ω, (e ω - s ω) * ((s ω - t θ) * (p θ ω : ℝ)) ∂base ∂π :=
    integral_mono_ae hInt_Ae (hInt_B.const_mul (-2)) (hslice.mono fun θ hθ => hθ.1)

  have hG_int : Integrable
      (Function.uncurry fun θ ω => (e ω - s ω) * ((s ω - t θ) * (p θ ω : ℝ)))
      (π.prod base) := by
    refine ⟨hG_joint.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have hb : (∫⁻ q, ENNReal.ofReal
        ‖(e q.2 - s q.2) * ((s q.2 - t q.1) * (p q.1 q.2 : ℝ))‖ ∂π.prod base)
        = ∫⁻ θ, ∫⁻ ω, ENNReal.ofReal
            ‖(e ω - s ω) * ((s ω - t θ) * (p θ ω : ℝ))‖ ∂base ∂π :=
      lintegral_prod _ (ENNReal.measurable_ofReal.comp hG_joint.norm).aemeasurable
    show (∫⁻ a : Θ × Ω, ENNReal.ofReal
        ‖(e a.2 - s a.2) * ((s a.2 - t a.1) * (p a.1 a.2 : ℝ))‖ ∂π.prod base) < ∞
    rw [hb]
    have hptw : ∀ θ ω, ENNReal.ofReal ‖(e ω - s ω) * ((s ω - t θ) * (p θ ω : ℝ))‖
        ≤ (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - s ω) ^ 2)
          + (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((s ω - t θ) ^ 2) := by
      intro θ ω
      calc ENNReal.ofReal ‖(e ω - s ω) * ((s ω - t θ) * (p θ ω : ℝ))‖
          ≤ ENNReal.ofReal (((e ω - s ω) ^ 2 + (s ω - t θ) ^ 2) * (p θ ω : ℝ)) := by
            apply ENNReal.ofReal_le_ofReal
            rw [Real.norm_eq_abs,
              show (e ω - s ω) * ((s ω - t θ) * (p θ ω : ℝ))
                = ((e ω - s ω) * (s ω - t θ)) * (p θ ω : ℝ) from by ring,
              abs_mul, abs_of_nonneg (p θ ω).coe_nonneg]
            exact mul_le_mul_of_nonneg_right (_root_.GD.N0230.N0564.d000053 _ _) (p θ ω).coe_nonneg
        _ = (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - s ω) ^ 2)
              + (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((s ω - t θ) ^ 2) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal,
              ENNReal.ofReal_add (by positivity) (by positivity)]
            ring
    calc (∫⁻ θ, ∫⁻ ω, ENNReal.ofReal
          ‖(e ω - s ω) * ((s ω - t θ) * (p θ ω : ℝ))‖ ∂base ∂π)
        ≤ ∫⁻ θ, (∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base)
            + ∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((s ω - t θ) ^ 2) ∂base ∂π := by
          refine lintegral_mono fun θ => ?_
          have hpθE : Measurable fun ω => (p θ ω : ℝ≥0∞) :=
            measurable_coe_nnreal_ennreal.comp (hp.comp measurable_prodMk_left)
          have h1 : Measurable fun ω =>
              (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - s ω) ^ 2) :=
            hpθE.mul (ENNReal.measurable_ofReal.comp (((he.sub hs)).pow_const 2))
          calc (∫⁻ ω, ENNReal.ofReal
                ‖(e ω - s ω) * ((s ω - t θ) * (p θ ω : ℝ))‖ ∂base)
              ≤ ∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - s ω) ^ 2)
                  + (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((s ω - t θ) ^ 2) ∂base :=
                lintegral_mono (hptw θ)
            _ = (∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base)
                  + ∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((s ω - t θ) ^ 2) ∂base :=
                lintegral_add_left h1 _
      _ = (∫⁻ θ, (∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base) ∂π)
            + ∫⁻ θ, (∫⁻ ω, (p θ ω : ℝ≥0∞) * ENNReal.ofReal ((s ω - t θ) ^ 2) ∂base) ∂π :=
          lintegral_add_left hmAe _
      _ < ∞ := by
          have h2 : (∫⁻ θ, (∫⁻ ω, (p θ ω : ℝ≥0∞)
              * ENNReal.ofReal ((s ω - t θ) ^ 2) ∂base) ∂π) ≠ ∞ := by
            have : (fun θ => ∫⁻ ω, (p θ ω : ℝ≥0∞)
                * ENNReal.ofReal ((s ω - t θ) ^ 2) ∂base)
                = fun θ => _root_.GD.N0230.N0564.d000052 base p t θ s := by
              funext θ; rw [hSb θ]
            rw [this]; exact hfin
          exact ENNReal.add_lt_top.mpr ⟨hAefin.lt_top, h2.lt_top⟩
  have hswap : ∫ θ, ∫ ω, (e ω - s ω) * ((s ω - t θ) * (p θ ω : ℝ)) ∂base ∂π = 0 := by
    rw [integral_integral_swap hG_int]
    have hzero : ∀ᵐ ω ∂base,
        ∫ θ, (e ω - s ω) * ((s ω - t θ) * (p θ ω : ℝ)) ∂π = 0 := by
      refine hbal.mono fun ω hω => ?_
      rw [integral_const_mul, hω, mul_zero]
    calc ∫ ω, ∫ θ, (e ω - s ω) * ((s ω - t θ) * (p θ ω : ℝ)) ∂π ∂base
        = ∫ ω, (0 : ℝ) ∂base := integral_congr_ae hzero
      _ = 0 := integral_zero _ _

  have hAzero : ∫ θ, (∫⁻ ω, (p θ ω : ℝ≥0∞)
      * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base).toReal ∂π = 0 := by
    have hle : ∫ θ, (∫⁻ ω, (p θ ω : ℝ≥0∞)
        * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base).toReal ∂π ≤ 0 := by
      calc ∫ θ, (∫⁻ ω, (p θ ω : ℝ≥0∞)
            * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base).toReal ∂π
          ≤ ∫ θ, (-2) * ∫ ω, (e ω - s ω) * ((s ω - t θ) * (p θ ω : ℝ)) ∂base ∂π := hIneq
        _ = (-2) * ∫ θ, ∫ ω, (e ω - s ω) * ((s ω - t θ) * (p θ ω : ℝ)) ∂base ∂π :=
            integral_const_mul _ _
        _ = 0 := by rw [hswap, mul_zero]
    have hge : 0 ≤ ∫ θ, (∫⁻ ω, (p θ ω : ℝ≥0∞)
        * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base).toReal ∂π :=
      integral_nonneg fun θ => ENNReal.toReal_nonneg
    linarith
  have hAe0 : ∀ᵐ θ ∂π, (∫⁻ ω, (p θ ω : ℝ≥0∞)
      * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base) = 0 := by
    have h0 : (fun θ => (∫⁻ ω, (p θ ω : ℝ≥0∞)
        * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base).toReal) =ᵐ[π] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall fun θ => ENNReal.toReal_nonneg) hInt_Ae).mp hAzero
    have hfinAe : ∀ᵐ θ ∂π, (∫⁻ ω, (p θ ω : ℝ≥0∞)
        * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base) < ∞ := by
      refine hae_fin.mono fun θ hθ => lt_of_le_of_lt (hAe_le θ) ?_
      exact ENNReal.mul_lt_top (by norm_num) hθ
    filter_upwards [h0, hfinAe] with θ h1 h2
    have h3 := ENNReal.toReal_eq_zero_iff _ |>.mp h1
    rcases h3 with h3 | h3
    · exact h3
    · exact absurd h3 h2.ne

  have hAlint : ∫⁻ θ, (∫⁻ ω, (p θ ω : ℝ≥0∞)
      * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base) ∂π = 0 := by
    rw [lintegral_congr_ae hAe0]; simp
  have hswap2 : ∫⁻ θ, (∫⁻ ω, (p θ ω : ℝ≥0∞)
        * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base) ∂π
      = ∫⁻ ω, (∫⁻ θ, (p θ ω : ℝ≥0∞) ∂π) * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base := by
    rw [lintegral_lintegral_swap hAe_joint.aemeasurable]
    refine lintegral_congr fun ω => ?_
    exact lintegral_mul_const'' _ ((hp.comp measurable_prodMk_right).coe_nnreal_ennreal.aemeasurable)
  have hzero_base : ∀ᵐ ω ∂base,
      (∫⁻ θ, (p θ ω : ℝ≥0∞) ∂π) * ENNReal.ofReal ((e ω - s ω) ^ 2) = 0 := by
    have hmW : Measurable fun ω => ∫⁻ θ, (p θ ω : ℝ≥0∞) ∂π :=
      Measurable.lintegral_prod_left' hpE
    have hm : Measurable fun ω =>
        (∫⁻ θ, (p θ ω : ℝ≥0∞) ∂π) * ENNReal.ofReal ((e ω - s ω) ^ 2) :=
      hmW.mul (ENNReal.measurable_ofReal.comp ((he.sub hs).pow_const 2))
    have hL0 : ∫⁻ ω, (∫⁻ θ, (p θ ω : ℝ≥0∞) ∂π)
        * ENNReal.ofReal ((e ω - s ω) ^ 2) ∂base = 0 := by
      rw [← hswap2]; exact hAlint
    have h0 := (lintegral_eq_zero_iff hm).mp hL0
    filter_upwards [h0] with ω hω
    simpa using hω
  filter_upwards [hzero_base, hpos] with ω h1 h2
  rcases mul_eq_zero.mp h1 with h3 | h3
  · exact absurd h3 h2.ne'
  · have h4 : (e ω - s ω) ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.mp h3
    have h5 : (e ω - s ω) ^ 2 = 0 := le_antisymm h4 (sq_nonneg _)
    have h6 : e ω - s ω = 0 := by
      have := sq_eq_zero_iff.mp h5
      exact this
    linarith [h6]


theorem d000057
    [SFinite base] [SFinite π]
    (hp : Measurable (Function.uncurry p)) (ht : Measurable t)
    (hs : Measurable s) (he : Measurable e)
    (hbal : ∀ᵐ ω ∂base, ∫ θ, (s ω - t θ) * (p θ ω : ℝ) ∂π = 0)
    (hfin : ∫⁻ θ, _root_.GD.N0230.N0564.d000052 base p t θ s ∂π ≠ ∞)
    (hpos : ∀ᵐ ω ∂base, 0 < ∫⁻ θ, (p θ ω : ℝ≥0∞) ∂π)
    (hdom : ∀ θ, _root_.GD.N0230.N0564.d000052 base p t θ e ≤ _root_.GD.N0230.N0564.d000052 base p t θ s) (θ : Θ) :
    e =ᵐ[_root_.GD.N0230.N0564.d000051 base p θ] s :=
  (_root_.GD.N0230.N0564.d000056 hp ht hs he hbal hfin hpos hdom).filter_mono
    (withDensity_absolutelyContinuous base _).ae_le






theorem d000058
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [SFinite ν] (R : ℝ × S → ℝ≥0∞)
    (hR : Measurable R)
    (hinv : ∀ c μpar x, R (μpar + c, x) = R (μpar, x))
    (hpos : ν {x | 0 < R (0, x)} ≠ 0) :
    ∫⁻ q, R q ∂((volume : Measure ℝ).prod ν) = ∞ := by
  have hconst : ∀ μpar x, R (μpar, x) = R (0, x) := by
    intro μpar x
    have := hinv μpar 0 x
    simpa using this
  have hinner : ∀ x : S, ∫⁻ μpar, R (μpar, x) ∂(volume : Measure ℝ) = R (0, x) * ∞ := by
    intro x
    calc ∫⁻ μpar, R (μpar, x) ∂(volume : Measure ℝ)
        = ∫⁻ _, R (0, x) ∂(volume : Measure ℝ) := lintegral_congr fun μpar => hconst μpar x
      _ = R (0, x) * volume Set.univ := lintegral_const _
      _ = R (0, x) * ∞ := by rw [Real.volume_univ]
  have hmes : MeasurableSet {x : S | 0 < R (0, x)} :=
    measurableSet_lt measurable_const (hR.comp measurable_prodMk_left)
  rw [lintegral_prod_symm _ hR.aemeasurable]
  refine top_unique ?_
  calc (⊤ : ℝ≥0∞) = ∞ * ν {x | 0 < R (0, x)} := (ENNReal.top_mul hpos).symm
    _ = ∫⁻ x in {x | 0 < R (0, x)}, ∞ ∂ν := (setLIntegral_const _ _).symm
    _ = ∫⁻ x in {x | 0 < R (0, x)}, R (0, x) * ∞ ∂ν := by
        refine (setLIntegral_congr_fun hmes fun x hx => ?_).symm
        exact ENNReal.mul_top (ne_of_gt hx)
    _ = ∫⁻ x in {x | 0 < R (0, x)}, ∫⁻ μpar, R (μpar, x) ∂(volume : Measure ℝ) ∂ν := by
        refine setLIntegral_congr_fun hmes fun x _ => (hinner x).symm
    _ ≤ ∫⁻ x, ∫⁻ μpar, R (μpar, x) ∂(volume : Measure ℝ) ∂ν :=
        setLIntegral_le_lintegral _ _



#print axioms _root_.GD.N0230.N0564.d000053
#print axioms _root_.GD.N0230.N0564.d000054
#print axioms _root_.GD.N0230.N0564.d000055
#print axioms _root_.GD.N0230.N0564.d000056
#print axioms _root_.GD.N0230.N0564.d000057
#print axioms _root_.GD.N0230.N0564.d000058

end N0564
end N0230
end GD
