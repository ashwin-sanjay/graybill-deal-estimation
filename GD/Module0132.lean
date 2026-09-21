import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.L2Space
import GD.Module0090
import GD.Module0131























open Filter MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace Topology

namespace GD
namespace N0230
namespace N0635

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}




theorem d001523
    (f : ℕ → α → ℝ) (z : α → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hf : ∀ j, AEStronglyMeasurable (f j) μ) (hz : MemLp z 2 μ)
    (hbound : ∀ j, eLpNorm (f j) 2 μ ≤ ENNReal.ofReal R) :
    UnifIntegrable (fun j x ↦ z x * f j x) 1 μ := by
  intro ε hε
  have hε' : 0 < ε / (R + 1) := by positivity
  obtain ⟨δ, hδ, hδ'⟩ :=
    hz.eLpNorm_indicator_le (p := 2) one_le_two ENNReal.ofNat_ne_top hε'
  refine ⟨δ, hδ, fun j s hs hμs ↦ ?_⟩
  have hind : s.indicator (fun x ↦ z x * f j x) = (s.indicator z) • (f j) := by
    funext x
    by_cases hx : x ∈ s <;> simp [Set.indicator, hx]
  rw [hind]
  calc eLpNorm ((s.indicator z) • f j) 1 μ
      ≤ eLpNorm (s.indicator z) 2 μ * eLpNorm (f j) 2 μ :=
        eLpNorm_smul_le_mul_eLpNorm (hf j) (hz.1.indicator hs)
    _ ≤ ENNReal.ofReal (ε / (R + 1)) * ENNReal.ofReal R :=
        mul_le_mul' (hδ' s hs hμs) (hbound j)
    _ = ENNReal.ofReal (ε / (R + 1) * R) :=
        (ENNReal.ofReal_mul hε'.le).symm
    _ ≤ ENNReal.ofReal ε := by
        apply ENNReal.ofReal_le_ofReal
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

variable [IsFiniteMeasure μ]




theorem d001524
    (f : ℕ → α → ℝ) (g z : α → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hf : ∀ j, AEStronglyMeasurable (f j) μ)
    (hg : MemLp g 2 μ) (hz : MemLp z 2 μ)
    (hbound : ∀ j, eLpNorm (f j) 2 μ ≤ ENNReal.ofReal R)
    (hmeas : TendstoInMeasure μ f atTop g) :
    Tendsto (fun j ↦ ∫ x, z x * f j x ∂μ) atTop
      (𝓝 (∫ x, z x * g x ∂μ)) := by
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨ms, -, hms⟩ :=
    TendstoInMeasure.exists_seq_tendsto_ae
      (fun ε hε ↦ (hmeas ε hε).comp hns)
  refine ⟨ms, ?_⟩
  have hzg : MemLp (fun x ↦ z x * g x) 1 μ := hg.mul' hz
  have hzf : ∀ k, MemLp (fun x ↦ z x * f (ns (ms k)) x) 1 μ := by
    intro k
    exact MemLp.mul' ⟨hf _, lt_of_le_of_lt (hbound _) ENNReal.ofReal_lt_top⟩ hz
  have hui : UnifIntegrable (fun k x ↦ z x * f (ns (ms k)) x) 1 μ := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ :=
      _root_.GD.N0230.N0635.d001523 f z R hR hf hz hbound hε
    exact ⟨δ, hδ, fun k s hs hμs ↦ hδ' (ns (ms k)) s hs hμs⟩
  have hae : ∀ᵐ x ∂μ, Tendsto (fun k ↦ z x * f (ns (ms k)) x) atTop
      (𝓝 (z x * g x)) := by
    filter_upwards [hms] with x hx
    exact tendsto_const_nhds.mul hx
  have hL1 := tendsto_Lp_finite_of_tendsto_ae (μ := μ) le_rfl ENNReal.one_ne_top
    (fun k ↦ (hzf k).1) hzg hui hae
  refine tendsto_integral_of_L1 (fun x ↦ z x * g x) hzg.1
    (Eventually.of_forall fun k ↦ memLp_one_iff_integrable.1 (hzf k)) ?_
  simpa only [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] using hL1




theorem d001525
    (u : ℕ → Lp ℝ 2 μ) (v : Lp ℝ 2 μ) (R : ℝ)
    (rep : ℕ → α → ℝ) (limRep : α → ℝ)
    (hrep : ∀ j, rep j =ᵐ[μ] u j) (hlim : limRep =ᵐ[μ] v)
    (hbound : ∀ j, ‖u j‖ ≤ R)
    (hmeas : TendstoInMeasure μ rep atTop limRep)
    (w : Lp ℝ 2 μ) :
    Tendsto (fun j ↦ ⟪w, u j⟫) atTop (𝓝 ⟪w, v⟫) := by
  have hR : 0 ≤ R := (norm_nonneg (u 0)).trans (hbound 0)
  have hmeas' : TendstoInMeasure μ (fun j x ↦ u j x) atTop (fun x ↦ v x) :=
    (hmeas.congr_left hrep).congr_right hlim
  have hbound' : ∀ j, eLpNorm (fun x ↦ u j x) 2 μ ≤ ENNReal.ofReal R := by
    intro j
    have h1 : eLpNorm (fun x ↦ u j x) 2 μ = ENNReal.ofReal ‖u j‖ := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (u j))]
    rw [h1]
    exact ENNReal.ofReal_le_ofReal (hbound j)
  have hpair := _root_.GD.N0230.N0635.d001524
    (fun j x ↦ u j x) (fun x ↦ v x) (fun x ↦ w x) R hR
    (fun j ↦ Lp.aestronglyMeasurable (u j)) (Lp.memLp v) (Lp.memLp w)
    hbound' hmeas'
  have hinner : ∀ y : Lp ℝ 2 μ, ⟪w, y⟫ = ∫ x, w x * y x ∂μ := by
    intro y
    simp [L2.inner_def, RCLike.inner_apply, mul_comm]
  simpa only [hinner] using hpair



theorem d001526
    (u : ℕ → Lp ℝ 2 μ) (v : Lp ℝ 2 μ) (R : ℝ)
    (rep : ℕ → α → ℝ) (limRep : α → ℝ)
    (hrep : ∀ j, rep j =ᵐ[μ] u j) (hlim : limRep =ᵐ[μ] v)
    (hbound : ∀ j, ‖u j‖ ≤ R)
    (hmeas : TendstoInMeasure μ rep atTop limRep) :
    _root_.GD.N0230.N0708.d001170 ℝ u atTop v := by
  apply _root_.GD.N0230.N0570.d001187
  intro z
  have := _root_.GD.N0230.N0635.d001525
    u v R rep limRep hrep hlim hbound hmeas z
  simpa only [real_inner_comm] using this




theorem d001527
    (u : ℕ → Lp ℝ 2 μ) (v : Lp ℝ 2 μ) (R : ℝ)
    (rep : ℕ → α → ℝ) (limRep : α → ℝ)
    (hrep : ∀ j, rep j =ᵐ[μ] u j) (hlim : limRep =ᵐ[μ] v)
    (hbound : ∀ j, ‖u j‖ ≤ R)
    (hmeas : TendstoInMeasure μ rep atTop limRep)
    (hnorm : Tendsto (fun j ↦ ‖u j‖) atTop (𝓝 ‖v‖)) :
    Tendsto u atTop (𝓝 v) := by
  apply _root_.GD.N0230.N0713.d001521 _ hnorm
  intro w
  exact _root_.GD.N0230.N0635.d001525
    u v R rep limRep hrep hlim hbound hmeas w

end

end N0635
end N0230
end GD
