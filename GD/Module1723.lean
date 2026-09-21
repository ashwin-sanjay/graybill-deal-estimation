import GD.Module1560
import GD.Module0598









set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0106.N0428.N0766.N1693
noncomputable section

open _root_.GD.N0118 _root_.GD.N0106.N0428.N0766.N1691

private theorem d028735 (c₁ c₂ : ℝ) {w r : ℝ} (hwr : w ≤ r) :
    Icc (c₁ - w) (c₁ + w) ×ˢ Icc (c₂ - w) (c₂ + w) ⊆
      Icc (c₁ - r) (c₁ + r) ×ˢ Icc (c₂ - r) (c₂ + r) := by
  intro p hp
  rcases hp with ⟨⟨hxlo, hxhi⟩, ⟨hylo, hyhi⟩⟩
  constructor <;> constructor <;> linarith




theorem d028736
    (c₁ c₂ radius w : ℝ) (g : ℝ × ℝ → ℝ)
    (hw : 0 < w) (hwr : w ≤ radius)
    (hg : ContinuousOn g
      (Icc (c₁ - radius) (c₁ + radius) ×ˢ Icc (c₂ - radius) (c₂ + radius))) :
    Integrable (fun p => _root_.GD.N0118.d008583 c₁ c₂ w p * g p) (volume.prod volume) := by
  have hsupport : Function.support (fun p => _root_.GD.N0118.d008583 c₁ c₂ w p * g p) ⊆
      Icc (c₁ - radius) (c₁ + radius) ×ˢ Icc (c₂ - radius) (c₂ + radius) :=
    (Function.support_mul_subset_left _ _).trans
      ((subset_tsupport _).trans
        ((_root_.GD.N0106.N0428.N0766.N1691.d024079 c₁ c₂ w hw.le).trans
          (_root_.GD.N0106.N0428.N0766.N1693.d028735 c₁ c₂ hwr)))
  apply (integrableOn_iff_integrable_of_support_subset hsupport).mp
  have hcont : ContinuousOn (fun p => _root_.GD.N0118.d008583 c₁ c₂ w p * g p)
      (Icc (c₁ - radius) (c₁ + radius) ×ˢ Icc (c₂ - radius) (c₂ + radius)) :=
    (_root_.GD.N0106.N0428.N0766.N1691.d024069 c₁ c₂ w hw).continuousOn.mul hg
  exact hcont.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)





theorem d028737
    (c₁ c₂ radius : ℝ) (hradius : 0 < radius)
    (g : ℝ × (ℝ × ℝ) → ℝ)
    (hg : ContinuousOn g
      (Icc (0 : ℝ) 1 ×ˢ
        (Icc (c₁ - radius) (c₁ + radius) ×ˢ Icc (c₂ - radius) (c₂ + radius))))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ w₀ > 0, w₀ ≤ radius ∧
      ∀ w, 0 < w → w ≤ w₀ → ∀ e ∈ Icc (0 : ℝ) 1,
        Integrable (fun p => _root_.GD.N0118.d008583 c₁ c₂ w p * g (e, p)) (volume.prod volume) ∧
        |(∫ p, _root_.GD.N0118.d008583 c₁ c₂ w p * g (e, p) ∂(volume.prod volume)) -
          g (e, (c₁, c₂))| ≤ epsilon := by
  let K : Set (ℝ × ℝ) :=
    Icc (c₁ - radius) (c₁ + radius) ×ˢ Icc (c₂ - radius) (c₂ + radius)
  let S : Set (ℝ × (ℝ × ℝ)) := Icc (0 : ℝ) 1 ×ˢ K
  have hcompact : IsCompact S := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hUC : UniformContinuousOn g S := hcompact.uniformContinuousOn_of_continuous hg
  obtain ⟨delta, hdelta, hcontrol⟩ :=
    Metric.uniformContinuousOn_iff.mp hUC epsilon hepsilon
  refine ⟨min radius (delta / 2), lt_min hradius (half_pos hdelta), min_le_left _ _, ?_⟩
  intro w hw hww₀ e he
  have hwr : w ≤ radius := hww₀.trans (min_le_left _ _)
  have hwdelta : w < delta :=
    (hww₀.trans (min_le_right _ _)).trans_lt (half_lt_self hdelta)
  have hcenter : (c₁, c₂) ∈ K := by
    dsimp [K]
    constructor <;> constructor <;> linarith
  have hpair : Continuous (fun p : ℝ × ℝ => (e, p)) :=
    continuous_const.prodMk continuous_id
  have hge : ContinuousOn (fun p => g (e, p)) K :=
    hg.comp' hpair.continuousOn (by intro p hp; exact ⟨he, hp⟩)
  have hIntg : Integrable (fun p => _root_.GD.N0118.d008583 c₁ c₂ w p * g (e, p))
      (volume.prod volume) :=
    _root_.GD.N0106.N0428.N0766.N1693.d028736 c₁ c₂ radius w (fun p => g (e, p)) hw hwr hge
  have hIntconst : Integrable (fun p => _root_.GD.N0118.d008583 c₁ c₂ w p * g (e, (c₁, c₂)))
      (volume.prod volume) :=
    (_root_.GD.N0118.d008591 c₁ c₂ w).mul_const _
  have hIntdiff : Integrable
      (fun p => _root_.GD.N0118.d008583 c₁ c₂ w p * (g (e, p) - g (e, (c₁, c₂))))
      (volume.prod volume) := by
    convert hIntg.sub hIntconst using 1
    funext p
    exact mul_sub (_root_.GD.N0118.d008583 c₁ c₂ w p) (g (e, p)) (g (e, (c₁, c₂)))
  have hBound : ∀ p : ℝ × ℝ, _root_.GD.N0118.d008583 c₁ c₂ w p ≠ 0 →
      |g (e, p) - g (e, (c₁, c₂))| ≤ epsilon := by
    intro p hp
    have hsmall : p ∈ Icc (c₁ - w) (c₁ + w) ×ˢ Icc (c₂ - w) (c₂ + w) :=
      _root_.GD.N0106.N0428.N0766.N1691.d024079 c₁ c₂ w hw.le (subset_tsupport _ hp)
    have hpK : p ∈ K := _root_.GD.N0106.N0428.N0766.N1693.d028735 c₁ c₂ hwr hsmall
    have hx : |p.1 - c₁| ≤ w := abs_le.mpr
      ⟨by linarith [hsmall.1.1], by linarith [hsmall.1.2]⟩
    have hy : |p.2 - c₂| ≤ w := abs_le.mpr
      ⟨by linarith [hsmall.2.1], by linarith [hsmall.2.2]⟩
    have hdist : dist (e, p) (e, (c₁, c₂)) < delta := by
      simp only [Prod.dist_eq, dist_self, Real.dist_eq]
      exact max_lt hdelta (max_lt (hx.trans_lt hwdelta) (hy.trans_lt hwdelta))
    have h := hcontrol (e, p) ⟨he, hpK⟩ (e, (c₁, c₂)) ⟨he, hcenter⟩ hdist
    simpa only [Real.dist_eq] using h.le
  have herror : |∫ p, _root_.GD.N0118.d008583 c₁ c₂ w p * (g (e, p) - g (e, (c₁, c₂)))
      ∂(volume.prod volume)| ≤ epsilon :=
    _root_.GD.N0147.d008603
      (_root_.GD.N0118.d008591 c₁ c₂ w) hIntdiff
      (Filter.Eventually.of_forall (_root_.GD.N0147.d008605 c₁ c₂ w))
      (_root_.GD.N0118.d008601 c₁ c₂ w hw) hepsilon.le (Filter.Eventually.of_forall hBound)
  have heq :
      (∫ p, _root_.GD.N0118.d008583 c₁ c₂ w p * (g (e, p) - g (e, (c₁, c₂))) ∂(volume.prod volume)) =
        (∫ p, _root_.GD.N0118.d008583 c₁ c₂ w p * g (e, p) ∂(volume.prod volume)) - g (e, (c₁, c₂)) := by
    simp_rw [mul_sub]
    rw [integral_sub hIntg hIntconst, integral_mul_const, _root_.GD.N0118.d008601 c₁ c₂ w hw, one_mul]
  exact ⟨hIntg, by simpa only [heq] using herror⟩

end
end GD.N0106.N0428.N0766.N1693

#print axioms _root_.GD.N0106.N0428.N0766.N1693.d028736
#print axioms _root_.GD.N0106.N0428.N0766.N1693.d028737
