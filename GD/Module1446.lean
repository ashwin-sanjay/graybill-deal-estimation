import GD.Module1444
import GD.Module1370

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section
namespace GD.N0074

theorem d022934
    {α : Type*} {m m₀ : MeasurableSpace α} {μ : Measure α}
    (hm : m ≤ m₀) [IsFiniteMeasure μ] [SigmaFinite (μ.trim hm)]
    {f q : α → ℝ} (hf : Integrable f μ) (hq : Integrable q μ)
    (hqm : AEStronglyMeasurable[m] q μ)
    (htest : ∀ h : α → ℝ, StronglyMeasurable[m] h →
      (∀ x, ‖h x‖ ≤ 1) → (∫ x, h x * (f x - q x) ∂μ) = 0) :
    q =ᵐ[μ] μ[f | m] := by
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hf
    (fun s _ _ ↦ hq.integrableOn) _ hqm
  intro s hs _
  have hsm : MeasurableSet s := hm _ hs
  have hb : ∀ x, ‖s.indicator (fun _ : α ↦ (1 : ℝ)) x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ s <;> simp [hx]
  have H := htest (s.indicator (fun _ : α ↦ (1 : ℝ)))
    (stronglyMeasurable_const.indicator hs) hb
  have hfun :
      (fun x ↦ s.indicator (fun _ : α ↦ (1 : ℝ)) x * (f x - q x)) =
        s.indicator (fun x ↦ f x - q x) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [hfun, integral_indicator hsm,
    integral_sub hf.integrableOn hq.integrableOn] at H
  exact (sub_eq_zero.mp H).symm

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N1012
open _root_.GD.N0230.N0602

theorem d022935
    (k : ℕ) (sizes : Fin k → ℕ)
    (d q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hqm : AEStronglyMeasurable[_root_.GD.N0232.N0719.N1012.d011397 k sizes]
      (q : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (htest : ∀ h : _root_.GD.N0232.N0719.d009173 k sizes → ℝ,
      StronglyMeasurable[_root_.GD.N0232.N0719.N1012.d011397 k sizes] h →
      (∀ x, ‖h x‖ ≤ 1) →
      (∫ x, h x * (d x - q x)
        ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) = 0) :
    q = _root_.GD.N0232.N0719.N1012.d011399 k sizes d := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
    unfold _root_.GD.N0232.N0719.N0859.d010813
    infer_instance
  apply Lp.ext
  exact (_root_.GD.N0074.d022934 (_root_.GD.N0232.N0719.N1012.d011398 k sizes)
    ((Lp.memLp d).integrable (by norm_num))
    ((Lp.memLp q).integrable (by norm_num)) hqm htest).trans
      (_root_.GD.N0074.d022922 k sizes d).symm

theorem d022936
    (k : ℕ) (sizes : Fin k → ℕ) (hsizes : ∀ i, 0 < sizes i)
    (d q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hqm : AEStronglyMeasurable[_root_.GD.N0232.N0719.N1012.d011397 k sizes]
      (q : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (htest : ∀ h : _root_.GD.N0074.N0308.d022069 k → ℝ,
      Measurable h → (∀ s, ‖h s‖ ≤ 1) →
      (∫ x, h (_root_.GD.N0074.N0308.d022071 k sizes x) * (d x - q x)
        ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) = 0) :
    q = _root_.GD.N0232.N0719.N1012.d011399 k sizes d := by
  apply _root_.GD.N0074.d022935 k sizes d q hqm
  intro h hh hbound
  obtain ⟨g, hg, hfg⟩ :=
    (_root_.GD.N0074.N0308.d022074
      k sizes hsizes h).mp hh.aestronglyMeasurable
  let clip : _root_.GD.N0074.N0308.d022069 k → ℝ :=
    fun s ↦ max (-1) (min 1 (g s))
  have hcmeas : Measurable clip :=
    measurable_const.max (measurable_const.min hg)
  have hcbound : ∀ s, ‖clip s‖ ≤ 1 := by
    intro s
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hclip : (fun x ↦ clip (_root_.GD.N0074.N0308.d022071 k sizes x)) =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010813 k sizes] h := by
    filter_upwards [hfg] with x hx
    have hb := abs_le.mp (show |h x| ≤ 1 by simpa only [Real.norm_eq_abs] using hbound x)
    change max (-1) (min 1 (g (_root_.GD.N0074.N0308.d022071 k sizes x))) = h x
    change h x = g (_root_.GD.N0074.N0308.d022071 k sizes x) at hx
    rw [← hx, min_eq_right hb.2, max_eq_right hb.1]
  calc
    (∫ x, h x * (d x - q x) ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) =
        ∫ x, clip (_root_.GD.N0074.N0308.d022071 k sizes x) * (d x - q x)
          ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes := by
      apply integral_congr_ae
      filter_upwards [hclip] with x hx
      rw [hx]
    _ = 0 := htest clip hcmeas hcbound

end GD.N0074

#print axioms _root_.GD.N0074.d022934
#print axioms _root_.GD.N0074.d022935
#print axioms _root_.GD.N0074.d022936
