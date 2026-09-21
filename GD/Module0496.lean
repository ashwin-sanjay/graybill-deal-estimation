import GD.Module0495
import Mathlib.MeasureTheory.Integral.DominatedConvergence























set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1508
noncomputable section

open MeasureTheory Set Filter Complex
open _root_.GD.N0106.N0428.N0765.N1533 _root_.GD.N0106.N0428.N0765.N1530
open scoped Topology




theorem d007601
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℂ} {g : X → ℂ} {B : ℕ → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hg : Integrable g μ)
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hupper : ∀ n, (∫ x, ‖f n x‖ ∂μ) ≤ B n)
    (hB : Tendsto B atTop (𝓝 (∫ x, ‖g x‖ ∂μ))) :
    Tendsto (fun n => ∫ x, ‖f n x‖ ∂μ) atTop (𝓝 (∫ x, ‖g x‖ ∂μ)) := by
  let lower : ℕ → X → ℝ := fun n x => min ‖f n x‖ ‖g x‖
  have hmeas (n : ℕ) : AEStronglyMeasurable (lower n) μ :=
    ((hf n).aestronglyMeasurable.norm.aemeasurable.min
      hg.aestronglyMeasurable.norm.aemeasurable).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, ‖lower n x‖ ≤ ‖g x‖ := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (norm_nonneg _) (norm_nonneg _))]
    exact min_le_right _ _
  have hlowerint (n : ℕ) : Integrable (lower n) μ :=
    hg.norm.mono' (hmeas n) (hbound n)
  have hlowerpoint : ∀ᵐ x ∂μ,
      Tendsto (fun n => lower n x) atTop (𝓝 ‖g x‖) := by
    filter_upwards [hpoint] with x hx
    simpa only [lower, min_self] using hx.norm.min
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖g x‖) atTop (𝓝 ‖g x‖))
  have hlower : Tendsto (fun n => ∫ x, lower n x ∂μ) atTop
      (𝓝 (∫ x, ‖g x‖ ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
      hmeas hg.norm hbound hlowerpoint
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hB
  · intro n
    exact integral_mono (hlowerint n) (hf n).norm (fun x => min_le_left _ _)
  · exact hupper



theorem d007602 {f : ℂ → ℂ} {d y : ℝ} {r : ℕ → ℝ}
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d)) (hy : |y| ≤ d)
    (hrmem : ∀ n, |r n| ≤ d) (hr : Tendsto r atTop (𝓝 y)) (x : ℝ) :
    Tendsto (fun n => _root_.GD.N0106.N0428.N0765.N1530.d005194 f (r n) x) atTop
      (𝓝 (_root_.GD.N0106.N0428.N0765.N1530.d005194 f y x)) := by
  have hmem (s : ℝ) (hs : |s| ≤ d) : _root_.GD.N0106.N0428.N0765.N1550.d005473 x s ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d := by
    simpa only [_root_.GD.N0106.N0428.N0765.N1533.d005164, mem_setOf_eq, _root_.GD.N0106.N0428.N0765.N1550.d005477] using hs
  have hmap : Continuous (fun s : ℝ => _root_.GD.N0106.N0428.N0765.N1550.d005473 x s) := by
    unfold _root_.GD.N0106.N0428.N0765.N1550.d005473
    fun_prop
  have hpt : Tendsto (fun n => _root_.GD.N0106.N0428.N0765.N1550.d005473 x (r n)) atTop
      (𝓝[_root_.GD.N0106.N0428.N0765.N1533.d005164 d] (_root_.GD.N0106.N0428.N0765.N1550.d005473 x y)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(hmap.tendsto y).comp hr, Eventually.of_forall (fun n => hmem (r n) (hrmem n))⟩
  exact (hc (_root_.GD.N0106.N0428.N0765.N1550.d005473 x y) (hmem y hy)).tendsto.comp hpt



theorem d007603
    {f : ℂ → ℂ} {d y : ℝ} {r : ℕ → ℝ}
    (hd : 0 < d) (hedge : y = -d ∨ y = d)
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (-d)))
    (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f d))
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ a s : ℝ,
      R ≤ |a| → |s| ≤ d → ‖f (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s)‖ ≤ ε)
    (hrmem : ∀ n, |r n| ≤ d) (hr : Tendsto r atTop (𝓝 y)) :
    Tendsto (fun n => _root_.GD.N0106.N0428.N0765.N1530.d005195 f (r n)) atTop (𝓝 (_root_.GD.N0106.N0428.N0765.N1530.d005195 f y)) := by
  obtain ⟨M, _hMpos, hM⟩ :=
    _root_.GD.N0106.N0428.N0765.N1551.d006791 hc hdecay
  have hrows (n : ℕ) := _root_.GD.N0106.N0428.N0765.N1531.d007569
    hd (hrmem n) hc hf hM hminus hplus
  have hy : |y| ≤ d := by
    rcases hedge with rfl | rfl <;> simp [abs_of_pos hd]
  have hgy : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f y) := by
    rcases hedge with rfl | rfl
    · exact hminus
    · exact hplus
  have hbudget : Continuous (fun s : ℝ => _root_.GD.N0106.N0428.N0765.N1530.d005196 f d s) := by
    unfold _root_.GD.N0106.N0428.N0765.N1530.d005196
    fun_prop
  have hedgeBudget : _root_.GD.N0106.N0428.N0765.N1530.d005196 f d y = _root_.GD.N0106.N0428.N0765.N1530.d005195 f y := by
    rcases hedge with rfl | rfl <;> unfold _root_.GD.N0106.N0428.N0765.N1530.d005196 <;>
      field_simp [hd.ne'] <;> ring
  have hbudgetlim : Tendsto (fun n => _root_.GD.N0106.N0428.N0765.N1530.d005196 f d (r n)) atTop
      (𝓝 (_root_.GD.N0106.N0428.N0765.N1530.d005195 f y)) := by
    rw [← hedgeBudget]
    exact (hbudget.tendsto y).comp hr
  exact _root_.GD.N0106.N0428.N0765.N1508.d007601
    (fun n => (hrows n).1) hgy
    (Eventually.of_forall (fun x => _root_.GD.N0106.N0428.N0765.N1508.d007602 hc hy hrmem hr x))
    (fun n => (hrows n).2) hbudgetlim



theorem d007604
    {f : ℂ → ℂ} {d : ℝ} {r : ℕ → ℝ}
    (hd : 0 < d)
    (hc : ContinuousOn f (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : DifferentiableOn ℂ f (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f (-d)))
    (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 f d))
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ a s : ℝ,
      R ≤ |a| → |s| ≤ d → ‖f (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s)‖ ≤ ε)
    (hrmem : ∀ n, |r n| ≤ d) (hr : Tendsto r atTop (𝓝 d)) :
    Tendsto (fun n => _root_.GD.N0106.N0428.N0765.N1530.d005195 f (-r n)) atTop (𝓝 (_root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d))) ∧
      Tendsto (fun n => _root_.GD.N0106.N0428.N0765.N1530.d005195 f (r n)) atTop (𝓝 (_root_.GD.N0106.N0428.N0765.N1530.d005195 f d)) ∧
      Tendsto (fun n => _root_.GD.N0106.N0428.N0765.N1530.d005195 f (-r n) + _root_.GD.N0106.N0428.N0765.N1530.d005195 f (r n)) atTop
        (𝓝 (_root_.GD.N0106.N0428.N0765.N1530.d005195 f (-d) + _root_.GD.N0106.N0428.N0765.N1530.d005195 f d)) := by
  have hm := _root_.GD.N0106.N0428.N0765.N1508.d007603 hd (Or.inl rfl)
    hc hf hminus hplus hdecay (fun n => by simpa only [abs_neg] using hrmem n) hr.neg
  have hp := _root_.GD.N0106.N0428.N0765.N1508.d007603 hd (Or.inr rfl)
    hc hf hminus hplus hdecay hrmem hr
  exact ⟨hm, hp, hm.add hp⟩

end
end GD.N0106.N0428.N0765.N1508

#print axioms _root_.GD.N0106.N0428.N0765.N1508.d007601
#print axioms _root_.GD.N0106.N0428.N0765.N1508.d007602
#print axioms _root_.GD.N0106.N0428.N0765.N1508.d007603
#print axioms _root_.GD.N0106.N0428.N0765.N1508.d007604
