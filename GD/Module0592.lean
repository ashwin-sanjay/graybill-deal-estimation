import GD.Module0496
import GD.Module0591




















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1639
noncomputable section

open MeasureTheory Set Filter Complex
open _root_.GD.N0106.N0428.N0765.N1533
open scoped Topology



theorem d008563
    {F : ℂ → ℝ → ℂ} {d y : ℝ} {r : ℕ → ℝ}
    (hd : 0 < d) (hedge : y = -d ∨ y = d)
    (hc : ∀ b : ℝ, ContinuousOn (fun z : ℂ => F z b) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : ∀ b : ℝ, DifferentiableOn ℂ (fun z : ℂ => F z b) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hdecay : ∀ b ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ a s : ℝ,
      R ≤ |a| → |s| ≤ d → ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s) b‖ ≤ ε)
    (hmeas : ∀ s : ℝ, |s| ≤ d → Measurable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F s))
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F (-d)) (volume.prod volume))
    (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F d) (volume.prod volume))
    (hrmem : ∀ n, |r n| ≤ d) (hr : Tendsto r atTop (𝓝 y)) :
    Tendsto (fun n => _root_.GD.N0106.N0428.N0765.N1658.d008463 F (r n)) atTop
      (𝓝 (_root_.GD.N0106.N0428.N0765.N1658.d008463 F y)) := by
  have hy : |y| ≤ d := by
    rcases hedge with rfl | rfl <;> simp [abs_of_pos hd]
  have hrows (n : ℕ) := _root_.GD.N0106.N0428.N0765.N1656.d008560
    hd (hrmem n) hc hf hdecay (hmeas (r n) (hrmem n)) hminus hplus
  have hgy : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F y) (volume.prod volume) := by
    rcases hedge with rfl | rfl
    · exact hminus
    · exact hplus
  let B : ℝ → ℝ := fun s =>
    ((d - s) / (2 * d)) * _root_.GD.N0106.N0428.N0765.N1658.d008463 F (-d) +
      ((d + s) / (2 * d)) * _root_.GD.N0106.N0428.N0765.N1658.d008463 F d
  have hB : Continuous B := by
    unfold B
    fun_prop
  have hBy : B y = _root_.GD.N0106.N0428.N0765.N1658.d008463 F y := by
    rcases hedge with rfl | rfl <;> unfold B <;>
      field_simp [hd.ne'] <;> ring
  have hBlim : Tendsto (fun n => B (r n)) atTop (𝓝 (_root_.GD.N0106.N0428.N0765.N1658.d008463 F y)) := by
    rw [← hBy]
    exact (hB.tendsto y).comp hr
  have hpoint : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
      Tendsto (fun n => _root_.GD.N0106.N0428.N0765.N1658.d008462 F (r n) p) atTop
        (𝓝 (_root_.GD.N0106.N0428.N0765.N1658.d008462 F y p)) := by
    filter_upwards [] with p
    exact _root_.GD.N0106.N0428.N0765.N1508.d007602
      (hc p.2) hy hrmem hr p.1
  exact _root_.GD.N0106.N0428.N0765.N1508.d007601
    (fun n => (hrows n).1) hgy hpoint (fun n => (hrows n).2) hBlim



theorem d008564
    {F : ℂ → ℂ → ℂ} {d a₀ b₀ : ℝ} {a b : ℕ → ℝ}
    (hd : 0 < d) (haedge : a₀ = -d ∨ a₀ = d) (hbedge : b₀ = -d ∨ b₀ = d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfA : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hfB : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hdecayA : ∀ γ : ℝ, |γ| ≤ d → ∀ t ε : ℝ, 0 < ε →
      ∃ R : ℝ, ∀ x s : ℝ, R ≤ |x| → |s| ≤ d →
        ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 x s) (_root_.GD.N0106.N0428.N0765.N1658.d008466 t γ)‖ ≤ ε)
    (hdecayBEdge : ∀ γ : ℝ, γ = -d ∨ γ = d → ∀ t ε : ℝ, 0 < ε →
      ∃ R : ℝ, ∀ x s : ℝ, R ≤ |x| → |s| ≤ d →
        ‖F (_root_.GD.N0106.N0428.N0765.N1658.d008466 t γ) (_root_.GD.N0106.N0428.N0765.N1550.d005473 x s)‖ ≤ ε)
    (hmm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (-d) (-d)) (volume.prod volume))
    (hmp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (-d) d) (volume.prod volume))
    (hpm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F d (-d)) (volume.prod volume))
    (hpp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F d d) (volume.prod volume))
    (hamem : ∀ n, |a n| ≤ d) (hbmem : ∀ n, |b n| ≤ d)
    (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀)) :
    Tendsto (fun n => _root_.GD.N0106.N0428.N0765.N1658.d008468 F (a n) (b n)) atTop
      (𝓝 (_root_.GD.N0106.N0428.N0765.N1658.d008468 F a₀ b₀)) := by
  have ha₀ : |a₀| ≤ d := by
    rcases haedge with rfl | rfl <;> simp [abs_of_pos hd]
  have hb₀ : |b₀| ≤ d := by
    rcases hbedge with rfl | rfl <;> simp [abs_of_pos hd]
  have hplanes (n : ℕ) := _root_.GD.N0106.N0428.N0765.N1656.d008561
    hd (hamem n) (hbmem n) hc hfA hfB hdecayA hdecayBEdge hmm hmp hpm hpp
  have hcorner : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F a₀ b₀) (volume.prod volume) :=
    (_root_.GD.N0106.N0428.N0765.N1656.d008561
      hd ha₀ hb₀ hc hfA hfB hdecayA hdecayBEdge hmm hmp hpm hpp).1
  let B : ℝ × ℝ → ℝ := fun q =>
    ((d - q.1) / (2 * d)) *
      (((d - q.2) / (2 * d)) * _root_.GD.N0106.N0428.N0765.N1658.d008468 F (-d) (-d) +
        ((d + q.2) / (2 * d)) * _root_.GD.N0106.N0428.N0765.N1658.d008468 F (-d) d) +
    ((d + q.1) / (2 * d)) *
      (((d - q.2) / (2 * d)) * _root_.GD.N0106.N0428.N0765.N1658.d008468 F d (-d) +
        ((d + q.2) / (2 * d)) * _root_.GD.N0106.N0428.N0765.N1658.d008468 F d d)
  have hB : Continuous B := by
    unfold B
    fun_prop
  have hBcorner : B (a₀, b₀) = _root_.GD.N0106.N0428.N0765.N1658.d008468 F a₀ b₀ := by
    rcases haedge with rfl | rfl <;> rcases hbedge with rfl | rfl <;>
      unfold B <;> dsimp only <;> field_simp [hd.ne'] <;> ring
  have hBlim : Tendsto (fun n => B (a n, b n)) atTop
      (𝓝 (_root_.GD.N0106.N0428.N0765.N1658.d008468 F a₀ b₀)) := by
    rw [← hBcorner]
    exact (hB.tendsto (a₀, b₀)).comp (ha.prodMk_nhds hb)
  have hpoint : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume),
      Tendsto (fun n => _root_.GD.N0106.N0428.N0765.N1658.d008467 F (a n) (b n) p) atTop
        (𝓝 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F a₀ b₀ p)) := by
    filter_upwards [] with p
    have hmap : Continuous (fun q : ℝ × ℝ =>
        (_root_.GD.N0106.N0428.N0765.N1658.d008466 p.1 q.1, _root_.GD.N0106.N0428.N0765.N1658.d008466 p.2 q.2)) := by
      unfold _root_.GD.N0106.N0428.N0765.N1658.d008466
      fun_prop
    have hpt : Tendsto (fun n =>
        (_root_.GD.N0106.N0428.N0765.N1658.d008466 p.1 (a n), _root_.GD.N0106.N0428.N0765.N1658.d008466 p.2 (b n))) atTop
        (𝓝[_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d]
          (_root_.GD.N0106.N0428.N0765.N1658.d008466 p.1 a₀, _root_.GD.N0106.N0428.N0765.N1658.d008466 p.2 b₀)) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨(hmap.tendsto (a₀, b₀)).comp (ha.prodMk_nhds hb),
          Eventually.of_forall (fun n =>
            ⟨_root_.GD.N0106.N0428.N0765.N1658.d008469 (hamem n) p.1,
              _root_.GD.N0106.N0428.N0765.N1658.d008469 (hbmem n) p.2⟩)⟩
    exact (hc _ ⟨_root_.GD.N0106.N0428.N0765.N1658.d008469 ha₀ p.1,
      _root_.GD.N0106.N0428.N0765.N1658.d008469 hb₀ p.2⟩).tendsto.comp hpt
  exact _root_.GD.N0106.N0428.N0765.N1508.d007601
    (fun n => (hplanes n).1) hcorner hpoint (fun n => (hplanes n).2) hBlim

end
end GD.N0106.N0428.N0765.N1639

#print axioms _root_.GD.N0106.N0428.N0765.N1639.d008563
#print axioms _root_.GD.N0106.N0428.N0765.N1639.d008564
