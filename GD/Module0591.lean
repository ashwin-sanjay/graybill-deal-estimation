import GD.Module0584
import GD.Module0442





























set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1656
noncomputable section

open MeasureTheory Set Complex Filter
open _root_.GD.N0106.N0428.N0765.N1533 _root_.GD.N0106.N0428.N0765.N1530 _root_.GD.N0106.N0428.N0765.N1531



theorem d008559 {F : ℂ → ℝ → ℂ} {d y : ℝ}
    (hd : 0 < d) (hy : |y| ≤ d)
    (hc : ∀ b : ℝ, ContinuousOn (fun z : ℂ => F z b) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : ∀ b : ℝ, DifferentiableOn ℂ (fun z : ℂ => F z b) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hM : ∀ b : ℝ, ∃ M : ℝ, ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖F z b‖ ≤ M)
    (hmeas : Measurable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F y))
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F (-d)) (volume.prod volume))
    (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F d) (volume.prod volume)) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F y) (volume.prod volume) ∧
      _root_.GD.N0106.N0428.N0765.N1658.d008463 F y ≤
        ((d - y) / (2 * d)) * _root_.GD.N0106.N0428.N0765.N1658.d008463 F (-d) +
        ((d + y) / (2 * d)) * _root_.GD.N0106.N0428.N0765.N1658.d008463 F d := by
  let cm : ℝ := (d - y) / (2 * d)
  let cp : ℝ := (d + y) / (2 * d)
  let am : ℝ → ℝ := fun b => ∫ a : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1658.d008462 F (-d) (a, b)‖
  let ap : ℝ → ℝ := fun b => ∫ a : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1658.d008462 F d (a, b)‖
  let ay : ℝ → ℝ := fun b => ∫ a : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1658.d008462 F y (a, b)‖
  have hsec : ∀ᵐ b : ℝ,
      Integrable (fun a : ℝ => _root_.GD.N0106.N0428.N0765.N1658.d008462 F y (a, b)) ∧
        ay b ≤ cm * am b + cp * ap b := by
    filter_upwards [hminus.prod_left_ae, hplus.prod_left_ae] with b hbm hbp
    have hm : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 (fun z : ℂ => F z b) (-d)) := hbm
    have hp : Integrable (_root_.GD.N0106.N0428.N0765.N1530.d005194 (fun z : ℂ => F z b) d) := hbp
    obtain ⟨M, hMb⟩ := hM b
    exact _root_.GD.N0106.N0428.N0765.N1531.d007569
      hd hy (hc b) (hf b) hMb hm hp
  have ham : Integrable am := hminus.integral_norm_prod_right
  have hap : Integrable ap := hplus.integral_norm_prod_right
  have hbudget : Integrable (fun b : ℝ => cm * am b + cp * ap b) :=
    (ham.const_mul cm).add (hap.const_mul cp)
  have haymeas : AEStronglyMeasurable ay :=
    hmeas.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
  have hay0 : ∀ b : ℝ, 0 ≤ ay b := fun b => integral_nonneg (fun _ => norm_nonneg _)
  have hay : Integrable ay := by
    apply Integrable.mono' hbudget haymeas
    filter_upwards [hsec] with b hb
    rw [Real.norm_eq_abs, abs_of_nonneg (hay0 b)]
    exact hb.2
  have hi : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F y) (volume.prod volume) :=
    (integrable_prod_iff' hmeas.aestronglyMeasurable).2
      ⟨hsec.mono (fun _ hb => hb.1), hay⟩
  refine ⟨hi, ?_⟩
  change _root_.GD.N0106.N0428.N0765.N1658.d008463 F y ≤
    cm * _root_.GD.N0106.N0428.N0765.N1658.d008463 F (-d) + cp * _root_.GD.N0106.N0428.N0765.N1658.d008463 F d
  calc
    _root_.GD.N0106.N0428.N0765.N1658.d008463 F y = ∫ b : ℝ, ay b := integral_prod_symm _ hi.norm
    _ ≤ ∫ b : ℝ, cm * am b + cp * ap b :=
      integral_mono_ae hay hbudget (hsec.mono (fun _ hb => hb.2))
    _ = cm * (∫ b : ℝ, am b) + cp * (∫ b : ℝ, ap b) := by
      rw [integral_add (ham.const_mul cm) (hap.const_mul cp),
        integral_const_mul, integral_const_mul]
    _ = cm * _root_.GD.N0106.N0428.N0765.N1658.d008463 F (-d) + cp * _root_.GD.N0106.N0428.N0765.N1658.d008463 F d := by
      rw [show (∫ b : ℝ, am b) = _root_.GD.N0106.N0428.N0765.N1658.d008463 F (-d) from
        (integral_prod_symm _ hminus.norm).symm,
        show (∫ b : ℝ, ap b) = _root_.GD.N0106.N0428.N0765.N1658.d008463 F d from
        (integral_prod_symm _ hplus.norm).symm]



theorem d008560 {F : ℂ → ℝ → ℂ} {d y : ℝ}
    (hd : 0 < d) (hy : |y| ≤ d)
    (hc : ∀ b : ℝ, ContinuousOn (fun z : ℂ => F z b) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hf : ∀ b : ℝ, DifferentiableOn ℂ (fun z : ℂ => F z b) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hdecay : ∀ b ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ a s : ℝ,
      R ≤ |a| → |s| ≤ d → ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s) b‖ ≤ ε)
    (hmeas : Measurable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F y))
    (hminus : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F (-d)) (volume.prod volume))
    (hplus : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F d) (volume.prod volume)) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F y) (volume.prod volume) ∧
      _root_.GD.N0106.N0428.N0765.N1658.d008463 F y ≤
        ((d - y) / (2 * d)) * _root_.GD.N0106.N0428.N0765.N1658.d008463 F (-d) +
        ((d + y) / (2 * d)) * _root_.GD.N0106.N0428.N0765.N1658.d008463 F d := by
  have hM : ∀ b : ℝ, ∃ M : ℝ, ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖F z b‖ ≤ M := by
    intro b
    obtain ⟨M, _hMpos, hMb⟩ :=
      _root_.GD.N0106.N0428.N0765.N1551.d006791 (hc b) (hdecay b)
    exact ⟨M, hMb⟩
  exact _root_.GD.N0106.N0428.N0765.N1656.d008559
    hd hy hc hf hM hmeas hminus hplus



theorem d008561 {F : ℂ → ℂ → ℂ} {d α β : ℝ}
    (hd : 0 < d) (hα : |α| ≤ d) (hβ : |β| ≤ d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfA : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hfB : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hdecayA : ∀ γ : ℝ, |γ| ≤ d → ∀ b ε : ℝ, 0 < ε →
      ∃ R : ℝ, ∀ a s : ℝ, R ≤ |a| → |s| ≤ d →
        ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s) (_root_.GD.N0106.N0428.N0765.N1658.d008466 b γ)‖ ≤ ε)
    (hdecayBEdge : ∀ γ : ℝ, γ = -d ∨ γ = d → ∀ a ε : ℝ, 0 < ε →
      ∃ R : ℝ, ∀ b s : ℝ, R ≤ |b| → |s| ≤ d →
        ‖F (_root_.GD.N0106.N0428.N0765.N1658.d008466 a γ) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε)
    (hmm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (-d) (-d)) (volume.prod volume))
    (hmp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (-d) d) (volume.prod volume))
    (hpm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F d (-d)) (volume.prod volume))
    (hpp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F d d) (volume.prod volume)) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F α β) (volume.prod volume) ∧
      _root_.GD.N0106.N0428.N0765.N1658.d008468 F α β ≤
        ((d - α) / (2 * d)) *
          (((d - β) / (2 * d)) * _root_.GD.N0106.N0428.N0765.N1658.d008468 F (-d) (-d) +
            ((d + β) / (2 * d)) * _root_.GD.N0106.N0428.N0765.N1658.d008468 F (-d) d) +
        ((d + α) / (2 * d)) *
          (((d - β) / (2 * d)) * _root_.GD.N0106.N0428.N0765.N1658.d008468 F d (-d) +
            ((d + β) / (2 * d)) * _root_.GD.N0106.N0428.N0765.N1658.d008468 F d d) := by
  have hcA (w : ℂ) (hw : w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d) :
      ContinuousOn (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d) := by
    have hm : Continuous (fun z : ℂ => (z, w)) := by fun_prop
    exact hc.comp hm.continuousOn (fun z hz => ⟨hz, hw⟩)
  have hcB (z : ℂ) (hz : z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d) :
      ContinuousOn (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d) := by
    have hm : Continuous (fun w : ℂ => (z, w)) := by fun_prop
    exact hc.comp hm.continuousOn (fun w hw => ⟨hz, hw⟩)
  have hmeas (a b : ℝ) (ha : |a| ≤ d) (hb : |b| ≤ d) :
      Measurable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F a b) := by
    have hm : Continuous (fun p : ℝ × ℝ =>
        (_root_.GD.N0106.N0428.N0765.N1658.d008466 p.1 a, _root_.GD.N0106.N0428.N0765.N1658.d008466 p.2 b)) := by
      unfold _root_.GD.N0106.N0428.N0765.N1658.d008466
      fun_prop
    exact (hc.comp_continuous hm (fun p =>
      ⟨_root_.GD.N0106.N0428.N0765.N1658.d008469 ha p.1,
        _root_.GD.N0106.N0428.N0765.N1658.d008469 hb p.2⟩)).measurable
  have hneg : |(-d : ℝ)| ≤ d := by
    simpa only [abs_neg, abs_of_pos hd] using (le_refl d)
  have hpos : |d| ≤ d := by
    simpa only [abs_of_pos hd] using (le_refl d)
  have hedge (a : ℝ) (ha : |a| ≤ d) (haedge : a = -d ∨ a = d)
      (hm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F a (-d)) (volume.prod volume))
      (hp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F a d) (volume.prod volume)) :
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F a β) (volume.prod volume) ∧
        _root_.GD.N0106.N0428.N0765.N1658.d008468 F a β ≤
          ((d - β) / (2 * d)) * _root_.GD.N0106.N0428.N0765.N1658.d008468 F a (-d) +
          ((d + β) / (2 * d)) * _root_.GD.N0106.N0428.N0765.N1658.d008468 F a d := by
    let G : ℂ → ℝ → ℂ := fun z t => F (_root_.GD.N0106.N0428.N0765.N1658.d008466 t a) z
    have hmG : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 G (-d)) (volume.prod volume) := hm.swap
    have hpG : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 G d) (volume.prod volume) := hp.swap
    have hGmeas : Measurable (_root_.GD.N0106.N0428.N0765.N1658.d008462 G β) :=
      (hmeas a β ha hβ).comp measurable_swap
    have hmass (b : ℝ) : _root_.GD.N0106.N0428.N0765.N1658.d008463 G b = _root_.GD.N0106.N0428.N0765.N1658.d008468 F a b :=
      integral_prod_swap (fun p : ℝ × ℝ => ‖_root_.GD.N0106.N0428.N0765.N1658.d008467 F a b p‖)
    obtain ⟨hiG, hbG⟩ := _root_.GD.N0106.N0428.N0765.N1656.d008560 hd hβ
      (fun t => hcB (_root_.GD.N0106.N0428.N0765.N1658.d008466 t a) (_root_.GD.N0106.N0428.N0765.N1658.d008469 ha t))
      (fun t => hfB (_root_.GD.N0106.N0428.N0765.N1658.d008466 t a) (_root_.GD.N0106.N0428.N0765.N1658.d008469 ha t))
      (hdecayBEdge a haedge) hGmeas hmG hpG
    refine ⟨hiG.swap, ?_⟩
    change _root_.GD.N0106.N0428.N0765.N1658.d008463 G β ≤
      ((d - β) / (2 * d)) * _root_.GD.N0106.N0428.N0765.N1658.d008463 G (-d) +
      ((d + β) / (2 * d)) * _root_.GD.N0106.N0428.N0765.N1658.d008463 G d at hbG
    rw [hmass β, hmass (-d), hmass d] at hbG
    exact hbG
  obtain ⟨him, hbm⟩ := hedge (-d) hneg (Or.inl rfl) hmm hmp
  obtain ⟨hip, hbp⟩ := hedge d hpos (Or.inr rfl) hpm hpp
  let G : ℂ → ℝ → ℂ := fun z t => F z (_root_.GD.N0106.N0428.N0765.N1658.d008466 t β)
  have hmG : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 G (-d)) (volume.prod volume) := him
  have hpG : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 G d) (volume.prod volume) := hip
  have hGmeas : Measurable (_root_.GD.N0106.N0428.N0765.N1658.d008462 G α) := hmeas α β hα hβ
  obtain ⟨hiG, hbG⟩ := _root_.GD.N0106.N0428.N0765.N1656.d008560 hd hα
    (fun t => hcA (_root_.GD.N0106.N0428.N0765.N1658.d008466 t β) (_root_.GD.N0106.N0428.N0765.N1658.d008469 hβ t))
    (fun t => hfA (_root_.GD.N0106.N0428.N0765.N1658.d008466 t β) (_root_.GD.N0106.N0428.N0765.N1658.d008469 hβ t))
    (hdecayA β hβ) hGmeas hmG hpG
  refine ⟨hiG, ?_⟩
  have hca : 0 ≤ (d - α) / (2 * d) :=
    div_nonneg (by linarith [(abs_le.mp hα).2]) (by positivity)
  have hpa : 0 ≤ (d + α) / (2 * d) :=
    div_nonneg (by linarith [(abs_le.mp hα).1]) (by positivity)
  exact hbG.trans (add_le_add (mul_le_mul_of_nonneg_left hbm hca)
    (mul_le_mul_of_nonneg_left hbp hpa))



theorem d008562
    {F : ℂ → ℂ → ℂ} {d α β : ℝ}
    (hd : 0 < d) (hα : |α| ≤ d) (hβ : |β| ≤ d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfA : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hfB : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hdecayA : ∀ γ : ℝ, |γ| ≤ d → ∀ b ε : ℝ, 0 < ε →
      ∃ R : ℝ, ∀ a s : ℝ, R ≤ |a| → |s| ≤ d →
        ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s) (_root_.GD.N0106.N0428.N0765.N1658.d008466 b γ)‖ ≤ ε)
    (hdecayBEdge : ∀ γ : ℝ, γ = -d ∨ γ = d → ∀ a ε : ℝ, 0 < ε →
      ∃ R : ℝ, ∀ b s : ℝ, R ≤ |b| → |s| ≤ d →
        ‖F (_root_.GD.N0106.N0428.N0765.N1658.d008466 a γ) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε)
    (hmm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (-d) (-d)) (volume.prod volume))
    (hmp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (-d) d) (volume.prod volume))
    (hpm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F d (-d)) (volume.prod volume))
    (hpp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F d d) (volume.prod volume)) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F α β) (volume.prod volume) ∧
      _root_.GD.N0106.N0428.N0765.N1658.d008468 F α β ≤ _root_.GD.N0106.N0428.N0765.N1650.d008510 F d := by
  obtain ⟨hi, hb⟩ := _root_.GD.N0106.N0428.N0765.N1656.d008561
    hd hα hβ hc hfA hfB hdecayA hdecayBEdge hmm hmp hpm hpp
  refine ⟨hi, hb.trans ?_⟩
  unfold _root_.GD.N0106.N0428.N0765.N1650.d008510
  apply _root_.GD.N0106.N0428.N0765.N1650.d008511 hd hα
  · apply _root_.GD.N0106.N0428.N0765.N1650.d008511 hd hβ
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
  · apply _root_.GD.N0106.N0428.N0765.N1650.d008511 hd hβ
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)

end
end GD.N0106.N0428.N0765.N1656

#print axioms _root_.GD.N0106.N0428.N0765.N1656.d008559
#print axioms _root_.GD.N0106.N0428.N0765.N1656.d008560
#print axioms _root_.GD.N0106.N0428.N0765.N1656.d008561
#print axioms _root_.GD.N0106.N0428.N0765.N1656.d008562
