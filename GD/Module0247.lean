import GD.Module0241
import GD.Module0091
import GD.Module0014











set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0230.N0707

noncomputable section

open _root_.GD.N0230.N0602 _root_.GD.N0230.N0633 _root_.GD.N0230.N0586

variable {Ω Θ : Type*} [MeasurableSpace Ω]



theorem d003550
    (μ₀ : Measure Ω) (μ : Θ → Measure Ω) (target : Θ → ℝ)
    (hμ : ∀ θ, μ θ ≪ μ₀)
    (θ₀ θ₁ : Θ) (href : μ θ₀ = μ₀) (htarget₀ : target θ₀ = 0)
    (htarget₁ : target θ₁ = 1) [IsProbabilityMeasure (μ θ₁)] :
    ¬ ∀ c : ℝ, 0 < c → ∃ p : _root_.GD.N0230.N0602.d000116 μ₀,
      ∀ θ, _root_.GD.N0230.N0602.d000117 (μ θ) (target θ) p ≤ ENNReal.ofReal c := by
  intro hsmall
  let cap : ℝ → Set (_root_.GD.N0230.N0602.d000116 μ₀) :=
    fun c => _root_.GD.N0230.N0602.d000118 μ₀ μ target (fun _ => ENNReal.ofReal c)
  let weakCap : ℝ → Set (WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 μ₀)) :=
    fun c => toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 μ₀) '' cap c
  have hnorm {c : ℝ} (hc : 0 ≤ c) {p : _root_.GD.N0230.N0602.d000116 μ₀} (hp : p ∈ cap c) :
      ‖p‖ ≤ Real.sqrt c := by
    have hb := hp θ₀
    rw [href, htarget₀, _root_.GD.N0230.N0602.d000124] at hb
    simp only [zero_sub, norm_neg] at hb
    have hs : ‖p‖ ^ 2 ≤ c := (ENNReal.ofReal_le_ofReal_iff hc).mp hb
    nlinarith [Real.sq_sqrt hc, Real.sqrt_nonneg c, norm_nonneg p]
  have hcompact (c : ℝ) (hc : 0 < c) : IsCompact (weakCap c) := by
    exact _root_.GD.N0230.N0633.d001201
      (Real.sqrt c) (_root_.GD.N0230.N0602.d000123 μ₀ μ target _ hμ)
      (_root_.GD.N0230.N0602.d000122 μ₀ μ target _ hμ) (fun p hp => hnorm hc.le hp)
  have hmono : Monotone weakCap := by
    intro c d hcd
    rintro q ⟨p, hp, rfl⟩
    exact ⟨p, fun θ => (hp θ).trans (ENNReal.ofReal_le_ofReal hcd), rfl⟩
  have hne (c : ℝ) (hc : 0 < c) : (weakCap c).Nonempty := by
    obtain ⟨p, hp⟩ := hsmall c hc
    exact ⟨_, p, hp, rfl⟩
  obtain ⟨q, hq⟩ := _root_.GD.N0230.N0586.d003514
    weakCap hmono 0 hcompact hne
  let p := (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 μ₀)).symm q
  have hp (c : ℝ) (hc : 0 < c) : p ∈ cap c := by
    obtain ⟨r, hr, heq⟩ := hq c hc
    have hpr : p = r := by simp [p, ← heq]
    simpa [hpr] using hr
  have hzero (θ : Θ) : _root_.GD.N0230.N0602.d000117 (μ θ) (target θ) p = 0 := by
    apply le_antisymm _ bot_le
    simpa using _root_.GD.N0230.N0586.d003515 (x := _root_.GD.N0230.N0602.d000117 (μ θ) (target θ) p)
      (v := 0) le_rfl (fun c hc => hp c hc θ)
  have hpzero : p = 0 := by
    have hb := hzero θ₀
    rw [href, htarget₀, _root_.GD.N0230.N0602.d000124] at hb
    simp only [zero_sub, norm_neg, ENNReal.ofReal_eq_zero] at hb
    apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖p‖, norm_nonneg p]
  have hae : (fun ω => (0 : _root_.GD.N0230.N0602.d000116 μ₀) ω) =ᵐ[μ θ₁] fun _ => (0 : ℝ) :=
    (hμ θ₁).ae_eq (Lp.coeFn_zero ℝ 2 μ₀)
  have hone : _root_.GD.N0230.N0602.d000117 (μ θ₁) (target θ₁) (0 : _root_.GD.N0230.N0602.d000116 μ₀) = 1 := by
    rw [_root_.GD.N0230.N0602.d000117, htarget₁]
    calc
      (∫⁻ ω, ENNReal.ofReal (((0 : _root_.GD.N0230.N0602.d000116 μ₀) ω - 1) ^ 2) ∂μ θ₁) =
          ∫⁻ _, (1 : ℝ≥0∞) ∂μ θ₁ := by
            apply lintegral_congr_ae
            filter_upwards [hae] with ω hω
            rw [hω]
            norm_num
      _ = 1 := by simp
  have hb := hzero θ₁
  rw [hpzero, hone] at hb
  exact one_ne_zero hb

end
end GD.N0230.N0707

#print axioms _root_.GD.N0230.N0707.d003550
