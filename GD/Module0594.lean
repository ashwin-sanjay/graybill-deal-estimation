import GD.Module0593
import GD.Module0588





















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1648
noncomputable section

open MeasureTheory Set Complex
open _root_.GD.N0106.N0428.N0765.N1533
open scoped Topology FourierTransform BigOperators

theorem d008569 (h x y : ℝ) :
    (h : ℂ) * _root_.GD.N0106.N0428.N0765.N1550.d005473 x y = _root_.GD.N0106.N0428.N0765.N1550.d005473 (h * x) (h * y) := by
  unfold _root_.GD.N0106.N0428.N0765.N1550.d005473
  push_cast
  ring

theorem d008570 (F : ℂ → ℂ → ℂ) (h : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1658.d008467 (_root_.GD.N0106.N0428.N0765.N1649.d008542 F h) 0 0 =
      _root_.GD.N0106.N0428.N0765.N1652.d005822 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) h := by
  rw [_root_.GD.N0106.N0428.N0765.N1649.d008543]
  simp only [mul_zero]
  funext p
  rcases p with ⟨a, b⟩
  rfl



theorem d008571 {F : ℂ → ℂ → ℂ} {d h : ℝ} (hh : 0 < h)
    (hdecay : ∀ β : ℝ, |β| ≤ d → ∀ b : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ R : ℝ, ∀ a s : ℝ,
        R ≤ |a| → |s| ≤ d → ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b β)‖ ≤ ε) :
    ∀ β : ℝ, |β| ≤ d / h → ∀ b : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ R : ℝ, ∀ a s : ℝ, R ≤ |a| → |s| ≤ d / h →
        ‖_root_.GD.N0106.N0428.N0765.N1649.d008542 F h (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b β)‖ ≤ ε := by
  intro β hβ b ε hε
  have hβ' : |h * β| ≤ d := by
    simpa only [abs_mul, abs_of_pos hh, mul_comm] using (le_div_iff₀ hh).mp hβ
  obtain ⟨R, hR⟩ := hdecay (h * β) hβ' (h * b) ε hε
  refine ⟨R / h, ?_⟩
  intro a s ha hs
  have ha' : R ≤ |h * a| := by
    simpa only [abs_mul, abs_of_pos hh, mul_comm] using (div_le_iff₀ hh).mp ha
  have hs' : |h * s| ≤ d := by
    simpa only [abs_mul, abs_of_pos hh, mul_comm] using (le_div_iff₀ hh).mp hs
  simpa only [_root_.GD.N0106.N0428.N0765.N1649.d008542, _root_.GD.N0106.N0428.N0765.N1648.d008569] using hR (h * a) (h * s) ha' hs'

theorem d008572 {F : ℂ → ℂ → ℂ} {d h : ℝ} (hh : 0 < h)
    (hdecay : ∀ a : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ b s : ℝ,
      R ≤ |b| → |s| ≤ d → ‖F (a : ℂ) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε) :
    ∀ a : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ b s : ℝ,
      R ≤ |b| → |s| ≤ d / h →
        ‖_root_.GD.N0106.N0428.N0765.N1649.d008542 F h (a : ℂ) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε := by
  intro a ε hε
  obtain ⟨R, hR⟩ := hdecay (h * a) ε hε
  refine ⟨R / h, ?_⟩
  intro b s hb hs
  have hb' : R ≤ |h * b| := by
    simpa only [abs_mul, abs_of_pos hh, mul_comm] using (div_le_iff₀ hh).mp hb
  have hs' : |h * s| ≤ d := by
    simpa only [abs_mul, abs_of_pos hh, mul_comm] using (le_div_iff₀ hh).mp hs
  simpa only [_root_.GD.N0106.N0428.N0765.N1649.d008542, _root_.GD.N0106.N0428.N0765.N1648.d008569, ← Complex.ofReal_mul] using
    hR (h * b) (h * s) hb' hs'



theorem d008573 {F : ℂ → ℂ → ℂ} {d M h : ℝ}
    (hd : 0 < d) (hh : 0 < h)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfA : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hfB : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖F z w‖ ≤ M)
    (hmm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (-d) (-d)) (volume.prod volume))
    (hmp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (-d) d) (volume.prod volume))
    (hpm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F d (-d)) (volume.prod volume))
    (hpp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F d d) (volume.prod volume))
    (hdecayA : ∀ β : ℝ, |β| ≤ d → ∀ b : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ R : ℝ, ∀ a s : ℝ,
        R ≤ |a| → |s| ≤ d → ‖F (_root_.GD.N0106.N0428.N0765.N1550.d005473 a s) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b β)‖ ≤ ε)
    (hdecayB : ∀ a : ℝ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ b s : ℝ,
      R ≤ |b| → |s| ≤ d → ‖F (a : ℂ) (_root_.GD.N0106.N0428.N0765.N1550.d005473 b s)‖ ≤ ε)
    (x y : ℝ) :
    h ^ 2 • (∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0
      (x + h * (p.1 : ℝ), y + h * (p.2 : ℝ))) =
      ∑' p : ℤ × ℤ, _root_.GD.N0106.N0428.N0765.N1652.d005817 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0)
        (p.1 / h) (p.2 / h) * fourier p.1 ((x / h : ℝ) : UnitAddCircle) *
          fourier p.2 ((y / h : ℝ) : UnitAddCircle) := by
  have hp : h * (d / h) = d := by field_simp [hh.ne'] <;> ring
  have hm : h * (-(d / h)) = -d := by field_simp [hh.ne'] <;> ring
  have hmm' : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 (_root_.GD.N0106.N0428.N0765.N1649.d008542 F h)
      (-(d / h)) (-(d / h))) (volume.prod volume) := by
    apply (_root_.GD.N0106.N0428.N0765.N1649.d008544 F hh _ _).2
    simpa only [hm] using hmm
  have hmp' : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 (_root_.GD.N0106.N0428.N0765.N1649.d008542 F h)
      (-(d / h)) (d / h)) (volume.prod volume) := by
    apply (_root_.GD.N0106.N0428.N0765.N1649.d008544 F hh _ _).2
    simpa only [hm, hp] using hmp
  have hpm' : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 (_root_.GD.N0106.N0428.N0765.N1649.d008542 F h)
      (d / h) (-(d / h))) (volume.prod volume) := by
    apply (_root_.GD.N0106.N0428.N0765.N1649.d008544 F hh _ _).2
    simpa only [hp, hm] using hpm
  have hpp' : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 (_root_.GD.N0106.N0428.N0765.N1649.d008542 F h)
      (d / h) (d / h)) (volume.prod volume) := by
    apply (_root_.GD.N0106.N0428.N0765.N1649.d008544 F hh _ _).2
    simpa only [hp] using hpp
  have hunit := _root_.GD.N0106.N0428.N0765.N1660.d008568 (div_pos hd hh)
    (_root_.GD.N0106.N0428.N0765.N1649.d008548 hh hc)
    (_root_.GD.N0106.N0428.N0765.N1649.d008549 hh hfA)
    (_root_.GD.N0106.N0428.N0765.N1649.d008550 hh hfB)
    (_root_.GD.N0106.N0428.N0765.N1649.d008551 hh hM) hmm' hmp' hpm' hpp'
    (_root_.GD.N0106.N0428.N0765.N1648.d008571 hh hdecayA) (_root_.GD.N0106.N0428.N0765.N1648.d008572 hh hdecayB) (x / h) (y / h)
  simp_rw [_root_.GD.N0106.N0428.N0765.N1648.d008570] at hunit
  have hpoint (p : ℤ × ℤ) :
      _root_.GD.N0106.N0428.N0765.N1652.d005822 (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0) h
        (x / h + (p.1 : ℝ), y / h + (p.2 : ℝ)) =
      _root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0 (x + h * (p.1 : ℝ), y + h * (p.2 : ℝ)) := by
    unfold _root_.GD.N0106.N0428.N0765.N1652.d005822
    apply congrArg (_root_.GD.N0106.N0428.N0765.N1658.d008467 F 0 0)
    apply Prod.ext <;> dsimp <;> field_simp [hh.ne'] <;> ring
  simp_rw [hpoint] at hunit
  rw [hunit, ← tsum_const_smul'']
  apply tsum_congr
  intro p
  rw [← smul_mul_assoc, ← smul_mul_assoc, _root_.GD.N0106.N0428.N0765.N1652.d005825 _ hh]

end
end GD.N0106.N0428.N0765.N1648

#print axioms _root_.GD.N0106.N0428.N0765.N1648.d008571
#print axioms _root_.GD.N0106.N0428.N0765.N1648.d008572
#print axioms _root_.GD.N0106.N0428.N0765.N1648.d008573
