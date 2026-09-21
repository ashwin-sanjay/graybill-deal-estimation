import GD.Module0584
import GD.Module0495
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.LinearAlgebra.Dimension.Constructions





















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1649
noncomputable section

open MeasureTheory Set Complex
open _root_.GD.N0106.N0428.N0765.N1533
open scoped Topology BigOperators

def d008542 (F : ℂ → ℂ → ℂ) (h : ℝ) (z w : ℂ) : ℂ :=
  F ((h : ℂ) * z) ((h : ℂ) * w)


theorem d008543 (F : ℂ → ℂ → ℂ) (h α β : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1658.d008467 (_root_.GD.N0106.N0428.N0765.N1649.d008542 F h) α β = fun p : ℝ × ℝ =>
      _root_.GD.N0106.N0428.N0765.N1658.d008467 F (h * α) (h * β) (h • p) := by
  funext p
  change F ((h : ℂ) * ((p.1 : ℂ) + (α : ℂ) * I))
      ((h : ℂ) * ((p.2 : ℂ) + (β : ℂ) * I)) =
    F (((h * p.1 : ℝ) : ℂ) + ((h * α : ℝ) : ℂ) * I)
      (((h * p.2 : ℝ) : ℂ) + ((h * β : ℝ) : ℂ) * I)
  congr 1 <;> push_cast <;> ring


theorem d008544 (F : ℂ → ℂ → ℂ) {h : ℝ}
    (hh : 0 < h) (α β : ℝ) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 (_root_.GD.N0106.N0428.N0765.N1649.d008542 F h) α β) (volume.prod volume) ↔
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (h * α) (h * β)) (volume.prod volume) := by
  rw [_root_.GD.N0106.N0428.N0765.N1649.d008543]
  simpa only [Measure.volume_eq_prod] using
    (integrable_comp_smul_iff (volume : Measure (ℝ × ℝ))
      (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (h * α) (h * β)) hh.ne')


theorem d008545 (F : ℂ → ℂ → ℂ) {h : ℝ}
    (hh : 0 < h) (α β : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1658.d008468 (_root_.GD.N0106.N0428.N0765.N1649.d008542 F h) α β =
      (h ^ 2)⁻¹ * _root_.GD.N0106.N0428.N0765.N1658.d008468 F (h * α) (h * β) := by
  unfold _root_.GD.N0106.N0428.N0765.N1658.d008468
  simp_rw [_root_.GD.N0106.N0428.N0765.N1649.d008543]
  have hdim : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  simpa only [hdim, smul_eq_mul, Measure.volume_eq_prod] using
    (Measure.integral_comp_smul_of_nonneg (volume : Measure (ℝ × ℝ))
      (fun p : ℝ × ℝ => ‖_root_.GD.N0106.N0428.N0765.N1658.d008467 F (h * α) (h * β) p‖)
      h (hR := hh.le))

theorem d008546 (F : ℂ → ℂ → ℂ) {h : ℝ}
    (hh : 0 < h) (α β : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1658.d008468 (_root_.GD.N0106.N0428.N0765.N1649.d008542 F h) (α / h) (β / h) =
      (h ^ 2)⁻¹ * _root_.GD.N0106.N0428.N0765.N1658.d008468 F α β := by
  have hα : h * (α / h) = α := by field_simp [hh.ne'] <;> ring
  have hβ : h * (β / h) = β := by field_simp [hh.ne'] <;> ring
  rw [_root_.GD.N0106.N0428.N0765.N1649.d008545 F hh, hα, hβ]


theorem d008547 (F : ℂ → ℂ → ℂ) {h : ℝ}
    (hh : 0 < h) (d : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1650.d008510 (_root_.GD.N0106.N0428.N0765.N1649.d008542 F h) (d / h) =
      (h ^ 2)⁻¹ * _root_.GD.N0106.N0428.N0765.N1650.d008510 F d := by
  have hp : h * (d / h) = d := by field_simp [hh.ne'] <;> ring
  have hm : h * (-(d / h)) = -d := by field_simp [hh.ne'] <;> ring
  unfold _root_.GD.N0106.N0428.N0765.N1650.d008510
  simp_rw [_root_.GD.N0106.N0428.N0765.N1649.d008545 F hh, hm, hp]
  have hscale : 0 ≤ (h ^ 2)⁻¹ := by positivity
  simp_rw [mul_max_of_nonneg _ _ hscale]

theorem d008548 {F : ℂ → ℂ → ℂ} {d h : ℝ}
    (hh : 0 < h)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d)) :
    ContinuousOn (Function.uncurry (_root_.GD.N0106.N0428.N0765.N1649.d008542 F h))
      (_root_.GD.N0106.N0428.N0765.N1533.d005164 (d / h) ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 (d / h)) := by
  have hlin : Continuous (fun p : ℂ × ℂ => ((h : ℂ) * p.1, (h : ℂ) * p.2)) := by
    fun_prop
  exact hc.comp hlin.continuousOn (fun p hp =>
    ⟨_root_.GD.N0106.N0428.N0765.N1554.d007594 hh hp.1,
      _root_.GD.N0106.N0428.N0765.N1554.d007594 hh hp.2⟩)

theorem d008549 {F : ℂ → ℂ → ℂ} {d h : ℝ}
    (hh : 0 < h)
    (hf : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d)) :
    ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 (d / h),
      DifferentiableOn ℂ (fun z : ℂ => _root_.GD.N0106.N0428.N0765.N1649.d008542 F h z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 (d / h)) := by
  intro w hw
  have hlin : Differentiable ℂ (fun z : ℂ => (h : ℂ) * z) := by fun_prop
  exact (hf _ (_root_.GD.N0106.N0428.N0765.N1554.d007594 hh hw)).comp
    hlin.differentiableOn (fun z hz => _root_.GD.N0106.N0428.N0765.N1554.d007595 hh hz)

theorem d008550 {F : ℂ → ℂ → ℂ} {d h : ℝ}
    (hh : 0 < h)
    (hf : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d)) :
    ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 (d / h),
      DifferentiableOn ℂ (fun w : ℂ => _root_.GD.N0106.N0428.N0765.N1649.d008542 F h z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 (d / h)) := by
  intro z hz
  have hlin : Differentiable ℂ (fun w : ℂ => (h : ℂ) * w) := by fun_prop
  exact (hf _ (_root_.GD.N0106.N0428.N0765.N1554.d007594 hh hz)).comp
    hlin.differentiableOn (fun w hw => _root_.GD.N0106.N0428.N0765.N1554.d007595 hh hw)

theorem d008551 {F : ℂ → ℂ → ℂ} {d M h : ℝ} (hh : 0 < h)
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖F z w‖ ≤ M) :
    ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 (d / h), ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 (d / h),
      ‖_root_.GD.N0106.N0428.N0765.N1649.d008542 F h z w‖ ≤ M := by
  intro z hz w hw
  exact hM _ (_root_.GD.N0106.N0428.N0765.N1554.d007594 hh hz)
    _ (_root_.GD.N0106.N0428.N0765.N1554.d007594 hh hw)


theorem d008552 (F : ℂ → ℂ → ℂ) {h : ℝ} (hh : 0 < h)
    (a b : ℝ) (n : ℤ × ℤ) :
    _root_.GD.N0106.N0428.N0765.N1649.d008542 F h ((a / h + (n.1 : ℝ) : ℝ) : ℂ)
      ((b / h + (n.2 : ℝ) : ℝ) : ℂ) =
      F ((a + h * (n.1 : ℝ) : ℝ) : ℂ) ((b + h * (n.2 : ℝ) : ℝ) : ℂ) := by
  have hpoint (x : ℝ) (k : ℤ) : h * (x / h + (k : ℝ)) = x + h * (k : ℝ) := by
    field_simp [hh.ne'] <;> ring
  simp only [_root_.GD.N0106.N0428.N0765.N1649.d008542, ← Complex.ofReal_mul, hpoint]



theorem d008553 {F : ℂ → ℂ → ℂ} {d M h : ℝ}
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
    (a b : ℝ) : Summable (fun n : ℤ × ℤ =>
      F ((a + h * (n.1 : ℝ) : ℝ) : ℂ) ((b + h * (n.2 : ℝ) : ℝ) : ℂ)) := by
  have hp : h * (d / h) = d := by field_simp [hh.ne'] <;> ring
  have hm : h * (-(d / h)) = -d := by field_simp [hh.ne'] <;> ring
  have hmm' : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 (_root_.GD.N0106.N0428.N0765.N1649.d008542 F h) (-(d / h)) (-(d / h)))
      (volume.prod volume) := by
    apply (_root_.GD.N0106.N0428.N0765.N1649.d008544 F hh _ _).2
    simpa only [hm] using hmm
  have hmp' : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 (_root_.GD.N0106.N0428.N0765.N1649.d008542 F h) (-(d / h)) (d / h))
      (volume.prod volume) := by
    apply (_root_.GD.N0106.N0428.N0765.N1649.d008544 F hh _ _).2
    simpa only [hm, hp] using hmp
  have hpm' : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 (_root_.GD.N0106.N0428.N0765.N1649.d008542 F h) (d / h) (-(d / h)))
      (volume.prod volume) := by
    apply (_root_.GD.N0106.N0428.N0765.N1649.d008544 F hh _ _).2
    simpa only [hp, hm] using hpm
  have hpp' : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 (_root_.GD.N0106.N0428.N0765.N1649.d008542 F h) (d / h) (d / h))
      (volume.prod volume) := by
    apply (_root_.GD.N0106.N0428.N0765.N1649.d008544 F hh _ _).2
    simpa only [hp] using hpp
  have hs := _root_.GD.N0106.N0428.N0765.N1650.d008513
    (div_pos hd hh) (_root_.GD.N0106.N0428.N0765.N1649.d008548 hh hc)
    (_root_.GD.N0106.N0428.N0765.N1649.d008549 hh hfA) (_root_.GD.N0106.N0428.N0765.N1649.d008550 hh hfB)
    (_root_.GD.N0106.N0428.N0765.N1649.d008551 hh hM) hmm' hmp' hpm' hpp' (a / h) (b / h)
  simpa only [_root_.GD.N0106.N0428.N0765.N1649.d008552 F hh a b] using hs

end
end GD.N0106.N0428.N0765.N1649

#print axioms _root_.GD.N0106.N0428.N0765.N1649.d008543
#print axioms _root_.GD.N0106.N0428.N0765.N1649.d008544
#print axioms _root_.GD.N0106.N0428.N0765.N1649.d008545
#print axioms _root_.GD.N0106.N0428.N0765.N1649.d008547
#print axioms _root_.GD.N0106.N0428.N0765.N1649.d008553
