import GD.Module0582



















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1650
noncomputable section

open MeasureTheory Set Complex
open _root_.GD.N0106.N0428.N0765.N1533
open scoped Topology BigOperators

def d008510 (F : ℂ → ℂ → ℂ) (d : ℝ) : ℝ :=
  max (max (_root_.GD.N0106.N0428.N0765.N1658.d008468 F (-d) (-d)) (_root_.GD.N0106.N0428.N0765.N1658.d008468 F (-d) d))
    (max (_root_.GD.N0106.N0428.N0765.N1658.d008468 F d (-d)) (_root_.GD.N0106.N0428.N0765.N1658.d008468 F d d))

theorem d008511 {d y u v B : ℝ} (hd : 0 < d) (hy : |y| ≤ d)
    (hu : u ≤ B) (hv : v ≤ B) :
    ((d - y) / (2 * d)) * u + ((d + y) / (2 * d)) * v ≤ B := by
  have hm : 0 ≤ (d - y) / (2 * d) :=
    div_nonneg (by linarith [(abs_le.mp hy).2]) (by positivity)
  have hp : 0 ≤ (d + y) / (2 * d) :=
    div_nonneg (by linarith [(abs_le.mp hy).1]) (by positivity)
  have hs : (d - y) / (2 * d) + (d + y) / (2 * d) = 1 := by
    field_simp [hd.ne']
    ring
  calc
    _ ≤ ((d - y) / (2 * d)) * B + ((d + y) / (2 * d)) * B :=
      add_le_add (mul_le_mul_of_nonneg_left hu hm) (mul_le_mul_of_nonneg_left hv hp)
    _ = B := by rw [← add_mul, hs, one_mul]

theorem d008512 {F : ℂ → ℂ → ℂ} {d M α β : ℝ}
    (hd : 0 < d) (hα : |α| ≤ d) (hβ : |β| ≤ d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ _root_.GD.N0106.N0428.N0765.N1533.d005164 d))
    (hfA : ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun z : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hfB : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d,
      DifferentiableOn ℂ (fun w : ℂ => F z w) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hM : ∀ z ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ∀ w ∈ _root_.GD.N0106.N0428.N0765.N1533.d005164 d, ‖F z w‖ ≤ M)
    (hmm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (-d) (-d)) (volume.prod volume))
    (hmp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F (-d) d) (volume.prod volume))
    (hpm : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F d (-d)) (volume.prod volume))
    (hpp : Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F d d) (volume.prod volume)) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008467 F α β) (volume.prod volume) ∧
      _root_.GD.N0106.N0428.N0765.N1658.d008468 F α β ≤ _root_.GD.N0106.N0428.N0765.N1650.d008510 F d := by
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
  obtain ⟨hi, hb⟩ := _root_.GD.N0106.N0428.N0765.N1658.d008470
    hd hα hβ hcA hfA hcB hfB hM hmeas hmm hmp hpm hpp
  refine ⟨hi, hb.trans ?_⟩
  unfold _root_.GD.N0106.N0428.N0765.N1650.d008510
  apply _root_.GD.N0106.N0428.N0765.N1650.d008511 hd hα
  · apply _root_.GD.N0106.N0428.N0765.N1650.d008511 hd hβ
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans (le_max_left _ _)
  · apply _root_.GD.N0106.N0428.N0765.N1650.d008511 hd hβ
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)




theorem d008513 {F : ℂ → ℂ → ℂ} {d M : ℝ}
    (hd : 0 < d)
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
      F ((a + (n.1 : ℝ) : ℝ) : ℂ) ((b + (n.2 : ℝ) : ℝ) : ℂ)) := by
  apply _root_.GD.N0106.N0428.N0765.N1645.d008501
    (R := d / 2) (B := _root_.GD.N0106.N0428.N0765.N1650.d008510 F d) (by positivity) (by linarith)
    hc hfA hfB
  intro α β hα hβ
  exact _root_.GD.N0106.N0428.N0765.N1650.d008512 hd
    (hα.trans (by linarith)) (hβ.trans (by linarith))
    hc hfA hfB hM hmm hmp hpm hpp

end
end GD.N0106.N0428.N0765.N1650

#print axioms _root_.GD.N0106.N0428.N0765.N1650.d008512
#print axioms _root_.GD.N0106.N0428.N0765.N1650.d008513
