import GD.Module0581
import GD.Module0576




















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1647
noncomputable section

open MeasureTheory Set Complex Filter TopologicalSpace
open _root_.GD.N0106.N0428.N0765.N1533 _root_.GD.N0106.N0428.N0765.N1532 _root_.GD.N0106.N0428.N0765.N1642 _root_.GD.N0106.N0428.N0765.N1637
open scoped Topology BigOperators

def d008502 (F : ℂ → ℝ → ℂ) (x : ℝ) : ℝ :=
  ∫ b : ℝ, ‖F (x : ℂ) b‖

def d008503 (F : ℂ → ℝ → ℂ) (R t : ℝ) : ℝ :=
  ∫ b : ℝ, _root_.GD.N0106.N0428.N0765.N1642.d008475 F R (t, b)

theorem d008504 (F : ℂ → ℝ → ℂ) (R t : ℝ) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1647.d008503 F R t :=
  integral_nonneg (fun b => _root_.GD.N0106.N0428.N0765.N1642.d008476 F R (t, b))

theorem d008505 {F : ℂ → ℝ → ℂ} {d R B : ℝ}
    (hR : 0 ≤ R) (hRd : R ≤ d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ (univ : Set ℝ)))
    (hslice : ∀ y : ℝ, |y| ≤ R →
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F y) (volume.prod volume) ∧ _root_.GD.N0106.N0428.N0765.N1658.d008463 F y ≤ B) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1647.d008503 F R) ∧ (∫ t : ℝ, _root_.GD.N0106.N0428.N0765.N1647.d008503 F R t) ≤ B := by
  obtain ⟨hi, hb⟩ := _root_.GD.N0106.N0428.N0765.N1642.d008477 hR hRd hc hslice
  refine ⟨hi.integral_prod_left, ?_⟩
  exact (integral_prod (_root_.GD.N0106.N0428.N0765.N1642.d008475 F R) hi).symm.le.trans hb



theorem d008506 {F : ℂ → ℝ → ℂ} {d R B : ℝ}
    (hR : 0 < R) (hRd : R < d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ (univ : Set ℝ)))
    (hf : ∀ b : ℝ, DifferentiableOn ℂ (fun z : ℂ => F z b) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hslice : ∀ y : ℝ, |y| ≤ R →
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F y) (volume.prod volume) ∧ _root_.GD.N0106.N0428.N0765.N1658.d008463 F y ≤ B)
    (x : ℝ) :
    ∀ᵐ t : ℝ, |x - t| ≤ R / 2 → _root_.GD.N0106.N0428.N0765.N1647.d008502 F x ≤ 2 * _root_.GD.N0106.N0428.N0765.N1647.d008503 F R t := by
  have hi := _root_.GD.N0106.N0428.N0765.N1642.d008478 hR.le hRd.le hc hslice
  have hrow := _root_.GD.N0106.N0428.N0765.N1642.d008481 hR hRd hc hf hslice x
  have hcF (b : ℝ) : ContinuousOn (fun z : ℂ => F z b) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d) := by
    have hmap : Continuous (fun z : ℂ => (z, b)) := by fun_prop
    exact hc.comp hmap.continuousOn (fun z hz => ⟨hz, mem_univ b⟩)
  filter_upwards [hi.prod_right_ae] with t ht
  intro hxt
  calc
    _root_.GD.N0106.N0428.N0765.N1647.d008502 F x ≤ ∫ b : ℝ, 2 * _root_.GD.N0106.N0428.N0765.N1642.d008475 F R (t, b) := by
      apply integral_mono_ae hrow.norm (ht.const_mul 2)
      exact ae_of_all _ (fun b =>
        _root_.GD.N0106.N0428.N0765.N1532.d007588 hR hRd (hcF b) (hf b) hxt)
    _ = 2 * _root_.GD.N0106.N0428.N0765.N1647.d008503 F R t := integral_const_mul _ _

theorem d008507 {F : ℂ → ℝ → ℂ} {x : ℝ}
    (hrow : Integrable (fun b : ℝ => F (x : ℂ) b))
    {u : ℝ → ℂ} (hu : Measurable u) (hunorm : ∀ b : ℝ, ‖u b‖ ≤ 1) :
    ‖∫ b : ℝ, u b * F (x : ℂ) b‖ ≤ _root_.GD.N0106.N0428.N0765.N1647.d008502 F x := by
  have hbound (b : ℝ) : ‖u b * F (x : ℂ) b‖ ≤ ‖F (x : ℂ) b‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hunorm b) (norm_nonneg _)).trans_eq (one_mul _)
  have hi : Integrable (fun b : ℝ => u b * F (x : ℂ) b) :=
    Integrable.mono' hrow.norm (hu.aestronglyMeasurable.mul hrow.aestronglyMeasurable)
      (ae_of_all _ hbound)
  exact (norm_integral_le_integral_norm _).trans
    (integral_mono_ae hi.norm hrow.norm (ae_of_all _ hbound))



theorem d008508 {F : ℂ → ℝ → ℂ} {d R B : ℝ}
    (hR : 0 < R) (hRd : R < d)
    (hc : ContinuousOn (Function.uncurry F) (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ (univ : Set ℝ)))
    (hf : ∀ b : ℝ, DifferentiableOn ℂ (fun z : ℂ => F z b) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hslice : ∀ y : ℝ, |y| ≤ R →
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 F y) (volume.prod volume) ∧ _root_.GD.N0106.N0428.N0765.N1658.d008463 F y ≤ B)
    {u : ℝ → ℂ} (hu : Measurable u) (hunorm : ∀ b : ℝ, ‖u b‖ ≤ 1)
    (K : Compacts ℝ) :
    Summable (fun n : ℤ =>
      ‖((⟨fun x : ℝ => ∫ b : ℝ, u b * F (x : ℂ) b,
          _root_.GD.N0106.N0428.N0765.N1642.d008482 hR hRd hc hf hslice hu hunorm⟩ : C(ℝ, ℂ)).comp
        (ContinuousMap.addRight (n : ℝ))).restrict K‖) := by
  let δ : ℝ := min (R / 8) (1 / 8)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδR : δ ≤ R / 8 := min_le_left _ _
  have hδ1 : δ ≤ 1 / 8 := min_le_right _ _
  apply _root_.GD.N0106.N0428.N0765.N1637.d008449 (A := _root_.GD.N0106.N0428.N0765.N1647.d008503 F R) hδ
    (by linarith) (_root_.GD.N0106.N0428.N0765.N1647.d008505 hR.le hRd.le hc hslice).1
    (_root_.GD.N0106.N0428.N0765.N1647.d008504 F R)
  intro x
  have hw := _root_.GD.N0106.N0428.N0765.N1647.d008507
    (_root_.GD.N0106.N0428.N0765.N1642.d008481 hR hRd hc hf hslice x) hu hunorm
  filter_upwards [_root_.GD.N0106.N0428.N0765.N1647.d008506 hR hRd hc hf hslice x] with t ht
  intro hxt
  exact hw.trans (ht (hxt.trans (by linarith)))






theorem d008509 {F : Bool → ℂ → ℝ → ℂ}
    {g : ℝ → ℤ → ℂ} {d R k : ℝ} {B : Bool → ℝ}
    (hR : 0 < R) (hRd : R < d) (hk : 0 < k)
    (hc : ∀ s : Bool, ContinuousOn (Function.uncurry (F s))
      (_root_.GD.N0106.N0428.N0765.N1533.d005164 d ×ˢ (univ : Set ℝ)))
    (hf : ∀ s : Bool, ∀ b : ℝ,
      DifferentiableOn ℂ (fun z : ℂ => F s z b) (_root_.GD.N0106.N0428.N0765.N1533.d005163 d))
    (hslice : ∀ s : Bool, ∀ y : ℝ, |y| ≤ R →
      Integrable (_root_.GD.N0106.N0428.N0765.N1658.d008462 (F s) y) (volume.prod volume) ∧
        _root_.GD.N0106.N0428.N0765.N1658.d008463 (F s) y ≤ B s)
    (hrow : ∀ x : ℝ, ∀ n : ℤ, ‖g x n‖ ≤ Real.exp (-k * |(n : ℝ)|) *
      (_root_.GD.N0106.N0428.N0765.N1647.d008502 (F false) x + _root_.GD.N0106.N0428.N0765.N1647.d008502 (F true) x))
    (a : ℝ) : Summable (fun p : ℤ × ℤ => g (a + (p.1 : ℝ)) p.2) := by
  let δ : ℝ := min (R / 8) (1 / 8)
  let A : ℝ → ℝ := fun t => _root_.GD.N0106.N0428.N0765.N1647.d008503 (F false) R t + _root_.GD.N0106.N0428.N0765.N1647.d008503 (F true) R t
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδR : δ ≤ R / 8 := min_le_left _ _
  have hδ1 : δ ≤ 1 / 8 := min_le_right _ _
  have hA : Integrable A :=
    (_root_.GD.N0106.N0428.N0765.N1647.d008505 hR.le hRd.le (hc false) (hslice false)).1.add
      (_root_.GD.N0106.N0428.N0765.N1647.d008505 hR.le hRd.le (hc true) (hslice true)).1
  have hA0 (t : ℝ) : 0 ≤ A t :=
    add_nonneg (_root_.GD.N0106.N0428.N0765.N1647.d008504 (F false) R t) (_root_.GD.N0106.N0428.N0765.N1647.d008504 (F true) R t)
  apply _root_.GD.N0106.N0428.N0765.N1637.d008451 hδ (by linarith) hA hA0 hk
  intro n x
  filter_upwards
    [_root_.GD.N0106.N0428.N0765.N1647.d008506 hR hRd (hc false) (hf false) (hslice false) x,
     _root_.GD.N0106.N0428.N0765.N1647.d008506 hR hRd (hc true) (hf true) (hslice true) x]
    with t hm hp
  intro hxt
  have ht : |x - t| ≤ R / 2 := hxt.trans (by linarith)
  have hmass : _root_.GD.N0106.N0428.N0765.N1647.d008502 (F false) x + _root_.GD.N0106.N0428.N0765.N1647.d008502 (F true) x ≤ 2 * A t := by
    exact (add_le_add (hm ht) (hp ht)).trans_eq (by dsimp only [A]; ring)
  exact (hrow x n).trans ((mul_le_mul_of_nonneg_left hmass (Real.exp_pos _).le).trans_eq
    (by ring))

end
end GD.N0106.N0428.N0765.N1647

#print axioms _root_.GD.N0106.N0428.N0765.N1647.d008506
#print axioms _root_.GD.N0106.N0428.N0765.N1647.d008508
#print axioms _root_.GD.N0106.N0428.N0765.N1647.d008509
