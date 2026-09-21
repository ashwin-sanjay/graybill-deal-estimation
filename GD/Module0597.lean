import Mathlib

open MeasureTheory Set
open scoped Interval

namespace GD.N0118


noncomputable def d008580 (c w x : ℝ) : ℝ :=
  (x - (c - w)) / w ^ 2


noncomputable def d008581 (c w x : ℝ) : ℝ :=
  ((c + w) - x) / w ^ 2







noncomputable def d008582 (c w x : ℝ) : ℝ :=
  (Ioc (c - w) c).indicator (_root_.GD.N0118.d008580 c w) x
    + (Ioc c (c + w)).indicator (_root_.GD.N0118.d008581 c w) x


noncomputable def d008583 (c₁ c₂ w : ℝ) (p : ℝ × ℝ) : ℝ :=
  _root_.GD.N0118.d008582 c₁ w p.1 * _root_.GD.N0118.d008582 c₂ w p.2

lemma d008584 (c w : ℝ) : Measurable (_root_.GD.N0118.d008580 c w) := by
  unfold _root_.GD.N0118.d008580
  fun_prop

lemma d008585 (c w : ℝ) : Measurable (_root_.GD.N0118.d008581 c w) := by
  unfold _root_.GD.N0118.d008581
  fun_prop

lemma d008586 (c w : ℝ) : Continuous (_root_.GD.N0118.d008580 c w) := by
  unfold _root_.GD.N0118.d008580
  fun_prop

lemma d008587 (c w : ℝ) : Continuous (_root_.GD.N0118.d008581 c w) := by
  unfold _root_.GD.N0118.d008581
  fun_prop

lemma d008588 (c w : ℝ) : Measurable (_root_.GD.N0118.d008582 c w) := by
  exact
    ((_root_.GD.N0118.d008584 c w).indicator measurableSet_Ioc).add
      ((_root_.GD.N0118.d008585 c w).indicator measurableSet_Ioc)

lemma d008589 (c w : ℝ) : Integrable (_root_.GD.N0118.d008582 c w) := by
  unfold _root_.GD.N0118.d008582
  apply Integrable.add
  · exact
      (_root_.GD.N0118.d008586 c w).integrableOn_Ioc.integrable_indicator measurableSet_Ioc
  · exact
      (_root_.GD.N0118.d008587 c w).integrableOn_Ioc.integrable_indicator measurableSet_Ioc

lemma d008590 (c₁ c₂ w : ℝ) : Measurable (_root_.GD.N0118.d008583 c₁ c₂ w) := by
  exact
    ((_root_.GD.N0118.d008588 c₁ w).comp measurable_fst).mul
      ((_root_.GD.N0118.d008588 c₂ w).comp measurable_snd)

lemma d008591 (c₁ c₂ w : ℝ) :
    Integrable (_root_.GD.N0118.d008583 c₁ c₂ w) (volume.prod volume) := by
  exact (_root_.GD.N0118.d008589 c₁ w).mul_prod (_root_.GD.N0118.d008589 c₂ w)

lemma d008592 (c w : ℝ) (hw : 0 < w) :
    ∫ x in Ioc (c - w) c, _root_.GD.N0118.d008580 c w x = (1 / 2 : ℝ) := by
  rw [← intervalIntegral.integral_of_le (by linarith : c - w ≤ c)]
  unfold _root_.GD.N0118.d008580
  rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ ↦ x / w ^ 2) (c - w)]
  simp only [sub_self, sub_sub_cancel]
  rw [intervalIntegral.integral_div, integral_id]
  field_simp [hw.ne']
  ring

lemma d008593 (c w : ℝ) (hw : 0 < w) :
    ∫ x in Ioc c (c + w), _root_.GD.N0118.d008581 c w x = (1 / 2 : ℝ) := by
  rw [← intervalIntegral.integral_of_le (by linarith : c ≤ c + w)]
  unfold _root_.GD.N0118.d008581
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x / w ^ 2) (c + w)]
  simp only [sub_self, add_sub_cancel_left]
  rw [intervalIntegral.integral_div, integral_id]
  field_simp [hw.ne']
  ring

theorem d008594 (c w : ℝ) (hw : 0 < w) :
    ∫ x, _root_.GD.N0118.d008582 c w x = 1 := by
  unfold _root_.GD.N0118.d008582
  rw [integral_add
      ((_root_.GD.N0118.d008586 c w).integrableOn_Ioc.integrable_indicator measurableSet_Ioc)
      ((_root_.GD.N0118.d008587 c w).integrableOn_Ioc.integrable_indicator measurableSet_Ioc),
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc,
    _root_.GD.N0118.d008592 c w hw, _root_.GD.N0118.d008593 c w hw]
  norm_num

lemma d008595 (c w x : ℝ) :
    _root_.GD.N0118.d008582 c w x ^ 2 =
      (Ioc (c - w) c).indicator (fun y ↦ _root_.GD.N0118.d008580 c w y ^ 2) x
        + (Ioc c (c + w)).indicator (fun y ↦ _root_.GD.N0118.d008581 c w y ^ 2) x := by
  by_cases hL : x ∈ Ioc (c - w) c
  · have hR : x ∉ Ioc c (c + w) := by
      intro hx
      linarith [hL.2, hx.1]
    simp [_root_.GD.N0118.d008582, hL, hR]
  · by_cases hR : x ∈ Ioc c (c + w)
    · simp [_root_.GD.N0118.d008582, hL, hR]
    · simp [_root_.GD.N0118.d008582, hL, hR]

lemma d008596 (c w : ℝ) :
    Integrable (fun x ↦ _root_.GD.N0118.d008582 c w x ^ 2) := by
  let fL : ℝ → ℝ := fun x ↦ _root_.GD.N0118.d008580 c w x ^ 2
  let fR : ℝ → ℝ := fun x ↦ _root_.GD.N0118.d008581 c w x ^ 2
  have hL : Integrable ((Ioc (c - w) c).indicator fL) :=
    ((_root_.GD.N0118.d008586 c w).pow 2).integrableOn_Ioc.integrable_indicator measurableSet_Ioc
  have hR : Integrable ((Ioc c (c + w)).indicator fR) :=
    ((_root_.GD.N0118.d008587 c w).pow 2).integrableOn_Ioc.integrable_indicator measurableSet_Ioc
  rw [show (fun x ↦ _root_.GD.N0118.d008582 c w x ^ 2) =
      fun x ↦ (Ioc (c - w) c).indicator fL x
        + (Ioc c (c + w)).indicator fR x by
      funext x
      exact _root_.GD.N0118.d008595 c w x]
  exact hL.add hR

lemma d008597 (c w : ℝ) (hw : 0 < w) :
    ∫ x in Ioc (c - w) c, _root_.GD.N0118.d008580 c w x ^ 2 = 1 / (3 * w) := by
  rw [← intervalIntegral.integral_of_le (by linarith : c - w ≤ c)]
  unfold _root_.GD.N0118.d008580
  rw [show (fun x : ℝ ↦ ((x - (c - w)) / w ^ 2) ^ 2) =
      fun x ↦ (x - (c - w)) ^ 2 / w ^ 4 by
      funext x
      ring]
  rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ ↦ x ^ 2 / w ^ 4) (c - w)]
  simp only [sub_self, sub_sub_cancel]
  rw [intervalIntegral.integral_div, integral_pow]
  field_simp [hw.ne']
  ring

lemma d008598 (c w : ℝ) (hw : 0 < w) :
    ∫ x in Ioc c (c + w), _root_.GD.N0118.d008581 c w x ^ 2 = 1 / (3 * w) := by
  rw [← intervalIntegral.integral_of_le (by linarith : c ≤ c + w)]
  unfold _root_.GD.N0118.d008581
  rw [show (fun x : ℝ ↦ (((c + w) - x) / w ^ 2) ^ 2) =
      fun x ↦ ((c + w) - x) ^ 2 / w ^ 4 by
      funext x
      ring]
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ 2 / w ^ 4) (c + w)]
  simp only [sub_self, add_sub_cancel_left]
  rw [intervalIntegral.integral_div, integral_pow]
  field_simp [hw.ne']
  ring

theorem d008599 (c w : ℝ) (hw : 0 < w) :
    ∫ x, _root_.GD.N0118.d008582 c w x ^ 2 = 2 / (3 * w) := by
  rw [show (fun x ↦ _root_.GD.N0118.d008582 c w x ^ 2) =
      fun x ↦ (Ioc (c - w) c).indicator (fun y ↦ _root_.GD.N0118.d008580 c w y ^ 2) x
        + (Ioc c (c + w)).indicator (fun y ↦ _root_.GD.N0118.d008581 c w y ^ 2) x by
      funext x
      exact _root_.GD.N0118.d008595 c w x]
  rw [integral_add
      (((_root_.GD.N0118.d008586 c w).pow 2).integrableOn_Ioc.integrable_indicator
        measurableSet_Ioc)
      (((_root_.GD.N0118.d008587 c w).pow 2).integrableOn_Ioc.integrable_indicator
        measurableSet_Ioc),
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc,
    _root_.GD.N0118.d008597 c w hw, _root_.GD.N0118.d008598 c w hw]
  ring

lemma d008600 (c₁ c₂ w : ℝ) :
    Integrable (fun p ↦ _root_.GD.N0118.d008583 c₁ c₂ w p ^ 2) (volume.prod volume) := by
  have h :=
    (_root_.GD.N0118.d008596 c₁ w).mul_prod (_root_.GD.N0118.d008596 c₂ w)
  have hfun : (fun p ↦ _root_.GD.N0118.d008583 c₁ c₂ w p ^ 2) =
      fun p ↦ _root_.GD.N0118.d008582 c₁ w p.1 ^ 2 * _root_.GD.N0118.d008582 c₂ w p.2 ^ 2 := by
    funext p
    simp [_root_.GD.N0118.d008583, mul_pow]
  rw [hfun]
  simpa only using h

theorem d008601 (c₁ c₂ w : ℝ) (hw : 0 < w) :
    ∫ p, _root_.GD.N0118.d008583 c₁ c₂ w p ∂(volume.prod volume) = 1 := by
  unfold _root_.GD.N0118.d008583
  rw [integral_prod_mul, _root_.GD.N0118.d008594 c₁ w hw, _root_.GD.N0118.d008594 c₂ w hw]
  norm_num

theorem d008602 (c₁ c₂ w : ℝ) (hw : 0 < w) :
    ∫ p, _root_.GD.N0118.d008583 c₁ c₂ w p ^ 2 ∂(volume.prod volume) = 4 / (9 * w ^ 2) := by
  have hfun : (fun p ↦ _root_.GD.N0118.d008583 c₁ c₂ w p ^ 2) =
      fun p ↦ _root_.GD.N0118.d008582 c₁ w p.1 ^ 2 * _root_.GD.N0118.d008582 c₂ w p.2 ^ 2 := by
    funext p
    simp [_root_.GD.N0118.d008583, mul_pow]
  rw [hfun]
  rw [integral_prod_mul
      (μ := volume) (ν := volume)
      (fun x : ℝ ↦ _root_.GD.N0118.d008582 c₁ w x ^ 2) (fun y : ℝ ↦ _root_.GD.N0118.d008582 c₂ w y ^ 2),
    _root_.GD.N0118.d008599 c₁ w hw, _root_.GD.N0118.d008599 c₂ w hw]
  field_simp [hw.ne']
  ring

end GD.N0118
