import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic




















set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set intervalIntegral

namespace GD.N0106.N0428.N0765.N1662

variable {a b : ℝ} {w f g : ℝ → ℝ}


theorem d005828 (hab : a < b)
    (hw : ContinuousOn w (Icc a b)) (hwnn : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hW : 0 < ∫ x in a..b, w x)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfm : MonotoneOn f (Icc a b)) (hgm : MonotoneOn g (Icc a b)) :
    (∫ x in a..b, f x * w x) * (∫ x in a..b, g x * w x)
      ≤ (∫ x in a..b, w x) * ∫ x in a..b, f x * g x * w x := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hwi : IntervalIntegrable w volume a b := hw.intervalIntegrable_of_Icc hab.le
  have hfwi : IntervalIntegrable (fun x => f x * w x) volume a b :=
    (hf.mul hw).intervalIntegrable_of_Icc hab.le
  have hgwi : IntervalIntegrable (fun x => g x * w x) volume a b :=
    (hg.mul hw).intervalIntegrable_of_Icc hab.le
  have hfgwi : IntervalIntegrable (fun x => f x * g x * w x) volume a b :=
    ((hf.mul hg).mul hw).intervalIntegrable_of_Icc hab.le
  set W := ∫ x in a..b, w x with hWdef
  set m := (∫ x in a..b, f x * w x) / W with hmdef
  have hmW : (∫ x in a..b, f x * w x) = m * W := by
    rw [hmdef, div_mul_cancel₀ _ hW.ne']
  have hlo : f a * W ≤ ∫ x in a..b, f x * w x := by
    rw [hWdef, ← intervalIntegral.integral_const_mul]
    apply integral_mono_on hab.le (hwi.const_mul _) hfwi
    intro x hx
    exact mul_le_mul_of_nonneg_right (hfm ha hx hx.1) (hwnn x hx)
  have hhi : (∫ x in a..b, f x * w x) ≤ f b * W := by
    rw [hWdef, ← intervalIntegral.integral_const_mul]
    apply integral_mono_on hab.le hfwi (hwi.const_mul _)
    intro x hx
    exact mul_le_mul_of_nonneg_right (hfm hx hb hx.2) (hwnn x hx)
  have hm0 : f a ≤ m := by
    rw [hmdef, le_div_iff₀ hW]; exact hlo
  have hm1 : m ≤ f b := by
    rw [hmdef, div_le_iff₀ hW]; exact hhi
  obtain ⟨t₀, ht₀, hft₀⟩ := intermediate_value_Icc hab.le hf ⟨hm0, hm1⟩
  have hh_nonneg : ∀ x ∈ Icc a b, 0 ≤ (f x - m) * (g x - g t₀) * w x := by
    intro x hx
    have hw0 := hwnn x hx
    rcases le_total x t₀ with hxt | hxt
    · have hf' : f x ≤ m := hft₀ ▸ hfm hx ht₀ hxt
      have hg' : g x ≤ g t₀ := hgm hx ht₀ hxt
      exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)) hw0
    · have hf' : m ≤ f x := hft₀ ▸ hfm ht₀ hx hxt
      have hg' : g t₀ ≤ g x := hgm ht₀ hx hxt
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) hw0
  have hint : 0 ≤ ∫ x in a..b, (f x - m) * (g x - g t₀) * w x :=
    integral_nonneg hab.le hh_nonneg
  have hexp : (∫ x in a..b, (f x - m) * (g x - g t₀) * w x)
      = (∫ x in a..b, f x * g x * w x) - g t₀ * (∫ x in a..b, f x * w x)
        - m * (∫ x in a..b, g x * w x) + m * g t₀ * W := by
    have e : (fun x => (f x - m) * (g x - g t₀) * w x)
        = fun x => ((f x * g x * w x - g t₀ * (f x * w x)) - m * (g x * w x))
          + m * g t₀ * w x := by
      funext x
      ring
    rw [e, integral_add ((hfgwi.sub (hfwi.const_mul _)).sub (hgwi.const_mul _)) (hwi.const_mul _),
      integral_sub (hfgwi.sub (hfwi.const_mul _)) (hgwi.const_mul _),
      integral_sub hfgwi (hfwi.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hexp, hmW] at hint
  rw [hmW]
  nlinarith [hint, hW]


theorem d005829 (hab : a < b)
    (hw : ContinuousOn w (Icc a b)) (hwnn : ∀ x ∈ Icc a b, 0 ≤ w x)
    (hW : 0 < ∫ x in a..b, w x)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hfm : MonotoneOn f (Icc a b)) (hgm : AntitoneOn g (Icc a b)) :
    (∫ x in a..b, w x) * (∫ x in a..b, f x * g x * w x)
      ≤ (∫ x in a..b, f x * w x) * ∫ x in a..b, g x * w x := by
  have h := _root_.GD.N0106.N0428.N0765.N1662.d005828 hab hw hwnn hW hf hg.neg hfm
    (fun x hx y hy hxy => neg_le_neg (hgm hx hy hxy))
  have e1 : (∫ x in a..b, -g x * w x) = -∫ x in a..b, g x * w x := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext x
    ring
  have e2 : (∫ x in a..b, f x * -g x * w x) = -∫ x in a..b, f x * g x * w x := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext x
    ring
  rw [e1, e2] at h
  linarith [h]

end GD.N0106.N0428.N0765.N1662
