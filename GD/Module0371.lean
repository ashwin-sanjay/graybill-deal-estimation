import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.Algebra.InfiniteSum.NatInt












set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1613
noncomputable section

open MeasureTheory Filter Set Asymptotics Complex ContinuousMap TopologicalSpace
open scoped Topology FourierTransform

private theorem d005624 {f : ℝ → ℂ} {C a : ℝ}
    (ha : 0 < a) (hb : ∀ x : ℝ, 0 ≤ x → ‖f x‖ ≤ C * Real.exp (-a * x)) :
    f =O[atTop] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
  have hO : f =O[atTop] (fun x : ℝ => Real.exp (-a * x)) := by
    apply IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb x hx
  have h := hO.trans (isLittleO_exp_neg_mul_rpow_atTop ha (-2)).isBigO
  refine h.congr' Filter.EventuallyEq.rfl ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [abs_of_nonneg hx]



theorem d005625 {f : ℝ → ℂ} {AL AR a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hleft : ∀ x : ℝ, x ≤ 0 → ‖f x‖ ≤ AL * Real.exp (a * x))
    (hright : ∀ x : ℝ, 0 ≤ x → ‖f x‖ ≤ AR * Real.exp (-b * x)) :
    f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
  rw [cocompact_eq_atBot_atTop, isBigO_sup]
  constructor
  · have hneg : (fun x : ℝ => f (-x)) =O[atTop]
        (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
      apply _root_.GD.N0106.N0428.N0765.N1613.d005624 ha
      intro x hx
      simpa only [mul_neg, neg_mul] using hleft (-x) (neg_nonpos.mpr hx)
    have hcomp := hneg.comp_tendsto tendsto_neg_atBot_atTop
    have hfcomp : (fun x : ℝ => f (-x)) ∘ (fun x : ℝ => -x) = f := by
      funext x
      simp only [Function.comp_apply, neg_neg]
    have hgcomp : (fun x : ℝ => |x| ^ (-2 : ℝ)) ∘ (fun x : ℝ => -x) =
        (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
      funext x
      simp only [Function.comp_apply, abs_neg]
    rw [hfcomp, hgcomp] at hcomp
    exact hcomp
  · exact _root_.GD.N0106.N0428.N0765.N1613.d005624 hb hright



theorem d005626 {f : ℝ → ℂ} {AL AR a b : ℝ}
    (hc : Continuous f) (ha : 0 < a) (hb : 0 < b)
    (hleft : ∀ x : ℝ, x ≤ 0 → ‖f x‖ ≤ AL * Real.exp (a * x))
    (hright : ∀ x : ℝ, 0 ≤ x → ‖f x‖ ≤ AR * Real.exp (-b * x)) :
    ∀ K : Compacts ℝ, Summable fun n : ℤ =>
      ‖((⟨f, hc⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight n)).restrict K‖ := by
  have hdecay := _root_.GD.N0106.N0428.N0765.N1613.d005625 ha hb hleft hright
  intro K
  exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : 1 < (2 : ℝ)))
    ((isBigO_norm_restrict_cocompact ⟨f, hc⟩ (by norm_num : 0 < (2 : ℝ))
      hdecay K).comp_tendsto Int.tendsto_coe_cofinite)


theorem d005627 {f : ℝ → ℂ} {AL AR a b : ℝ}
    (hc : Continuous f) (ha : 0 < a) (hb : 0 < b)
    (hleft : ∀ x : ℝ, x ≤ 0 → ‖f x‖ ≤ AL * Real.exp (a * x))
    (hright : ∀ x : ℝ, 0 ≤ x → ‖f x‖ ≤ AR * Real.exp (-b * x)) (x : ℝ) :
    Summable (fun n : ℤ => f (x + n)) := by
  have hk := _root_.GD.N0106.N0428.N0765.N1613.d005626 hc ha hb hleft hright
  have hs : Summable (fun n : ℤ =>
      (⟨f, hc⟩ : C(ℝ, ℂ)).comp (ContinuousMap.addRight n)) :=
    summable_of_locally_summable_norm hk
  simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    ContinuousMap.coe_addRight] using (hasSum_apply hs.hasSum x).summable

theorem d005628 {k : ℝ} (hk : 0 < k) (C : ℝ) :
    HasSum (fun n : ℕ => C * Real.exp (-k * n))
      (C * (1 - Real.exp (-k))⁻¹) := by
  have hq : Real.exp (-k) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h := (hasSum_geometric_of_lt_one (Real.exp_pos (-k)).le hq).mul_left C
  simpa only [mul_comm (-k), Real.exp_nat_mul] using h

theorem d005629 {k : ℝ} (hk : 0 < k) (C : ℝ) :
    HasSum (fun n : ℕ => C * Real.exp (-k * (n + 1)))
      (C / (Real.exp k - 1)) := by
  have h := (hasSum_nat_add_iff' 1).mpr (_root_.GD.N0106.N0428.N0765.N1613.d005628 hk C)
  have he : Real.exp k ≠ 0 := (Real.exp_pos k).ne'
  have hd : Real.exp k - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hk))
  have halg : C * (1 - Real.exp (-k))⁻¹ - C = C / (Real.exp k - 1) := by
    rw [Real.exp_neg]
    field_simp [he, hd] <;> ring
  simpa only [Finset.sum_range_one, Nat.cast_zero, mul_zero, Real.exp_zero,
    mul_one, Nat.cast_add, Nat.cast_one, halg] using h


theorem d005630 {s : ℤ → ℂ} {C k : ℝ}
    (hk : 0 < k) (hb : ∀ n : ℤ, ‖s n‖ ≤ C * Real.exp (-k * |(n : ℝ)|)) :
    Summable s := by
  apply Summable.of_nat_of_neg_add_one
  · apply (_root_.GD.N0106.N0428.N0765.N1613.d005628 hk C).summable.of_norm_bounded
    intro n
    simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using hb n
  · apply (_root_.GD.N0106.N0428.N0765.N1613.d005629 hk C).summable.of_norm_bounded
    intro n
    simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      abs_neg, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)] using hb (-(n + 1))


theorem d005631 {s : ℤ → ℂ} {C k : ℝ}
    (hk : 0 < k) (hb : ∀ n : ℤ, ‖s n‖ ≤ C * Real.exp (-k * |(n : ℝ)|)) :
    ‖(∑' n : ℤ, s n) - s 0‖ ≤ 2 * C / (Real.exp k - 1) := by
  have hs := _root_.GD.N0106.N0428.N0765.N1613.d005630 hk hb
  have hp : Summable (fun n : ℕ => s n) := hs.comp_injective Nat.cast_injective
  have hn : Summable (fun n : ℕ => s (-(n + 1))) := by
    apply hs.comp_injective
    intro m n hmn
    have hcast : (m : ℤ) = (n : ℤ) := by linarith
    exact_mod_cast hcast
  have hsplit : (∑' n : ℤ, s n) - s 0 =
      (∑' n : ℕ, s ((n : ℤ) + 1)) + ∑' n : ℕ, s (-(n + 1)) := by
    rw [tsum_of_nat_of_neg_add_one hp hn, hp.tsum_eq_zero_add]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero]
    abel
  have hpbound : ‖∑' n : ℕ, s ((n : ℤ) + 1)‖ ≤ C / (Real.exp k - 1) := by
    apply tsum_of_norm_bounded (_root_.GD.N0106.N0428.N0765.N1613.d005629 hk C)
    intro n
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one,
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)] using hb (n + 1)
  have hnbound : ‖∑' n : ℕ, s (-(n + 1))‖ ≤ C / (Real.exp k - 1) := by
    apply tsum_of_norm_bounded (_root_.GD.N0106.N0428.N0765.N1613.d005629 hk C)
    intro n
    simpa only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      abs_neg, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)] using hb (-(n + 1))
  rw [hsplit]
  calc
    _ ≤ ‖∑' n : ℕ, s ((n : ℤ) + 1)‖ + ‖∑' n : ℕ, s (-(n + 1))‖ := norm_add_le _ _
    _ ≤ C / (Real.exp k - 1) + C / (Real.exp k - 1) := add_le_add hpbound hnbound
    _ = 2 * C / (Real.exp k - 1) := by ring

theorem d005632 (f : ℝ → ℂ) : 𝓕 f 0 = ∫ x : ℝ, f x := by
  simp only [Real.fourier_real_eq_integral_exp_smul, mul_zero, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, one_smul]



theorem d005633 {f : ℝ → ℂ} {AL AR a b C k : ℝ}
    (hc : Continuous f) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k)
    (hleft : ∀ x : ℝ, x ≤ 0 → ‖f x‖ ≤ AL * Real.exp (a * x))
    (hright : ∀ x : ℝ, 0 ≤ x → ‖f x‖ ≤ AR * Real.exp (-b * x))
    (hfourier : ∀ xi : ℝ, ‖𝓕 f xi‖ ≤ C * Real.exp (-k * |xi|)) (x : ℝ) :
    ‖(∑' n : ℤ, f (x + n)) - ∫ t : ℝ, f t‖ ≤ 2 * C / (Real.exp k - 1) := by
  have hF : Summable (fun n : ℤ => 𝓕 f n) :=
    _root_.GD.N0106.N0428.N0765.N1613.d005630 hk (fun n => hfourier n)
  have hnorm := _root_.GD.N0106.N0428.N0765.N1613.d005626 hc ha hb hleft hright
  have hpoisson := Real.tsum_eq_tsum_fourier (f := (⟨f, hc⟩ : C(ℝ, ℂ))) hnorm hF x
  let mode (n : ℤ) : ℂ := 𝓕 f n * fourier n (x : UnitAddCircle)
  have hmode : ∀ n : ℤ, ‖mode n‖ ≤ C * Real.exp (-k * |(n : ℝ)|) := by
    intro n
    have hphase : ‖fourier n (x : UnitAddCircle)‖ = 1 := Circle.norm_coe _
    simpa only [mode, norm_mul, hphase, mul_one] using hfourier n
  have hzero : mode 0 = ∫ t : ℝ, f t := by
    simp only [mode, Int.cast_zero, fourier_zero, mul_one, _root_.GD.N0106.N0428.N0765.N1613.d005632]
  have herror := _root_.GD.N0106.N0428.N0765.N1613.d005631 hk hmode
  rw [hzero] at herror
  change (∑' n : ℤ, f (x + n)) = ∑' n : ℤ, mode n at hpoisson
  rw [← hpoisson] at herror
  exact herror


theorem d005634 (f : ℝ → ℂ) {h : ℝ} (hh : 0 < h) (xi : ℝ) :
    𝓕 (fun x : ℝ => f (h * x)) xi = h⁻¹ • 𝓕 f (xi / h) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  have he : (fun x : ℝ => Complex.exp (↑(-2 * Real.pi * x * xi) * Complex.I) • f (h*x)) =
      (fun x : ℝ => (fun y : ℝ =>
        Complex.exp (↑(-2 * Real.pi * y * (xi / h)) * Complex.I) • f y) (h*x)) := by
    funext x
    have heq : -2 * Real.pi * x * xi = -2 * Real.pi * (h*x) * (xi/h) := by
      field_simp [hh.ne'] <;> ring
    rw [heq]
  rw [he]
  simpa only [abs_of_pos (inv_pos.mpr hh)] using
    Measure.integral_comp_mul_left (fun y : ℝ =>
      Complex.exp (↑(-2 * Real.pi * y * (xi / h)) * Complex.I) • f y) h


theorem d005635 {f : ℝ → ℂ} {AL AR a b C k h : ℝ}
    (hc : Continuous f) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) (hh : 0 < h)
    (hleft : ∀ x : ℝ, x ≤ 0 → ‖f x‖ ≤ AL * Real.exp (a * x))
    (hright : ∀ x : ℝ, 0 ≤ x → ‖f x‖ ≤ AR * Real.exp (-b * x))
    (hfourier : ∀ xi : ℝ, ‖𝓕 f xi‖ ≤ C * Real.exp (-k * |xi|)) (offset : ℝ) :
    ‖(h : ℂ) * (∑' n : ℤ, f (offset + h * n)) - ∫ t : ℝ, f t‖ ≤
      2 * C / (Real.exp (k / h) - 1) := by
  let g : ℝ → ℂ := fun x => f (h * x)
  have hg : Continuous g := hc.comp (continuous_const.mul continuous_id)
  have hgl : ∀ x : ℝ, x ≤ 0 → ‖g x‖ ≤ AL * Real.exp ((a*h)*x) := by
    intro x hx
    simpa only [g, mul_assoc] using hleft (h*x) (mul_nonpos_of_nonneg_of_nonpos hh.le hx)
  have hgr : ∀ x : ℝ, 0 ≤ x → ‖g x‖ ≤ AR * Real.exp (-(b*h)*x) := by
    intro x hx
    simpa only [g, neg_mul, mul_assoc] using hright (h*x) (mul_nonneg hh.le hx)
  have hgF : ∀ xi : ℝ, ‖𝓕 g xi‖ ≤ (h⁻¹*C) * Real.exp (-(k/h)*|xi|) := by
    intro xi
    rw [show g = (fun x : ℝ => f (h*x)) from rfl, _root_.GD.N0106.N0428.N0765.N1613.d005634 f hh, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
    have he : -k * |xi/h| = -(k/h)*|xi| := by
      rw [abs_div, abs_of_pos hh]
      ring
    simpa only [he, mul_assoc] using
      mul_le_mul_of_nonneg_left (hfourier (xi/h)) (inv_pos.mpr hh).le
  have hu := _root_.GD.N0106.N0428.N0765.N1613.d005633 hg (mul_pos ha hh) (mul_pos hb hh) (div_pos hk hh)
    hgl hgr hgF (offset/h)
  have hsum : (∑' n : ℤ, g (offset/h+n)) = ∑' n : ℤ, f (offset+h*n) := by
    apply tsum_congr
    intro n
    change f (h * (offset/h + (n : ℝ))) = f (offset + h*n)
    congr 1
    field_simp [hh.ne'] <;> ring
  have hInt : (∫ x : ℝ, g x) = h⁻¹ • ∫ x : ℝ, f x := by
    simpa only [g, abs_of_pos (inv_pos.mpr hh)] using Measure.integral_comp_mul_left f h
  have hid : (h : ℂ) * (∑' n : ℤ, f (offset+h*n)) - ∫ x : ℝ, f x =
      h • ((∑' n : ℤ, g (offset/h+n)) - ∫ x : ℝ, g x) := by
    rw [hsum, hInt, smul_sub, smul_smul, mul_inv_cancel₀ hh.ne', one_smul]
    rfl
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  calc
    _ ≤ h * (2 * (h⁻¹*C) / (Real.exp (k/h)-1)) := mul_le_mul_of_nonneg_left hu hh.le
    _ = 2 * (h*h⁻¹) * C / (Real.exp (k/h)-1) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hh.ne', mul_one]



theorem d005636 {f : ℝ → ℝ} {AL AR a b C k h : ℝ}
    (hc : Continuous f) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) (hh : 0 < h)
    (hleft : ∀ x : ℝ, x ≤ 0 → |f x| ≤ AL * Real.exp (a * x))
    (hright : ∀ x : ℝ, 0 ≤ x → |f x| ≤ AR * Real.exp (-b * x))
    (hfourier : ∀ xi : ℝ, ‖𝓕 (fun x : ℝ => (f x : ℂ)) xi‖ ≤
      C * Real.exp (-k * |xi|)) (offset : ℝ) :
    |h * (∑' n : ℤ, f (offset+h*n)) - ∫ t : ℝ, f t| ≤
      2 * C / (Real.exp (k/h)-1) := by
  have hc' : Continuous (fun x : ℝ => (f x : ℂ)) := Complex.continuous_ofReal.comp hc
  have hl : ∀ x : ℝ, x ≤ 0 → ‖(f x : ℂ)‖ ≤ AL * Real.exp (a*x) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hleft
  have hr : ∀ x : ℝ, 0 ≤ x → ‖(f x : ℂ)‖ ≤ AR * Real.exp (-b*x) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hright
  have he := _root_.GD.N0106.N0428.N0765.N1613.d005635 hc' ha hb hk hh hl hr hfourier offset
  simpa only [← Complex.ofReal_tsum, integral_complex_ofReal, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using he

end
end GD.N0106.N0428.N0765.N1613

#print axioms _root_.GD.N0106.N0428.N0765.N1613.d005625
#print axioms _root_.GD.N0106.N0428.N0765.N1613.d005626
#print axioms _root_.GD.N0106.N0428.N0765.N1613.d005627
#print axioms _root_.GD.N0106.N0428.N0765.N1613.d005628
#print axioms _root_.GD.N0106.N0428.N0765.N1613.d005629
#print axioms _root_.GD.N0106.N0428.N0765.N1613.d005630
#print axioms _root_.GD.N0106.N0428.N0765.N1613.d005631
#print axioms _root_.GD.N0106.N0428.N0765.N1613.d005632
#print axioms _root_.GD.N0106.N0428.N0765.N1613.d005633
#print axioms _root_.GD.N0106.N0428.N0765.N1613.d005634
#print axioms _root_.GD.N0106.N0428.N0765.N1613.d005635
#print axioms _root_.GD.N0106.N0428.N0765.N1613.d005636
