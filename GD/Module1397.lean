import GD.Module1393
import GD.Module1396
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap










set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace GD.N0188
noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0180 _root_.GD.N0163
open _root_.GD.N0164 _root_.GD.N0172

variable {I : Type*} [Fintype I]
variable (p : I → ℝ) (t : I → _root_.GD.N0232.N0720.N1441.d013676)


def d022486 : Measure _root_.GD.N0232.N0720.N1436.d013217 :=
  _root_.GD.N0232.N0720.N1436.d013288.withDensity (fun x => ENNReal.ofReal (_root_.GD.N0163.d022178 p t x))

theorem d022487 :
    ∀ᵐ x ∂_root_.GD.N0188.d022486 p t, x ∈ _root_.GD.N0232.N0720.N1436.d013218 :=
  (withDensity_absolutelyContinuous _root_.GD.N0232.N0720.N1436.d013288
    (fun x => ENNReal.ofReal (_root_.GD.N0163.d022178 p t x))).ae_le
      (ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219)

theorem d022488 : Integrable (_root_.GD.N0163.d022178 p t) _root_.GD.N0232.N0720.N1436.d013288 := by
  unfold _root_.GD.N0163.d022178 _root_.GD.N0163.d022177
  apply integrable_finsetSum
  intro i _
  exact (_root_.GD.N0180.d022169 (t i)).const_mul (p i)

section Positive
variable [Nonempty I] (hp : ∀ i, 0 < p i)
include hp

theorem d022489 : 0 ≤ᵐ[_root_.GD.N0232.N0720.N1436.d013288] _root_.GD.N0163.d022178 p t := by
  filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with x hx
  exact (_root_.GD.N0163.d022195 p t hp hx).le

theorem d022490 : IsFiniteMeasure (_root_.GD.N0188.d022486 p t) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (_root_.GD.N0188.d022488 p t)
    (_root_.GD.N0188.d022489 p t hp)]
  exact ENNReal.ofReal_ne_top


theorem d022491 (f : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) :
    (∫ x, f x ∂_root_.GD.N0188.d022486 p t) =
      ∫ x, _root_.GD.N0163.d022178 p t x * f x ∂_root_.GD.N0232.N0720.N1436.d013288 := by
  rw [_root_.GD.N0188.d022486,
    integral_withDensity_eq_integral_toReal_smul
      (_root_.GD.N0163.d022190 p t).ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0188.d022489 p t hp] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul]

theorem d022492 (f : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hf : Measurable f)
    {B : ℝ} (hB : ∀ x, |f x| ≤ B) : MemLp f 2 (_root_.GD.N0188.d022486 p t) := by
  letI := _root_.GD.N0188.d022490 p t hp
  exact MemLp.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using hB x))

end Positive


theorem d022493 (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ)
    {B : ℝ} (hB : ∀ x, |g x| ≤ B) (x : _root_.GD.N0232.N0720.N1436.d013217) :
    |_root_.GD.N0163.d022211 g x| ≤ max B 0 := by
  by_cases hx : x ∈ _root_.GD.N0232.N0720.N1436.d013218
  · rw [show _root_.GD.N0163.d022211 g x = g ⟨x, hx⟩ from
      _root_.GD.N0163.d022212 g ⟨x, hx⟩]
    exact (hB ⟨x, hx⟩).trans (le_max_left _ _)
  · have hn : ¬ ∃ y : _root_.GD.N0232.N0720.N1436.d013218, (y : _root_.GD.N0232.N0720.N1436.d013217) = x := by
      rintro ⟨y, hy⟩
      exact hx (hy ▸ y.property)
    rw [_root_.GD.N0163.d022211, Function.extend_apply' g (fun _ => 0) x hn, abs_zero]
    exact le_max_right _ _

section Positive
variable [Nonempty I] (hp : ∀ i, 0 < p i)


def d022494 (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ x, |g x| ≤ B) : Lp ℝ 2 (_root_.GD.N0188.d022486 p t) :=
  (_root_.GD.N0188.d022492 p t hp (_root_.GD.N0163.d022211 g)
    (_root_.GD.N0163.d022213 g hg) (_root_.GD.N0188.d022493 g hB)).toLp
      (_root_.GD.N0163.d022211 g)

theorem d022495 (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    _root_.GD.N0188.d022494 p t hp g hg hB =ᵐ[_root_.GD.N0188.d022486 p t] _root_.GD.N0163.d022211 g :=
  MemLp.coeFn_toLp _


theorem d022496 (g h : _root_.GD.N0232.N0720.N1436.d013218 → ℝ)
    (hg : Measurable g) (hh : Measurable h) {B C : ℝ}
    (hB : ∀ x, |g x| ≤ B) (hC : ∀ x, |h x| ≤ C) :
    ‖_root_.GD.N0188.d022494 p t hp g hg hB - _root_.GD.N0188.d022494 p t hp h hh hC‖ ^ 2 =
      ∫ x, _root_.GD.N0163.d022178 p t x * (_root_.GD.N0163.d022211 g x - _root_.GD.N0163.d022211 h x) ^ 2
        ∂_root_.GD.N0232.N0720.N1436.d013288 := by
  calc
    _ = ∫ x, (_root_.GD.N0163.d022211 g x - _root_.GD.N0163.d022211 h x) ^ 2
        ∂_root_.GD.N0188.d022486 p t := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (_root_.GD.N0188.d022494 p t hp g hg hB)
          (_root_.GD.N0188.d022494 p t hp h hh hC),
        _root_.GD.N0188.d022495 p t hp g hg hB, _root_.GD.N0188.d022495 p t hp h hh hC] with x hx hxg hxh
      simp only [hx, hxg, hxh, Pi.sub_apply, real_inner_self_eq_norm_sq,
        Real.norm_eq_abs, sq_abs]
    _ = _ := _root_.GD.N0188.d022491 p t hp _

include hp in

theorem d022497 (g h : _root_.GD.N0232.N0720.N1436.d013218 → ℝ)
    (hg : Measurable g) (hh : Measurable h) {B C : ℝ}
    (hB : ∀ x, |g x| ≤ B) (hC : ∀ x, |h x| ≤ C) :
    MemLp (fun x => _root_.GD.N0163.d022211 g x - _root_.GD.N0163.d022211 h x) 2
      (_root_.GD.N0188.d022486 p t) := by
  exact (_root_.GD.N0188.d022492 p t hp _ (_root_.GD.N0163.d022213 g hg)
    (_root_.GD.N0188.d022493 g hB)).sub
      (_root_.GD.N0188.d022492 p t hp _ (_root_.GD.N0163.d022213 h hh)
        (_root_.GD.N0188.d022493 h hC))

def d022498 (g : _root_.GD.N0172.d022466) : Lp ℝ 2 (_root_.GD.N0188.d022486 p t) :=
  _root_.GD.N0188.d022494 p t hp g.1 g.property.1 (B := 1)
    (fun x => by rw [abs_of_nonneg (g.property.2 x).1]; exact (g.property.2 x).2)

theorem d022499 (g h : _root_.GD.N0172.d022466) :
    ‖_root_.GD.N0188.d022498 p t hp g - _root_.GD.N0188.d022498 p t hp h‖ ^ 2 =
      ∫ x, _root_.GD.N0163.d022178 p t x * (_root_.GD.N0163.d022211 g.1 x - _root_.GD.N0163.d022211 h.1 x) ^ 2
        ∂_root_.GD.N0232.N0720.N1436.d013288 :=
  _root_.GD.N0188.d022496 p t hp g.1 h.1 g.property.1 h.property.1
    (B := 1) (C := 1)
    (fun x => by rw [abs_of_nonneg (g.property.2 x).1]; exact (g.property.2 x).2)
    (fun x => by rw [abs_of_nonneg (h.property.2 x).1]; exact (h.property.2 x).2)


theorem d022500 (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    ‖_root_.GD.N0188.d022494 p t hp g hg hB - _root_.GD.N0188.d022498 p t hp (_root_.GD.N0172.d022478 p t hp)‖ ^ 2 =
      (∫ r, _root_.GD.N0164.d022430 (_root_.GD.N0163.d022211 g) r ∂_root_.GD.N0164.d022432 p t) -
        _root_.GD.N0163.d022186 p t := by
  have hnorm :
      ‖_root_.GD.N0188.d022494 p t hp g hg hB - _root_.GD.N0188.d022498 p t hp (_root_.GD.N0172.d022478 p t hp)‖ ^ 2 =
        ∫ x, _root_.GD.N0163.d022178 p t x *
          (_root_.GD.N0163.d022211 g x - _root_.GD.N0163.d022211 (_root_.GD.N0172.d022478 p t hp).1 x) ^ 2
            ∂_root_.GD.N0232.N0720.N1436.d013288 :=
    _root_.GD.N0188.d022496 p t hp g (_root_.GD.N0172.d022478 p t hp).1
      hg (_root_.GD.N0172.d022478 p t hp).property.1 hB (C := 1)
      (fun x => by
        rw [abs_of_nonneg ((_root_.GD.N0172.d022478 p t hp).property.2 x).1]
        exact ((_root_.GD.N0172.d022478 p t hp).property.2 x).2)
  rw [hnorm, _root_.GD.N0172.d022479,
    _root_.GD.N0164.d022435 p t (fun i => (hp i).le)]
  have h := _root_.GD.N0163.d022207 p t hp (_root_.GD.N0163.d022211 g)
    (_root_.GD.N0163.d022213 g hg) (_root_.GD.N0188.d022493 g hB)
  change (∫ x, _root_.GD.N0163.d022184 p t (_root_.GD.N0163.d022211 g) x
      ∂_root_.GD.N0232.N0720.N1436.d013288) = _
  linarith


theorem d022501 (g : _root_.GD.N0172.d022466) :
    ‖_root_.GD.N0188.d022498 p t hp g - _root_.GD.N0188.d022498 p t hp (_root_.GD.N0172.d022478 p t hp)‖ ^ 2 =
      (∫ r, _root_.GD.N0164.d022430 (_root_.GD.N0163.d022211 g.1) r ∂_root_.GD.N0164.d022432 p t) -
        _root_.GD.N0163.d022186 p t :=
  _root_.GD.N0188.d022500 p t hp g.1 g.property.1 (B := 1)
    (fun x => by rw [abs_of_nonneg (g.property.2 x).1]; exact (g.property.2 x).2)

end Positive
end
end GD.N0188

#print axioms _root_.GD.N0188.d022488
#print axioms _root_.GD.N0188.d022487
#print axioms _root_.GD.N0188.d022489
#print axioms _root_.GD.N0188.d022490
#print axioms _root_.GD.N0188.d022491
#print axioms _root_.GD.N0188.d022492
#print axioms _root_.GD.N0188.d022493
#print axioms _root_.GD.N0188.d022495
#print axioms _root_.GD.N0188.d022496
#print axioms _root_.GD.N0188.d022497
#print axioms _root_.GD.N0188.d022499
#print axioms _root_.GD.N0188.d022500
#print axioms _root_.GD.N0188.d022501
