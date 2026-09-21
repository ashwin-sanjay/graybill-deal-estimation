import GD.Module0460
import GD.Module0564
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv





set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory Filter Set
open scoped Topology

namespace GD.N0106.N0428.N0770.N1744
noncomputable section

def d008350 (c t : ℝ) : ℝ := Real.exp (-c * Real.sqrt t)
def d008351 (c t : ℝ) : ℝ := c / (2 * Real.sqrt t) * _root_.GD.N0106.N0428.N0770.N1744.d008350 c t
def d008352 (c t : ℝ) : ℝ :=
  (c ^ 2 / (4 * t) + c / (4 * t * Real.sqrt t)) * _root_.GD.N0106.N0428.N0770.N1744.d008350 c t

theorem d008353 (c : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (_root_.GD.N0106.N0428.N0770.N1744.d008350 c) (-(_root_.GD.N0106.N0428.N0770.N1744.d008351 c t)) t := by
  convert! ((Real.hasDerivAt_sqrt ht.ne').const_mul (-c)).exp using 1
  unfold _root_.GD.N0106.N0428.N0770.N1744.d008351 _root_.GD.N0106.N0428.N0770.N1744.d008350
  ring

theorem d008354 (c : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (_root_.GD.N0106.N0428.N0770.N1744.d008351 c) (-(_root_.GD.N0106.N0428.N0770.N1744.d008352 c t)) t := by
  have hq : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have hd := (hasDerivAt_const t c).div ((Real.hasDerivAt_sqrt ht.ne').const_mul 2)
    (mul_ne_zero (by norm_num) hq)
  have hp := hd.mul (_root_.GD.N0106.N0428.N0770.N1744.d008353 c ht)
  have h : HasDerivAt (_root_.GD.N0106.N0428.N0770.N1744.d008351 c)
      (-((c ^ 2 / (4 * Real.sqrt t ^ 2) + c / (4 * Real.sqrt t ^ 3)) *
        _root_.GD.N0106.N0428.N0770.N1744.d008350 c t)) t := by
    convert! hp using 1
    unfold _root_.GD.N0106.N0428.N0770.N1744.d008351
    simp only [Pi.div_apply]
    field_simp [hq]
    ring
  have hq3 : Real.sqrt t ^ 3 = t * Real.sqrt t := by
    rw [pow_succ, Real.sq_sqrt ht.le]
  simpa only [Real.sq_sqrt ht.le, hq3, _root_.GD.N0106.N0428.N0770.N1744.d008352, mul_assoc] using h

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {A : Ω → ℝ}


theorem d008355 (hA : Measurable A) (ha : ∀ᵐ ω ∂μ, 0 ≤ A ω)
    {c : ℝ} (hL : ∀ s > 0, (∫ ω, Real.exp (-(s * A ω)) ∂μ) = _root_.GD.N0106.N0428.N0770.N1744.d008350 c s)
    {t : ℝ} (ht : 0 < t) :
    (∫ ω, A ω * Real.exp (-(t * A ω)) ∂μ) = _root_.GD.N0106.N0428.N0770.N1744.d008351 c t := by
  have he : (fun s : ℝ => ∫ ω, Real.exp (-(s * A ω)) ∂μ) =ᶠ[𝓝 t]
      _root_.GD.N0106.N0428.N0770.N1744.d008350 c := (eventually_gt_nhds ht).mono fun s hs => hL s hs
  have hd := (_root_.GD.N0106.N0428.N0770.N1744.d008353 c ht).congr_of_eventuallyEq he
  exact neg_injective ((_root_.GD.N0106.N0428.N0770.N1744.d007150 hA ha ht).unique hd)



theorem d008356 (hA : Measurable A) (ha : ∀ᵐ ω ∂μ, 0 ≤ A ω)
    {c : ℝ} (hL : ∀ s > 0, (∫ ω, Real.exp (-(s * A ω)) ∂μ) = _root_.GD.N0106.N0428.N0770.N1744.d008350 c s)
    {t : ℝ} (ht : 0 < t) :
    (∫ ω, A ω ^ 2 * Real.exp (-(t * A ω)) ∂μ) = _root_.GD.N0106.N0428.N0770.N1744.d008352 c t := by
  have he : (fun s : ℝ => ∫ ω, A ω * Real.exp (-(s * A ω)) ∂μ) =ᶠ[𝓝 t]
      _root_.GD.N0106.N0428.N0770.N1744.d008351 c := (eventually_gt_nhds ht).mono fun s hs =>
        _root_.GD.N0106.N0428.N0770.N1744.d008355 hA ha hL hs
  have hd := (_root_.GD.N0106.N0428.N0770.N1744.d008354 c ht).congr_of_eventuallyEq he
  have hg : HasDerivAt (fun s : ℝ => ∫ ω, A ω * Real.exp (-(s * A ω)) ∂μ)
      (-(∫ ω, A ω ^ 2 * Real.exp (-(t * A ω)) ∂μ)) t := by
    simpa only [pow_one, Nat.reduceAdd] using _root_.GD.N0106.N0428.N0770.N1744.d007149 hA ha ht 1
  exact neg_injective (hg.unique hd)

end
end GD.N0106.N0428.N0770.N1744

namespace GD.N0106.N0428.N0770.N1702
noncomputable section

open ProbabilityTheory


def d008357 (sigma x : ℝ) : ℝ := 2 / (sigma ^ 2 * x ^ 2)

theorem d008358 (sigma : ℝ) : Measurable (_root_.GD.N0106.N0428.N0770.N1702.d008357 sigma) := by
  unfold _root_.GD.N0106.N0428.N0770.N1702.d008357
  fun_prop

theorem d008359 (sigma x : ℝ) : 0 ≤ _root_.GD.N0106.N0428.N0770.N1702.d008357 sigma x := by
  unfold _root_.GD.N0106.N0428.N0770.N1702.d008357
  positivity

theorem d008360 (sigma : ℝ) {t : ℝ} (ht : 0 < t) (n : ℕ) :
    Integrable (fun x => _root_.GD.N0106.N0428.N0770.N1702.d008357 sigma x ^ n * Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1702.d008357 sigma x)))
      (gaussianReal 0 1) :=
  _root_.GD.N0106.N0428.N0770.N1744.d007148 (_root_.GD.N0106.N0428.N0770.N1702.d008358 sigma)
    (ae_of_all _ (_root_.GD.N0106.N0428.N0770.N1702.d008359 sigma)) ht n

theorem d008361 {sigma t : ℝ} (hsigma : 0 < sigma) (ht : 0 ≤ t) :
    (∫ x : ℝ, Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1702.d008357 sigma x)) ∂gaussianReal 0 1) =
      _root_.GD.N0106.N0428.N0770.N1744.d008350 (2 / sigma) t := by
  simpa only [_root_.GD.N0106.N0428.N0770.N1702.d008357, _root_.GD.N0106.N0428.N0770.N1744.d008350, neg_mul] using
    _root_.GD.N0106.N0428.N0770.N1702.d008348 hsigma ht


theorem d008362 {sigma t : ℝ}
    (hsigma : 0 < sigma) (ht : 0 < t) :
    (∫ x : ℝ, _root_.GD.N0106.N0428.N0770.N1702.d008357 sigma x * Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1702.d008357 sigma x)) ∂gaussianReal 0 1) =
      (2 / sigma) / (2 * Real.sqrt t) * Real.exp (-(2 / sigma) * Real.sqrt t) := by
  exact _root_.GD.N0106.N0428.N0770.N1744.d008355 (_root_.GD.N0106.N0428.N0770.N1702.d008358 sigma)
    (ae_of_all _ (_root_.GD.N0106.N0428.N0770.N1702.d008359 sigma))
    (fun s hs => _root_.GD.N0106.N0428.N0770.N1702.d008361 hsigma hs.le) ht


theorem d008363 {sigma t : ℝ}
    (hsigma : 0 < sigma) (ht : 0 < t) :
    (∫ x : ℝ, _root_.GD.N0106.N0428.N0770.N1702.d008357 sigma x ^ 2 * Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1702.d008357 sigma x))
      ∂gaussianReal 0 1) =
      ((2 / sigma) ^ 2 / (4 * t) + (2 / sigma) / (4 * t * Real.sqrt t)) *
        Real.exp (-(2 / sigma) * Real.sqrt t) := by
  exact _root_.GD.N0106.N0428.N0770.N1744.d008356 (_root_.GD.N0106.N0428.N0770.N1702.d008358 sigma)
    (ae_of_all _ (_root_.GD.N0106.N0428.N0770.N1702.d008359 sigma))
    (fun s hs => _root_.GD.N0106.N0428.N0770.N1702.d008361 hsigma hs.le) ht

end
end GD.N0106.N0428.N0770.N1702

#print axioms _root_.GD.N0106.N0428.N0770.N1744.d008353
#print axioms _root_.GD.N0106.N0428.N0770.N1744.d008354
#print axioms _root_.GD.N0106.N0428.N0770.N1744.d008355
#print axioms _root_.GD.N0106.N0428.N0770.N1744.d008356
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d008360
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d008362
#print axioms _root_.GD.N0106.N0428.N0770.N1702.d008363
