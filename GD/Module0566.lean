import GD.Module0565
import GD.Module0462
import Mathlib.MeasureTheory.Integral.Pi





set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators

namespace GD.N0106.N0428.N0770.N1750
noncomputable section

open _root_.GD.N0106.N0428.N0770.N1702

def d008364 (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => gaussianReal 0 1)

instance d008365 (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) := by
  unfold _root_.GD.N0106.N0428.N0770.N1750.d008364
  infer_instance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def d008366 (sigma : ι → ℝ) (i : ι) (ω : ι → ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0770.N1702.d008357 (sigma i) (ω i)

def d008367 (sigma : ι → ℝ) (ω : ι → ℝ) : ℝ :=
  ∑ i, _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω

def d008368 (sigma : ι → ℝ) : ℝ := ∑ i, 2 / sigma i

theorem d008369 (sigma : ι → ℝ) (i : ι) :
    Measurable (_root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i) :=
  (_root_.GD.N0106.N0428.N0770.N1702.d008358 (sigma i)).comp (measurable_pi_apply i)

theorem d008370 (sigma : ι → ℝ) (i : ι) :
    ∀ᵐ ω ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι, 0 ≤ _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω :=
  ae_of_all _ (fun ω => _root_.GD.N0106.N0428.N0770.N1702.d008359 (sigma i) (ω i))

theorem d008371 (sigma : ι → ℝ) :
    iIndepFun (_root_.GD.N0106.N0428.N0770.N1750.d008366 sigma) (_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) :=
  iIndepFun_pi (μ := fun _ : ι => gaussianReal 0 1)
    (X := fun i => _root_.GD.N0106.N0428.N0770.N1702.d008357 (sigma i))
    (fun i => (_root_.GD.N0106.N0428.N0770.N1702.d008358 (sigma i)).aemeasurable)

theorem d008372 (sigma : ι → ℝ) (i : ι)
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω ^ n *
      Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω))) (_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) :=
  integrable_comp_eval (μ := fun _ : ι => gaussianReal 0 1) (i := i)
    (_root_.GD.N0106.N0428.N0770.N1702.d008360 (sigma i) ht n)


theorem d008373 (sigma : ι → ℝ) (i : ι) (t : ℝ) (n : ℕ) :
    (∫ ω, _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω ^ n *
      Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω)) ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) =
      ∫ x : ℝ, _root_.GD.N0106.N0428.N0770.N1702.d008357 (sigma i) x ^ n * Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1702.d008357 (sigma i) x))
        ∂gaussianReal 0 1 := by
  have hm := (((_root_.GD.N0106.N0428.N0770.N1702.d008358 (sigma i)).pow_const n).mul
    (((_root_.GD.N0106.N0428.N0770.N1702.d008358 (sigma i)).const_mul t).neg.exp)).aestronglyMeasurable
      (μ := gaussianReal 0 1)
  simpa only [_root_.GD.N0106.N0428.N0770.N1750.d008364, _root_.GD.N0106.N0428.N0770.N1750.d008366] using!
    (integral_comp_eval (μ := fun _ : ι => gaussianReal 0 1) (i := i)
      (f := fun x : ℝ => _root_.GD.N0106.N0428.N0770.N1702.d008357 (sigma i) x ^ n * Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1702.d008357 (sigma i) x))) hm)

theorem d008374 {sigma : ι → ℝ} (hsigma : ∀ i, 0 < sigma i)
    {t : ℝ} (ht : 0 < t) (i : ι) :
    (∫ ω, Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω)) ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) =
      _root_.GD.N0106.N0428.N0770.N1744.d008350 (2 / sigma i) t := by
  have he := _root_.GD.N0106.N0428.N0770.N1750.d008373 sigma i t 0
  simp only [pow_zero, one_mul] at he
  exact he.trans (_root_.GD.N0106.N0428.N0770.N1702.d008361 (hsigma i) ht.le)

theorem d008375 {sigma : ι → ℝ} (hsigma : ∀ i, 0 < sigma i)
    {t : ℝ} (ht : 0 < t) (i : ι) :
    (∫ ω, _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω * Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω))
      ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) = _root_.GD.N0106.N0428.N0770.N1744.d008351 (2 / sigma i) t := by
  have he := _root_.GD.N0106.N0428.N0770.N1750.d008373 sigma i t 1
  simp only [pow_one] at he
  exact he.trans (_root_.GD.N0106.N0428.N0770.N1702.d008362 (hsigma i) ht)

theorem d008376 {sigma : ι → ℝ} (hsigma : ∀ i, 0 < sigma i)
    {t : ℝ} (ht : 0 < t) (i : ι) :
    (∫ ω, _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω ^ 2 * Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω))
      ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) = _root_.GD.N0106.N0428.N0770.N1744.d008352 (2 / sigma i) t :=
  (_root_.GD.N0106.N0428.N0770.N1750.d008373 sigma i t 2).trans
    (_root_.GD.N0106.N0428.N0770.N1702.d008363 (hsigma i) ht)

theorem d008377 (sigma : ι → ℝ) (t : ℝ) :
    (∏ i, _root_.GD.N0106.N0428.N0770.N1744.d008350 (2 / sigma i) t) =
      Real.exp (-_root_.GD.N0106.N0428.N0770.N1750.d008368 sigma * Real.sqrt t) := by
  simp_rw [_root_.GD.N0106.N0428.N0770.N1744.d008350]
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.sum_mul, Finset.sum_neg_distrib]
  rfl


theorem d008378 {sigma : ι → ℝ} (hsigma : ∀ i, 0 < sigma i)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun ω => Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω))) (_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) ∧
      (∫ ω, Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω)) ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) =
        Real.exp (-_root_.GD.N0106.N0428.N0770.N1750.d008368 sigma * Real.sqrt t) := by
  obtain ⟨hi, he⟩ := _root_.GD.N0106.N0428.N0770.N1744.d007169 (_root_.GD.N0106.N0428.N0770.N1750.d008369 sigma)
    (_root_.GD.N0106.N0428.N0770.N1750.d008370 sigma) (_root_.GD.N0106.N0428.N0770.N1750.d008371 sigma) ht
  refine ⟨hi, ?_⟩
  change (∫ ω, Real.exp (-(t * ∑ i, _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω))
    ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) = _
  rw [he]
  simp_rw [_root_.GD.N0106.N0428.N0770.N1750.d008374 hsigma ht]
  exact _root_.GD.N0106.N0428.N0770.N1750.d008377 sigma t

theorem d008379 {sigma : ι → ℝ} (hsigma : ∀ i, 0 < sigma i)
    {t : ℝ} (ht : 0 < t) (i : ι) :
    Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω * Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω)))
      (_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) ∧
      (∫ ω, _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω * Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω))
        ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) =
        ((2 / sigma i) / (2 * Real.sqrt t)) * Real.exp (-_root_.GD.N0106.N0428.N0770.N1750.d008368 sigma * Real.sqrt t) := by
  obtain ⟨hi, he⟩ := _root_.GD.N0106.N0428.N0770.N1744.d007171 (_root_.GD.N0106.N0428.N0770.N1750.d008369 sigma)
    (_root_.GD.N0106.N0428.N0770.N1750.d008370 sigma) (_root_.GD.N0106.N0428.N0770.N1750.d008371 sigma) ht i
  refine ⟨hi, he.trans ?_⟩
  simp_rw [_root_.GD.N0106.N0428.N0770.N1750.d008375 hsigma ht, _root_.GD.N0106.N0428.N0770.N1750.d008374 hsigma ht]
  rw [_root_.GD.N0106.N0428.N0770.N1744.d008351, mul_assoc,
    Finset.mul_prod_erase Finset.univ
      (fun k => _root_.GD.N0106.N0428.N0770.N1744.d008350 (2 / sigma k) t) (Finset.mem_univ i),
    _root_.GD.N0106.N0428.N0770.N1750.d008377]

theorem d008380 {sigma : ι → ℝ} (hsigma : ∀ i, 0 < sigma i)
    {t : ℝ} (ht : 0 < t) (i : ι) :
    Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω ^ 2 * Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω)))
      (_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) ∧
      (∫ ω, _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω ^ 2 * Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω))
        ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) =
        ((2 / sigma i) ^ 2 / (4 * t) + (2 / sigma i) / (4 * t * Real.sqrt t)) *
          Real.exp (-_root_.GD.N0106.N0428.N0770.N1750.d008368 sigma * Real.sqrt t) := by
  obtain ⟨hi, he⟩ := _root_.GD.N0106.N0428.N0770.N1744.d007172 (_root_.GD.N0106.N0428.N0770.N1750.d008369 sigma)
    (_root_.GD.N0106.N0428.N0770.N1750.d008370 sigma) (_root_.GD.N0106.N0428.N0770.N1750.d008371 sigma) ht i
  refine ⟨hi, he.trans ?_⟩
  simp_rw [_root_.GD.N0106.N0428.N0770.N1750.d008376 hsigma ht, _root_.GD.N0106.N0428.N0770.N1750.d008374 hsigma ht]
  rw [_root_.GD.N0106.N0428.N0770.N1744.d008352, mul_assoc,
    Finset.mul_prod_erase Finset.univ
      (fun k => _root_.GD.N0106.N0428.N0770.N1744.d008350 (2 / sigma k) t) (Finset.mem_univ i),
    _root_.GD.N0106.N0428.N0770.N1750.d008377]

theorem d008381 {sigma : ι → ℝ} (hsigma : ∀ i, 0 < sigma i)
    {t : ℝ} (ht : 0 < t) {i j : ι} (hij : i ≠ j) :
    Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω * _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma j ω *
      Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω))) (_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) ∧
      (∫ ω, _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω * _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma j ω *
        Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω)) ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) =
        ((2 / sigma i) * (2 / sigma j) / (4 * t)) *
          Real.exp (-_root_.GD.N0106.N0428.N0770.N1750.d008368 sigma * Real.sqrt t) := by
  obtain ⟨hi, he⟩ := _root_.GD.N0106.N0428.N0770.N1744.d007173 (_root_.GD.N0106.N0428.N0770.N1750.d008369 sigma)
    (_root_.GD.N0106.N0428.N0770.N1750.d008370 sigma) (_root_.GD.N0106.N0428.N0770.N1750.d008371 sigma) ht hij
  refine ⟨hi, he.trans ?_⟩
  simp_rw [_root_.GD.N0106.N0428.N0770.N1750.d008375 hsigma ht, _root_.GD.N0106.N0428.N0770.N1750.d008374 hsigma ht]
  have hp := _root_.GD.N0106.N0428.N0770.N1744.d007166
    (fun k => _root_.GD.N0106.N0428.N0770.N1744.d008350 (2 / sigma k) t) hij
  have hc : (2 / sigma i) / (2 * Real.sqrt t) * ((2 / sigma j) / (2 * Real.sqrt t)) =
      (2 / sigma i) * (2 / sigma j) / (4 * t) := by
    rw [div_mul_div_comm]
    congr 1
    nlinarith [Real.sq_sqrt ht.le]
  calc
    _ = (((2 / sigma i) / (2 * Real.sqrt t)) * ((2 / sigma j) / (2 * Real.sqrt t))) *
        (_root_.GD.N0106.N0428.N0770.N1744.d008350 (2 / sigma i) t * _root_.GD.N0106.N0428.N0770.N1744.d008350 (2 / sigma j) t *
          ∏ k ∈ (Finset.univ.erase i).erase j, _root_.GD.N0106.N0428.N0770.N1744.d008350 (2 / sigma k) t) := by
      unfold _root_.GD.N0106.N0428.N0770.N1744.d008351
      ring
    _ = _ := by rw [← hp, _root_.GD.N0106.N0428.N0770.N1750.d008377, hc]

end
end GD.N0106.N0428.N0770.N1750

#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008371
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008372
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008373
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008378
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008379
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008380
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008381
