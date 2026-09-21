import GD.Module0567
import GD.Module0485
import GD.Module0483
import Mathlib.Probability.Moments.Covariance






set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace GD.N0106.N0428.N0770.N1750
noncomputable section

open _root_.GD.N0106.N0428.N0770.N1752
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem d008396 {sigma : ι → ℝ}
    (hsigma : ∀ i, 0 < sigma i) {t : ℝ} (ht : 0 < t) (i : ι) :
    (∫⁻ ω, ENNReal.ofReal (_root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω *
      Real.exp (-(_root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω * t))) ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) =
      ENNReal.ofReal (_root_.GD.N0106.N0428.N0770.N1752.d007497 (2 / sigma i) (_root_.GD.N0106.N0428.N0770.N1750.d008368 sigma) t) := by
  obtain ⟨hi, he⟩ := _root_.GD.N0106.N0428.N0770.N1750.d008379 hsigma ht i
  have hswap : ∀ ω, _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω * t = t * _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω :=
    fun ω => mul_comm (_root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω) t
  simp_rw [hswap]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ω =>
    mul_nonneg (_root_.GD.N0106.N0428.N0770.N1750.d008385 sigma i ω) (Real.exp_pos _).le), he]
  rfl

theorem d008397 {sigma : ι → ℝ}
    (hsigma : ∀ i, 0 < sigma i) {t : ℝ} (ht : 0 < t) (i : ι) :
    (∫⁻ ω, ENNReal.ofReal (t * _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω ^ 2 *
      Real.exp (-(_root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω * t))) ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) =
      ENNReal.ofReal (_root_.GD.N0106.N0428.N0770.N1752.d007498 (2 / sigma i) (_root_.GD.N0106.N0428.N0770.N1750.d008368 sigma) t) := by
  obtain ⟨hi, he⟩ := _root_.GD.N0106.N0428.N0770.N1750.d008380 hsigma ht i
  have hswap : ∀ ω, _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω * t = t * _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω :=
    fun ω => mul_comm (_root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω) t
  simp_rw [hswap, mul_assoc]
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul t) (ae_of_all _ fun ω =>
    mul_nonneg ht.le (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)),
    integral_const_mul, he]
  rfl

theorem d008398 {sigma : ι → ℝ}
    (hsigma : ∀ i, 0 < sigma i) {t : ℝ} (ht : 0 < t)
    {i j : ι} (hij : i ≠ j) :
    (∫⁻ ω, ENNReal.ofReal (t * _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω *
      _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma j ω * Real.exp (-(_root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω * t)))
        ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) =
      ENNReal.ofReal (_root_.GD.N0106.N0428.N0770.N1752.d007499 (2 / sigma i) (2 / sigma j) (_root_.GD.N0106.N0428.N0770.N1750.d008368 sigma) t) := by
  obtain ⟨hi, he⟩ := _root_.GD.N0106.N0428.N0770.N1750.d008381 hsigma ht hij
  have hscale : ∀ ω, t * _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω * _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma j ω *
      Real.exp (-(_root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω * t)) =
      t * (_root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω * _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma j ω *
        Real.exp (-(t * _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω))) := by
    intro ω
    rw [mul_comm (_root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω) t]
    ring
  simp_rw [hscale]
  rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul t) (ae_of_all _ fun ω =>
    mul_nonneg ht.le (mul_nonneg (mul_nonneg (_root_.GD.N0106.N0428.N0770.N1750.d008385 sigma i ω)
      (_root_.GD.N0106.N0428.N0770.N1750.d008385 sigma j ω)) (Real.exp_pos _).le)),
    integral_const_mul, he]
  rfl



theorem d008399 [Nonempty ι] {sigma : ι → ℝ}
    (hsigma : ∀ i, 0 < sigma i) (i : ι) :
    (∫ ω, _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i ω ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) =
      (2 / sigma i) / _root_.GD.N0106.N0428.N0770.N1750.d008368 sigma := by
  have hc : 0 < 2 / sigma i := div_pos (by norm_num) (hsigma i)
  have hC := _root_.GD.N0106.N0428.N0770.N1750.d008394 hsigma
  obtain ⟨hscalar, hvalue⟩ := _root_.GD.N0106.N0428.N0770.N1752.d007506 hc hC
  have hw : Integrable (_root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i) (_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) := by
    simpa only [pow_one] using _root_.GD.N0106.N0428.N0770.N1750.d008390 sigma i 1
  apply (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg (_root_.GD.N0106.N0428.N0770.N1750.d008388 sigma i)) (div_nonneg hc.le hC.le)).mp
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (_root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i ω) ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι :=
      ofReal_integral_eq_lintegral_ofReal hw
        (ae_of_all _ (_root_.GD.N0106.N0428.N0770.N1750.d008388 sigma i))
    _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ ω, ENNReal.ofReal (_root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω *
        Real.exp (-(_root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω * t))) ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι :=
      _root_.GD.N0106.N0428.N0770.d007514 (_root_.GD.N0106.N0428.N0770.N1750.d008364 ι)
        (_root_.GD.N0106.N0428.N0770.N1750.d008369 sigma i) (_root_.GD.N0106.N0428.N0770.N1750.d008383 sigma)
        (_root_.GD.N0106.N0428.N0770.N1750.d008370 sigma i) (_root_.GD.N0106.N0428.N0770.N1750.d008393 hsigma)
    _ = ∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal (_root_.GD.N0106.N0428.N0770.N1752.d007497 (2 / sigma i) (_root_.GD.N0106.N0428.N0770.N1750.d008368 sigma) t) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact _root_.GD.N0106.N0428.N0770.N1750.d008396 hsigma ht i
    _ = ENNReal.ofReal (∫ t : ℝ in Ioi 0,
        _root_.GD.N0106.N0428.N0770.N1752.d007497 (2 / sigma i) (_root_.GD.N0106.N0428.N0770.N1750.d008368 sigma) t) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal hscalar
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      unfold _root_.GD.N0106.N0428.N0770.N1752.d007497
      positivity
    _ = _ := congrArg ENNReal.ofReal hvalue


theorem d008400 [Nonempty ι] {sigma : ι → ℝ}
    (hsigma : ∀ i, 0 < sigma i) (i : ι) :
    (∫ ω, _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i ω ^ 2 ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) =
      (((2 / sigma i) / _root_.GD.N0106.N0428.N0770.N1750.d008368 sigma) ^ 2 + (2 / sigma i) / _root_.GD.N0106.N0428.N0770.N1750.d008368 sigma) / 2 := by
  have hc : 0 < 2 / sigma i := div_pos (by norm_num) (hsigma i)
  have hC := _root_.GD.N0106.N0428.N0770.N1750.d008394 hsigma
  obtain ⟨hscalar, hvalue⟩ := _root_.GD.N0106.N0428.N0770.N1752.d007507 hc hC
  apply (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg fun ω => sq_nonneg (_root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i ω)) (by positivity)).mp
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (_root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i ω ^ 2) ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι :=
      ofReal_integral_eq_lintegral_ofReal (_root_.GD.N0106.N0428.N0770.N1750.d008390 sigma i 2)
        (ae_of_all _ fun ω => sq_nonneg (_root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i ω))
    _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ ω, ENNReal.ofReal (t * _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω ^ 2 *
        Real.exp (-(_root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω * t))) ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι :=
      _root_.GD.N0106.N0428.N0770.d007511 (_root_.GD.N0106.N0428.N0770.N1750.d008364 ι)
        (_root_.GD.N0106.N0428.N0770.N1750.d008369 sigma i) (_root_.GD.N0106.N0428.N0770.N1750.d008383 sigma)
        (_root_.GD.N0106.N0428.N0770.N1750.d008393 hsigma)
    _ = ∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal (_root_.GD.N0106.N0428.N0770.N1752.d007498 (2 / sigma i) (_root_.GD.N0106.N0428.N0770.N1750.d008368 sigma) t) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact _root_.GD.N0106.N0428.N0770.N1750.d008397 hsigma ht i
    _ = ENNReal.ofReal (∫ t : ℝ in Ioi 0,
        _root_.GD.N0106.N0428.N0770.N1752.d007498 (2 / sigma i) (_root_.GD.N0106.N0428.N0770.N1750.d008368 sigma) t) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal hscalar
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      unfold _root_.GD.N0106.N0428.N0770.N1752.d007498
      change 0 < t at ht
      positivity
    _ = _ := congrArg ENNReal.ofReal hvalue


theorem d008401 [Nonempty ι] {sigma : ι → ℝ}
    (hsigma : ∀ i, 0 < sigma i) {i j : ι} (hij : i ≠ j) :
    (∫ ω, _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i ω * _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma j ω ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) =
      (2 / sigma i) * (2 / sigma j) / (2 * _root_.GD.N0106.N0428.N0770.N1750.d008368 sigma ^ 2) := by
  have hc : 0 < 2 / sigma i := div_pos (by norm_num) (hsigma i)
  have hd : 0 < 2 / sigma j := div_pos (by norm_num) (hsigma j)
  have hC := _root_.GD.N0106.N0428.N0770.N1750.d008394 hsigma
  obtain ⟨hscalar, hvalue⟩ := _root_.GD.N0106.N0428.N0770.N1752.d007508 hc hd hC
  apply (ENNReal.ofReal_eq_ofReal_iff
    (integral_nonneg fun ω => mul_nonneg (_root_.GD.N0106.N0428.N0770.N1750.d008388 sigma i ω)
      (_root_.GD.N0106.N0428.N0770.N1750.d008388 sigma j ω)) (by positivity)).mp
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (_root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i ω * _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma j ω)
        ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι :=
      ofReal_integral_eq_lintegral_ofReal (_root_.GD.N0106.N0428.N0770.N1750.d008391 sigma i j)
        (ae_of_all _ fun ω => mul_nonneg (_root_.GD.N0106.N0428.N0770.N1750.d008388 sigma i ω)
          (_root_.GD.N0106.N0428.N0770.N1750.d008388 sigma j ω))
    _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ ω, ENNReal.ofReal (t * _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω *
        _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma j ω * Real.exp (-(_root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω * t)))
          ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι :=
      _root_.GD.N0106.N0428.N0770.d007516 (_root_.GD.N0106.N0428.N0770.N1750.d008364 ι)
        (_root_.GD.N0106.N0428.N0770.N1750.d008369 sigma i) (_root_.GD.N0106.N0428.N0770.N1750.d008369 sigma j)
        (_root_.GD.N0106.N0428.N0770.N1750.d008383 sigma) (_root_.GD.N0106.N0428.N0770.N1750.d008370 sigma i)
        (_root_.GD.N0106.N0428.N0770.N1750.d008370 sigma j) (_root_.GD.N0106.N0428.N0770.N1750.d008393 hsigma)
    _ = ∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal (_root_.GD.N0106.N0428.N0770.N1752.d007499 (2 / sigma i) (2 / sigma j) (_root_.GD.N0106.N0428.N0770.N1750.d008368 sigma) t) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact _root_.GD.N0106.N0428.N0770.N1750.d008398 hsigma ht hij
    _ = ENNReal.ofReal (∫ t : ℝ in Ioi 0,
        _root_.GD.N0106.N0428.N0770.N1752.d007499 (2 / sigma i) (2 / sigma j) (_root_.GD.N0106.N0428.N0770.N1750.d008368 sigma) t) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal hscalar
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      unfold _root_.GD.N0106.N0428.N0770.N1752.d007499
      change 0 < t at ht
      positivity
    _ = _ := congrArg ENNReal.ofReal hvalue

theorem d008402 (sigma : ι → ℝ) (i : ι) :
    MemLp (_root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i) 2 (_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) :=
  (memLp_two_iff_integrable_sq (_root_.GD.N0106.N0428.N0770.N1750.d008384 sigma i).aestronglyMeasurable).mpr
    (_root_.GD.N0106.N0428.N0770.N1750.d008390 sigma i 2)


theorem d008403 [Nonempty ι] {sigma : ι → ℝ}
    (hsigma : ∀ i, 0 < sigma i) {i j : ι} (hij : i ≠ j) :
    covariance (_root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i) (_root_.GD.N0106.N0428.N0770.N1750.d008382 sigma j) (_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) =
      -((2 / sigma i) * (2 / sigma j) / (2 * _root_.GD.N0106.N0428.N0770.N1750.d008368 sigma ^ 2)) := by
  rw [covariance_eq_sub (_root_.GD.N0106.N0428.N0770.N1750.d008402 sigma i) (_root_.GD.N0106.N0428.N0770.N1750.d008402 sigma j)]
  change (∫ ω, _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i ω * _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma j ω ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) -
    (∫ ω, _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i ω ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) *
      (∫ ω, _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma j ω ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) = _
  rw [_root_.GD.N0106.N0428.N0770.N1750.d008401 hsigma hij,
    _root_.GD.N0106.N0428.N0770.N1750.d008399 hsigma i, _root_.GD.N0106.N0428.N0770.N1750.d008399 hsigma j]
  ring


theorem d008404 [Nonempty ι] {sigma : ι → ℝ}
    (hsigma : ∀ i, 0 < sigma i) (i : ι) :
    covariance (_root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i) (_root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i) (_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) =
      ((2 / sigma i) / _root_.GD.N0106.N0428.N0770.N1750.d008368 sigma) * (1 - (2 / sigma i) / _root_.GD.N0106.N0428.N0770.N1750.d008368 sigma) / 2 := by
  rw [covariance_eq_sub (_root_.GD.N0106.N0428.N0770.N1750.d008402 sigma i) (_root_.GD.N0106.N0428.N0770.N1750.d008402 sigma i)]
  change (∫ ω, _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i ω * _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i ω ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) -
    (∫ ω, _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i ω ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) *
      (∫ ω, _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i ω ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) = _
  simp_rw [← sq]
  rw [_root_.GD.N0106.N0428.N0770.N1750.d008400 hsigma i, _root_.GD.N0106.N0428.N0770.N1750.d008399 hsigma i]
  ring

end
end GD.N0106.N0428.N0770.N1750

#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008396
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008397
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008398
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008399
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008400
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008401
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008402
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008403
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008404
