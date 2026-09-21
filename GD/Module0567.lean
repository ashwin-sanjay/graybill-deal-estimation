import GD.Module0566




set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators

namespace GD.N0106.N0428.N0770.N1750
noncomputable section

open _root_.GD.N0106.N0428.N0770.N1702
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def d008382 (sigma : ι → ℝ) (i : ι) (ω : ι → ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω / _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω

theorem d008383 (sigma : ι → ℝ) : Measurable (_root_.GD.N0106.N0428.N0770.N1750.d008367 sigma) := by
  unfold _root_.GD.N0106.N0428.N0770.N1750.d008367
  exact Finset.measurable_sum _ (fun i _ => _root_.GD.N0106.N0428.N0770.N1750.d008369 sigma i)

theorem d008384 (sigma : ι → ℝ) (i : ι) :
    Measurable (_root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i) :=
  (_root_.GD.N0106.N0428.N0770.N1750.d008369 sigma i).div (_root_.GD.N0106.N0428.N0770.N1750.d008383 sigma)

theorem d008385 (sigma : ι → ℝ) (i : ι) (ω : ι → ℝ) :
    0 ≤ _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω := _root_.GD.N0106.N0428.N0770.N1702.d008359 _ _

theorem d008386 (sigma : ι → ℝ) (ω : ι → ℝ) :
    0 ≤ _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω :=
  Finset.sum_nonneg (fun i _ => _root_.GD.N0106.N0428.N0770.N1750.d008385 sigma i ω)

theorem d008387 (sigma : ι → ℝ) (i : ι) (ω : ι → ℝ) :
    _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω ≤ _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω :=
  Finset.single_le_sum (fun j _ => _root_.GD.N0106.N0428.N0770.N1750.d008385 sigma j ω) (Finset.mem_univ i)

theorem d008388 (sigma : ι → ℝ) (i : ι) (ω : ι → ℝ) :
    0 ≤ _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i ω :=
  div_nonneg (_root_.GD.N0106.N0428.N0770.N1750.d008385 sigma i ω) (_root_.GD.N0106.N0428.N0770.N1750.d008386 sigma ω)

theorem d008389 (sigma : ι → ℝ) (i : ι) (ω : ι → ℝ) :
    _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i ω ≤ 1 := by
  by_cases hzero : _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω = 0
  · simp [_root_.GD.N0106.N0428.N0770.N1750.d008382, hzero]
  · have hp : 0 < _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω :=
      lt_of_le_of_ne (_root_.GD.N0106.N0428.N0770.N1750.d008386 sigma ω) (Ne.symm hzero)
    exact (div_le_one hp).mpr (_root_.GD.N0106.N0428.N0770.N1750.d008387 sigma i ω)

theorem d008390 (sigma : ι → ℝ) (i : ι) (n : ℕ) :
    Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i ω ^ n) (_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((_root_.GD.N0106.N0428.N0770.N1750.d008384 sigma i).pow_const n).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (_root_.GD.N0106.N0428.N0770.N1750.d008388 sigma i ω) n)]
  exact pow_le_one₀ (_root_.GD.N0106.N0428.N0770.N1750.d008388 sigma i ω) (_root_.GD.N0106.N0428.N0770.N1750.d008389 sigma i ω)

theorem d008391 (sigma : ι → ℝ) (i j : ι) :
    Integrable (fun ω => _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i ω * _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma j ω)
      (_root_.GD.N0106.N0428.N0770.N1750.d008364 ι) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((_root_.GD.N0106.N0428.N0770.N1750.d008384 sigma i).mul (_root_.GD.N0106.N0428.N0770.N1750.d008384 sigma j)).aestronglyMeasurable
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (_root_.GD.N0106.N0428.N0770.N1750.d008388 sigma i ω) (_root_.GD.N0106.N0428.N0770.N1750.d008388 sigma j ω))]
  simpa using mul_le_mul (_root_.GD.N0106.N0428.N0770.N1750.d008389 sigma i ω)
    (_root_.GD.N0106.N0428.N0770.N1750.d008389 sigma j ω) (_root_.GD.N0106.N0428.N0770.N1750.d008388 sigma j ω) (by norm_num : (0 : ℝ) ≤ 1)

theorem d008392 {sigma : ι → ℝ}
    (hsigma : ∀ i, 0 < sigma i) (i : ι) :
    ∀ᵐ ω ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι, 0 < _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i ω := by
  letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
  have hn : ∀ᵐ ω ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι, ω i ≠ 0 :=
    Measure.ae_eval_ne (fun _ : ι => gaussianReal 0 1) i 0
  filter_upwards [hn] with ω hω
  exact div_pos (by norm_num) (mul_pos (sq_pos_of_pos (hsigma i)) (sq_pos_of_ne_zero hω))

theorem d008393 [Nonempty ι] {sigma : ι → ℝ}
    (hsigma : ∀ i, 0 < sigma i) :
    ∀ᵐ ω ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι, 0 < _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma ω := by
  let i : ι := Classical.choice inferInstance
  filter_upwards [_root_.GD.N0106.N0428.N0770.N1750.d008392 hsigma i] with ω hω
  exact hω.trans_le (_root_.GD.N0106.N0428.N0770.N1750.d008387 sigma i ω)

theorem d008394 [Nonempty ι] {sigma : ι → ℝ}
    (hsigma : ∀ i, 0 < sigma i) : 0 < _root_.GD.N0106.N0428.N0770.N1750.d008368 sigma := by
  let i : ι := Classical.choice inferInstance
  have hi : 0 < 2 / sigma i := div_pos (by norm_num) (hsigma i)
  exact hi.trans_le (Finset.single_le_sum
    (fun j _ => (div_pos (by norm_num : (0 : ℝ) < 2) (hsigma j)).le) (Finset.mem_univ i))

theorem d008395 [Nonempty ι] {sigma : ι → ℝ}
    (hsigma : ∀ i, 0 < sigma i) :
    ∀ᵐ ω ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 ι, (∑ i, _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i ω) = 1 := by
  filter_upwards [_root_.GD.N0106.N0428.N0770.N1750.d008393 hsigma] with ω hω
  simp only [_root_.GD.N0106.N0428.N0770.N1750.d008382, ← Finset.sum_div]
  exact div_self hω.ne'

end
end GD.N0106.N0428.N0770.N1750

#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008389
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008390
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008391
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008392
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008393
#print axioms _root_.GD.N0106.N0428.N0770.N1750.d008395
