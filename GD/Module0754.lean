import GD.Module0753
import GD.Module0209

set_option autoImplicit false
set_option warningAsError true












open MeasureTheory Set
open scoped BigOperators ContDiff

namespace GD.N0232.N0719.N0989

open _root_.GD.N0232.N0719.N0873
open _root_.GD.N0232.N0720.N1377
open _root_.GD.N0232.N0720.N1379

noncomputable section
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

def d011338 : Set (_root_.GD.N0232.N0719.N0873.d011295 I) := {x | ∀ i, 0 < x.2 i}
def d011339 (p : I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) : ℝ :=
  ∑ i, p i * ((x.1 i) ^ 2 + 2 * x.2 i)
def d011340 (p : I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) : ℝ := ∑ i, p i * x.1 i

def d011341 (p : I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) : _root_.GD.N0232.N0719.N0873.d011295 I →L[ℝ] ℝ :=
  ∑ i, (2 * p i) • (x.1 i • _root_.GD.N0232.N0719.N0873.d011298 i + _root_.GD.N0232.N0719.N0873.d011299 i)
def d011342 (p : I → ℝ) : _root_.GD.N0232.N0719.N0873.d011295 I →L[ℝ] ℝ := ∑ i, p i • _root_.GD.N0232.N0719.N0873.d011298 i

omit [DecidableEq I] in
theorem d011343 (p : I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) :
    HasFDerivAt (_root_.GD.N0232.N0719.N0989.d011339 p) (_root_.GD.N0232.N0719.N0989.d011341 p x) x := by
  unfold _root_.GD.N0232.N0719.N0989.d011339 _root_.GD.N0232.N0719.N0989.d011341
  apply HasFDerivAt.fun_sum
  intro i _
  apply ((((_root_.GD.N0232.N0719.N0873.d011298 i).hasFDerivAt.pow 2).add
    ((_root_.GD.N0232.N0719.N0873.d011299 i).hasFDerivAt.const_mul 2)).const_mul (p i)).congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [smul_eq_mul]
  ring

omit [DecidableEq I] in
theorem d011344 (p : I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) :
    HasFDerivAt (_root_.GD.N0232.N0719.N0989.d011340 p) (_root_.GD.N0232.N0719.N0989.d011342 p) x := by
  convert (_root_.GD.N0232.N0719.N0989.d011342 p).hasFDerivAt (x := x) using 1
  ext y
  simp [_root_.GD.N0232.N0719.N0989.d011342, _root_.GD.N0232.N0719.N0989.d011340, smul_eq_mul]

omit [DecidableEq I] in
theorem d011345 (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    {x : _root_.GD.N0232.N0719.N0873.d011295 I} (hx : x ∈ _root_.GD.N0232.N0719.N0989.d011338) : 0 < _root_.GD.N0232.N0719.N0989.d011339 p x := by
  have hex : ∃ i, 0 < p i := by
    by_contra h
    push Not at h
    have hz : ∀ i, p i = 0 := fun i => le_antisymm (h i) (hp i)
    simp [hz] at hsum
  obtain ⟨i, hi⟩ := hex
  apply Finset.sum_pos' (fun j _ => mul_nonneg (hp j) (by
    have := hx j
    nlinarith [sq_nonneg (x.1 j)]))
  exact ⟨i, Finset.mem_univ i, mul_pos hi (by
    have := hx i
    nlinarith [sq_nonneg (x.1 i)])⟩

def d011346 (n : ℕ) (xi : ℝ) (p : I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) : ℝ :=
  _root_.GD.N0232.N0720.N1377.d002852 n (_root_.GD.N0232.N0719.N0989.d011339 p x) (_root_.GD.N0232.N0719.N0989.d011340 p x * xi)
def d011347 (n : ℕ) (xi : ℝ) (p : I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) : _root_.GD.N0232.N0719.N0873.d011295 I →L[ℝ] ℝ :=
  (-(1 / 2 : ℝ) * _root_.GD.N0232.N0719.N0989.d011346 (n + 2) xi p x) • _root_.GD.N0232.N0719.N0989.d011341 p x +
    (xi * _root_.GD.N0232.N0719.N0989.d011346 (n + 1) xi p x) • _root_.GD.N0232.N0719.N0989.d011342 p

omit [DecidableEq I] in
theorem d011348 (n : ℕ) (xi : ℝ) (p : I → ℝ)
    {x : _root_.GD.N0232.N0719.N0873.d011295 I} (hA : 0 < _root_.GD.N0232.N0719.N0989.d011339 p x) :
    HasFDerivAt (_root_.GD.N0232.N0719.N0989.d011346 n xi p) (_root_.GD.N0232.N0719.N0989.d011347 n xi p x) x := by
  apply ((_root_.GD.N0232.N0720.N1379.d002889 n (p := (_root_.GD.N0232.N0719.N0989.d011339 p x, _root_.GD.N0232.N0719.N0989.d011340 p x * xi)) hA).comp x
    ((_root_.GD.N0232.N0719.N0989.d011343 p x).prodMk ((_root_.GD.N0232.N0719.N0989.d011344 p x).mul_const xi))).congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [_root_.GD.N0232.N0719.N0989.d011347, _root_.GD.N0232.N0719.N0989.d011346,
    _root_.GD.N0232.N0720.N1379.d002883, smul_eq_mul]
  ring

omit [DecidableEq I] in
theorem d011349 (n : ℕ) (xi : ℝ) (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ContDiffOn ℝ ∞ (_root_.GD.N0232.N0719.N0989.d011346 n xi p) _root_.GD.N0232.N0719.N0989.d011338 := by
  have hq : ContDiff ℝ ∞ (_root_.GD.N0232.N0719.N0989.d011339 p) := by unfold _root_.GD.N0232.N0719.N0989.d011339; fun_prop
  have hl : ContDiff ℝ ∞ (_root_.GD.N0232.N0719.N0989.d011340 p) := by unfold _root_.GD.N0232.N0719.N0989.d011340; fun_prop
  exact (_root_.GD.N0232.N0720.N1379.d002891 n).comp
    (hq.prodMk (hl.mul contDiff_const)).contDiffOn
    (fun x hx => _root_.GD.N0232.N0719.N0989.d011345 p hp hsum hx)

theorem d011350 (n : ℕ) (xi : ℝ) (p : I → ℝ)
    {x : _root_.GD.N0232.N0719.N0873.d011295 I} (hA : 0 < _root_.GD.N0232.N0719.N0989.d011339 p x) (i : I) :
    fderiv ℝ (_root_.GD.N0232.N0719.N0989.d011346 n xi p) x (_root_.GD.N0232.N0719.N0873.d011296 i) =
      -p i * x.1 i * _root_.GD.N0232.N0719.N0989.d011346 (n + 2) xi p x +
        p i * xi * _root_.GD.N0232.N0719.N0989.d011346 (n + 1) xi p x := by
  rw [(_root_.GD.N0232.N0719.N0989.d011348 n xi p hA).fderiv]
  simp [_root_.GD.N0232.N0719.N0989.d011347, _root_.GD.N0232.N0719.N0989.d011341, _root_.GD.N0232.N0719.N0989.d011342, _root_.GD.N0232.N0719.N0873.d011296, _root_.GD.N0232.N0719.N0873.d011298,
    _root_.GD.N0232.N0719.N0873.d011299, Pi.single_apply, smul_eq_mul]
  ring

theorem d011351 (n : ℕ) (xi : ℝ) (p : I → ℝ)
    {x : _root_.GD.N0232.N0719.N0873.d011295 I} (hA : 0 < _root_.GD.N0232.N0719.N0989.d011339 p x) (i : I) :
    fderiv ℝ (_root_.GD.N0232.N0719.N0989.d011346 n xi p) x (_root_.GD.N0232.N0719.N0873.d011297 i) = -p i * _root_.GD.N0232.N0719.N0989.d011346 (n + 2) xi p x := by
  rw [(_root_.GD.N0232.N0719.N0989.d011348 n xi p hA).fderiv]
  simp [_root_.GD.N0232.N0719.N0989.d011347, _root_.GD.N0232.N0719.N0989.d011341, _root_.GD.N0232.N0719.N0989.d011342, _root_.GD.N0232.N0719.N0873.d011297, _root_.GD.N0232.N0719.N0873.d011298,
    _root_.GD.N0232.N0719.N0873.d011299, Pi.single_apply, smul_eq_mul]
  ring

def d011352 (n : ℕ) (weight xi : J → ℝ) (p : J → I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) : ℝ :=
  ∑ j, weight j * _root_.GD.N0232.N0719.N0989.d011346 (n + 1) (xi j) (p j) x
def d011353 (n : ℕ) (weight xi : J → ℝ) (p : J → I → ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) : ℝ :=
  ∑ j, weight j * xi j * _root_.GD.N0232.N0719.N0989.d011346 n (xi j) (p j) x

omit [DecidableEq I] in
theorem d011354 (n : ℕ) (weight xi : J → ℝ) (p : J → I → ℝ)
    (hp : ∀ j i, 0 ≤ p j i) (hsum : ∀ j, ∑ i, p j i = 1) :
    ContDiffOn ℝ ∞ (_root_.GD.N0232.N0719.N0989.d011352 n weight xi p) _root_.GD.N0232.N0719.N0989.d011338 := by
  exact ContDiffOn.sum fun j _ => contDiffOn_const.mul
    (_root_.GD.N0232.N0719.N0989.d011349 (n + 1) (xi j) (p j) (hp j) (hsum j))

omit [DecidableEq I] in
theorem d011355 (n : ℕ) (weight xi : J → ℝ) (p : J → I → ℝ)
    (hp : ∀ j i, 0 ≤ p j i) (hsum : ∀ j, ∑ i, p j i = 1) :
    ContDiffOn ℝ ∞ (_root_.GD.N0232.N0719.N0989.d011353 n weight xi p) _root_.GD.N0232.N0719.N0989.d011338 := by
  exact ContDiffOn.sum fun j _ => contDiffOn_const.mul
    (_root_.GD.N0232.N0719.N0989.d011349 n (xi j) (p j) (hp j) (hsum j))

omit [DecidableEq I] in
theorem d011356 (n : ℕ) (weight xi : J → ℝ) (p : J → I → ℝ)
    (hw : ∀ j, 0 ≤ weight j) (hwpos : ∃ j, 0 < weight j)
    (hp : ∀ j i, 0 ≤ p j i) (hsum : ∀ j, ∑ i, p j i = 1)
    {x : _root_.GD.N0232.N0719.N0873.d011295 I} (hx : x ∈ _root_.GD.N0232.N0719.N0989.d011338) : 0 < _root_.GD.N0232.N0719.N0989.d011352 n weight xi p x := by
  have hpos j : 0 < _root_.GD.N0232.N0719.N0989.d011346 (n + 1) (xi j) (p j) x :=
    _root_.GD.N0232.N0720.N1377.d002861 (n + 1) (_root_.GD.N0232.N0719.N0989.d011345 (p j) (hp j) (hsum j) hx) _
  obtain ⟨j, hj⟩ := hwpos
  exact Finset.sum_pos' (fun l _ => mul_nonneg (hw l) (hpos l).le)
    ⟨j, Finset.mem_univ j, mul_pos hj (hpos j)⟩


theorem d011357 (n : ℕ) (weight xi : J → ℝ) (p : J → I → ℝ)
    {x : _root_.GD.N0232.N0719.N0873.d011295 I} (hA : ∀ j, 0 < _root_.GD.N0232.N0719.N0989.d011339 (p j) x) (i : I) :
    fderiv ℝ (_root_.GD.N0232.N0719.N0989.d011353 n weight xi p) x (_root_.GD.N0232.N0719.N0873.d011297 i) =
      x.1 i * fderiv ℝ (_root_.GD.N0232.N0719.N0989.d011352 n weight xi p) x (_root_.GD.N0232.N0719.N0873.d011297 i) -
        fderiv ℝ (_root_.GD.N0232.N0719.N0989.d011352 n weight xi p) x (_root_.GD.N0232.N0719.N0873.d011296 i) := by
  have hd (j : J) (m : ℕ) := (_root_.GD.N0232.N0719.N0989.d011348 m (xi j) (p j) (hA j)).differentiableAt
  unfold _root_.GD.N0232.N0719.N0989.d011352 _root_.GD.N0232.N0719.N0989.d011353
  rw [fderiv_fun_sum (fun j _ => (hd j n).const_mul (weight j * xi j)),
    fderiv_fun_sum (fun j _ => (hd j (n + 1)).const_mul (weight j))]
  simp only [sum_apply, fderiv_const_mul (hd _ _), smul_apply, smul_eq_mul,
    _root_.GD.N0232.N0719.N0989.d011351 _ _ _ (hA _), _root_.GD.N0232.N0719.N0989.d011350 _ _ _ (hA _)]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Nat.add_assoc]
  ring

def d011358 (a : ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) : _root_.GD.N0232.N0719.N0873.d011295 I := (a • x.1, a ^ 2 • x.2)

omit [DecidableEq I] in
theorem d011359 (p : I → ℝ) (a : ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) :
    _root_.GD.N0232.N0719.N0989.d011339 p (_root_.GD.N0232.N0719.N0989.d011358 a x) = a ^ 2 * _root_.GD.N0232.N0719.N0989.d011339 p x := by
  unfold _root_.GD.N0232.N0719.N0989.d011339 _root_.GD.N0232.N0719.N0989.d011358
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

omit [DecidableEq I] in
theorem d011360 (p : I → ℝ) (a : ℝ) (x : _root_.GD.N0232.N0719.N0873.d011295 I) :
    _root_.GD.N0232.N0719.N0989.d011340 p (_root_.GD.N0232.N0719.N0989.d011358 a x) = a * _root_.GD.N0232.N0719.N0989.d011340 p x := by
  unfold _root_.GD.N0232.N0719.N0989.d011340 _root_.GD.N0232.N0719.N0989.d011358
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

omit [DecidableEq I] in
theorem d011361 (n : ℕ) (xi : ℝ) (p : I → ℝ)
    {a : ℝ} (ha : 0 < a) (x : _root_.GD.N0232.N0719.N0873.d011295 I) :
    _root_.GD.N0232.N0719.N0989.d011346 n xi p (_root_.GD.N0232.N0719.N0989.d011358 a x) = (a ^ (n + 1))⁻¹ * _root_.GD.N0232.N0719.N0989.d011346 n xi p x := by
  unfold _root_.GD.N0232.N0719.N0989.d011346
  rw [_root_.GD.N0232.N0719.N0989.d011359, _root_.GD.N0232.N0719.N0989.d011360, mul_assoc,
    _root_.GD.N0232.N0720.N1377.d002866 n _ _ ha]

omit [DecidableEq I] in
theorem d011362 (n : ℕ) (weight xi : J → ℝ) (p : J → I → ℝ)
    {a : ℝ} (ha : 0 < a) (x : _root_.GD.N0232.N0719.N0873.d011295 I) :
    _root_.GD.N0232.N0719.N0989.d011352 n weight xi p (_root_.GD.N0232.N0719.N0989.d011358 a x) =
      (a ^ (n + 2))⁻¹ * _root_.GD.N0232.N0719.N0989.d011352 n weight xi p x := by
  unfold _root_.GD.N0232.N0719.N0989.d011352
  simp_rw [_root_.GD.N0232.N0719.N0989.d011361 _ _ _ ha]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Nat.add_assoc]
  ring

omit [DecidableEq I] in
theorem d011363 (n : ℕ) (weight xi : J → ℝ) (p : J → I → ℝ)
    {a : ℝ} (ha : 0 < a) (x : _root_.GD.N0232.N0719.N0873.d011295 I) :
    _root_.GD.N0232.N0719.N0989.d011353 n weight xi p (_root_.GD.N0232.N0719.N0989.d011358 a x) =
      (a ^ (n + 1))⁻¹ * _root_.GD.N0232.N0719.N0989.d011353 n weight xi p x := by
  unfold _root_.GD.N0232.N0719.N0989.d011353
  simp_rw [_root_.GD.N0232.N0719.N0989.d011361 _ _ _ ha]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq I] in

theorem d011364 (xi : ℝ) (p : I → ℝ) (hsum : ∑ i, p i = 1)
    (x : _root_.GD.N0232.N0719.N0873.d011295 I) {r : ℝ} (hr : r ≠ 0) :
    _root_.GD.N0232.N0719.N0873.d011302 (xi / r) (fun i => r ^ 2 * p i) x =
      _root_.GD.N0232.N0719.N0989.d011339 p x / 2 * r ^ 2 - _root_.GD.N0232.N0719.N0989.d011340 p x * xi * r + xi ^ 2 / 2 := by
  unfold _root_.GD.N0232.N0719.N0873.d011302 _root_.GD.N0232.N0719.N0989.d011339 _root_.GD.N0232.N0719.N0989.d011340
  calc
    _ = ∑ i, (p i * ((x.1 i) ^ 2 + 2 * x.2 i) / 2 * r ^ 2 -
        p i * x.1 i * xi * r + p i * (xi ^ 2 / 2)) := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.sum_div, hsum, one_mul]

omit [DecidableEq I] in

theorem d011365 (n : ℕ) (xi : ℝ) (p : I → ℝ)
    (hsum : ∑ i, p i = 1) (x : _root_.GD.N0232.N0719.N0873.d011295 I) :
    _root_.GD.N0232.N0719.N0989.d011346 n xi p x = Real.exp (xi ^ 2 / 2) *
      ∫ r in Ioi 0, r ^ n * _root_.GD.N0232.N0719.N0873.d011306 1 (xi / r) (fun i => r ^ 2 * p i) x := by
  rw [← integral_const_mul]
  unfold _root_.GD.N0232.N0719.N0989.d011346 _root_.GD.N0232.N0720.N1377.d002852
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  change r ^ n * Real.exp (-_root_.GD.N0232.N0719.N0989.d011339 p x / 2 * r ^ 2 + _root_.GD.N0232.N0719.N0989.d011340 p x * xi * r) =
    Real.exp (xi ^ 2 / 2) * (r ^ n *
      (1 * Real.exp (-_root_.GD.N0232.N0719.N0873.d011302 (xi / r) (fun i => r ^ 2 * p i) x)))
  rw [one_mul, _root_.GD.N0232.N0719.N0989.d011364 xi p hsum x (ne_of_gt hr)]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

end
end GD.N0232.N0719.N0989

#print axioms _root_.GD.N0232.N0719.N0989.d011357
#print axioms _root_.GD.N0232.N0719.N0989.d011362
#print axioms _root_.GD.N0232.N0719.N0989.d011365
