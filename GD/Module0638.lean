import GD.Module0637
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence











noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory NNReal

namespace GD.N0232.N0719.N0885

variable {ι : Type*} [Fintype ι]


def d009311 (p : ι → ℝ) (y : ι → ℝ) : ℝ := ∑ i, p i * y i


def d009312 (p : ι → ℝ) (y : ι → ℝ) : ι → ℝ :=
  fun i => y i - _root_.GD.N0232.N0719.N0885.d009311 p y

def d009313 (p : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, p i • ContinuousLinearMap.proj i

@[simp] theorem d009314 (p : ι → ℝ) (y : ι → ℝ) :
    _root_.GD.N0232.N0719.N0885.d009313 p y = _root_.GD.N0232.N0719.N0885.d009311 p y := by
  simp [_root_.GD.N0232.N0719.N0885.d009313, _root_.GD.N0232.N0719.N0885.d009311]

theorem d009315 (m : ℝ) (v : ι → ℝ≥0) (i : ι) :
    HasGaussianLaw (fun y : ι → ℝ => y i)
      (Measure.pi (fun j => gaussianReal m (v j))) where
  isGaussian_map := by
    rw [(measurePreserving_eval (fun j => gaussianReal m (v j)) i).map_eq]
    infer_instance

theorem d009316 (m : ℝ) (v : ι → ℝ≥0) :
    HasGaussianLaw (fun y : ι → ℝ => y)
      (Measure.pi (fun j => gaussianReal m (v j))) := by
  exact (iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)).hasGaussianLaw
    (_root_.GD.N0232.N0719.N0885.d009315 m v)

theorem d009317 [DecidableEq ι] (m : ℝ) (v : ι → ℝ≥0) (i j : ι) :
    cov[fun y : ι → ℝ => y i, fun y => y j;
      Measure.pi (fun j => gaussianReal m (v j))] =
      if i = j then (v i : ℝ) else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl, covariance_self (measurable_pi_apply i).aemeasurable]
    calc
      _ = Var[id; gaussianReal m (v i)] :=
        (measurePreserving_eval (fun j => gaussianReal m (v j)) i).variance_fun_comp
          measurable_id.aemeasurable
      _ = _ := variance_id_gaussianReal
  · rw [if_neg hij]
    have h : IndepFun (fun y : ι → ℝ => y i) (fun y => y j)
        (Measure.pi (fun j => gaussianReal m (v j))) :=
      (iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hij
    exact h.covariance_eq_zero (_root_.GD.N0232.N0719.N0885.d009315 m v i).memLp_two
      (_root_.GD.N0232.N0719.N0885.d009315 m v j).memLp_two

theorem d009318 (m : ℝ) (v : ι → ℝ≥0) (p : ι → ℝ) :
    HasGaussianLaw (_root_.GD.N0232.N0719.N0885.d009311 p) (Measure.pi (fun j => gaussianReal m (v j))) := by
  simpa using (_root_.GD.N0232.N0719.N0885.d009316 m v).map_fun (_root_.GD.N0232.N0719.N0885.d009313 p)

theorem d009319
    (m : ℝ) (v : ι → ℝ≥0) (p : ι → ℝ) (j : ι) :
    cov[_root_.GD.N0232.N0719.N0885.d009311 p, fun y => y j;
      Measure.pi (fun j => gaussianReal m (v j))] = p j * (v j : ℝ) := by
  classical
  unfold _root_.GD.N0232.N0719.N0885.d009311
  rw [covariance_fun_sum_left]
  · simp_rw [covariance_const_mul_left, _root_.GD.N0232.N0719.N0885.d009317]
    simp
  · exact fun i => (_root_.GD.N0232.N0719.N0885.d009315 m v i).memLp_two.const_mul (p i)
  · exact (_root_.GD.N0232.N0719.N0885.d009315 m v j).memLp_two



theorem d009320
    (m : ℝ) (v : ι → ℝ≥0) (p : ι → ℝ) (c : ℝ)
    (hp : ∑ i, p i = 1) (hpv : ∀ i, p i * (v i : ℝ) = c) :
    cov[_root_.GD.N0232.N0719.N0885.d009311 p, _root_.GD.N0232.N0719.N0885.d009311 p;
      Measure.pi (fun j => gaussianReal m (v j))] = c := by
  change cov[_root_.GD.N0232.N0719.N0885.d009311 p, fun y => ∑ i, p i * y i; _] = c
  rw [covariance_fun_sum_right]
  · simp_rw [covariance_const_mul_right, _root_.GD.N0232.N0719.N0885.d009319, hpv]
    rw [← Finset.sum_mul, hp, one_mul]
  · exact fun i => (_root_.GD.N0232.N0719.N0885.d009315 m v i).memLp_two.const_mul (p i)
  · exact (_root_.GD.N0232.N0719.N0885.d009318 m v p).memLp_two




theorem d009321
    (m : ℝ) (v : ι → ℝ≥0) (p : ι → ℝ) (c : ℝ)
    (hp : ∑ i, p i = 1) (hpv : ∀ i, p i * (v i : ℝ) = c) :
    IndepFun (_root_.GD.N0232.N0719.N0885.d009311 p) (_root_.GD.N0232.N0719.N0885.d009312 p)
      (Measure.pi (fun j => gaussianReal m (v j))) := by
  let A : (ι → ℝ) →L[ℝ] (Unit → ℝ) :=
    ContinuousLinearMap.pi (fun _ => _root_.GD.N0232.N0719.N0885.d009313 p)
  let B : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj i - _root_.GD.N0232.N0719.N0885.d009313 p)
  have hg : HasGaussianLaw
      (fun y : ι → ℝ => ((fun _ : Unit => _root_.GD.N0232.N0719.N0885.d009311 p y), _root_.GD.N0232.N0719.N0885.d009312 p y))
      (Measure.pi (fun j => gaussianReal m (v j))) := by
    convert! (_root_.GD.N0232.N0719.N0885.d009316 m v).map_fun (A.prod B) using 1
    funext y
    apply Prod.ext
    · funext u
      change _root_.GD.N0232.N0719.N0885.d009311 p y = _root_.GD.N0232.N0719.N0885.d009313 p y
      exact (_root_.GD.N0232.N0719.N0885.d009314 p y).symm
    · funext i
      change y i - _root_.GD.N0232.N0719.N0885.d009311 p y = y i - _root_.GD.N0232.N0719.N0885.d009313 p y
      rw [_root_.GD.N0232.N0719.N0885.d009314]
  have hi := hg.indepFun_of_covariance_eval (fun _ j => by
    change cov[_root_.GD.N0232.N0719.N0885.d009311 p, fun y => y j - _root_.GD.N0232.N0719.N0885.d009311 p y; _] = 0
    rw [covariance_fun_sub_right
      (_root_.GD.N0232.N0719.N0885.d009318 m v p).memLp_two
      (_root_.GD.N0232.N0719.N0885.d009315 m v j).memLp_two
      (_root_.GD.N0232.N0719.N0885.d009318 m v p).memLp_two,
      _root_.GD.N0232.N0719.N0885.d009319, _root_.GD.N0232.N0719.N0885.d009320 m v p c hp hpv,
      hpv, sub_self])
  exact hi.comp (measurable_pi_apply ()) measurable_id


def d009322 (v : ι → ℝ≥0) : ℝ := ∑ i, (v i : ℝ)⁻¹

def d009323 (v : ι → ℝ≥0) (i : ι) : ℝ :=
  (v i : ℝ)⁻¹ / _root_.GD.N0232.N0719.N0885.d009322 v

theorem d009324 [Nonempty ι]
    (v : ι → ℝ≥0) (hv : ∀ i, 0 < v i) : 0 < _root_.GD.N0232.N0719.N0885.d009322 v := by
  exact Finset.sum_pos (fun i _ => inv_pos.mpr (hv i)) Finset.univ_nonempty

theorem d009325 [Nonempty ι]
    (v : ι → ℝ≥0) (hv : ∀ i, 0 < v i) : ∑ i, _root_.GD.N0232.N0719.N0885.d009323 v i = 1 := by
  simp only [_root_.GD.N0232.N0719.N0885.d009323, ← Finset.sum_div]
  change _root_.GD.N0232.N0719.N0885.d009322 v / _root_.GD.N0232.N0719.N0885.d009322 v = 1
  exact div_self (ne_of_gt (_root_.GD.N0232.N0719.N0885.d009324 v hv))

theorem d009326 [Nonempty ι]
    (v : ι → ℝ≥0) (hv : ∀ i, 0 < v i) (i : ι) :
    _root_.GD.N0232.N0719.N0885.d009323 v i * (v i : ℝ) = (_root_.GD.N0232.N0719.N0885.d009322 v)⁻¹ := by
  unfold _root_.GD.N0232.N0719.N0885.d009323
  field_simp [ne_of_gt (show (0 : ℝ) < v i from hv i)]


theorem d009327 [Nonempty ι]
    (m : ℝ) (v : ι → ℝ≥0) (hv : ∀ i, 0 < v i) :
    IndepFun (_root_.GD.N0232.N0719.N0885.d009311 (_root_.GD.N0232.N0719.N0885.d009323 v)) (_root_.GD.N0232.N0719.N0885.d009312 (_root_.GD.N0232.N0719.N0885.d009323 v))
      (Measure.pi (fun j => gaussianReal m (v j))) :=
  _root_.GD.N0232.N0719.N0885.d009321 m v (_root_.GD.N0232.N0719.N0885.d009323 v) (_root_.GD.N0232.N0719.N0885.d009322 v)⁻¹
    (_root_.GD.N0232.N0719.N0885.d009325 v hv) (_root_.GD.N0232.N0719.N0885.d009326 v hv)


theorem d009328 [Nonempty ι]
    (m : ℝ) (v : ι → ℝ≥0) (hv : ∀ i, 0 < v i) :
    Var[_root_.GD.N0232.N0719.N0885.d009311 (_root_.GD.N0232.N0719.N0885.d009323 v); Measure.pi (fun j => gaussianReal m (v j))] =
      (_root_.GD.N0232.N0719.N0885.d009322 v)⁻¹ := by
  rw [← covariance_self (_root_.GD.N0232.N0719.N0885.d009318 m v (_root_.GD.N0232.N0719.N0885.d009323 v)).aemeasurable]
  exact _root_.GD.N0232.N0719.N0885.d009320 m v (_root_.GD.N0232.N0719.N0885.d009323 v) (_root_.GD.N0232.N0719.N0885.d009322 v)⁻¹
    (_root_.GD.N0232.N0719.N0885.d009325 v hv) (_root_.GD.N0232.N0719.N0885.d009326 v hv)


def d009329 {k : ℕ} (sizes : Fin k → ℕ) (scales : Fin k → ℝ)
    (i : Fin k) : ℝ≥0 :=
  ⟨scales i ^ 2 / (sizes i : ℝ),
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)⟩

theorem d009330 {k : ℕ}
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i) (i : Fin k) :
    0 < _root_.GD.N0232.N0719.N0885.d009329 sizes scales i := by
  change 0 < scales i ^ 2 / (sizes i : ℝ)
  exact div_pos (sq_pos_of_pos (hscales i))
    (Nat.cast_pos.mpr (lt_of_lt_of_le (by decide : 0 < 2) (hsizes i)))




theorem d009331
    {k : ℕ} (hk : 0 < k) (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ) (hscales : ∀ i, 0 < scales i) :
    IndepFun (_root_.GD.N0232.N0719.N0885.d009311 (_root_.GD.N0232.N0719.N0885.d009323 (_root_.GD.N0232.N0719.N0885.d009329 sizes scales)))
      (_root_.GD.N0232.N0719.N0885.d009312 (_root_.GD.N0232.N0719.N0885.d009323 (_root_.GD.N0232.N0719.N0885.d009329 sizes scales)))
      (_root_.GD.N0232.N0719.N0933.d009300 k sizes location scales) := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  rw [_root_.GD.N0232.N0719.N0933.d009302 k sizes hsizes location scales]
  exact _root_.GD.N0232.N0719.N0885.d009327 location (_root_.GD.N0232.N0719.N0885.d009329 sizes scales)
    (_root_.GD.N0232.N0719.N0885.d009330 sizes hsizes scales hscales)

end GD.N0232.N0719.N0885

#print axioms _root_.GD.N0232.N0719.N0885.d009321
#print axioms _root_.GD.N0232.N0719.N0885.d009327
#print axioms _root_.GD.N0232.N0719.N0885.d009328
#print axioms _root_.GD.N0232.N0719.N0885.d009331
