import GD.Module0754
import GD.Module0313

set_option autoImplicit false
set_option warningAsError true












open Set
open scoped BigOperators

namespace GD.N0232.N0719.N0992

open _root_.GD.N0232.N0719.N0873 _root_.GD.N0232.N0719.N0989
open _root_.GD.N0232.N0720.N1377
open _root_.GD.N0232.N0720.N1375
open _root_.GD.N0232.N0720.N1382
  (d004663 d004664 d004658)

noncomputable section
variable {I : Type*} [Fintype I]

theorem d011366 (p : I → ℝ) (hsum : ∑ i, p i = 1) (x : _root_.GD.N0232.N0719.N0873.d011295 I) :
    _root_.GD.N0232.N0719.N0989.d011339 p x - _root_.GD.N0232.N0719.N0989.d011340 p x ^ 2 =
      ∑ i, p i * ((x.1 i - _root_.GD.N0232.N0719.N0989.d011340 p x) ^ 2 + 2 * x.2 i) := by
  have hexpand (i : I) : p i * ((x.1 i - _root_.GD.N0232.N0719.N0989.d011340 p x) ^ 2 + 2 * x.2 i) =
      p i * ((x.1 i) ^ 2 + 2 * x.2 i) -
        2 * _root_.GD.N0232.N0719.N0989.d011340 p x * (p i * x.1 i) + _root_.GD.N0232.N0719.N0989.d011340 p x ^ 2 * p i := by ring
  simp_rw [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hsum]
  change _root_.GD.N0232.N0719.N0989.d011339 p x - _root_.GD.N0232.N0719.N0989.d011340 p x ^ 2 =
    _root_.GD.N0232.N0719.N0989.d011339 p x - 2 * _root_.GD.N0232.N0719.N0989.d011340 p x * _root_.GD.N0232.N0719.N0989.d011340 p x + _root_.GD.N0232.N0719.N0989.d011340 p x ^ 2 * 1
  ring

theorem d011367 (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (x : _root_.GD.N0232.N0719.N0873.d011295 I) (delta : ℝ)
    (hx : ∀ i, delta ≤ x.2 i) :
    _root_.GD.N0232.N0719.N0989.d011340 p x ^ 2 + 2 * delta ≤ _root_.GD.N0232.N0719.N0989.d011339 p x := by
  have hlow : (∑ i, p i * (2 * delta)) ≤
      ∑ i, p i * ((x.1 i - _root_.GD.N0232.N0719.N0989.d011340 p x) ^ 2 + 2 * x.2 i) := by
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (hp i)
    nlinarith [sq_nonneg (x.1 i - _root_.GD.N0232.N0719.N0989.d011340 p x), hx i]
  rw [← Finset.sum_mul, hsum, one_mul, ← _root_.GD.N0232.N0719.N0992.d011366 p hsum x] at hlow
  linarith

theorem d011368 (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (x : _root_.GD.N0232.N0719.N0873.d011295 I) (R : ℝ) (hx : ∀ i, |x.1 i| ≤ R) :
    |_root_.GD.N0232.N0719.N0989.d011340 p x| ≤ R := by
  calc
    |_root_.GD.N0232.N0719.N0989.d011340 p x| ≤ ∑ i, |p i * x.1 i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, p i * |x.1 i| := by simp_rw [abs_mul, abs_of_nonneg (hp _)]
    _ ≤ ∑ i, p i * R := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hx i) (hp i)
    _ = R := by rw [← Finset.sum_mul, hsum, one_mul]

theorem d011369 (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (x : _root_.GD.N0232.N0719.N0873.d011295 I) {delta R : ℝ}
    (hd : 0 < delta) (hR : 0 < R)
    (hres : ∀ i, delta ≤ x.2 i) (hmean : ∀ i, |x.1 i| ≤ R) :
    2 * delta ≤ _root_.GD.N0232.N0719.N0989.d011339 p x ∧
      _root_.GD.N0232.N0719.N0989.d011340 p x ^ 2 / (2 * _root_.GD.N0232.N0719.N0989.d011339 p x) ≤ _root_.GD.N0232.N0720.N1382.d004663 delta R := by
  have hgap := _root_.GD.N0232.N0719.N0992.d011367 p hp hsum x delta hres
  have hb := _root_.GD.N0232.N0719.N0992.d011368 p hp hsum x R hmean
  have hbsq : _root_.GD.N0232.N0719.N0989.d011340 p x ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR.le).2 hb
  have hA : 0 < _root_.GD.N0232.N0719.N0989.d011339 p x := by nlinarith [sq_nonneg (_root_.GD.N0232.N0719.N0989.d011340 p x)]
  refine ⟨by nlinarith [sq_nonneg (_root_.GD.N0232.N0719.N0989.d011340 p x)], ?_⟩
  unfold _root_.GD.N0232.N0720.N1382.d004663
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * _root_.GD.N0232.N0719.N0989.d011339 p x)
    (by positivity : 0 < 2 * (R ^ 2 + 2 * delta))).2
  have h1 := mul_le_mul_of_nonneg_left hgap (sq_nonneg R)
  have h2 := mul_le_mul_of_nonneg_left hbsq hd.le
  nlinarith



theorem d011370 (n m : ℕ) {delta R beta : ℝ}
    (hd : 0 < delta) (hR : 0 < R) (hbeta : _root_.GD.N0232.N0720.N1382.d004663 delta R < beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : I → ℝ), (∀ i, 0 ≤ p i) → (∑ i, p i = 1) →
      ∀ (x : _root_.GD.N0232.N0719.N0873.d011295 I), (∀ i, delta ≤ x.2 i) → (∀ i, |x.1 i| ≤ R) → ∀ xi : ℝ,
        ‖xi ^ m * _root_.GD.N0232.N0719.N0989.d011346 n xi p x‖ ≤ C * Real.exp (beta * xi ^ 2) := by
  let b := _root_.GD.N0232.N0720.N1382.d004663 delta R
  let a := (b + beta) / 2
  let loss := a / b
  have hb : 0 < b := _root_.GD.N0232.N0720.N1382.d004664 hd hR
  have hba : b < a := by dsimp [a, b]; linarith
  have hab : a < beta := by dsimp [a, b]; linarith
  have hloss : 1 < loss := (lt_div_iff₀ hb).2 (by simpa using hba)
  have hlosspos : 0 < loss := lt_trans zero_lt_one hloss
  have hlossb : loss * b = a := div_mul_cancel₀ _ hb.ne'
  have hred : 0 < 2 * delta * (loss - 1) / loss := by positivity
  let C0 := _root_.GD.N0232.N0720.N1377.d002852 n (2 * delta * (loss - 1) / loss) 0
  have hC0 : 0 < C0 := _root_.GD.N0232.N0720.N1377.d002861 n hred 0
  obtain ⟨Cp, hCp, hpoly⟩ := _root_.GD.N0232.N0720.N1382.d004658 m hab
  refine ⟨C0 * Cp, mul_pos hC0 hCp, ?_⟩
  intro p hp hsum x hres hmean xi
  obtain ⟨hA, hrate⟩ := _root_.GD.N0232.N0719.N0992.d011369 p hp hsum x hd hR hres hmean
  have hApos : 0 < _root_.GD.N0232.N0719.N0989.d011339 p x := lt_of_lt_of_le (by positivity) hA
  have hI := _root_.GD.N0232.N0720.N1375.d002934 n (Amin := 2 * delta)
    (by positivity) hA hloss hrate xi
  rw [hlossb] at hI
  have hIpos := (_root_.GD.N0232.N0720.N1377.d002861 n hApos (_root_.GD.N0232.N0719.N0989.d011340 p x * xi)).le
  calc
    ‖xi ^ m * _root_.GD.N0232.N0719.N0989.d011346 n xi p x‖ =
        |xi| ^ m * _root_.GD.N0232.N0720.N1377.d002852 n (_root_.GD.N0232.N0719.N0989.d011339 p x) (_root_.GD.N0232.N0719.N0989.d011340 p x * xi) := by
      rw [_root_.GD.N0232.N0719.N0989.d011346, norm_mul, norm_pow, Real.norm_eq_abs xi,
        Real.norm_eq_abs (_root_.GD.N0232.N0720.N1377.d002852 _ _ _), abs_of_nonneg hIpos]
    _ ≤ |xi| ^ m * (Real.exp (a * xi ^ 2) * C0) :=
      mul_le_mul_of_nonneg_left hI (pow_nonneg (abs_nonneg _) _)
    _ = C0 * (|xi| ^ m * Real.exp (a * xi ^ 2)) := by ring
    _ ≤ C0 * (Cp * Real.exp (beta * xi ^ 2)) :=
      mul_le_mul_of_nonneg_left (hpoly xi) hC0.le
    _ = _ := by ring

end
end GD.N0232.N0719.N0992

#print axioms _root_.GD.N0232.N0719.N0992.d011367
#print axioms _root_.GD.N0232.N0719.N0992.d011370
