import GD.Module0322
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Lp.Matrix
















namespace GD.N0234.N0741

noncomputable section

open scoped ENNReal
open WithLp

variable {n : Type*} [Fintype n] [DecidableEq n]


def d004813 (M : Matrix n n ℝ) (x : EuclideanSpace ℝ n) : ℝ :=
  ∑ i, (M.mulVec x.ofLp i) ^ 2



theorem d004814
    (M : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    0 ≤ _root_.GD.N0234.N0741.d004813 M x := by
  exact Finset.sum_nonneg fun i _ ↦ sq_nonneg (M.mulVec x.ofLp i)


theorem d004815
    (M : Matrix n n ℝ) (c : ℝ) (x : EuclideanSpace ℝ n) :
    _root_.GD.N0234.N0741.d004813 M (c • x) = c ^ 2 * _root_.GD.N0234.N0741.d004813 M x := by
  simp only [_root_.GD.N0234.N0741.d004813, WithLp.ofLp_smul, Matrix.mulVec_smul,
    Pi.smul_apply, smul_eq_mul, mul_pow]
  exact (Finset.mul_sum _ _ _).symm



theorem d004816
    (M : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    _root_.GD.N0234.N0741.d004813 M x =
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [_root_.GD.N0234.N0741.d004813, Matrix.ofLp_toEuclideanCLM]



theorem d004817 (M : Matrix n n ℝ) :
    M.det ≠ 0 ↔ Function.Injective M.mulVec := by
  constructor
  · intro hdet x y hxy
    have hzero : M.mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    by_contra hne
    have hdiff : x - y ≠ 0 := sub_ne_zero.mpr hne
    exact hdet <|
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨x - y, hdiff, hzero⟩
  · intro hinj hdet
    obtain ⟨x, hx, hzero⟩ :=
      Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    apply hx
    apply hinj
    simpa using hzero



theorem d004818 (M : Matrix n n ℝ) :
    M.det ≠ 0 ↔
      Function.Injective (Matrix.toEuclideanCLM (𝕜 := ℝ) M) := by
  rw [_root_.GD.N0234.N0741.d004817]
  constructor
  · intro hinj x y hxy
    apply WithLp.ofLp_injective 2
    apply hinj
    have h := congrArg WithLp.ofLp hxy
    simpa using h
  · intro hinj x y hxy
    apply WithLp.toLp_injective 2
    apply hinj
    simpa using congrArg (WithLp.toLp 2) hxy



theorem d004819
    (M : Matrix n n ℝ) (hdet : M.det ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x : EuclideanSpace ℝ n,
        δ * ‖x‖ ^ 2 ≤ _root_.GD.N0234.N0741.d004813 M x := by
  have hinj :
      Function.Injective
        ((Matrix.toEuclideanCLM (𝕜 := ℝ) M).toLinearMap) := by
    simpa using (_root_.GD.N0234.N0741.d004818 M).mp hdet
  obtain ⟨K, -, hanti⟩ :=
    (LinearMap.injective_iff_antilipschitz
      (Matrix.toEuclideanCLM (𝕜 := ℝ) M).toLinearMap).mp hinj
  obtain ⟨c, hc, hbound⟩ :=
    antilipschitzWith_iff_exists_mul_le_norm.mp ⟨K, hanti⟩
  refine ⟨c ^ 2, sq_pos_of_pos hc, ?_⟩
  intro x
  have hsquare :
      (c * ‖x‖) ^ 2 ≤
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M x‖ ^ 2 := by
    exact (sq_le_sq₀
      (mul_nonneg hc.le (norm_nonneg x))
      (norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) M x))).2
        (hbound x)
  rw [_root_.GD.N0234.N0741.d004816]
  calc
    c ^ 2 * ‖x‖ ^ 2 = (c * ‖x‖) ^ 2 := by ring
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M x‖ ^ 2 := hsquare



theorem d004820
    (M : Matrix n n ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hcoercive :
      ∀ x : EuclideanSpace ℝ n,
        δ * ‖x‖ ^ 2 ≤ _root_.GD.N0234.N0741.d004813 M x) :
    M.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hMv⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let x : EuclideanSpace ℝ n := WithLp.toLp 2 v
  have hx : x ≠ 0 := by
    intro hx0
    apply hv
    exact WithLp.toLp_injective 2 (by simpa [x] using hx0)
  have henergy : _root_.GD.N0234.N0741.d004813 M x = 0 := by
    simp [_root_.GD.N0234.N0741.d004813, x, hMv]
  have hlower := hcoercive x
  rw [henergy] at hlower
  have hnorm : 0 < ‖x‖ ^ 2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx)
  nlinarith



theorem d004821
    (M : Matrix n n ℝ) :
    M.det ≠ 0 ↔
      ∃ δ : ℝ, 0 < δ ∧
        ∀ x : EuclideanSpace ℝ n,
          δ * ‖x‖ ^ 2 ≤ _root_.GD.N0234.N0741.d004813 M x := by
  constructor
  · exact _root_.GD.N0234.N0741.d004819 M
  · rintro ⟨δ, hδ, hcoercive⟩
    exact _root_.GD.N0234.N0741.d004820 M δ hδ hcoercive



theorem d004822 (M : Matrix n n ℝ) :
    (M.det ≠ 0) ↔
      Function.Injective (Matrix.toEuclideanCLM (𝕜 := ℝ) M) ∧
      ∃ δ : ℝ, 0 < δ ∧
        ∀ x : EuclideanSpace ℝ n,
          δ * ‖x‖ ^ 2 ≤ _root_.GD.N0234.N0741.d004813 M x := by
  constructor
  · intro hdet
    exact ⟨(_root_.GD.N0234.N0741.d004818 M).mp hdet,
      _root_.GD.N0234.N0741.d004819 M hdet⟩
  · rintro ⟨hinj, -⟩
    exact (_root_.GD.N0234.N0741.d004818 M).mpr hinj



theorem d004823
    (M : Matrix n n ℝ) :
    M.det = 0 ↔
      ∃ x : EuclideanSpace ℝ n, x ≠ 0 ∧ _root_.GD.N0234.N0741.d004813 M x = 0 := by
  constructor
  · intro hdet
    obtain ⟨v, hv, hMv⟩ :=
      Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    refine ⟨WithLp.toLp 2 v, ?_, ?_⟩
    · intro hx
      apply hv
      exact WithLp.toLp_injective 2 (by simpa using hx)
    · simp [_root_.GD.N0234.N0741.d004813, hMv]
  · rintro ⟨x, hx, henergy⟩
    by_contra hdet
    obtain ⟨δ, hδ, hcoercive⟩ :=
      _root_.GD.N0234.N0741.d004819 M hdet
    have hlower := hcoercive x
    rw [henergy] at hlower
    have hnorm : 0 < ‖x‖ ^ 2 :=
      sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hx)
    nlinarith

end

end GD.N0234.N0741
