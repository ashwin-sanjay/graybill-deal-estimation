import GD.Module0331
import Mathlib.LinearAlgebra.Matrix.DotProduct
















open scoped BigOperators

namespace GD
namespace N0233
namespace N0731

noncomputable section

open Matrix
open _root_.GD.N0233.N0729
open _root_.GD.N0233.N0730

variable {m n : Type*}
variable [Fintype m] [DecidableEq m]
variable [Fintype n] [DecidableEq n]


def d004958 {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  v ⬝ᵥ v


theorem d004959
    {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    0 ≤ _root_.GD.N0233.N0731.d004958 v := by
  unfold _root_.GD.N0233.N0731.d004958 dotProduct
  exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (v i)


theorem d004960
    {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    _root_.GD.N0233.N0731.d004958 v = 0 ↔ v = 0 := by
  exact dotProduct_self_eq_zero




theorem d004961
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) (z : n → ℝ) :
    (B *ᵥ _root_.GD.N0233.N0730.d004943 B y - y) ⬝ᵥ (B *ᵥ z) = 0 := by
  have hnormal :=
    _root_.GD.N0233.N0730.d004946 B hdet y
  calc
    (B *ᵥ _root_.GD.N0233.N0730.d004943 B y - y) ⬝ᵥ (B *ᵥ z) =
        ((B *ᵥ _root_.GD.N0233.N0730.d004943 B y - y) ᵥ* B) ⬝ᵥ z :=
      Matrix.dotProduct_mulVec _ _ _
    _ = (B.transpose *ᵥ
          (B *ᵥ _root_.GD.N0233.N0730.d004943 B y - y)) ⬝ᵥ z := by
      rw [Matrix.mulVec_transpose]
    _ = 0 := by
      rw [hnormal, zero_dotProduct]





theorem d004962
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) (x : n → ℝ) :
    _root_.GD.N0233.N0731.d004958 (B *ᵥ x - y) =
      _root_.GD.N0233.N0731.d004958 (B *ᵥ _root_.GD.N0233.N0730.d004943 B y - y) +
        _root_.GD.N0233.N0731.d004958
          (B *ᵥ (x - _root_.GD.N0233.N0730.d004943 B y)) := by
  let r : m → ℝ := B *ᵥ _root_.GD.N0233.N0730.d004943 B y - y
  let z : m → ℝ := B *ᵥ (x - _root_.GD.N0233.N0730.d004943 B y)
  have hdecomp : B *ᵥ x - y = r + z := by
    dsimp [r, z]
    rw [Matrix.mulVec_sub]
    abel
  have hcross : r ⬝ᵥ z = 0 := by
    dsimp [r, z]
    exact
      _root_.GD.N0233.N0731.d004961
        B hdet y (x - _root_.GD.N0233.N0730.d004943 B y)
  rw [hdecomp]
  unfold _root_.GD.N0233.N0731.d004958
  calc
    (r + z) ⬝ᵥ (r + z) =
        r ⬝ᵥ r + r ⬝ᵥ z +
          (z ⬝ᵥ r + z ⬝ᵥ z) := by
      rw [add_dotProduct, dotProduct_add, dotProduct_add]
    _ = r ⬝ᵥ r + z ⬝ᵥ z := by
      rw [hcross, dotProduct_comm z r, hcross]
      ring


theorem d004963
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) (x : n → ℝ) :
    _root_.GD.N0233.N0731.d004958 (B *ᵥ _root_.GD.N0233.N0730.d004943 B y - y) ≤
      _root_.GD.N0233.N0731.d004958 (B *ᵥ x - y) := by
  rw [_root_.GD.N0233.N0731.d004962 B hdet y x]
  exact le_add_of_nonneg_right <|
    _root_.GD.N0233.N0731.d004959
      (B *ᵥ (x - _root_.GD.N0233.N0730.d004943 B y))





theorem d004964
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) (x : n → ℝ) :
    _root_.GD.N0233.N0731.d004958 (B *ᵥ x - y) =
        _root_.GD.N0233.N0731.d004958 (B *ᵥ _root_.GD.N0233.N0730.d004943 B y - y) ↔
      x = _root_.GD.N0233.N0730.d004943 B y := by
  constructor
  · intro heq
    have hpyth :=
      _root_.GD.N0233.N0731.d004962 B hdet y x
    have hzero :
        _root_.GD.N0233.N0731.d004958
          (B *ᵥ (x - _root_.GD.N0233.N0730.d004943 B y)) = 0 := by
      linarith
    have hseen :
        B *ᵥ (x - _root_.GD.N0233.N0730.d004943 B y) = 0 :=
      (_root_.GD.N0233.N0731.d004960
        (B *ᵥ (x - _root_.GD.N0233.N0730.d004943 B y))).mp hzero
    have hinjective : Function.Injective B.mulVec :=
      (_root_.GD.N0233.N0729.d004931 B).mp hdet
    have hdiff : x - _root_.GD.N0233.N0730.d004943 B y = 0 := by
      apply hinjective
      simpa using hseen
    exact sub_eq_zero.mp hdiff
  · rintro rfl
    rfl


theorem d004965
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) :
    (∀ x : n → ℝ,
      _root_.GD.N0233.N0731.d004958 (B *ᵥ _root_.GD.N0233.N0730.d004943 B y - y) ≤
        _root_.GD.N0233.N0731.d004958 (B *ᵥ x - y)) ∧
      ∀ x : n → ℝ,
        _root_.GD.N0233.N0731.d004958 (B *ᵥ x - y) =
            _root_.GD.N0233.N0731.d004958 (B *ᵥ _root_.GD.N0233.N0730.d004943 B y - y) →
          x = _root_.GD.N0233.N0730.d004943 B y := by
  exact
    ⟨_root_.GD.N0233.N0731.d004963 B hdet y,
      fun x hx ↦
        (_root_.GD.N0233.N0731.d004964
          B hdet y x).mp hx⟩

end

end N0731
end N0233
end GD
