import GD.Module0331





















namespace GD
namespace N0233
namespace N0732

noncomputable section

open Matrix
open _root_.GD.N0233.N0729
open _root_.GD.N0233.N0730

variable {m n : Type*}
variable [Fintype m] [DecidableEq m]
variable [Fintype n] [DecidableEq n]


def d004966 (B : Matrix m n ℝ) : Matrix m m ℝ :=
  B * (_root_.GD.N0233.N0729.d004921 B)⁻¹ * B.transpose

omit [DecidableEq m] in




theorem d004967
    (B : Matrix m n ℝ) (y : m → ℝ) :
    _root_.GD.N0233.N0732.d004966 B *ᵥ y =
      B *ᵥ _root_.GD.N0233.N0730.d004943 B y := by
  simp [_root_.GD.N0233.N0732.d004966, _root_.GD.N0233.N0730.d004943, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

omit [Fintype n] [DecidableEq m] [DecidableEq n] in

@[simp]
theorem d004968 (B : Matrix m n ℝ) :
    (_root_.GD.N0233.N0729.d004921 B).transpose = _root_.GD.N0233.N0729.d004921 B := by
  simp [_root_.GD.N0233.N0729.d004921, Matrix.transpose_mul]

omit [DecidableEq m] in




theorem d004969
    (B : Matrix m n ℝ) :
    (_root_.GD.N0233.N0732.d004966 B).transpose =
      _root_.GD.N0233.N0732.d004966 B := by
  simp [_root_.GD.N0233.N0732.d004966, Matrix.transpose_mul,
    Matrix.transpose_nonsing_inv, Matrix.mul_assoc]




theorem d004970
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (x : n → ℝ) :
    _root_.GD.N0233.N0732.d004966 B *ᵥ (B *ᵥ x) =
      B *ᵥ x := by
  rw [_root_.GD.N0233.N0732.d004967,
    _root_.GD.N0233.N0730.d004949 B hdet x]




theorem d004971
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0) :
    _root_.GD.N0233.N0732.d004966 B * _root_.GD.N0233.N0732.d004966 B =
      _root_.GD.N0233.N0732.d004966 B := by
  rw [Matrix.ext_iff_mulVec]
  intro y
  calc
    (_root_.GD.N0233.N0732.d004966 B * _root_.GD.N0233.N0732.d004966 B) *ᵥ y =
        _root_.GD.N0233.N0732.d004966 B *ᵥ
          (_root_.GD.N0233.N0732.d004966 B *ᵥ y) :=
      (Matrix.mulVec_mulVec _ _ _).symm
    _ = _root_.GD.N0233.N0732.d004966 B *ᵥ
          (B *ᵥ _root_.GD.N0233.N0730.d004943 B y) := by
      exact congrArg
        (fun z ↦ _root_.GD.N0233.N0732.d004966 B *ᵥ z)
        (_root_.GD.N0233.N0732.d004967 B y)
    _ = B *ᵥ _root_.GD.N0233.N0730.d004943 B y :=
      _root_.GD.N0233.N0732.d004970
        B hdet (_root_.GD.N0233.N0730.d004943 B y)
    _ = _root_.GD.N0233.N0732.d004966 B *ᵥ y :=
      (_root_.GD.N0233.N0732.d004967 B y).symm





theorem d004972
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) :
    B.transpose *ᵥ
        (_root_.GD.N0233.N0732.d004966 B *ᵥ y - y) = 0 := by
  rw [_root_.GD.N0233.N0732.d004967]
  exact _root_.GD.N0233.N0730.d004946 B hdet y




theorem d004973
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) :
    _root_.GD.N0233.N0732.d004966 B *ᵥ
        (y - _root_.GD.N0233.N0732.d004966 B *ᵥ y) = 0 := by
  rw [Matrix.mulVec_sub]
  have hidemPoint :
      _root_.GD.N0233.N0732.d004966 B *ᵥ
          (_root_.GD.N0233.N0732.d004966 B *ᵥ y) =
        _root_.GD.N0233.N0732.d004966 B *ᵥ y := by
    calc
      _root_.GD.N0233.N0732.d004966 B *ᵥ
          (_root_.GD.N0233.N0732.d004966 B *ᵥ y) =
          (_root_.GD.N0233.N0732.d004966 B * _root_.GD.N0233.N0732.d004966 B) *ᵥ y :=
        Matrix.mulVec_mulVec _ _ _
      _ = _root_.GD.N0233.N0732.d004966 B *ᵥ y := by
        rw [_root_.GD.N0233.N0732.d004971 B hdet]
  rw [hidemPoint, sub_self]





theorem d004974
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) :
    _root_.GD.N0233.N0732.d004966 B *ᵥ y = y ↔
      ∃ x : n → ℝ, B *ᵥ x = y := by
  constructor
  · intro hy
    exact ⟨_root_.GD.N0233.N0730.d004943 B y,
      (_root_.GD.N0233.N0732.d004967 B y).symm.trans hy⟩
  · rintro ⟨x, rfl⟩
    exact _root_.GD.N0233.N0732.d004970 B hdet x





theorem d004975
    (B : Matrix m n ℝ) (T : Matrix n n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (hT : det T ≠ 0) :
    _root_.GD.N0233.N0732.d004966 (B * T) =
      _root_.GD.N0233.N0732.d004966 B := by
  have hTunit : IsUnit (det T) :=
    isUnit_iff_ne_zero.mpr hT
  rw [Matrix.ext_iff_mulVec]
  intro y
  rw [_root_.GD.N0233.N0732.d004967,
    _root_.GD.N0233.N0732.d004967,
    _root_.GD.N0233.N0730.d004957 B T hdet hT y]
  have hcancel :
      T *ᵥ (T⁻¹ *ᵥ _root_.GD.N0233.N0730.d004943 B y) =
        _root_.GD.N0233.N0730.d004943 B y := by
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hTunit,
      Matrix.one_mulVec]
  calc
    (B * T) *ᵥ (T⁻¹ *ᵥ _root_.GD.N0233.N0730.d004943 B y) =
        B *ᵥ (T *ᵥ (T⁻¹ *ᵥ _root_.GD.N0233.N0730.d004943 B y)) :=
      (Matrix.mulVec_mulVec _ _ _).symm
    _ = B *ᵥ _root_.GD.N0233.N0730.d004943 B y :=
      congrArg (fun z ↦ B *ᵥ z) hcancel





theorem d004976
    (Q : Matrix m m ℝ) (B : Matrix m n ℝ)
    (hQ : Q.transpose * Q = 1) :
    _root_.GD.N0233.N0732.d004966 (Q * B) =
      Q * _root_.GD.N0233.N0732.d004966 B * Q.transpose := by
  unfold _root_.GD.N0233.N0732.d004966
  rw [_root_.GD.N0233.N0730.d004954 Q B hQ]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]




theorem d004977
    (Q : Matrix m m ℝ) (B : Matrix m n ℝ)
    (hQ : Q.transpose * Q = 1)
    (y : m → ℝ) :
    _root_.GD.N0233.N0732.d004966 (Q * B) *ᵥ (Q *ᵥ y) =
      Q *ᵥ (_root_.GD.N0233.N0732.d004966 B *ᵥ y) := by
  rw [_root_.GD.N0233.N0732.d004967,
    _root_.GD.N0233.N0730.d004956 Q B hQ y]
  calc
    (Q * B) *ᵥ _root_.GD.N0233.N0730.d004943 B y =
        Q *ᵥ (B *ᵥ _root_.GD.N0233.N0730.d004943 B y) :=
      (Matrix.mulVec_mulVec _ _ _).symm
    _ = Q *ᵥ (_root_.GD.N0233.N0732.d004966 B *ᵥ y) :=
      congrArg (fun z ↦ Q *ᵥ z)
        (_root_.GD.N0233.N0732.d004967 B y).symm

end

end N0732
end N0233
end GD
