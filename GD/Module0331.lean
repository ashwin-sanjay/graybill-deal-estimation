import GD.Module0330
import GD.Module0273


















namespace GD
namespace N0233
namespace N0730

noncomputable section

open Matrix
open _root_.GD.N0233.N0729
open _root_.GD.N0234.N0739
open _root_.GD.N0234.N0741

variable {m n : Type*}
variable [Fintype m] [DecidableEq m]
variable [Fintype n] [DecidableEq n]





def d004943 (B : Matrix m n ℝ) (y : m → ℝ) : n → ℝ :=
  (_root_.GD.N0233.N0729.d004921 B)⁻¹ *ᵥ (B.transpose *ᵥ y)

omit [DecidableEq m] in


theorem d004944
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0) :
    IsUnit (det (_root_.GD.N0233.N0729.d004921 B)) :=
  isUnit_iff_ne_zero.mpr hdet





theorem d004945
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) :
    (_root_.GD.N0233.N0729.d004921 B).mulVec (_root_.GD.N0233.N0730.d004943 B y) =
      B.transpose *ᵥ y := by
  unfold _root_.GD.N0233.N0730.d004943
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (_root_.GD.N0233.N0730.d004944 B hdet),
    Matrix.one_mulVec]





theorem d004946
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) :
    B.transpose *ᵥ (B *ᵥ _root_.GD.N0233.N0730.d004943 B y - y) = 0 := by
  calc
    B.transpose *ᵥ (B *ᵥ _root_.GD.N0233.N0730.d004943 B y - y) =
        (_root_.GD.N0233.N0729.d004921 B) *ᵥ _root_.GD.N0233.N0730.d004943 B y -
          B.transpose *ᵥ y := by
      simp [_root_.GD.N0233.N0729.d004921, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    _ = 0 := by
      rw [_root_.GD.N0233.N0730.d004945 B hdet y, sub_self]





theorem d004947
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) (x : n → ℝ)
    (hx : (_root_.GD.N0233.N0729.d004921 B) *ᵥ x = B.transpose *ᵥ y) :
    _root_.GD.N0233.N0730.d004943 B y = x := by
  apply
    (_root_.GD.N0234.N0741.d004817 (_root_.GD.N0233.N0729.d004921 B)).mp hdet
  exact
    (_root_.GD.N0233.N0730.d004945 B hdet y).trans hx.symm


theorem d004948
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) {x z : n → ℝ}
    (hx : (_root_.GD.N0233.N0729.d004921 B) *ᵥ x = B.transpose *ᵥ y)
    (hz : (_root_.GD.N0233.N0729.d004921 B) *ᵥ z = B.transpose *ᵥ y) :
    x = z := by
  have hax := _root_.GD.N0233.N0730.d004947 B hdet y x hx
  have haz := _root_.GD.N0233.N0730.d004947 B hdet y z hz
  exact hax.symm.trans haz





theorem d004949
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (x : n → ℝ) :
    _root_.GD.N0233.N0730.d004943 B (B *ᵥ x) = x := by
  unfold _root_.GD.N0233.N0730.d004943
  calc
    (_root_.GD.N0233.N0729.d004921 B)⁻¹ *ᵥ (B.transpose *ᵥ (B *ᵥ x)) =
        (_root_.GD.N0233.N0729.d004921 B)⁻¹ *ᵥ ((_root_.GD.N0233.N0729.d004921 B) *ᵥ x) := by
      simp [_root_.GD.N0233.N0729.d004921, Matrix.mul_assoc]
    _ = ((_root_.GD.N0233.N0729.d004921 B)⁻¹ * _root_.GD.N0233.N0729.d004921 B) *ᵥ x :=
      Matrix.mulVec_mulVec _ _ _
    _ = x := by
      rw [Matrix.nonsing_inv_mul _
        (_root_.GD.N0233.N0730.d004944 B hdet), Matrix.one_mulVec]





theorem d004950
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) (x : n → ℝ)
    (hx : B *ᵥ x = y) :
    _root_.GD.N0233.N0730.d004943 B y = x := by
  rw [← hx]
  exact _root_.GD.N0233.N0730.d004949 B hdet x


theorem d004951
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    {y : m → ℝ} {x z : n → ℝ}
    (hx : B *ᵥ x = y)
    (hz : B *ᵥ z = y) :
    x = z := by
  have hax := _root_.GD.N0233.N0730.d004950 B hdet y x hx
  have haz := _root_.GD.N0233.N0730.d004950 B hdet y z hz
  exact hax.symm.trans haz

omit [DecidableEq m] [DecidableEq n] in


theorem d004952
    (B : Matrix m n ℝ) (T : Matrix n n ℝ) :
    _root_.GD.N0233.N0729.d004921 (B * T) = _root_.GD.N0234.N0739.d004031 T (_root_.GD.N0233.N0729.d004921 B) := by
  simp [_root_.GD.N0233.N0729.d004921, _root_.GD.N0234.N0739.d004031, Matrix.transpose_mul, Matrix.mul_assoc]


theorem d004953
    (B : Matrix m n ℝ) (T : Matrix n n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (hT : det T ≠ 0) :
    det (_root_.GD.N0233.N0729.d004921 (B * T)) ≠ 0 := by
  rw [_root_.GD.N0233.N0730.d004952]
  exact
    (_root_.GD.N0234.N0739.d004036 T (_root_.GD.N0233.N0729.d004921 B) hT).2 hdet





theorem d004954
    (Q : Matrix m m ℝ) (B : Matrix m n ℝ)
    (hQ : Q.transpose * Q = 1) :
    _root_.GD.N0233.N0729.d004921 (Q * B) = _root_.GD.N0233.N0729.d004921 B := by
  simp only [_root_.GD.N0233.N0729.d004921, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Q.transpose Q B, hQ, Matrix.one_mul]





theorem d004955
    (Q : Matrix m m ℝ) (B : Matrix m n ℝ)
    (hQ : Q.transpose * Q = 1)
    (y : m → ℝ) :
    (Q * B).transpose *ᵥ (Q *ᵥ y) =
      B.transpose *ᵥ y := by
  simp [Matrix.transpose_mul, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, hQ]







theorem d004956
    (Q : Matrix m m ℝ) (B : Matrix m n ℝ)
    (hQ : Q.transpose * Q = 1)
    (y : m → ℝ) :
    _root_.GD.N0233.N0730.d004943 (Q * B) (Q *ᵥ y) =
      _root_.GD.N0233.N0730.d004943 B y := by
  unfold _root_.GD.N0233.N0730.d004943
  rw [_root_.GD.N0233.N0730.d004954 Q B hQ,
    _root_.GD.N0233.N0730.d004955 Q B hQ y]









theorem d004957
    (B : Matrix m n ℝ) (T : Matrix n n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (hT : det T ≠ 0)
    (y : m → ℝ) :
    _root_.GD.N0233.N0730.d004943 (B * T) y =
      T⁻¹ *ᵥ _root_.GD.N0233.N0730.d004943 B y := by
  have hTunit : IsUnit (det T) :=
    isUnit_iff_ne_zero.mpr hT
  have hnew :
      det (_root_.GD.N0233.N0729.d004921 (B * T)) ≠ 0 :=
    _root_.GD.N0233.N0730.d004953 B T hdet hT
  have hnormal :
      (_root_.GD.N0233.N0729.d004921 (B * T)).mulVec
          (T⁻¹ *ᵥ _root_.GD.N0233.N0730.d004943 B y) =
        (B * T).transpose *ᵥ y := by
    rw [_root_.GD.N0233.N0730.d004952]
    simp only [_root_.GD.N0234.N0739.d004031, Matrix.transpose_mul]
    simp only [Matrix.mulVec_mulVec]
    rw [Matrix.mul_assoc (T.transpose * _root_.GD.N0233.N0729.d004921 B),
      Matrix.mul_nonsing_inv _ hTunit, Matrix.mul_one]
    calc
      (T.transpose * _root_.GD.N0233.N0729.d004921 B) *ᵥ _root_.GD.N0233.N0730.d004943 B y =
          T.transpose *ᵥ
            ((_root_.GD.N0233.N0729.d004921 B) *ᵥ _root_.GD.N0233.N0730.d004943 B y) :=
        (Matrix.mulVec_mulVec _ _ _).symm
      _ = T.transpose *ᵥ (B.transpose *ᵥ y) := by
        rw [_root_.GD.N0233.N0730.d004945 B hdet y]
      _ = (T.transpose * B.transpose) *ᵥ y :=
        Matrix.mulVec_mulVec _ _ _
  have hanchorNormal :=
    _root_.GD.N0233.N0730.d004945 (B * T) hnew y
  apply
    (_root_.GD.N0234.N0741.d004817
      (_root_.GD.N0233.N0729.d004921 (B * T))).mp hnew
  exact hanchorNormal.trans hnormal.symm

end

end N0730
end N0233
end GD
