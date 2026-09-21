import GD.Module0334
import GD.Module0330
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.SchurComplement





















open scoped BigOperators

namespace GD
namespace N0233
namespace N0721

noncomputable section

open Matrix
open _root_.GD.N0233.N0722
open _root_.GD.N0233.N0729
open _root_.GD.N0233.N0730
open _root_.GD.N0233.N0731
open _root_.GD.N0233.N0732

variable {m n : Type*}
variable [Fintype m] [DecidableEq m]
variable [Fintype n] [DecidableEq n]


def d004996
    (B : Matrix m n ℝ) (y : m → ℝ) :
    Matrix m (n ⊕ Fin 1) ℝ :=
  Matrix.fromCols B (Matrix.replicateCol (Fin 1) y)


def d004997 (B : Matrix m n ℝ) : ℝ :=
  det (_root_.GD.N0233.N0729.d004921 B)


def d004998
    (B : Matrix m n ℝ) (y : m → ℝ) : ℝ :=
  det (_root_.GD.N0233.N0729.d004921 (_root_.GD.N0233.N0721.d004996 B y))

omit [DecidableEq m] [Fintype n] [DecidableEq n] in



theorem d004999
    (B : Matrix m n ℝ) (y : m → ℝ) :
    _root_.GD.N0233.N0729.d004921 (_root_.GD.N0233.N0721.d004996 B y) =
      Matrix.fromBlocks
        (_root_.GD.N0233.N0729.d004921 B)
        (B.transpose * Matrix.replicateCol (Fin 1) y)
        ((Matrix.replicateCol (Fin 1) y).transpose * B)
        ((Matrix.replicateCol (Fin 1) y).transpose *
          Matrix.replicateCol (Fin 1) y) := by
  simp [_root_.GD.N0233.N0729.d004921, _root_.GD.N0233.N0721.d004996, Matrix.transpose_fromCols]





theorem d005000
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) :
    det
        (((Matrix.replicateCol (Fin 1) y).transpose *
            Matrix.replicateCol (Fin 1) y) -
          ((Matrix.replicateCol (Fin 1) y).transpose * B) *
            (_root_.GD.N0233.N0729.d004921 B)⁻¹ *
            (B.transpose * Matrix.replicateCol (Fin 1) y)) =
      _root_.GD.N0233.N0731.d004958 (_root_.GD.N0233.N0722.d004978 B y) := by
  rw [Matrix.det_fin_one]
  have hproduct :
      ((((Matrix.replicateCol (Fin 1) y).transpose * B) *
          (_root_.GD.N0233.N0729.d004921 B)⁻¹ *
          (B.transpose * Matrix.replicateCol (Fin 1) y)) 0 0) =
        y ⬝ᵥ (B *ᵥ _root_.GD.N0233.N0730.d004943 B y) := by
    unfold _root_.GD.N0233.N0730.d004943
    rw [Matrix.transpose_replicateCol]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.replicateCol_mulVec]
    rw [← Matrix.replicateCol_mulVec]
    rw [← Matrix.replicateCol_mulVec]
    exact Matrix.replicateRow_mul_replicateCol_apply _ _ 0 0
  rw [Matrix.sub_apply, hproduct]
  rw [Matrix.transpose_replicateCol]
  rw [Matrix.replicateRow_mul_replicateCol_apply]
  rw [← _root_.GD.N0233.N0722.d004984 B hdet y]
  unfold _root_.GD.N0233.N0722.d004979 _root_.GD.N0233.N0722.d004978
  rw [sub_dotProduct, _root_.GD.N0233.N0732.d004967,
    dotProduct_comm (B *ᵥ _root_.GD.N0233.N0730.d004943 B y) y]






theorem d005001
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) :
    _root_.GD.N0233.N0721.d004998 B y =
      _root_.GD.N0233.N0721.d004997 B *
        _root_.GD.N0233.N0731.d004958 (_root_.GD.N0233.N0722.d004978 B y) := by
  letI :=
    Matrix.invertibleOfIsUnitDet
      (_root_.GD.N0233.N0729.d004921 B) (isUnit_iff_ne_zero.mpr hdet)
  unfold _root_.GD.N0233.N0721.d004998 _root_.GD.N0233.N0721.d004997
  rw [_root_.GD.N0233.N0721.d004999]
  rw [Matrix.det_fromBlocks₁₁]
  rw [Matrix.invOf_eq_nonsing_inv]
  rw [_root_.GD.N0233.N0721.d005000 B hdet y]




theorem d005002
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) :
    _root_.GD.N0233.N0721.d004998 B y =
      _root_.GD.N0233.N0721.d004997 B *
        _root_.GD.N0233.N0731.d004958 (B *ᵥ _root_.GD.N0233.N0730.d004943 B y - y) := by
  rw [_root_.GD.N0233.N0721.d005001
    B hdet y]
  rw [_root_.GD.N0233.N0722.d004986]
  unfold _root_.GD.N0233.N0731.d004958
  rw [neg_dotProduct, dotProduct_neg, neg_neg]





theorem d005003
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) :
    _root_.GD.N0233.N0721.d004998 B y = 0 ↔
      ∃ x : n → ℝ, B *ᵥ x = y := by
  rw [_root_.GD.N0233.N0721.d005001
    B hdet y, mul_eq_zero]
  simp only [_root_.GD.N0233.N0721.d004997, hdet, false_or]
  rw [_root_.GD.N0233.N0731.d004960]
  exact _root_.GD.N0233.N0722.d004982 B hdet y





theorem d005004
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) :
    0 < _root_.GD.N0233.N0721.d004998 B y ↔
      ¬ ∃ x : n → ℝ, B *ᵥ x = y := by
  have hobs :
      0 < _root_.GD.N0233.N0721.d004997 B := by
    unfold _root_.GD.N0233.N0721.d004997
    rw [_root_.GD.N0233.N0729.d004930]
    have hplucker :
        _root_.GD.N0233.N0729.d004925 B ≠ 0 := by
      rw [← _root_.GD.N0233.N0729.d004930]
      exact hdet
    exact lt_of_le_of_ne
      (_root_.GD.N0233.N0729.d004927 B) hplucker.symm
  rw [_root_.GD.N0233.N0721.d005001
    B hdet y, mul_pos_iff_of_pos_left hobs]
  rw [not_exists]
  constructor
  · intro hsq x hx
    have hzero :
        _root_.GD.N0233.N0722.d004978 B y = 0 :=
      (_root_.GD.N0233.N0722.d004982 B hdet y).2 ⟨x, hx⟩
    rw [hzero, (_root_.GD.N0233.N0731.d004960 _).2 rfl] at hsq
    exact (lt_irrefl 0 hsq)
  · intro hnot
    have hres : _root_.GD.N0233.N0722.d004978 B y ≠ 0 := by
      intro hzero
      obtain ⟨x, hx⟩ :=
        (_root_.GD.N0233.N0722.d004982 B hdet y).1 hzero
      exact hnot x hx
    have hsqne :
        _root_.GD.N0233.N0731.d004958 (_root_.GD.N0233.N0722.d004978 B y) ≠ 0 := by
      intro hzero
      exact hres ((_root_.GD.N0233.N0731.d004960 _).1 hzero)
    exact lt_of_le_of_ne
      (_root_.GD.N0233.N0731.d004959 (_root_.GD.N0233.N0722.d004978 B y))
      hsqne.symm





theorem d005005
    (B : Matrix m n ℝ) (y : m → ℝ) :
    _root_.GD.N0233.N0721.d004998 B y =
      _root_.GD.N0233.N0729.d004925 (_root_.GD.N0233.N0721.d004996 B y) := by
  unfold _root_.GD.N0233.N0721.d004998
  exact
    _root_.GD.N0233.N0729.d004930
      (_root_.GD.N0233.N0721.d004996 B y)





theorem d005006
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) :
    (∃ x : n → ℝ, B *ᵥ x = y) ↔
      ∀ g : _root_.GD.N0233.N0729.d004922 (m := m) (n := n ⊕ Fin 1),
        det (_root_.GD.N0233.N0729.d004923 (_root_.GD.N0233.N0721.d004996 B y) g) = 0 := by
  rw [← _root_.GD.N0233.N0721.d005003 B hdet y]
  rw [_root_.GD.N0233.N0721.d005005]
  exact
    _root_.GD.N0233.N0729.d004934
      (_root_.GD.N0233.N0721.d004996 B y)





theorem d005007
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) :
    (¬ ∃ x : n → ℝ, B *ᵥ x = y) ↔
      ∃ g : _root_.GD.N0233.N0729.d004922 (m := m) (n := n ⊕ Fin 1),
        det (_root_.GD.N0233.N0729.d004923 (_root_.GD.N0233.N0721.d004996 B y) g) ≠ 0 := by
  rw [← _root_.GD.N0233.N0721.d005004 B hdet y]
  rw [_root_.GD.N0233.N0721.d005005]
  constructor
  · intro hpos
    exact
      (_root_.GD.N0233.N0729.d004932
        (_root_.GD.N0233.N0721.d004996 B y)).1 (ne_of_gt hpos)
  · intro hex
    have hne :
        _root_.GD.N0233.N0729.d004925 (_root_.GD.N0233.N0721.d004996 B y) ≠ 0 :=
      (_root_.GD.N0233.N0729.d004932
        (_root_.GD.N0233.N0721.d004996 B y)).2 hex
    exact lt_of_le_of_ne
      (_root_.GD.N0233.N0729.d004927 (_root_.GD.N0233.N0721.d004996 B y))
      hne.symm

end

end N0721
end N0233
end GD
