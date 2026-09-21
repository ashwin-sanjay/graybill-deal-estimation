import GD.Module0232



















namespace GD
namespace N0233
namespace N0733

open scoped BigOperators
open Matrix Polynomial

variable {n m R : Type*}
variable [Fintype n] [DecidableEq n]
variable [Fintype m] [DecidableEq m]
variable [CommRing R]


def d004019 (U : Matrix n m R) (w : m → R) : Matrix n n R :=
  U * diagonal w * U.transpose


def d004020 (U : Matrix n m R) (w : m → R) : Matrix m m R :=
  diagonal w * (U.transpose * U)

private theorem d004021
    (U : Matrix n m R) (w : m → R) :
    ((X : R[X]) • U.map C) *
        ((diagonal w * U.transpose).map C) =
      (X : R[X]) • (_root_.GD.N0233.N0733.d004019 U w).map C := by
  rw [Matrix.smul_mul]
  simp only [_root_.GD.N0233.N0733.d004019, Matrix.mul_assoc, Matrix.map_mul]

private theorem d004022
    (U : Matrix n m R) (w : m → R) :
    ((diagonal w * U.transpose).map C) *
        ((X : R[X]) • U.map C) =
      (X : R[X]) • (_root_.GD.N0233.N0733.d004020 U w).map C := by
  rw [Matrix.mul_smul]
  simp only [_root_.GD.N0233.N0733.d004020, Matrix.mul_assoc, Matrix.map_mul]





theorem d004023
    (U : Matrix n m R) (w : m → R) :
    det (1 + (X : R[X]) • (_root_.GD.N0233.N0733.d004019 U w).map C) =
      det (1 + (X : R[X]) • (_root_.GD.N0233.N0733.d004020 U w).map C) := by
  calc
    det (1 + (X : R[X]) • (_root_.GD.N0233.N0733.d004019 U w).map C) =
        det
          (1 + ((X : R[X]) • U.map C) *
            ((diagonal w * U.transpose).map C)) := by
          rw [_root_.GD.N0233.N0733.d004021]
    _ = det
          (1 + ((diagonal w * U.transpose).map C) *
            ((X : R[X]) • U.map C)) :=
      Matrix.det_one_add_mul_comm _ _
    _ = det (1 + (X : R[X]) • (_root_.GD.N0233.N0733.d004020 U w).map C) := by
      rw [_root_.GD.N0233.N0733.d004022]





theorem d004024
    (U : Matrix n m R) (w : m → R) :
    det (_root_.GD.N0233.N0733.d004019 U w) =
      ∑ s ∈ Finset.univ.powersetCard (Fintype.card n),
        ((_root_.GD.N0233.N0733.d004020 U w).submatrix
          (Subtype.val : s → m) (Subtype.val : s → m)).det := by
  have htop :
      (det (1 + (X : R[X]) • (_root_.GD.N0233.N0733.d004019 U w).map C)).coeff
          (Fintype.card n) =
        det (_root_.GD.N0233.N0733.d004019 U w) := by
    simpa [add_comm] using
      (Polynomial.coeff_det_X_add_C_card
        (_root_.GD.N0233.N0733.d004019 U w) (1 : Matrix n n R))
  have hminor :=
    Matrix.coeff_det_one_add_X_smul_eq_sum_minors
      (_root_.GD.N0233.N0733.d004020 U w) (Fintype.card n)
  rw [← htop, _root_.GD.N0233.N0733.d004023 U w]
  exact hminor



def d004025
    (U : Matrix n m R) {s : Finset m} (e : n ≃ s) : Matrix n n R :=
  U.submatrix id (Subtype.val ∘ e)





theorem d004026
    (U : Matrix n m R) (w : m → R) {s : Finset m} (e : n ≃ s) :
    ((_root_.GD.N0233.N0733.d004020 U w).submatrix
        (Subtype.val : s → m) (Subtype.val : s → m)).submatrix e e =
      diagonal (fun i ↦ w (e i : m)) *
        ((_root_.GD.N0233.N0733.d004025 U e).transpose * _root_.GD.N0233.N0733.d004025 U e) := by
  ext i j
  simp [_root_.GD.N0233.N0733.d004020, _root_.GD.N0233.N0733.d004025, Matrix.mul_apply, Matrix.diagonal_apply,
    Function.comp_def]





theorem d004027
    (U : Matrix n m R) (w : m → R) {s : Finset m} (e : n ≃ s) :
    ((_root_.GD.N0233.N0733.d004020 U w).submatrix
        (Subtype.val : s → m) (Subtype.val : s → m)).det =
      (∏ i : n, w (e i : m)) * det (_root_.GD.N0233.N0733.d004025 U e) ^ 2 := by
  have hreindex := congrArg det (_root_.GD.N0233.N0733.d004026 U w e)
  rw [Matrix.det_submatrix_equiv_self] at hreindex
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_transpose] at hreindex
  calc
    ((_root_.GD.N0233.N0733.d004020 U w).submatrix
        (Subtype.val : s → m) (Subtype.val : s → m)).det =
        (∏ i : n, w (e i : m)) *
          (det (_root_.GD.N0233.N0733.d004025 U e) * det (_root_.GD.N0233.N0733.d004025 U e)) := by
      simpa [mul_assoc] using hreindex
    _ = (∏ i : n, w (e i : m)) * det (_root_.GD.N0233.N0733.d004025 U e) ^ 2 := by ring




noncomputable def d004028
    (s : Finset m)
    (hs : s ∈ Finset.univ.powersetCard (Fintype.card n)) : n ≃ s :=
  Fintype.equivOfCardEq <| by
    have hcard : s.card = Fintype.card n :=
      (Finset.mem_powersetCard.mp hs).2
    simpa using hcard.symm



noncomputable def d004029
    (U : Matrix n m R) (w : m → R) (s : Finset m) : R :=
  if hs : s ∈ Finset.univ.powersetCard (Fintype.card n) then
    let e := _root_.GD.N0233.N0733.d004028 (n := n) s hs
    (∏ i : n, w (e i : m)) * det (_root_.GD.N0233.N0733.d004025 U e) ^ 2
  else
    0









theorem d004030
    (U : Matrix n m R) (w : m → R) :
    det (_root_.GD.N0233.N0733.d004019 U w) =
      ∑ s ∈ Finset.univ.powersetCard (Fintype.card n),
        _root_.GD.N0233.N0733.d004029 U w s := by
  rw [_root_.GD.N0233.N0733.d004024]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [_root_.GD.N0233.N0733.d004029, hs, dite_true]
  exact _root_.GD.N0233.N0733.d004027
    U w (_root_.GD.N0233.N0733.d004028 (n := n) s hs)

end N0733
end N0233
end GD
