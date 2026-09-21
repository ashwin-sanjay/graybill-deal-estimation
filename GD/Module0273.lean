import GD.Module0232



















namespace GD
namespace N0234
namespace N0739

open Matrix

variable {n R : Type*}
variable [Fintype n] [DecidableEq n]
variable [CommRing R]


def d004031 (T G : Matrix n n R) : Matrix n n R :=
  T.transpose * G * T


@[simp]
theorem d004032 (G : Matrix n n R) :
    _root_.GD.N0234.N0739.d004031 (1 : Matrix n n R) G = G := by
  simp [_root_.GD.N0234.N0739.d004031]

omit [DecidableEq n] in




theorem d004033
    (T S G : Matrix n n R) :
    _root_.GD.N0234.N0739.d004031 (T * S) G =
      _root_.GD.N0234.N0739.d004031 S (_root_.GD.N0234.N0739.d004031 T G) := by
  simp only [_root_.GD.N0234.N0739.d004031, Matrix.transpose_mul]
  noncomm_ring





theorem d004034
    (T G : Matrix n n R) :
    det (_root_.GD.N0234.N0739.d004031 T G) = det T ^ 2 * det G := by
  simp only [_root_.GD.N0234.N0739.d004031, det_mul, det_transpose]
  ring

section Real

variable (T G : Matrix n n ℝ)





theorem d004035
    (hT : det T ≠ 0) :
    det (_root_.GD.N0234.N0739.d004031 T G) = 0 ↔ det G = 0 := by
  rw [_root_.GD.N0234.N0739.d004034, mul_eq_zero]
  simp [hT]


theorem d004036
    (hT : det T ≠ 0) :
    det (_root_.GD.N0234.N0739.d004031 T G) ≠ 0 ↔ det G ≠ 0 := by
  rw [ne_eq, ne_eq, _root_.GD.N0234.N0739.d004035 T G hT]





theorem d004037
    (hT : det T ≠ 0) :
    0 < det (_root_.GD.N0234.N0739.d004031 T G) ↔ 0 < det G := by
  rw [_root_.GD.N0234.N0739.d004034]
  exact mul_pos_iff_of_pos_left (sq_pos_of_ne_zero hT)

end Real

end N0739
end N0234
end GD
