import GD.Module0692




















open scoped BigOperators

namespace GD.N0232.N0719.N1002

noncomputable section

open _root_.GD.N0232.N0719.N1016


def d010214 (x y z : ℝ) : ℝ :=
  (x + y + z) / 3


def d010215 (x y z : ℝ) : ℝ :=
  (x - _root_.GD.N0232.N0719.N1002.d010214 x y z) ^ 3 +
    (y - _root_.GD.N0232.N0719.N1002.d010214 x y z) ^ 3 +
    (z - _root_.GD.N0232.N0719.N1002.d010214 x y z) ^ 3


def d010216 (x y z : ℝ) : ℝ :=
  (x - _root_.GD.N0232.N0719.N1002.d010214 x y z) *
    (y - _root_.GD.N0232.N0719.N1002.d010214 x y z) *
    (z - _root_.GD.N0232.N0719.N1002.d010214 x y z)


theorem d010217 (x y z c : ℝ) :
    _root_.GD.N0232.N0719.N1002.d010215 (x + c) (y + c) (z + c) =
      _root_.GD.N0232.N0719.N1002.d010215 x y z := by
  simp only [_root_.GD.N0232.N0719.N1002.d010215, _root_.GD.N0232.N0719.N1002.d010214]
  ring


theorem d010218 (x y z : ℝ) :
    _root_.GD.N0232.N0719.N1002.d010215 (-x) (-y) (-z) = -_root_.GD.N0232.N0719.N1002.d010215 x y z := by
  simp only [_root_.GD.N0232.N0719.N1002.d010215, _root_.GD.N0232.N0719.N1002.d010214]
  ring


theorem d010219 (x y z : ℝ) :
    _root_.GD.N0232.N0719.N1002.d010215 y x z = _root_.GD.N0232.N0719.N1002.d010215 x y z := by
  simp only [_root_.GD.N0232.N0719.N1002.d010215, _root_.GD.N0232.N0719.N1002.d010214]
  ring


theorem d010220 (x y z : ℝ) :
    _root_.GD.N0232.N0719.N1002.d010215 y z x = _root_.GD.N0232.N0719.N1002.d010215 x y z := by
  simp only [_root_.GD.N0232.N0719.N1002.d010215, _root_.GD.N0232.N0719.N1002.d010214]
  ring




theorem d010221 (x y z : ℝ) :
    _root_.GD.N0232.N0719.N1002.d010215 x y z = 3 * _root_.GD.N0232.N0719.N1002.d010216 x y z := by
  simp only [_root_.GD.N0232.N0719.N1002.d010215, _root_.GD.N0232.N0719.N1002.d010216, _root_.GD.N0232.N0719.N1002.d010214]
  ring


theorem d010222 :
    _root_.GD.N0232.N0719.N1002.d010215 0 1 3 = (20 : ℝ) / 9 := by
  norm_num [_root_.GD.N0232.N0719.N1002.d010215, _root_.GD.N0232.N0719.N1002.d010214]



theorem d010223 :
    _root_.GD.N0232.N0719.N1002.d010215 0 1 3 ≠ 0 := by
  rw [_root_.GD.N0232.N0719.N1002.d010222]
  norm_num


theorem d010224 (x y z : ℝ) :
    _root_.GD.N0232.N0719.N1002.d010216 x y z = 0 ↔
      2 * x = y + z ∨ 2 * y = x + z ∨ 2 * z = x + y := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hxy | hz
    · rcases mul_eq_zero.mp hxy with hx | hy
      · left
        simp only [_root_.GD.N0232.N0719.N1002.d010214] at hx
        linarith
      · right
        left
        simp only [_root_.GD.N0232.N0719.N1002.d010214] at hy
        linarith
    · right
      right
      simp only [_root_.GD.N0232.N0719.N1002.d010214] at hz
      linarith
  · rintro (hx | hy | hz)
    · apply mul_eq_zero_of_left
      apply mul_eq_zero_of_left
      simp only [_root_.GD.N0232.N0719.N1002.d010214]
      linarith
    · apply mul_eq_zero_of_left
      apply mul_eq_zero_of_right
      simp only [_root_.GD.N0232.N0719.N1002.d010214]
      linarith
    · apply mul_eq_zero_of_right
      simp only [_root_.GD.N0232.N0719.N1002.d010214]
      linarith


theorem d010225 (x y z : ℝ) :
    _root_.GD.N0232.N0719.N1002.d010215 x y z = 0 ↔
      2 * x = y + z ∨ 2 * y = x + z ∨ 2 * z = x + y := by
  rw [_root_.GD.N0232.N0719.N1002.d010221]
  constructor
  · intro h
    have hp : _root_.GD.N0232.N0719.N1002.d010216 x y z = 0 := by
      rcases mul_eq_zero.mp h with hthree | hp
      · norm_num at hthree
      · exact hp
    exact (_root_.GD.N0232.N0719.N1002.d010224 x y z).mp hp
  · intro h
    rw [(_root_.GD.N0232.N0719.N1002.d010224 x y z).mpr h]
    ring





theorem d010226
    (f : ℝ → ℝ → ℝ)
    (htranslate : ∀ x y c, f (x + c) (y + c) = f x y)
    (hswap : ∀ x y, f y x = f x y)
    (hodd : ∀ x y, f (-x) (-y) = -f x y) :
    ∀ x y, f x y = 0 := by
  intro x y
  have hreflect : f (-y) (-x) = f x y := by
    calc
      f (-y) (-x) = f (x + (-(x + y))) (y + (-(x + y))) := by
        congr 2 <;> ring
      _ = f x y := htranslate x y (-(x + y))
  have hneg : f (-y) (-x) = -f x y := by
    calc
      f (-y) (-x) = f (-x) (-y) := hswap (-x) (-y)
      _ = -f x y := hodd x y
  linarith



def d010227
    (A B C x y z : ℝ) : ℝ :=
  A * (x ^ 3 + y ^ 3 + z ^ 3) +
    B * (x ^ 2 * y + x ^ 2 * z + y ^ 2 * x +
      y ^ 2 * z + z ^ 2 * x + z ^ 2 * y) +
    C * x * y * z


def d010228 (A B C : ℝ) : Prop :=
  ∀ x y z t,
    _root_.GD.N0232.N0719.N1002.d010227 A B C (x + t) (y + t) (z + t) =
      _root_.GD.N0232.N0719.N1002.d010227 A B C x y z


theorem d010229 (A B C : ℝ) :
    _root_.GD.N0232.N0719.N1002.d010228 A B C ↔
      2 * B = -3 * A ∧ C = 6 * A := by
  constructor
  · intro h
    have hdiag := h 0 0 0 1
    have hedge := h 1 0 0 (-1)
    simp only [_root_.GD.N0232.N0719.N1002.d010227] at hdiag hedge
    constructor <;> nlinarith
  · rintro ⟨hB, hC⟩ x y z t
    have hB' : B = -(3 * A) / 2 := by linarith
    have hC' : C = 6 * A := by linarith
    rw [hB', hC']
    simp only [_root_.GD.N0232.N0719.N1002.d010227]
    ring



theorem d010230
    {A B C : ℝ} (h : _root_.GD.N0232.N0719.N1002.d010228 A B C)
    (x y z : ℝ) :
    _root_.GD.N0232.N0719.N1002.d010227 A B C x y z =
      (9 * A / 2) * _root_.GD.N0232.N0719.N1002.d010215 x y z := by
  rcases (_root_.GD.N0232.N0719.N1002.d010229 A B C).mp h with ⟨hB, hC⟩
  have hB' : B = -(3 * A) / 2 := by linarith
  have hC' : C = 6 * A := by linarith
  rw [hB', hC']
  simp only [_root_.GD.N0232.N0719.N1002.d010227, _root_.GD.N0232.N0719.N1002.d010215, _root_.GD.N0232.N0719.N1002.d010214]
  ring



theorem d010231 (x y z : ℝ) :
    _root_.GD.N0232.N0719.N1016.d003609 (1 / 3 : ℝ) (1 / 3 : ℝ) (1 / 3 : ℝ) x y z =
      -(3 / 2 : ℝ) * _root_.GD.N0232.N0719.N1002.d010215 x y z := by
  norm_num [_root_.GD.N0232.N0719.N1016.d003609, _root_.GD.N0232.N0719.N1002.d010215, _root_.GD.N0232.N0719.N1002.d010214]
  ring


theorem d010232 (x y z : ℝ) :
    _root_.GD.N0232.N0719.N1016.d003609 (1 / 3 : ℝ) (1 / 3 : ℝ) (1 / 3 : ℝ) x y z =
      -(9 / 2 : ℝ) * _root_.GD.N0232.N0719.N1002.d010216 x y z := by
  rw [_root_.GD.N0232.N0719.N1002.d010231,
    _root_.GD.N0232.N0719.N1002.d010221]
  ring



theorem d010233 (x y z : ℝ) :
    _root_.GD.N0232.N0719.N1016.d003609 (1 / 3 : ℝ) (1 / 3 : ℝ) (1 / 3 : ℝ) x y z = 0 ↔
      2 * x = y + z ∨ 2 * y = x + z ∨ 2 * z = x + y := by
  rw [_root_.GD.N0232.N0719.N1002.d010232]
  constructor
  · intro h
    have hp : _root_.GD.N0232.N0719.N1002.d010216 x y z = 0 := by
      rcases mul_eq_zero.mp h with hcoef | hp
      · norm_num at hcoef
      · exact hp
    exact (_root_.GD.N0232.N0719.N1002.d010224 x y z).mp hp
  · intro h
    rw [(_root_.GD.N0232.N0719.N1002.d010224 x y z).mpr h]
    ring

end

end GD.N0232.N0719.N1002
