import GD.Module0332
import GD.Module0333

























namespace GD
namespace N0233
namespace N0722

noncomputable section

open Matrix
open _root_.GD.N0233.N0729
open _root_.GD.N0233.N0730
open _root_.GD.N0233.N0731
open _root_.GD.N0233.N0732

variable {m n : Type*}
variable [Fintype m] [DecidableEq m]
variable [Fintype n] [DecidableEq n]


def d004978
    (B : Matrix m n ℝ) (y : m → ℝ) : m → ℝ :=
  y - _root_.GD.N0233.N0732.d004966 B *ᵥ y


def d004979
    (B : Matrix m n ℝ) (y z : m → ℝ) : ℝ :=
  _root_.GD.N0233.N0722.d004978 B y ⬝ᵥ z




theorem d004980
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) :
    B.transpose *ᵥ _root_.GD.N0233.N0722.d004978 B y = 0 := by
  have h :=
    _root_.GD.N0233.N0732.d004972 B hdet y
  have hneg :
      _root_.GD.N0233.N0722.d004978 B y =
        -(_root_.GD.N0233.N0732.d004966 B *ᵥ y - y) := by
    unfold _root_.GD.N0233.N0722.d004978
    abel
  rw [hneg, Matrix.mulVec_neg, h, neg_zero]




theorem d004981
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) (x : n → ℝ) :
    _root_.GD.N0233.N0722.d004979 B y (B *ᵥ x) = 0 := by
  unfold _root_.GD.N0233.N0722.d004979
  calc
    _root_.GD.N0233.N0722.d004978 B y ⬝ᵥ (B *ᵥ x) =
        (_root_.GD.N0233.N0722.d004978 B y ᵥ* B) ⬝ᵥ x :=
      Matrix.dotProduct_mulVec _ _ _
    _ = (B.transpose *ᵥ _root_.GD.N0233.N0722.d004978 B y) ⬝ᵥ x := by
      rw [Matrix.mulVec_transpose]
    _ = 0 := by
      rw [_root_.GD.N0233.N0722.d004980 B hdet y,
        zero_dotProduct]




theorem d004982
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) :
    _root_.GD.N0233.N0722.d004978 B y = 0 ↔
      ∃ x : n → ℝ, B *ᵥ x = y := by
  constructor
  · intro hzero
    have hfix :
        _root_.GD.N0233.N0732.d004966 B *ᵥ y = y := by
      have :
          y = _root_.GD.N0233.N0732.d004966 B *ᵥ y :=
        sub_eq_zero.mp hzero
      exact this.symm
    exact
      (_root_.GD.N0233.N0732.d004974
        B hdet y).mp hfix
  · rintro ⟨x, hx⟩
    have hfix :
        _root_.GD.N0233.N0732.d004966 B *ᵥ y = y :=
      (_root_.GD.N0233.N0732.d004974
        B hdet y).mpr ⟨x, hx⟩
    unfold _root_.GD.N0233.N0722.d004978
    rw [hfix, sub_self]




theorem d004983
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) :
    _root_.GD.N0233.N0722.d004978 B y = 0 ↔
      B *ᵥ _root_.GD.N0233.N0730.d004943 B y = y := by
  constructor
  · intro hzero
    have hfix :
        _root_.GD.N0233.N0732.d004966 B *ᵥ y = y := by
      have :
          y = _root_.GD.N0233.N0732.d004966 B *ᵥ y :=
        sub_eq_zero.mp hzero
      exact this.symm
    exact (_root_.GD.N0233.N0732.d004967 B y).symm.trans hfix
  · intro hanchor
    exact
      (_root_.GD.N0233.N0722.d004982
        B hdet y).mpr ⟨_root_.GD.N0233.N0730.d004943 B y, hanchor⟩





theorem d004984
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) :
    _root_.GD.N0233.N0722.d004979 B y y =
      _root_.GD.N0233.N0731.d004958 (_root_.GD.N0233.N0722.d004978 B y) := by
  let r : m → ℝ := _root_.GD.N0233.N0722.d004978 B y
  let p : m → ℝ := _root_.GD.N0233.N0732.d004966 B *ᵥ y
  have hy : y = p + r := by
    dsimp [p, r, _root_.GD.N0233.N0722.d004978]
    abel
  have hp :
      _root_.GD.N0233.N0722.d004979 B y p = 0 := by
    dsimp [p]
    rw [_root_.GD.N0233.N0732.d004967]
    exact
      _root_.GD.N0233.N0722.d004981
        B hdet y (_root_.GD.N0233.N0730.d004943 B y)
  unfold _root_.GD.N0233.N0722.d004979 at hp
  change r ⬝ᵥ p = 0 at hp
  unfold _root_.GD.N0233.N0731.d004958
  change r ⬝ᵥ y = r ⬝ᵥ r
  rw [hy, dotProduct_add, hp, zero_add]





theorem d004985
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ)
    (hres : _root_.GD.N0233.N0722.d004978 B y ≠ 0) :
    0 < _root_.GD.N0233.N0722.d004979 B y y := by
  rw [_root_.GD.N0233.N0722.d004984 B hdet y]
  have hnonneg :=
    _root_.GD.N0233.N0731.d004959
      (_root_.GD.N0233.N0722.d004978 B y)
  have hne :
      _root_.GD.N0233.N0731.d004958 (_root_.GD.N0233.N0722.d004978 B y) ≠ 0 := by
    intro hzero
    exact hres <|
      (_root_.GD.N0233.N0731.d004960
        (_root_.GD.N0233.N0722.d004978 B y)).mp hzero
  exact lt_of_le_of_ne hnonneg hne.symm

omit [DecidableEq m] in





theorem d004986
    (B : Matrix m n ℝ) (y : m → ℝ) :
    _root_.GD.N0233.N0722.d004978 B y =
      -(B *ᵥ _root_.GD.N0233.N0730.d004943 B y - y) := by
  unfold _root_.GD.N0233.N0722.d004978
  rw [_root_.GD.N0233.N0732.d004967]
  abel





theorem d004987
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) :
    _root_.GD.N0233.N0722.d004979 B y y =
      _root_.GD.N0233.N0731.d004958
        (B *ᵥ _root_.GD.N0233.N0730.d004943 B y - y) := by
  have hneg :
      ∀ v : m → ℝ,
        _root_.GD.N0233.N0731.d004958 (-v) =
          _root_.GD.N0233.N0731.d004958 v := by
    intro v
    unfold _root_.GD.N0233.N0731.d004958
    rw [neg_dotProduct, dotProduct_neg, neg_neg]
  rw [_root_.GD.N0233.N0722.d004984 B hdet y,
    _root_.GD.N0233.N0722.d004986,
    hneg]








theorem d004988
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) :
    (_root_.GD.N0233.N0722.d004979 B y y =
      _root_.GD.N0233.N0731.d004958
        (B *ᵥ _root_.GD.N0233.N0730.d004943 B y - y)) ∧
    (∀ x : n → ℝ,
      _root_.GD.N0233.N0722.d004979 B y y ≤
        _root_.GD.N0233.N0731.d004958 (B *ᵥ x - y)) ∧
    (∀ x : n → ℝ,
      _root_.GD.N0233.N0731.d004958 (B *ᵥ x - y) =
          _root_.GD.N0233.N0722.d004979 B y y ↔
        x = _root_.GD.N0233.N0730.d004943 B y) := by
  have hmargin :=
    _root_.GD.N0233.N0722.d004987
      B hdet y
  refine ⟨hmargin, ?_, ?_⟩
  · intro x
    rw [hmargin]
    exact
      _root_.GD.N0233.N0731.d004963
        B hdet y x
  · intro x
    rw [hmargin]
    exact
      _root_.GD.N0233.N0731.d004964
        B hdet y x






theorem d004989
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (y : m → ℝ) :
    ((B *ᵥ _root_.GD.N0233.N0730.d004943 B y = y) ∧
        ∀ x : n → ℝ, B *ᵥ x = y →
          x = _root_.GD.N0233.N0730.d004943 B y) ∨
      ((∀ x : n → ℝ,
          _root_.GD.N0233.N0722.d004979 B y (B *ᵥ x) = 0) ∧
        0 < _root_.GD.N0233.N0722.d004979 B y y) := by
  by_cases hres : _root_.GD.N0233.N0722.d004978 B y = 0
  · left
    have hanchor :=
      (_root_.GD.N0233.N0722.d004983
        B hdet y).mp hres
    refine ⟨hanchor, ?_⟩
    intro x hx
    exact
      (_root_.GD.N0233.N0730.d004950
        B hdet y x hx).symm
  · right
    exact
      ⟨_root_.GD.N0233.N0722.d004981 B hdet y,
        _root_.GD.N0233.N0722.d004985 B hdet y hres⟩

omit [DecidableEq m] in



theorem d004990
    (B : Matrix m n ℝ)
    (y : m → ℝ)
    (hexact : ∃ x : n → ℝ, B *ᵥ x = y)
    (hann : ∀ x : n → ℝ,
      _root_.GD.N0233.N0722.d004979 B y (B *ᵥ x) = 0) :
    ¬ 0 < _root_.GD.N0233.N0722.d004979 B y y := by
  rintro hpos
  rcases hexact with ⟨x, rfl⟩
  simpa using hpos.ne' (hann x)


def d004991
    (B : Matrix m n ℝ) (b y : m → ℝ) : m → ℝ :=
  _root_.GD.N0233.N0722.d004978 B (y - b)





def d004992
    (B : Matrix m n ℝ) (b y z : m → ℝ) : ℝ :=
  _root_.GD.N0233.N0722.d004991 B b y ⬝ᵥ (z - b)


theorem d004993
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (b y : m → ℝ) (x : n → ℝ) :
    _root_.GD.N0233.N0722.d004992 B b y (b + B *ᵥ x) = 0 := by
  unfold _root_.GD.N0233.N0722.d004992 _root_.GD.N0233.N0722.d004991
  have hsub : b + B *ᵥ x - b = B *ᵥ x := by
    abel
  rw [hsub]
  exact _root_.GD.N0233.N0722.d004981 B hdet (y - b) x





theorem d004994
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (b y : m → ℝ) :
    _root_.GD.N0233.N0722.d004992 B b y y =
      _root_.GD.N0233.N0731.d004958
        (_root_.GD.N0233.N0722.d004991 B b y) := by
  unfold _root_.GD.N0233.N0722.d004992 _root_.GD.N0233.N0722.d004991
  exact _root_.GD.N0233.N0722.d004984 B hdet (y - b)






theorem d004995
    (B : Matrix m n ℝ)
    (hdet : det (_root_.GD.N0233.N0729.d004921 B) ≠ 0)
    (b y : m → ℝ) :
    ((b + B *ᵥ _root_.GD.N0233.N0730.d004943 B (y - b) = y) ∧
        ∀ x : n → ℝ, b + B *ᵥ x = y →
          x = _root_.GD.N0233.N0730.d004943 B (y - b)) ∨
      ((∀ x : n → ℝ,
          _root_.GD.N0233.N0722.d004992 B b y
            (b + B *ᵥ x) = 0) ∧
        0 < _root_.GD.N0233.N0722.d004992 B b y y) := by
  have halt :=
    _root_.GD.N0233.N0722.d004989
      B hdet (y - b)
  rcases halt with hexact | hsep
  · left
    rcases hexact with ⟨hanchor, hunique⟩
    constructor
    · have : B *ᵥ _root_.GD.N0233.N0730.d004943 B (y - b) = y - b :=
        hanchor
      rw [this]
      abel
    · intro x hx
      apply hunique x
      have : B *ᵥ x = y - b := by
        rw [← hx]
        abel
      exact this
  · right
    rcases hsep with ⟨hann, hpos⟩
    constructor
    · exact _root_.GD.N0233.N0722.d004993 B hdet b y
    · rw [_root_.GD.N0233.N0722.d004994 B hdet b y]
      change
        0 <
          _root_.GD.N0233.N0731.d004958
            (_root_.GD.N0233.N0722.d004978 B (y - b))
      rw [← _root_.GD.N0233.N0722.d004984 B hdet (y - b)]
      exact hpos

end

end N0722
end N0233
end GD
