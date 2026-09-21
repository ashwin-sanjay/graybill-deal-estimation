import Mathlib.Analysis.InnerProductSpace.Projection.Submodule





















open scoped RealInnerProductSpace

namespace GD
namespace N0233
namespace N0728

noncomputable section

variable
    {H Y : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]


def d003226 (A : H →L[ℝ] Y) (x : H) : H :=
  A.ker.starProjection x


def d003227 (A : H →L[ℝ] Y) (x : H) : H :=
  x - _root_.GD.N0233.N0728.d003226 A x


theorem d003228 (A : H →L[ℝ] Y) (x : H) :
    _root_.GD.N0233.N0728.d003226 A x ∈ A.ker :=
  A.ker.starProjection_apply_mem x



theorem d003229 (A : H →L[ℝ] Y) (x : H) :
    _root_.GD.N0233.N0728.d003227 A x ∈ A.kerᗮ := by
  exact A.ker.sub_starProjection_mem_orthogonal x


theorem d003230 (A : H →L[ℝ] Y) (x : H) :
    _root_.GD.N0233.N0728.d003227 A x + _root_.GD.N0233.N0728.d003226 A x = x := by
  simp [_root_.GD.N0233.N0728.d003227]


@[simp]
theorem d003231 (A : H →L[ℝ] Y) (x : H) :
    A (_root_.GD.N0233.N0728.d003226 A x) = 0 := by
  exact LinearMap.mem_ker.mp (_root_.GD.N0233.N0728.d003228 A x)


@[simp]
theorem d003232 (A : H →L[ℝ] Y) (x : H) :
    A (_root_.GD.N0233.N0728.d003227 A x) = A x := by
  simp [_root_.GD.N0233.N0728.d003227]


theorem d003233
    (A : H →L[ℝ] Y) {x : H} (hx : x ∈ A.kerᗮ) :
    _root_.GD.N0233.N0728.d003227 A x = x := by
  have hproj : A.ker.orthogonalProjectionOnto x = 0 :=
    A.ker.orthogonalProjectionOnto_apply_of_mem_orthogonal hx
  have hstar : A.ker.starProjection x = 0 := by
    change ((A.ker.orthogonalProjectionOnto x : A.ker) : H) = 0
    rw [hproj]
    rfl
  simp [_root_.GD.N0233.N0728.d003227, _root_.GD.N0233.N0728.d003226, hstar]


theorem d003234
    (A : H →L[ℝ] Y) {x z : H}
    (hx : x ∈ A.kerᗮ) (hz : z ∈ A.kerᗮ)
    (hmap : A x = A z) :
    x = z := by
  have hker : x - z ∈ A.ker := by
    apply LinearMap.mem_ker.mpr
    simpa [hmap]
  have hortho : x - z ∈ A.kerᗮ :=
    A.kerᗮ.sub_mem hx hz
  have hinner : inner ℝ (x - z) (x - z) = 0 :=
    (Submodule.mem_orthogonal' A.ker (x - z)).1 hortho (x - z) hker
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hinner)


theorem d003235
    (A : H →L[ℝ] Y) {x z : H} (hmap : A x = A z) :
    _root_.GD.N0233.N0728.d003227 A x = _root_.GD.N0233.N0728.d003227 A z :=
  _root_.GD.N0233.N0728.d003234 A
    (_root_.GD.N0233.N0728.d003229 A x)
    (_root_.GD.N0233.N0728.d003229 A z)
    (by simpa using hmap)



theorem d003236
    (A : H →L[ℝ] Y) (x : H) :
    ‖x‖ ^ 2 =
      ‖_root_.GD.N0233.N0728.d003227 A x‖ ^ 2 + ‖_root_.GD.N0233.N0728.d003226 A x‖ ^ 2 := by
  have hpyth :=
    A.ker.norm_sq_eq_add_norm_sq_starProjection x
  simpa [_root_.GD.N0233.N0728.d003227, _root_.GD.N0233.N0728.d003226,
    A.ker.starProjection_orthogonal_val, add_comm] using hpyth



theorem d003237 (A : H →L[ℝ] Y) (x : H) :
    ‖_root_.GD.N0233.N0728.d003227 A x‖ ≤ ‖x‖ := by
  rw [_root_.GD.N0233.N0728.d003227, _root_.GD.N0233.N0728.d003226, ← A.ker.starProjection_orthogonal_val]
  exact (A.kerᗮ).norm_starProjection_apply_le x



theorem d003238
    (A : H →L[ℝ] Y) {x : H} (hvertical : _root_.GD.N0233.N0728.d003226 A x ≠ 0) :
    ‖_root_.GD.N0233.N0728.d003227 A x‖ < ‖x‖ := by
  have htax : 0 < ‖_root_.GD.N0233.N0728.d003226 A x‖ ^ 2 := by
    exact sq_pos_of_pos (norm_pos_iff.mpr hvertical)
  have hdecomp := _root_.GD.N0233.N0728.d003236 A x
  nlinarith [norm_nonneg (_root_.GD.N0233.N0728.d003227 A x), norm_nonneg x]


abbrev d003239 (A : H →L[ℝ] Y) :=
  LinearMap.range A.toLinearMap


def d003240 (A : H →L[ℝ] Y) (y : _root_.GD.N0233.N0728.d003239 A) : H :=
  Classical.choose y.property

@[simp]
theorem d003241 (A : H →L[ℝ] Y) (y : _root_.GD.N0233.N0728.d003239 A) :
    A (_root_.GD.N0233.N0728.d003240 A y) = y.1 :=
  Classical.choose_spec y.property


def d003242 (A : H →L[ℝ] Y) (y : _root_.GD.N0233.N0728.d003239 A) : H :=
  _root_.GD.N0233.N0728.d003227 A (_root_.GD.N0233.N0728.d003240 A y)

@[simp]
theorem d003243 (A : H →L[ℝ] Y) (y : _root_.GD.N0233.N0728.d003239 A) :
    A (_root_.GD.N0233.N0728.d003242 A y) = y.1 := by
  simp [_root_.GD.N0233.N0728.d003242]

theorem d003244
    (A : H →L[ℝ] Y) (y : _root_.GD.N0233.N0728.d003239 A) :
    _root_.GD.N0233.N0728.d003242 A y ∈ A.kerᗮ :=
  _root_.GD.N0233.N0728.d003229 A (_root_.GD.N0233.N0728.d003240 A y)


theorem d003245
    (A : H →L[ℝ] Y) (y : _root_.GD.N0233.N0728.d003239 A) {x : H}
    (hxmap : A x = y.1) (hxorthogonal : x ∈ A.kerᗮ) :
    x = _root_.GD.N0233.N0728.d003242 A y :=
  _root_.GD.N0233.N0728.d003234 A hxorthogonal
    (_root_.GD.N0233.N0728.d003244 A y)
    (hxmap.trans (_root_.GD.N0233.N0728.d003243 A y).symm)


theorem d003246
    (A : H →L[ℝ] Y) (y : _root_.GD.N0233.N0728.d003239 A) {x : H}
    (hxmap : A x = y.1) :
    _root_.GD.N0233.N0728.d003227 A x = _root_.GD.N0233.N0728.d003242 A y := by
  apply _root_.GD.N0233.N0728.d003234 A
    (_root_.GD.N0233.N0728.d003229 A x)
    (_root_.GD.N0233.N0728.d003244 A y)
  simpa using hxmap


def d003247 (A : H →L[ℝ] Y) (y : _root_.GD.N0233.N0728.d003239 A) : ℝ :=
  ‖_root_.GD.N0233.N0728.d003242 A y‖ ^ 2

theorem d003248
    (A : H →L[ℝ] Y) (y : _root_.GD.N0233.N0728.d003239 A) :
    0 ≤ _root_.GD.N0233.N0728.d003247 A y := by
  simp [_root_.GD.N0233.N0728.d003247]



theorem d003249
    (A : H →L[ℝ] Y) (y : _root_.GD.N0233.N0728.d003239 A) {x : H}
    (hxmap : A x = y.1) :
    ‖x‖ ^ 2 =
      _root_.GD.N0233.N0728.d003247 A y + ‖_root_.GD.N0233.N0728.d003226 A x‖ ^ 2 := by
  rw [_root_.GD.N0233.N0728.d003236 A x,
    _root_.GD.N0233.N0728.d003246 A y hxmap]
  rfl


theorem d003250
    (A : H →L[ℝ] Y) (y : _root_.GD.N0233.N0728.d003239 A) {x : H}
    (hxmap : A x = y.1) :
    ‖_root_.GD.N0233.N0728.d003242 A y‖ ≤ ‖x‖ := by
  rw [← _root_.GD.N0233.N0728.d003246 A y hxmap]
  exact _root_.GD.N0233.N0728.d003237 A x


theorem d003251
    (A : H →L[ℝ] Y) (y : _root_.GD.N0233.N0728.d003239 A) {x : H}
    (hxmap : A x = y.1) :
    _root_.GD.N0233.N0728.d003247 A y ≤ ‖x‖ ^ 2 := by
  have h := _root_.GD.N0233.N0728.d003250 A y hxmap
  simpa [_root_.GD.N0233.N0728.d003247] using
    (sq_le_sq₀ (norm_nonneg (_root_.GD.N0233.N0728.d003242 A y)) (norm_nonneg x)).2 h



theorem d003252
    (A : H →L[ℝ] Y) (y : _root_.GD.N0233.N0728.d003239 A) {x : H}
    (hxmap : A x = y.1) :
    ‖x‖ = ‖_root_.GD.N0233.N0728.d003242 A y‖ ↔ x = _root_.GD.N0233.N0728.d003242 A y := by
  constructor
  · intro hnorm
    have hdecomp :=
      _root_.GD.N0233.N0728.d003249 A y hxmap
    have htaxsq : ‖_root_.GD.N0233.N0728.d003226 A x‖ ^ 2 = 0 := by
      dsimp [_root_.GD.N0233.N0728.d003247] at hdecomp
      rw [hnorm] at hdecomp
      linarith
    have hvertical : _root_.GD.N0233.N0728.d003226 A x = 0 := by
      apply norm_eq_zero.mp
      exact (sq_eq_zero_iff).mp htaxsq
    calc
      x = _root_.GD.N0233.N0728.d003227 A x := by simp [_root_.GD.N0233.N0728.d003227, hvertical]
      _ = _root_.GD.N0233.N0728.d003242 A y := _root_.GD.N0233.N0728.d003246 A y hxmap
  · intro hx
    rw [hx]


theorem d003253
    (A : H →L[ℝ] Y) (y : _root_.GD.N0233.N0728.d003239 A) :
    _root_.GD.N0233.N0728.d003247 A y = 0 ↔ y = 0 := by
  constructor
  · intro henergy
    have hminzero : _root_.GD.N0233.N0728.d003242 A y = 0 := by
      apply norm_eq_zero.mp
      exact (sq_eq_zero_iff).mp (by simpa [_root_.GD.N0233.N0728.d003247] using henergy)
    apply Subtype.ext
    change y.1 = (0 : Y)
    rw [← _root_.GD.N0233.N0728.d003243 A y, hminzero]
    simp
  · rintro rfl
    have hzero : _root_.GD.N0233.N0728.d003242 A (0 : _root_.GD.N0233.N0728.d003239 A) = 0 := by
      exact (_root_.GD.N0233.N0728.d003245 A (0 : _root_.GD.N0233.N0728.d003239 A)
        (x := 0) (by simp) (by simp)).symm
    simp [_root_.GD.N0233.N0728.d003247, hzero]

end

end N0728
end N0233
end GD
