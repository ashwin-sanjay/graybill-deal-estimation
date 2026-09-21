import GD.Module0643

















open scoped BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0931

noncomputable section

open _root_.GD.N0232.N0719.N0928

variable {I J : Type*} [Fintype I] [Fintype J]


def d009445 (shift dilation : ℝ) (y : I → ℝ) : I → ℝ :=
  fun i ↦ shift + dilation * y i


def d009446 (dilation : ℝ) (t : I → ℝ) : I → ℝ :=
  fun i ↦ dilation ^ 2 * t i


theorem d009447
    (p y : I → ℝ) (shift dilation : ℝ)
    (hsum : ∑ i, p i = 1) :
    _root_.GD.N0232.N0719.N0928.d009405 p (_root_.GD.N0232.N0719.N0931.d009445 shift dilation y) =
      shift + dilation * _root_.GD.N0232.N0719.N0928.d009405 p y := by
  unfold _root_.GD.N0232.N0719.N0928.d009405 _root_.GD.N0232.N0719.N0931.d009445
  calc
    (∑ i, p i * (shift + dilation * y i)) =
        shift * (∑ i, p i) + dilation * (∑ i, p i * y i) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = shift + dilation * (∑ i, p i * y i) := by rw [hsum, mul_one]



theorem d009448
    (p y : I → ℝ) (shift dilation : ℝ)
    (hsum : ∑ i, p i = 1) :
    _root_.GD.N0232.N0719.N0928.d009406 p (_root_.GD.N0232.N0719.N0931.d009445 shift dilation y) =
      dilation ^ 2 * _root_.GD.N0232.N0719.N0928.d009406 p y := by
  unfold _root_.GD.N0232.N0719.N0928.d009406
  rw [_root_.GD.N0232.N0719.N0931.d009447 p y shift dilation hsum]
  calc
    (1 / 2 : ℝ) *
          ∑ i, p i *
            (_root_.GD.N0232.N0719.N0931.d009445 shift dilation y i -
              (shift + dilation * _root_.GD.N0232.N0719.N0928.d009405 p y)) ^ 2 =
        (1 / 2 : ℝ) *
          ∑ i, dilation ^ 2 *
            (p i * (y i - _root_.GD.N0232.N0719.N0928.d009405 p y) ^ 2) := by
      apply congrArg ((1 / 2 : ℝ) * ·)
      apply Finset.sum_congr rfl
      intro i hi
      unfold _root_.GD.N0232.N0719.N0931.d009445
      ring
    _ = dilation ^ 2 *
          ((1 / 2 : ℝ) *
            ∑ i, p i * (y i - _root_.GD.N0232.N0719.N0928.d009405 p y) ^ 2) := by
      rw [← Finset.mul_sum]
      ring


theorem d009449
    (shape p y t : I → ℝ) (shift dilation : ℝ)
    (hsum : ∑ i, p i = 1) :
    _root_.GD.N0232.N0719.N0928.d009407 shape p
        (_root_.GD.N0232.N0719.N0931.d009445 shift dilation y)
        (_root_.GD.N0232.N0719.N0931.d009446 dilation t) =
      dilation ^ 2 * _root_.GD.N0232.N0719.N0928.d009407 shape p y t := by
  unfold _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0719.N0931.d009446
  rw [_root_.GD.N0232.N0719.N0931.d009448 p y shift dilation hsum]
  calc
    dilation ^ 2 * _root_.GD.N0232.N0719.N0928.d009406 p y +
          ∑ i, shape i * p i * (dilation ^ 2 * t i) =
        dilation ^ 2 * _root_.GD.N0232.N0719.N0928.d009406 p y +
          dilation ^ 2 * ∑ i, shape i * p i * t i := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = dilation ^ 2 *
          (_root_.GD.N0232.N0719.N0928.d009406 p y +
            ∑ i, shape i * p i * t i) := by ring


def d009450 (shape : I → ℝ) (s dilation : ℝ) : ℝ :=
  (dilation ^ 2) ^ (-_root_.GD.N0232.N0719.N0928.d009415 shape s)


theorem d009451
    (shape p y t : I → ℝ) (s shift : ℝ)
    {dilation : ℝ} (hdilation : 0 < dilation)
    (hsum : ∑ i, p i = 1)
    (henergy : 0 ≤ _root_.GD.N0232.N0719.N0928.d009407 shape p y t) :
    _root_.GD.N0232.N0719.N0928.d009437 shape p
        (_root_.GD.N0232.N0719.N0931.d009445 shift dilation y)
        (_root_.GD.N0232.N0719.N0931.d009446 dilation t) s =
      _root_.GD.N0232.N0719.N0931.d009450 shape s dilation *
        _root_.GD.N0232.N0719.N0928.d009437 shape p y t s := by
  unfold _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0931.d009450
  rw [_root_.GD.N0232.N0719.N0931.d009449 shape p y t shift dilation hsum]
  rw [Real.mul_rpow (sq_nonneg dilation) henergy]
  ring


def d009452
    (shape : I → ℝ) (s : ℝ)
    (weight : J → ℝ) (profile : J → I → ℝ)
    (y t : I → ℝ) : ℝ :=
  ∑ j, weight j * _root_.GD.N0232.N0719.N0928.d009437 shape (profile j) y t s


def d009453
    (shape : I → ℝ) (s : ℝ)
    (weight : J → ℝ) (profile : J → I → ℝ)
    (y t : I → ℝ) : ℝ :=
  ∑ j, weight j * _root_.GD.N0232.N0719.N0928.d009437 shape (profile j) y t s *
    _root_.GD.N0232.N0719.N0928.d009405 (profile j) y


def d009454
    (shape : I → ℝ) (s : ℝ)
    (weight : J → ℝ) (profile : J → I → ℝ)
    (y t : I → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0931.d009453 shape s weight profile y t /
    _root_.GD.N0232.N0719.N0931.d009452 shape s weight profile y t



theorem d009455
    (shape : I → ℝ) (s : ℝ)
    (weight : J → ℝ) (profile : J → I → ℝ)
    (y t : I → ℝ) (shift : ℝ)
    {dilation : ℝ} (hdilation : 0 < dilation)
    (hsum : ∀ j, ∑ i, profile j i = 1)
    (henergy : ∀ j, 0 ≤ _root_.GD.N0232.N0719.N0928.d009407 shape (profile j) y t) :
    _root_.GD.N0232.N0719.N0931.d009452 shape s weight profile
        (_root_.GD.N0232.N0719.N0931.d009445 shift dilation y)
        (_root_.GD.N0232.N0719.N0931.d009446 dilation t) =
      _root_.GD.N0232.N0719.N0931.d009450 shape s dilation *
        _root_.GD.N0232.N0719.N0931.d009452 shape s weight profile y t := by
  unfold _root_.GD.N0232.N0719.N0931.d009452
  calc
    (∑ j, weight j *
        _root_.GD.N0232.N0719.N0928.d009437 shape (profile j)
          (_root_.GD.N0232.N0719.N0931.d009445 shift dilation y)
          (_root_.GD.N0232.N0719.N0931.d009446 dilation t) s) =
      ∑ j, _root_.GD.N0232.N0719.N0931.d009450 shape s dilation *
        (weight j * _root_.GD.N0232.N0719.N0928.d009437 shape (profile j) y t s) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [_root_.GD.N0232.N0719.N0931.d009451
        shape (profile j) y t s shift hdilation (hsum j) (henergy j)]
      ring
    _ = _root_.GD.N0232.N0719.N0931.d009450 shape s dilation *
        (∑ j, weight j *
          _root_.GD.N0232.N0719.N0928.d009437 shape (profile j) y t s) := by
      rw [Finset.mul_sum]



theorem d009456
    (shape : I → ℝ) (s : ℝ)
    (weight : J → ℝ) (profile : J → I → ℝ)
    (y t : I → ℝ) (shift : ℝ)
    {dilation : ℝ} (hdilation : 0 < dilation)
    (hsum : ∀ j, ∑ i, profile j i = 1)
    (henergy : ∀ j, 0 ≤ _root_.GD.N0232.N0719.N0928.d009407 shape (profile j) y t) :
    _root_.GD.N0232.N0719.N0931.d009453 shape s weight profile
        (_root_.GD.N0232.N0719.N0931.d009445 shift dilation y)
        (_root_.GD.N0232.N0719.N0931.d009446 dilation t) =
      _root_.GD.N0232.N0719.N0931.d009450 shape s dilation *
        (shift * _root_.GD.N0232.N0719.N0931.d009452 shape s weight profile y t +
          dilation * _root_.GD.N0232.N0719.N0931.d009453 shape s weight profile y t) := by
  unfold _root_.GD.N0232.N0719.N0931.d009453 _root_.GD.N0232.N0719.N0931.d009452
  calc
    (∑ j, weight j *
        _root_.GD.N0232.N0719.N0928.d009437 shape (profile j)
          (_root_.GD.N0232.N0719.N0931.d009445 shift dilation y)
          (_root_.GD.N0232.N0719.N0931.d009446 dilation t) s *
        _root_.GD.N0232.N0719.N0928.d009405 (profile j) (_root_.GD.N0232.N0719.N0931.d009445 shift dilation y)) =
      ∑ j, _root_.GD.N0232.N0719.N0931.d009450 shape s dilation *
        (shift * (weight j *
          _root_.GD.N0232.N0719.N0928.d009437 shape (profile j) y t s) +
        dilation * (weight j *
          _root_.GD.N0232.N0719.N0928.d009437 shape (profile j) y t s *
            _root_.GD.N0232.N0719.N0928.d009405 (profile j) y)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [_root_.GD.N0232.N0719.N0931.d009451
        shape (profile j) y t s shift hdilation (hsum j) (henergy j),
        _root_.GD.N0232.N0719.N0931.d009447 (profile j) y shift dilation (hsum j)]
      ring
    _ = _root_.GD.N0232.N0719.N0931.d009450 shape s dilation *
        (shift * (∑ j, weight j *
          _root_.GD.N0232.N0719.N0928.d009437 shape (profile j) y t s) +
        dilation * (∑ j, weight j *
          _root_.GD.N0232.N0719.N0928.d009437 shape (profile j) y t s *
            _root_.GD.N0232.N0719.N0928.d009405 (profile j) y)) := by
      calc
        (∑ j, _root_.GD.N0232.N0719.N0931.d009450 shape s dilation *
            (shift * (weight j *
              _root_.GD.N0232.N0719.N0928.d009437 shape (profile j) y t s) +
            dilation * (weight j *
              _root_.GD.N0232.N0719.N0928.d009437 shape (profile j) y t s *
                _root_.GD.N0232.N0719.N0928.d009405 (profile j) y))) =
          ∑ j, ((_root_.GD.N0232.N0719.N0931.d009450 shape s dilation * shift) *
                (weight j * _root_.GD.N0232.N0719.N0928.d009437 shape (profile j) y t s) +
              (_root_.GD.N0232.N0719.N0931.d009450 shape s dilation * dilation) *
                (weight j * _root_.GD.N0232.N0719.N0928.d009437 shape (profile j) y t s *
                  _root_.GD.N0232.N0719.N0928.d009405 (profile j) y)) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
        _ = (_root_.GD.N0232.N0719.N0931.d009450 shape s dilation * shift) *
              (∑ j, weight j *
                _root_.GD.N0232.N0719.N0928.d009437 shape (profile j) y t s) +
            (_root_.GD.N0232.N0719.N0931.d009450 shape s dilation * dilation) *
              (∑ j, weight j *
                _root_.GD.N0232.N0719.N0928.d009437 shape (profile j) y t s *
                  _root_.GD.N0232.N0719.N0928.d009405 (profile j) y) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ = _ := by ring



theorem d009457
    (shape : I → ℝ) (s : ℝ)
    (weight : J → ℝ) (profile : J → I → ℝ)
    (y t : I → ℝ) (shift : ℝ)
    {dilation : ℝ} (hdilation : 0 < dilation)
    (hsum : ∀ j, ∑ i, profile j i = 1)
    (henergy : ∀ j, 0 ≤ _root_.GD.N0232.N0719.N0928.d009407 shape (profile j) y t)
    (hdenom : _root_.GD.N0232.N0719.N0931.d009452 shape s weight profile y t ≠ 0) :
    _root_.GD.N0232.N0719.N0931.d009454 shape s weight profile
        (_root_.GD.N0232.N0719.N0931.d009445 shift dilation y)
        (_root_.GD.N0232.N0719.N0931.d009446 dilation t) =
      shift + dilation *
        _root_.GD.N0232.N0719.N0931.d009454 shape s weight profile y t := by
  have hchar : _root_.GD.N0232.N0719.N0931.d009450 shape s dilation ≠ 0 := by
    unfold _root_.GD.N0232.N0719.N0931.d009450
    exact ne_of_gt (Real.rpow_pos_of_pos (sq_pos_of_pos hdilation) _)
  unfold _root_.GD.N0232.N0719.N0931.d009454
  rw [_root_.GD.N0232.N0719.N0931.d009456 shape s weight profile y t shift
      hdilation hsum henergy,
    _root_.GD.N0232.N0719.N0931.d009455 shape s weight profile y t shift
      hdilation hsum henergy]
  field_simp [hchar, hdenom]



theorem d009458
    [Nonempty J]
    (shape : I → ℝ) (s : ℝ)
    (weight : J → ℝ) (profile : J → I → ℝ)
    (y t : I → ℝ)
    (hweight : ∀ j, 0 < weight j)
    (hprofile : ∀ j i, 0 < profile j i)
    (henergy : ∀ j, 0 < _root_.GD.N0232.N0719.N0928.d009407 shape (profile j) y t)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    0 < _root_.GD.N0232.N0719.N0931.d009452 shape s weight profile y t := by
  classical
  unfold _root_.GD.N0232.N0719.N0931.d009452
  exact Finset.sum_pos'
    (fun j _ ↦
      (mul_pos (hweight j)
        (_root_.GD.N0232.N0719.N0928.d009440 shape (profile j) y t s
          (hprofile j) (henergy j) hpower)).le)
    ⟨Classical.choice inferInstance, Finset.mem_univ _,
      mul_pos (hweight _)
        (_root_.GD.N0232.N0719.N0928.d009440 shape
          (profile (Classical.choice inferInstance)) y t s
          (hprofile _) (henergy _) hpower)⟩




theorem d009459
    [Nonempty J]
    (shape : I → ℝ) (s : ℝ)
    (weight : J → ℝ) (profile : J → I → ℝ)
    (y t : I → ℝ) (shift : ℝ)
    {dilation : ℝ} (hdilation : 0 < dilation)
    (hsum : ∀ j, ∑ i, profile j i = 1)
    (hweight : ∀ j, 0 < weight j)
    (hprofile : ∀ j i, 0 < profile j i)
    (henergy : ∀ j, 0 < _root_.GD.N0232.N0719.N0928.d009407 shape (profile j) y t)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    _root_.GD.N0232.N0719.N0931.d009454 shape s weight profile
        (_root_.GD.N0232.N0719.N0931.d009445 shift dilation y)
        (_root_.GD.N0232.N0719.N0931.d009446 dilation t) =
      shift + dilation *
        _root_.GD.N0232.N0719.N0931.d009454 shape s weight profile y t := by
  apply _root_.GD.N0232.N0719.N0931.d009457 shape s weight profile y t shift
      hdilation hsum (fun j ↦ (henergy j).le)
  exact (_root_.GD.N0232.N0719.N0931.d009458 shape s weight profile y t
    hweight hprofile henergy hpower).ne'

end

end N0931
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0931.d009449
#print axioms _root_.GD.N0232.N0719.N0931.d009451
#print axioms _root_.GD.N0232.N0719.N0931.d009457
#print axioms _root_.GD.N0232.N0719.N0931.d009459
