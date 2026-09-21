import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

















open scoped BigOperators Matrix
open MeasureTheory MeasureTheory.Measure

namespace GD.N0234

section CommRing

variable {ι R : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [CommRing R]


theorem d003286 (u v : ι → R) :
    Matrix.det (1 + Matrix.vecMulVec u v) = 1 + v ⬝ᵥ u := by
  rw [Matrix.vecMulVec_eq (Fin 1)]
  exact Matrix.det_one_add_replicateCol_mul_replicateRow u v



theorem d003287 (c : R) (w : ι → R) :
    Matrix.det (1 + Matrix.vecMulVec (fun _ => c) w) =
      1 + c * ∑ j, w j := by
  rw [_root_.GD.N0234.d003286]
  simp only [dotProduct]
  rw [← Finset.sum_mul, mul_comm]

end CommRing

section Field

variable {ι K : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Field K]



def d003288 (wₖ : K) (w : ι → K) : Matrix ι ι K :=
  1 + Matrix.vecMulVec (fun _ => wₖ⁻¹) w

omit [Fintype ι] in

@[simp]
theorem d003289 (wₖ : K) (w : ι → K) (i j : ι) :
    _root_.GD.N0234.d003288 wₖ w i j =
      (if i = j then 1 else 0) + w j / wₖ := by
  simp [_root_.GD.N0234.d003288, Matrix.one_apply, Matrix.vecMulVec_apply,
    div_eq_mul_inv, mul_comm]


theorem d003290 (wₖ : K) (w : ι → K) :
    Matrix.det (_root_.GD.N0234.d003288 wₖ w) =
      1 + (∑ j, w j) / wₖ := by
  rw [_root_.GD.N0234.d003288, _root_.GD.N0234.d003287]
  simp only [div_eq_mul_inv]
  congr 1
  rw [mul_comm]



theorem d003291
    (wₖ : K) (w : ι → K)
    (hwₖ : wₖ ≠ 0)
    (hnorm : wₖ + ∑ j, w j = 1) :
    Matrix.det (_root_.GD.N0234.d003288 wₖ w) = 1 / wₖ := by
  rw [_root_.GD.N0234.d003290]
  calc
    1 + (∑ j, w j) / wₖ =
        wₖ / wₖ + (∑ j, w j) / wₖ := by rw [div_self hwₖ]
    _ = (wₖ + ∑ j, w j) / wₖ := (add_div _ _ _).symm
    _ = 1 / wₖ := by rw [hnorm]

end Field

section Coordinates

variable {n : ℕ}


noncomputable def d003292
    (wₖ : ℝ) (w x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i + (∑ j, w j * x j) / wₖ


noncomputable def d003293
    (w y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => y i - ∑ j, w j * y j



theorem d003294
    (wₖ : ℝ) (w x : Fin n → ℝ) :
    _root_.GD.N0234.d003288 wₖ w *ᵥ x = _root_.GD.N0234.d003292 wₖ w x := by
  funext i
  simp [_root_.GD.N0234.d003288, _root_.GD.N0234.d003292, Matrix.add_mulVec,
    Matrix.vecMulVec_mulVec, dotProduct, div_eq_mul_inv,
    Finset.mul_sum, mul_assoc, mul_comm]



theorem d003295
    (wₖ : ℝ) (w : Fin n → ℝ)
    (hwₖ : wₖ ≠ 0)
    (hnorm : wₖ + ∑ j, w j = 1) :
    Matrix.det (_root_.GD.N0234.d003288 wₖ w) = 1 / wₖ :=
  _root_.GD.N0234.d003291 wₖ w hwₖ hnorm



theorem d003296
    (wₖ : ℝ) (w x : Fin n → ℝ)
    (hwₖ : wₖ ≠ 0)
    (hnorm : wₖ + ∑ j, w j = 1) :
    _root_.GD.N0234.d003293 w (_root_.GD.N0234.d003292 wₖ w x) = x := by
  funext i
  have hsum :
      (∑ j, w j * _root_.GD.N0234.d003292 wₖ w x j) =
        (∑ j, w j * x j) +
          (∑ j, w j) * ((∑ j, w j * x j) / wₖ) := by
    simp only [_root_.GD.N0234.d003292, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul]
  change
    _root_.GD.N0234.d003292 wₖ w x i -
        (∑ j, w j * _root_.GD.N0234.d003292 wₖ w x j) = x i
  rw [hsum]
  simp only [_root_.GD.N0234.d003292]
  field_simp [hwₖ]
  rw [hnorm]
  ring




theorem d003297
    (wₖ : ℝ) (w y : Fin n → ℝ)
    (hwₖ : wₖ ≠ 0)
    (hnorm : wₖ + ∑ j, w j = 1) :
    _root_.GD.N0234.d003292 wₖ w (_root_.GD.N0234.d003293 w y) = y := by
  funext i
  have hsum :
      (∑ j, w j * _root_.GD.N0234.d003293 w y j) =
        (∑ j, w j * y j) -
          (∑ j, w j) * (∑ j, w j * y j) := by
    simp only [_root_.GD.N0234.d003293, mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul]
  change
    _root_.GD.N0234.d003293 w y i +
        (∑ j, w j * _root_.GD.N0234.d003293 w y j) / wₖ = y i
  rw [hsum]
  simp only [_root_.GD.N0234.d003293]
  have hcomplement : 1 - ∑ j, w j = wₖ := by
    linarith [hnorm]
  field_simp [hwₖ]
  rw [hcomplement]
  ring






noncomputable def d003298
    (wₖ : ℝ) (w : Fin n → ℝ)
    (hwₖ : wₖ ≠ 0)
    (hnorm : wₖ + ∑ j, w j = 1) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun := _root_.GD.N0234.d003292 wₖ w
  invFun := _root_.GD.N0234.d003293 w
  left_inv := fun x ↦
    _root_.GD.N0234.d003296 wₖ w x hwₖ hnorm
  right_inv := fun y ↦
    _root_.GD.N0234.d003297 wₖ w y hwₖ hnorm
  map_add' := by
    intro x y
    funext i
    simp only [_root_.GD.N0234.d003292, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro c x
    funext i
    have hsum :
        (∑ j, w j * (c * x j)) =
          c * ∑ j, w j * x j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    change
      c * x i + (∑ j, w j * (c * x j)) / wₖ =
        c * (x i + (∑ j, w j * x j) / wₖ)
    rw [hsum]
    ring

@[simp]
theorem d003299
    (wₖ : ℝ) (w : Fin n → ℝ)
    (hwₖ : wₖ ≠ 0)
    (hnorm : wₖ + ∑ j, w j = 1)
    (x : Fin n → ℝ) :
    _root_.GD.N0234.d003298 wₖ w hwₖ hnorm x =
      _root_.GD.N0234.d003292 wₖ w x :=
  rfl



theorem d003300
    (wₖ : ℝ) (w : Fin n → ℝ)
    (hwₖ : wₖ ≠ 0)
    (hnorm : wₖ + ∑ j, w j = 1) :
    (_root_.GD.N0234.d003298 wₖ w hwₖ hnorm :
        (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)).toLinearMap =
      Matrix.toLin' (_root_.GD.N0234.d003288 wₖ w) := by
  apply LinearMap.ext
  intro x
  exact (_root_.GD.N0234.d003294 wₖ w x).symm



theorem d003301
    (wₖ : ℝ) (w : Fin n → ℝ)
    (hwₖ : wₖ ≠ 0)
    (hnorm : wₖ + ∑ j, w j = 1) :
    LinearMap.det
        (_root_.GD.N0234.d003298 wₖ w hwₖ hnorm :
          (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)).toLinearMap =
      1 / wₖ := by
  rw [_root_.GD.N0234.d003300, LinearMap.det_toLin']
  exact _root_.GD.N0234.d003295 wₖ w hwₖ hnorm






theorem d003302
    (wₖ : ℝ) (w : Fin n → ℝ)
    (hwₖ : wₖ ≠ 0)
    (hnorm : wₖ + ∑ j, w j = 1) :
    Measure.map (_root_.GD.N0234.d003292 wₖ w)
        (volume : Measure (Fin n → ℝ)) =
      ENNReal.ofReal |wₖ| • volume := by
  rw [show _root_.GD.N0234.d003292 wₖ w =
      (_root_.GD.N0234.d003298 wₖ w hwₖ hnorm :
        (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)).toLinearMap from rfl]
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi]
  · rw [_root_.GD.N0234.d003301]
    congr 2
    field_simp [hwₖ]
  · rw [_root_.GD.N0234.d003301]
    exact one_div_ne_zero hwₖ






theorem d003303
    (wₖ : ℝ) (w : Fin n → ℝ)
    (hwₖ : wₖ ≠ 0)
    (hnorm : wₖ + ∑ j, w j = 1)
    (s : Set (Fin n → ℝ)) :
    volume (_root_.GD.N0234.d003292 wₖ w ⁻¹' s) =
      ENNReal.ofReal |wₖ| * volume s := by
  rw [show _root_.GD.N0234.d003292 wₖ w =
      (_root_.GD.N0234.d003298 wₖ w hwₖ hnorm :
        (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)).toLinearMap from rfl]
  rw [addHaar_preimage_linearMap]
  · rw [_root_.GD.N0234.d003301]
    congr 2
    field_simp [hwₖ]
  · rw [_root_.GD.N0234.d003301]
    exact one_div_ne_zero hwₖ





theorem d003304
    (wₖ : ℝ) (w : Fin n → ℝ)
    (hwₖ : wₖ ≠ 0)
    (hnorm : wₖ + ∑ j, w j = 1)
    (s : Set (Fin n → ℝ)) :
    volume (_root_.GD.N0234.d003292 wₖ w '' s) =
      ENNReal.ofReal |1 / wₖ| * volume s := by
  rw [show _root_.GD.N0234.d003292 wₖ w =
      (_root_.GD.N0234.d003298 wₖ w hwₖ hnorm :
        (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)).toLinearMap from rfl]
  rw [addHaar_image_linearMap, _root_.GD.N0234.d003301]

end Coordinates

end GD.N0234
