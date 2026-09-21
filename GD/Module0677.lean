import GD.Module0676
import GD.Module0654
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic















open MeasureTheory Set
open scoped BigOperators

namespace GD.N0232.N0719.N0922

noncomputable section

open _root_.GD.N0232.N0719.N0928
open _root_.GD.N0232.N0719.N0929
open _root_.GD.N0232.N0719.N0927


def d009915 : Fin 3 → ℝ :=
  _root_.GD.N0232.N0719.N0954.d009355 _root_.GD.N0232.N0719.N0927.d009909

@[simp] theorem d009916 : _root_.GD.N0232.N0719.N0922.d009915 0 = 1 / 2 := by
  unfold _root_.GD.N0232.N0719.N0922.d009915 _root_.GD.N0232.N0719.N0954.d009355
  rw [show _root_.GD.N0232.N0719.N0927.d009909 0 = 2 by rfl]
  norm_num

@[simp] theorem d009917 : _root_.GD.N0232.N0719.N0922.d009915 1 = 5 / 2 := by
  unfold _root_.GD.N0232.N0719.N0922.d009915 _root_.GD.N0232.N0719.N0954.d009355
  rw [show _root_.GD.N0232.N0719.N0927.d009909 1 = 6 by rfl]
  norm_num

@[simp] theorem d009918 : _root_.GD.N0232.N0719.N0922.d009915 2 = 5 / 2 := by
  unfold _root_.GD.N0232.N0719.N0922.d009915 _root_.GD.N0232.N0719.N0954.d009355
  rw [show _root_.GD.N0232.N0719.N0927.d009909 2 = 6 by rfl]
  norm_num



@[simp] theorem d009919 :
    _root_.GD.N0232.N0719.N0928.d009415 _root_.GD.N0232.N0719.N0922.d009915 (5 / 2) = 8 := by
  simpa [_root_.GD.N0232.N0719.N0922.d009915, _root_.GD.N0232.N0719.N0927.d009897] using _root_.GD.N0232.N0719.N0927.d009911



def d009920 (xz : ℝ × ℝ) :
    _root_.GD.N0232.N0719.N0857.d009377 3 :=
  ![1 - xz.1 - xz.2, xz.1]

theorem d009921 (xz : ℝ × ℝ) :
    ∑ j, _root_.GD.N0232.N0719.N0922.d009920 xz j = 1 - xz.2 := by
  calc
    (∑ j, _root_.GD.N0232.N0719.N0922.d009920 xz j) = _root_.GD.N0232.N0719.N0922.d009920 xz 0 + _root_.GD.N0232.N0719.N0922.d009920 xz 1 := by
      exact Fin.sum_univ_two _
    _ = 1 - xz.2 := by
      simp [_root_.GD.N0232.N0719.N0922.d009920]
      ring


def d009922 (xz : ℝ × ℝ) : Fin 3 → ℝ :=
  _root_.GD.N0232.N0719.N0853.d009567 (by norm_num) (_root_.GD.N0232.N0719.N0922.d009920 xz)

@[simp] theorem d009923 (xz : ℝ × ℝ) :
    _root_.GD.N0232.N0719.N0922.d009922 xz 0 = 1 - xz.1 - xz.2 := by
  rw [show (0 : Fin 3) = _root_.GD.N0232.N0719.N0954.d009344 3
      (by norm_num) (Sum.inl 0) by rfl]
  exact _root_.GD.N0232.N0719.N0853.d009568
    (by norm_num) (_root_.GD.N0232.N0719.N0922.d009920 xz) 0

@[simp] theorem d009924 (xz : ℝ × ℝ) :
    _root_.GD.N0232.N0719.N0922.d009922 xz 1 = xz.1 := by
  rw [show (1 : Fin 3) = _root_.GD.N0232.N0719.N0954.d009344 3
      (by norm_num) (Sum.inl 1) by rfl]
  exact _root_.GD.N0232.N0719.N0853.d009568
    (by norm_num) (_root_.GD.N0232.N0719.N0922.d009920 xz) 1

@[simp] theorem d009925 (xz : ℝ × ℝ) :
    _root_.GD.N0232.N0719.N0922.d009922 xz 2 = xz.2 := by
  rw [show (2 : Fin 3) = _root_.GD.N0232.N0719.N0954.d009344 3
      (by norm_num) (Sum.inr 0) by rfl]
  unfold _root_.GD.N0232.N0719.N0922.d009922
  have h := _root_.GD.N0232.N0719.N0853.d009569
      (by norm_num) (_root_.GD.N0232.N0719.N0922.d009920 xz)
  rw [h, _root_.GD.N0232.N0719.N0922.d009921]
  ring


def d009926 : Set (ℝ × ℝ) :=
  {xz | 0 < xz.1 ∧ 0 < xz.2 ∧ xz.1 + xz.2 < 1}

theorem d009927 (xz : ℝ × ℝ) :
    _root_.GD.N0232.N0719.N0922.d009920 xz ∈ _root_.GD.N0232.N0719.N0955.d009607 3 ↔
      xz ∈ _root_.GD.N0232.N0719.N0922.d009926 := by
  unfold _root_.GD.N0232.N0719.N0955.d009607 _root_.GD.N0232.N0719.N0922.d009926
  constructor
  · rintro ⟨hq, hlast⟩
    have hp0 := hq (0 : Fin 2)
    have hx := hq (1 : Fin 2)
    have hz : 0 < xz.2 := by
      rw [_root_.GD.N0232.N0719.N0922.d009921] at hlast
      linarith
    have hp0' : 0 < 1 - xz.1 - xz.2 := by
      simpa [_root_.GD.N0232.N0719.N0922.d009920] using hp0
    exact ⟨by simpa [_root_.GD.N0232.N0719.N0922.d009920] using hx, hz,
      by linarith⟩
  · rintro ⟨hx, hz, hsum⟩
    constructor
    · intro j
      fin_cases j
      · simpa [_root_.GD.N0232.N0719.N0922.d009920] using (show 0 < 1 - xz.1 - xz.2 by linarith)
      · simpa [_root_.GD.N0232.N0719.N0922.d009920] using hx
    · rw [_root_.GD.N0232.N0719.N0922.d009921]
      linarith




def d009928 (ε : ℝ) (y t : Fin 3 → ℝ) : Prop :=
  0 < ε ∧ ε ≤ 1 ∧
  ε ≤ t 0 ∧ t 0 ≤ 2 * ε ∧
  1 ≤ t 1 ∧ t 1 ≤ 2 ∧
  1 ≤ t 2 ∧ t 2 ≤ 2 ∧
  1 ≤ y 1 - y 0 ∧ y 1 - y 0 ≤ 2 ∧
  1 ≤ y 2 - y 0 ∧ y 2 - y 0 ≤ 2

theorem d009929
    {xz : ℝ × ℝ} (hxz : xz ∈ _root_.GD.N0232.N0719.N0922.d009926) :
    ∀ i, 0 ≤ _root_.GD.N0232.N0719.N0922.d009922 xz i := by
  intro i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · rw [_root_.GD.N0232.N0719.N0922.d009923]
    linarith [hxz.2.2]
  · rw [_root_.GD.N0232.N0719.N0922.d009924]
    exact hxz.1.le
  · rw [_root_.GD.N0232.N0719.N0922.d009925]
    exact hxz.2.1.le

theorem d009930 (xz : ℝ × ℝ) :
    ∑ i, _root_.GD.N0232.N0719.N0922.d009922 xz i = 1 := by
  rw [Fin.sum_univ_three]
  simp only [_root_.GD.N0232.N0719.N0922.d009923, _root_.GD.N0232.N0719.N0922.d009924, _root_.GD.N0232.N0719.N0922.d009925]
  ring



theorem d009931
    {ε : ℝ} {y t : Fin 3 → ℝ} (hE : _root_.GD.N0232.N0719.N0922.d009928 ε y t)
    {xz : ℝ × ℝ} (hxz : xz ∈ _root_.GD.N0232.N0719.N0922.d009926) :
    (1 / 2 : ℝ) * (ε + (xz.1 + xz.2)) ≤
      _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t := by
  have hcontrast := _root_.GD.N0232.N0719.N0928.d009441
    (_root_.GD.N0232.N0719.N0922.d009922 xz) y (_root_.GD.N0232.N0719.N0922.d009929 hxz)
  unfold _root_.GD.N0232.N0719.N0928.d009407
  rw [Fin.sum_univ_three]
  simp only [_root_.GD.N0232.N0719.N0922.d009916, _root_.GD.N0232.N0719.N0922.d009917, _root_.GD.N0232.N0719.N0922.d009918,
    _root_.GD.N0232.N0719.N0922.d009923, _root_.GD.N0232.N0719.N0922.d009924, _root_.GD.N0232.N0719.N0922.d009925]
  rcases hE with
    ⟨hε, hε1, ht0l, ht0u, ht1l, ht1u, ht2l, ht2u,
      hy1l, hy1u, hy2l, hy2u⟩
  have hp0 : 0 ≤ 1 - xz.1 - xz.2 := by linarith [hxz.2.2]
  have hx : 0 ≤ xz.1 := hxz.1.le
  have hz : 0 ≤ xz.2 := hxz.2.1.le
  have h0 := mul_le_mul_of_nonneg_left ht0l hp0
  have h1 := mul_le_mul_of_nonneg_left ht1l hx
  have h2 := mul_le_mul_of_nonneg_left ht2l hz
  nlinarith



theorem d009932
    (y : Fin 3 → ℝ) (xz : ℝ × ℝ) :
    _root_.GD.N0232.N0719.N0928.d009406 (_root_.GD.N0232.N0719.N0922.d009922 xz) y ≤
      (1 / 2 : ℝ) *
        ∑ i, _root_.GD.N0232.N0719.N0922.d009922 xz i * (y i - y 0) ^ 2 := by
  have hcompletion :=
    _root_.GD.N0232.N0719.N0928.d009419
      (_root_.GD.N0232.N0719.N0922.d009922 xz) y (y 0) (_root_.GD.N0232.N0719.N0922.d009930 xz)
  nlinarith [sq_nonneg (y 0 - _root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0719.N0922.d009922 xz) y)]



theorem d009933
    {ε : ℝ} {y t : Fin 3 → ℝ} (hE : _root_.GD.N0232.N0719.N0922.d009928 ε y t)
    {xz : ℝ × ℝ} (hxz : xz ∈ _root_.GD.N0232.N0719.N0922.d009926) :
    _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t ≤
      7 * (ε + (xz.1 + xz.2)) := by
  have hcontrast := _root_.GD.N0232.N0719.N0922.d009932 y xz
  unfold _root_.GD.N0232.N0719.N0928.d009407 at ⊢
  rw [Fin.sum_univ_three]
  rw [Fin.sum_univ_three] at hcontrast
  simp only [_root_.GD.N0232.N0719.N0922.d009916, _root_.GD.N0232.N0719.N0922.d009917, _root_.GD.N0232.N0719.N0922.d009918,
    _root_.GD.N0232.N0719.N0922.d009923, _root_.GD.N0232.N0719.N0922.d009924, _root_.GD.N0232.N0719.N0922.d009925] at ⊢ hcontrast
  rcases hE with
    ⟨hε, hε1, ht0l, ht0u, ht1l, ht1u, ht2l, ht2u,
      hy1l, hy1u, hy2l, hy2u⟩
  have hp0 : 0 ≤ 1 - xz.1 - xz.2 := by linarith [hxz.2.2]
  have hp0le : 1 - xz.1 - xz.2 ≤ 1 := by linarith [hxz.1, hxz.2.1]
  have hx : 0 ≤ xz.1 := hxz.1.le
  have hz : 0 ≤ xz.2 := hxz.2.1.le
  have h0 := mul_le_mul_of_nonneg_left ht0u hp0
  have h1 := mul_le_mul_of_nonneg_left ht1u hx
  have h2 := mul_le_mul_of_nonneg_left ht2u hz
  have hy1sq : (y 1 - y 0) ^ 2 ≤ 4 := by nlinarith
  have hy2sq : (y 2 - y 0) ^ 2 ≤ 4 := by nlinarith
  have hy1w := mul_le_mul_of_nonneg_left hy1sq hx
  have hy2w := mul_le_mul_of_nonneg_left hy2sq hz
  nlinarith



theorem d009934
    {ε : ℝ} {y t : Fin 3 → ℝ} (hE : _root_.GD.N0232.N0719.N0922.d009928 ε y t)
    {xz : ℝ × ℝ} (hxz : xz ∈ _root_.GD.N0232.N0719.N0922.d009926) :
    xz.1 + xz.2 ≤
      _root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0719.N0922.d009922 xz) y - y 0 := by
  unfold _root_.GD.N0232.N0719.N0928.d009405
  rw [Fin.sum_univ_three]
  simp only [_root_.GD.N0232.N0719.N0922.d009923, _root_.GD.N0232.N0719.N0922.d009924, _root_.GD.N0232.N0719.N0922.d009925]
  rcases hE with
    ⟨hε, hε1, ht0l, ht0u, ht1l, ht1u, ht2l, ht2u,
      hy1l, hy1u, hy2l, hy2u⟩
  have hx : 0 ≤ xz.1 := hxz.1.le
  have hz : 0 ≤ xz.2 := hxz.2.1.le
  have h1 := mul_le_mul_of_nonneg_left hy1l hx
  have h2 := mul_le_mul_of_nonneg_left hy2l hz
  nlinarith


theorem d009935
    {xz : ℝ × ℝ} (hxz : xz ∈ _root_.GD.N0232.N0719.N0922.d009926) :
    _root_.GD.N0232.N0719.N0928.d009409 _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) =
      (1 - xz.1 - xz.2) * xz.1 ^ 3 * xz.2 ^ 3 := by
  unfold _root_.GD.N0232.N0719.N0928.d009409
  rw [Fin.prod_univ_three]
  simp only [_root_.GD.N0232.N0719.N0922.d009916, _root_.GD.N0232.N0719.N0922.d009917, _root_.GD.N0232.N0719.N0922.d009918,
    _root_.GD.N0232.N0719.N0922.d009923, _root_.GD.N0232.N0719.N0922.d009924, _root_.GD.N0232.N0719.N0922.d009925]
  norm_num [Real.rpow_one, Real.rpow_natCast]

end

end GD.N0232.N0719.N0922
