import GD.Module1030
















open Filter MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace GD
namespace N0232
namespace N0720
namespace N1118

noncomputable section

open _root_.GD.N0230.N0617
open _root_.GD.N0232.N0720.N1078
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1126
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1484
open _root_.GD.N0232.N0720.N1499

variable {m n : ℕ}
variable {iota kappa : Type*}
variable [Fintype iota] [DecidableEq iota]
variable [Fintype kappa] [DecidableEq kappa]

set_option linter.unusedSectionVars false




theorem d016458
    (z₀ z₁ a₀ a₁ : ℝ) (hz₀ : 0 < z₀) (hz₁ : 0 < z₁) :
    a₀ ^ 2 / z₀ + a₁ ^ 2 / z₁ - (a₀ + a₁) ^ 2 / (z₀ + z₁) =
      (z₀ * z₁ / (z₀ + z₁)) * (a₀ / z₀ - a₁ / z₁) ^ 2 := by
  field_simp [hz₀.ne', hz₁.ne', (add_pos hz₀ hz₁).ne']
  ring


theorem d016459
    (z₀ z₁ a₀ a₁ : ℝ) (hz₀ : 0 < z₀) (hz₁ : 0 < z₁) :
    (a₀ ^ 2 / z₀ + a₁ ^ 2 / z₁) / 2 -
        ((a₀ + a₁) / 2) ^ 2 / ((z₀ + z₁) / 2) =
      (1 / 2 : ℝ) * (z₀ * z₁ / (z₀ + z₁)) *
        (a₀ / z₀ - a₁ / z₁) ^ 2 := by
  field_simp [hz₀.ne', hz₁.ne', (add_pos hz₀ hz₁).ne']
  ring


theorem d016460
    (alpha z₀ z₁ a₀ a₁ : ℝ)
    (halpha₀ : 0 ≤ alpha) (halpha₁ : alpha ≤ 1)
    (hz₀ : 0 < z₀) (hz₁ : 0 < z₁) :
    alpha * (a₀ ^ 2 / z₀) + (1 - alpha) * (a₁ ^ 2 / z₁) -
        (alpha * a₀ + (1 - alpha) * a₁) ^ 2 /
          (alpha * z₀ + (1 - alpha) * z₁) =
      (alpha * (1 - alpha) * z₀ * z₁ /
          (alpha * z₀ + (1 - alpha) * z₁)) *
        (a₀ / z₀ - a₁ / z₁) ^ 2 := by
  have hnonneg : 0 ≤ 1 - alpha := sub_nonneg.mpr halpha₁
  have hzbar : 0 < alpha * z₀ + (1 - alpha) * z₁ := by
    by_cases halpha : alpha = 0
    · subst alpha
      simpa using hz₁
    · have halphaPos : 0 < alpha :=
        lt_of_le_of_ne halpha₀ (Ne.symm halpha)
      exact add_pos_of_pos_of_nonneg (mul_pos halphaPos hz₀)
        (mul_nonneg hnonneg hz₁.le)
  field_simp [hz₀.ne', hz₁.ne', hzbar.ne']
  ring



theorem d016461
    (z₀ z₁ u₀ u₁ : ℝ) (hz₀ : 1 ≤ z₀) (hz₁ : 1 ≤ z₁) :
    (1 / 4 : ℝ) * (u₀ - u₁) ^ 2 ≤
      (1 / 2 : ℝ) * (z₀ * z₁ / (z₀ + z₁)) * (u₀ - u₁) ^ 2 := by
  have hzsum : 0 < z₀ + z₁ := by linarith
  have hprod : z₀ + z₁ ≤ 2 * (z₀ * z₁) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz₀) (sub_nonneg.mpr hz₁)]
  have hratio : (1 / 2 : ℝ) ≤ z₀ * z₁ / (z₀ + z₁) := by
    rw [le_div_iff₀ hzsum]
    nlinarith
  have hcoefficient : (1 / 4 : ℝ) ≤
      (1 / 2 : ℝ) * (z₀ * z₁ / (z₀ + z₁)) := by
    nlinarith
  exact mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg (u₀ - u₁))


theorem d016462
    (z₀ z₁ a₀ a₁ : ℝ) (hz₀ : 0 < z₀) (hz₁ : 0 < z₁) :
    ((a₀ + a₁) / 2) ^ 2 / ((z₀ + z₁) / 2) ≤
      (a₀ ^ 2 / z₀ + a₁ ^ 2 / z₁) / 2 := by
  rw [sub_nonneg.symm, _root_.GD.N0232.N0720.N1118.d016459 z₀ z₁ a₀ a₁ hz₀ hz₁]
  positivity

private theorem d016463
    {alpha : Type*} [Fintype alpha]
    (weight value : alpha → ℝ) :
    (∑ x, weight x / 2 * value x) =
      (∑ x, weight x * value x) / 2 := by
  calc
    (∑ x, weight x / 2 * value x) =
        ∑ x, (weight x * value x) / 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = (∑ x, weight x * value x) / 2 := by
      rw [Finset.sum_div]

private theorem d016464
    {gamma : Type*} [Fintype gamma]
    (scale : ℝ) (weight value : gamma → ℝ) :
    (∑ x, (scale * weight x) * value x) =
      scale * ∑ x, weight x * value x := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring




def d016465
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168) :
    iota ⊕ kappa → _root_.GD.N0232.N0720.N1080.d014168
  | Sum.inl i => packet₀ i
  | Sum.inr j => packet₁ j


def d016466
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ) :
    iota ⊕ kappa → ℝ
  | Sum.inl i => weight₀ i / 2
  | Sum.inr j => weight₁ j / 2


def d016467
    (alpha : ℝ) (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ) :
    iota ⊕ kappa → ℝ
  | Sum.inl i => alpha * weight₀ i
  | Sum.inr j => (1 - alpha) * weight₁ j

theorem d016468
    (alpha : ℝ) (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (halpha₀ : 0 ≤ alpha) (halpha₁ : alpha ≤ 1)
    (hweight₀ : ∀ i, 0 ≤ weight₀ i) (hweight₁ : ∀ j, 0 ≤ weight₁ j) :
    ∀ x, 0 ≤ _root_.GD.N0232.N0720.N1118.d016467 alpha weight₀ weight₁ x := by
  have hnonneg : 0 ≤ 1 - alpha := sub_nonneg.mpr halpha₁
  rintro (i | j)
  · exact mul_nonneg halpha₀ (hweight₀ i)
  · exact mul_nonneg hnonneg (hweight₁ j)

theorem d016469
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (hweight₀ : ∀ i, 0 ≤ weight₀ i) (hweight₁ : ∀ j, 0 ≤ weight₁ j) :
    ∀ x, 0 ≤ _root_.GD.N0232.N0720.N1118.d016466 weight₀ weight₁ x := by
  rintro (i | j)
  · exact div_nonneg (hweight₀ i) (by norm_num)
  · exact div_nonneg (hweight₁ j) (by norm_num)



theorem d016470
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1126.d016415 (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
        (_root_.GD.N0232.N0720.N1118.d016466 weight₀ weight₁) omega =
      (_root_.GD.N0232.N0720.N1126.d016415 packet₀ weight₀ omega +
        _root_.GD.N0232.N0720.N1126.d016415 packet₁ weight₁ omega) / 2 := by
  classical
  simp only [_root_.GD.N0232.N0720.N1126.d016415, _root_.GD.N0230.N0617.d000163, _root_.GD.N0232.N0720.N1126.d016413,
    _root_.GD.N0232.N0720.N1118.d016465, _root_.GD.N0232.N0720.N1118.d016466, Fintype.sum_sum_type]
  rw [_root_.GD.N0232.N0720.N1118.d016463, _root_.GD.N0232.N0720.N1118.d016463]
  ring



theorem d016471
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0230.N0617.d000164 (_root_.GD.N0232.N0720.N1118.d016466 weight₀ weight₁)
        (_root_.GD.N0232.N0720.N1126.d016413 (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁))
        (_root_.GD.N0232.N0720.N1126.d016414 (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)) omega =
      (_root_.GD.N0230.N0617.d000164 weight₀ (_root_.GD.N0232.N0720.N1126.d016413 packet₀)
          (_root_.GD.N0232.N0720.N1126.d016414 packet₀) omega +
        _root_.GD.N0230.N0617.d000164 weight₁ (_root_.GD.N0232.N0720.N1126.d016413 packet₁)
          (_root_.GD.N0232.N0720.N1126.d016414 packet₁) omega) / 2 := by
  classical
  simp only [_root_.GD.N0230.N0617.d000164, _root_.GD.N0232.N0720.N1126.d016413, _root_.GD.N0232.N0720.N1126.d016414,
    _root_.GD.N0232.N0720.N1118.d016465, _root_.GD.N0232.N0720.N1118.d016466, Fintype.sum_sum_type]
  simp_rw [mul_assoc]
  rw [_root_.GD.N0232.N0720.N1118.d016463, _root_.GD.N0232.N0720.N1118.d016463]
  ring



theorem d016472
    (alpha : ℝ)
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1126.d016415 (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
        (_root_.GD.N0232.N0720.N1118.d016467 alpha weight₀ weight₁) omega =
      alpha * _root_.GD.N0232.N0720.N1126.d016415 packet₀ weight₀ omega +
        (1 - alpha) * _root_.GD.N0232.N0720.N1126.d016415 packet₁ weight₁ omega := by
  classical
  simp only [_root_.GD.N0232.N0720.N1126.d016415, _root_.GD.N0230.N0617.d000163, _root_.GD.N0232.N0720.N1126.d016413,
    _root_.GD.N0232.N0720.N1118.d016465, _root_.GD.N0232.N0720.N1118.d016467, Fintype.sum_sum_type]
  rw [_root_.GD.N0232.N0720.N1118.d016464, _root_.GD.N0232.N0720.N1118.d016464]
  ring



theorem d016473
    (alpha : ℝ)
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0230.N0617.d000164 (_root_.GD.N0232.N0720.N1118.d016467 alpha weight₀ weight₁)
        (_root_.GD.N0232.N0720.N1126.d016413 (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁))
        (_root_.GD.N0232.N0720.N1126.d016414 (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)) omega =
      alpha * _root_.GD.N0230.N0617.d000164 weight₀ (_root_.GD.N0232.N0720.N1126.d016413 packet₀)
          (_root_.GD.N0232.N0720.N1126.d016414 packet₀) omega +
        (1 - alpha) * _root_.GD.N0230.N0617.d000164 weight₁ (_root_.GD.N0232.N0720.N1126.d016413 packet₁)
          (_root_.GD.N0232.N0720.N1126.d016414 packet₁) omega := by
  classical
  simp only [_root_.GD.N0230.N0617.d000164, _root_.GD.N0232.N0720.N1126.d016413, _root_.GD.N0232.N0720.N1126.d016414,
    _root_.GD.N0232.N0720.N1118.d016465, _root_.GD.N0232.N0720.N1118.d016467, Fintype.sum_sum_type]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum]



def d016474
    (alpha : ℝ)
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  (alpha * (1 - alpha) *
      _root_.GD.N0232.N0720.N1126.d016415 packet₀ weight₀ omega *
      _root_.GD.N0232.N0720.N1126.d016415 packet₁ weight₁ omega /
    (alpha * _root_.GD.N0232.N0720.N1126.d016415 packet₀ weight₀ omega +
      (1 - alpha) * _root_.GD.N0232.N0720.N1126.d016415 packet₁ weight₁ omega)) *
    (_root_.GD.N0232.N0720.N1126.d016416 packet₀ weight₀ omega -
      _root_.GD.N0232.N0720.N1126.d016416 packet₁ weight₁ omega) ^ 2


def d016475
    (alpha : ℝ)
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ) : ℝ :=
  ∫ omega, _root_.GD.N0232.N0720.N1118.d016474 alpha
    (m := m) (n := n) packet₀ packet₁ weight₀ weight₁ omega
      ∂_root_.GD.N0232.N0720.N1080.d014172 m n



def d016476
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) : ℝ :=
  (1 / 2 : ℝ) *
    (_root_.GD.N0232.N0720.N1126.d016415 packet₀ weight₀ omega *
        _root_.GD.N0232.N0720.N1126.d016415 packet₁ weight₁ omega /
      (_root_.GD.N0232.N0720.N1126.d016415 packet₀ weight₀ omega +
        _root_.GD.N0232.N0720.N1126.d016415 packet₁ weight₁ omega)) *
    (_root_.GD.N0232.N0720.N1126.d016416 packet₀ weight₀ omega -
      _root_.GD.N0232.N0720.N1126.d016416 packet₁ weight₁ omega) ^ 2


def d016477
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ) : ℝ :=
  ∫ omega, _root_.GD.N0232.N0720.N1118.d016476
    (m := m) (n := n) packet₀ packet₁ weight₀ weight₁ omega
      ∂_root_.GD.N0232.N0720.N1080.d014172 m n


theorem d016478
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (hweight₀ : ∀ i, 0 ≤ weight₀ i) (hweight₁ : ∀ j, 0 ≤ weight₁ j)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    (_root_.GD.N0232.N0720.N1126.d016417 packet₀ weight₀ omega +
        _root_.GD.N0232.N0720.N1126.d016417 packet₁ weight₁ omega) / 2 -
      _root_.GD.N0232.N0720.N1126.d016417 (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
        (_root_.GD.N0232.N0720.N1118.d016466 weight₀ weight₁) omega =
      _root_.GD.N0232.N0720.N1118.d016476
        packet₀ packet₁ weight₀ weight₁ omega := by
  let z₀ := _root_.GD.N0232.N0720.N1126.d016415 packet₀ weight₀ omega
  let z₁ := _root_.GD.N0232.N0720.N1126.d016415 packet₁ weight₁ omega
  let a₀ := _root_.GD.N0230.N0617.d000164 weight₀ (_root_.GD.N0232.N0720.N1126.d016413 packet₀)
    (_root_.GD.N0232.N0720.N1126.d016414 packet₀) omega
  let a₁ := _root_.GD.N0230.N0617.d000164 weight₁ (_root_.GD.N0232.N0720.N1126.d016413 packet₁)
    (_root_.GD.N0232.N0720.N1126.d016414 packet₁) omega
  have hz₀ : 0 < z₀ := _root_.GD.N0230.N0617.d000169 weight₀
    (_root_.GD.N0232.N0720.N1126.d016413 packet₀) hweight₀ (_root_.GD.N0232.N0720.N1126.d016419 packet₀) omega
  have hz₁ : 0 < z₁ := _root_.GD.N0230.N0617.d000169 weight₁
    (_root_.GD.N0232.N0720.N1126.d016413 packet₁) hweight₁ (_root_.GD.N0232.N0720.N1126.d016419 packet₁) omega
  have hscalar := _root_.GD.N0232.N0720.N1118.d016459 z₀ z₁ a₀ a₁ hz₀ hz₁
  change
    (a₀ ^ 2 / z₀ + a₁ ^ 2 / z₁) / 2 -
        _root_.GD.N0230.N0617.d000164 (_root_.GD.N0232.N0720.N1118.d016466 weight₀ weight₁)
            (_root_.GD.N0232.N0720.N1126.d016413 (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁))
            (_root_.GD.N0232.N0720.N1126.d016414 (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)) omega ^ 2 /
          _root_.GD.N0232.N0720.N1126.d016415 (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
            (_root_.GD.N0232.N0720.N1118.d016466 weight₀ weight₁) omega =
      (1 / 2 : ℝ) * (z₀ * z₁ / (z₀ + z₁)) *
        (a₀ / z₀ - a₁ / z₁) ^ 2
  rw [_root_.GD.N0232.N0720.N1118.d016470,
    _root_.GD.N0232.N0720.N1118.d016471]
  exact hscalar


theorem d016479
    (alpha : ℝ)
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (halpha₀ : 0 ≤ alpha) (halpha₁ : alpha ≤ 1)
    (hweight₀ : ∀ i, 0 ≤ weight₀ i) (hweight₁ : ∀ j, 0 ≤ weight₁ j)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    alpha * _root_.GD.N0232.N0720.N1126.d016417 packet₀ weight₀ omega +
        (1 - alpha) * _root_.GD.N0232.N0720.N1126.d016417 packet₁ weight₁ omega -
      _root_.GD.N0232.N0720.N1126.d016417 (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
        (_root_.GD.N0232.N0720.N1118.d016467 alpha weight₀ weight₁) omega =
      _root_.GD.N0232.N0720.N1118.d016474 alpha
        packet₀ packet₁ weight₀ weight₁ omega := by
  let z₀ := _root_.GD.N0232.N0720.N1126.d016415 packet₀ weight₀ omega
  let z₁ := _root_.GD.N0232.N0720.N1126.d016415 packet₁ weight₁ omega
  let a₀ := _root_.GD.N0230.N0617.d000164 weight₀ (_root_.GD.N0232.N0720.N1126.d016413 packet₀)
    (_root_.GD.N0232.N0720.N1126.d016414 packet₀) omega
  let a₁ := _root_.GD.N0230.N0617.d000164 weight₁ (_root_.GD.N0232.N0720.N1126.d016413 packet₁)
    (_root_.GD.N0232.N0720.N1126.d016414 packet₁) omega
  have hz₀ : 0 < z₀ := _root_.GD.N0230.N0617.d000169 weight₀
    (_root_.GD.N0232.N0720.N1126.d016413 packet₀) hweight₀ (_root_.GD.N0232.N0720.N1126.d016419 packet₀) omega
  have hz₁ : 0 < z₁ := _root_.GD.N0230.N0617.d000169 weight₁
    (_root_.GD.N0232.N0720.N1126.d016413 packet₁) hweight₁ (_root_.GD.N0232.N0720.N1126.d016419 packet₁) omega
  have hscalar := _root_.GD.N0232.N0720.N1118.d016460
    alpha z₀ z₁ a₀ a₁ halpha₀ halpha₁ hz₀ hz₁
  change
    alpha * (a₀ ^ 2 / z₀) + (1 - alpha) * (a₁ ^ 2 / z₁) -
        _root_.GD.N0230.N0617.d000164 (_root_.GD.N0232.N0720.N1118.d016467 alpha weight₀ weight₁)
            (_root_.GD.N0232.N0720.N1126.d016413 (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁))
            (_root_.GD.N0232.N0720.N1126.d016414 (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)) omega ^ 2 /
          _root_.GD.N0232.N0720.N1126.d016415 (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
            (_root_.GD.N0232.N0720.N1118.d016467 alpha weight₀ weight₁) omega =
      (alpha * (1 - alpha) * z₀ * z₁ /
          (alpha * z₀ + (1 - alpha) * z₁)) *
        (a₀ / z₀ - a₁ / z₁) ^ 2
  rw [_root_.GD.N0232.N0720.N1118.d016472,
    _root_.GD.N0232.N0720.N1118.d016473]
  exact hscalar

theorem d016480
    (alpha : ℝ)
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (halpha₀ : 0 ≤ alpha) (halpha₁ : alpha ≤ 1)
    (hweight₀ : ∀ i, 0 ≤ weight₀ i) (hweight₁ : ∀ j, 0 ≤ weight₁ j)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    0 ≤ _root_.GD.N0232.N0720.N1118.d016474 alpha
      packet₀ packet₁ weight₀ weight₁ omega := by
  have hz₀ : 0 < _root_.GD.N0232.N0720.N1126.d016415 packet₀ weight₀ omega :=
    _root_.GD.N0230.N0617.d000169 weight₀ (_root_.GD.N0232.N0720.N1126.d016413 packet₀) hweight₀
      (_root_.GD.N0232.N0720.N1126.d016419 packet₀) omega
  have hz₁ : 0 < _root_.GD.N0232.N0720.N1126.d016415 packet₁ weight₁ omega :=
    _root_.GD.N0230.N0617.d000169 weight₁ (_root_.GD.N0232.N0720.N1126.d016413 packet₁) hweight₁
      (_root_.GD.N0232.N0720.N1126.d016419 packet₁) omega
  have hnonneg : 0 ≤ 1 - alpha := sub_nonneg.mpr halpha₁
  have hzbar : 0 <
      alpha * _root_.GD.N0232.N0720.N1126.d016415 packet₀ weight₀ omega +
        (1 - alpha) * _root_.GD.N0232.N0720.N1126.d016415 packet₁ weight₁ omega := by
    by_cases halpha : alpha = 0
    · subst alpha
      simpa using hz₁
    · have halphaPos : 0 < alpha :=
        lt_of_le_of_ne halpha₀ (Ne.symm halpha)
      exact add_pos_of_pos_of_nonneg (mul_pos halphaPos hz₀)
        (mul_nonneg hnonneg hz₁.le)
  unfold _root_.GD.N0232.N0720.N1118.d016474
  positivity

theorem d016481
    (alpha : ℝ)
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (halpha₀ : 0 ≤ alpha) (halpha₁ : alpha ≤ 1)
    (hweight₀ : ∀ i, 0 ≤ weight₀ i) (hweight₁ : ∀ j, 0 ≤ weight₁ j) :
    0 ≤ _root_.GD.N0232.N0720.N1118.d016475 alpha
      (m := m) (n := n) packet₀ packet₁ weight₀ weight₁ := by
  unfold _root_.GD.N0232.N0720.N1118.d016475
  exact integral_nonneg fun omega ↦
    _root_.GD.N0232.N0720.N1118.d016480 alpha
      packet₀ packet₁ weight₀ weight₁ halpha₀ halpha₁
      hweight₀ hweight₁ omega

theorem d016482
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (hweight₀ : ∀ i, 0 ≤ weight₀ i) (hweight₁ : ∀ j, 0 ≤ weight₁ j)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    0 ≤ _root_.GD.N0232.N0720.N1118.d016476
      packet₀ packet₁ weight₀ weight₁ omega := by
  have hz₀ : 0 < _root_.GD.N0232.N0720.N1126.d016415 packet₀ weight₀ omega :=
    _root_.GD.N0230.N0617.d000169 weight₀ (_root_.GD.N0232.N0720.N1126.d016413 packet₀) hweight₀
      (_root_.GD.N0232.N0720.N1126.d016419 packet₀) omega
  have hz₁ : 0 < _root_.GD.N0232.N0720.N1126.d016415 packet₁ weight₁ omega :=
    _root_.GD.N0230.N0617.d000169 weight₁ (_root_.GD.N0232.N0720.N1126.d016413 packet₁) hweight₁
      (_root_.GD.N0232.N0720.N1126.d016419 packet₁) omega
  unfold _root_.GD.N0232.N0720.N1118.d016476
  positivity

theorem d016483
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (hweight₀ : ∀ i, 0 ≤ weight₀ i) (hweight₁ : ∀ j, 0 ≤ weight₁ j) :
    0 ≤ _root_.GD.N0232.N0720.N1118.d016477
      (m := m) (n := n) packet₀ packet₁ weight₀ weight₁ := by
  unfold _root_.GD.N0232.N0720.N1118.d016477
  exact integral_nonneg fun omega ↦
    _root_.GD.N0232.N0720.N1118.d016482
      packet₀ packet₁ weight₀ weight₁ hweight₀ hweight₁ omega


theorem d016484
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (hweight₀ : ∀ i, 0 ≤ weight₀ i) (hweight₁ : ∀ j, 0 ≤ weight₁ j)
    (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    (1 / 4 : ℝ) *
        (_root_.GD.N0232.N0720.N1126.d016416 packet₀ weight₀ omega -
          _root_.GD.N0232.N0720.N1126.d016416 packet₁ weight₁ omega) ^ 2 ≤
      _root_.GD.N0232.N0720.N1118.d016476
        packet₀ packet₁ weight₀ weight₁ omega := by
  have hz₀ : 1 ≤ _root_.GD.N0232.N0720.N1126.d016415 packet₀ weight₀ omega :=
    _root_.GD.N0230.N0617.d000168 weight₀ (_root_.GD.N0232.N0720.N1126.d016413 packet₀) hweight₀
      (_root_.GD.N0232.N0720.N1126.d016419 packet₀) omega
  have hz₁ : 1 ≤ _root_.GD.N0232.N0720.N1126.d016415 packet₁ weight₁ omega :=
    _root_.GD.N0230.N0617.d000168 weight₁ (_root_.GD.N0232.N0720.N1126.d016413 packet₁) hweight₁
      (_root_.GD.N0232.N0720.N1126.d016419 packet₁) omega
  exact _root_.GD.N0232.N0720.N1118.d016461
    (_root_.GD.N0232.N0720.N1126.d016415 packet₀ weight₀ omega)
    (_root_.GD.N0232.N0720.N1126.d016415 packet₁ weight₁ omega)
    (_root_.GD.N0232.N0720.N1126.d016416 packet₀ weight₀ omega)
    (_root_.GD.N0232.N0720.N1126.d016416 packet₁ weight₁ omega) hz₀ hz₁



private theorem d016485
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ) :
    (∑ x, _root_.GD.N0232.N0720.N1118.d016466 weight₀ weight₁ x *
      (_root_.GD.N0232.N0720.N1126.d016414 (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁) x ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016431 s (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁) x)) =
      ((∑ i, weight₀ i *
          (_root_.GD.N0232.N0720.N1126.d016414 packet₀ i ^ 2 - _root_.GD.N0232.N0720.N1126.d016431 s packet₀ i)) +
        ∑ j, weight₁ j *
          (_root_.GD.N0232.N0720.N1126.d016414 packet₁ j ^ 2 - _root_.GD.N0232.N0720.N1126.d016431 s packet₁ j)) / 2 := by
  classical
  simp only [_root_.GD.N0232.N0720.N1118.d016465, _root_.GD.N0232.N0720.N1118.d016466,
    _root_.GD.N0232.N0720.N1126.d016414, _root_.GD.N0232.N0720.N1126.d016431, Fintype.sum_sum_type]
  rw [_root_.GD.N0232.N0720.N1118.d016463, _root_.GD.N0232.N0720.N1118.d016463]
  ring

private theorem d016486
    (alpha : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ) :
    (∑ x, _root_.GD.N0232.N0720.N1118.d016467 alpha weight₀ weight₁ x *
      (_root_.GD.N0232.N0720.N1126.d016414 (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁) x ^ 2 -
        _root_.GD.N0232.N0720.N1126.d016431 s (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁) x)) =
      alpha * (∑ i, weight₀ i *
          (_root_.GD.N0232.N0720.N1126.d016414 packet₀ i ^ 2 - _root_.GD.N0232.N0720.N1126.d016431 s packet₀ i)) +
        (1 - alpha) * ∑ j, weight₁ j *
          (_root_.GD.N0232.N0720.N1126.d016414 packet₁ j ^ 2 - _root_.GD.N0232.N0720.N1126.d016431 s packet₁ j) := by
  classical
  simp only [_root_.GD.N0232.N0720.N1118.d016465, _root_.GD.N0232.N0720.N1118.d016467,
    _root_.GD.N0232.N0720.N1126.d016414, _root_.GD.N0232.N0720.N1126.d016431, Fintype.sum_sum_type]
  rw [_root_.GD.N0232.N0720.N1118.d016464, _root_.GD.N0232.N0720.N1118.d016464]

private theorem d016487
    (packet : iota → _root_.GD.N0232.N0720.N1080.d014168) (weight : iota → ℝ)
    (hweight : ∀ i, 0 ≤ weight i) :
    Integrable (_root_.GD.N0232.N0720.N1126.d016417 (m := m) (n := n) packet weight)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  exact _root_.GD.N0230.N0617.d000183
    (_root_.GD.N0232.N0720.N1080.d014172 m n) weight (_root_.GD.N0232.N0720.N1126.d016413 packet) (_root_.GD.N0232.N0720.N1126.d016414 packet)
      hweight (_root_.GD.N0232.N0720.N1126.d016419 packet) (_root_.GD.N0232.N0720.N1126.d016420 packet)
      (_root_.GD.N0232.N0720.N1126.d016421 packet)

private theorem d016488
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (hweight₀ : ∀ i, 0 ≤ weight₀ i) (hweight₁ : ∀ j, 0 ≤ weight₁ j) :
    Integrable (_root_.GD.N0232.N0720.N1118.d016476
      (m := m) (n := n) packet₀ packet₁ weight₀ weight₁)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have hcorr₀ := _root_.GD.N0232.N0720.N1118.d016487
    (m := m) (n := n) packet₀ weight₀ hweight₀
  have hcorr₁ := _root_.GD.N0232.N0720.N1118.d016487
    (m := m) (n := n) packet₁ weight₁ hweight₁
  have hmidWeight := _root_.GD.N0232.N0720.N1118.d016469
    weight₀ weight₁ hweight₀ hweight₁
  have hcorrMid := _root_.GD.N0232.N0720.N1118.d016487
    (m := m) (n := n) (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
      (_root_.GD.N0232.N0720.N1118.d016466 weight₀ weight₁) hmidWeight
  have hrepr :
      _root_.GD.N0232.N0720.N1118.d016476
          (m := m) (n := n) packet₀ packet₁ weight₀ weight₁ =
        fun omega ↦
          (_root_.GD.N0232.N0720.N1126.d016417 packet₀ weight₀ omega +
            _root_.GD.N0232.N0720.N1126.d016417 packet₁ weight₁ omega) / 2 -
          _root_.GD.N0232.N0720.N1126.d016417 (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
            (_root_.GD.N0232.N0720.N1118.d016466 weight₀ weight₁) omega := by
    funext omega
    rw [_root_.GD.N0232.N0720.N1118.d016478
      packet₀ packet₁ weight₀ weight₁ hweight₀ hweight₁ omega]
  rw [hrepr]
  exact (hcorr₀.add hcorr₁).div_const 2 |>.sub hcorrMid

private theorem d016489
    (alpha : ℝ)
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (halpha₀ : 0 ≤ alpha) (halpha₁ : alpha ≤ 1)
    (hweight₀ : ∀ i, 0 ≤ weight₀ i) (hweight₁ : ∀ j, 0 ≤ weight₁ j) :
    Integrable (_root_.GD.N0232.N0720.N1118.d016474 alpha
      (m := m) (n := n) packet₀ packet₁ weight₀ weight₁)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  have hcorr₀ := _root_.GD.N0232.N0720.N1118.d016487
    (m := m) (n := n) packet₀ weight₀ hweight₀
  have hcorr₁ := _root_.GD.N0232.N0720.N1118.d016487
    (m := m) (n := n) packet₁ weight₁ hweight₁
  have hconvexWeight := _root_.GD.N0232.N0720.N1118.d016468 alpha
    weight₀ weight₁ halpha₀ halpha₁ hweight₀ hweight₁
  have hcorrMix := _root_.GD.N0232.N0720.N1118.d016487
    (m := m) (n := n) (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
      (_root_.GD.N0232.N0720.N1118.d016467 alpha weight₀ weight₁) hconvexWeight
  have hrepr :
      _root_.GD.N0232.N0720.N1118.d016474 alpha
          (m := m) (n := n) packet₀ packet₁ weight₀ weight₁ =
        fun omega ↦
          alpha * _root_.GD.N0232.N0720.N1126.d016417 packet₀ weight₀ omega +
            (1 - alpha) * _root_.GD.N0232.N0720.N1126.d016417 packet₁ weight₁ omega -
          _root_.GD.N0232.N0720.N1126.d016417 (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
            (_root_.GD.N0232.N0720.N1118.d016467 alpha weight₀ weight₁) omega := by
    funext omega
    symm
    exact _root_.GD.N0232.N0720.N1118.d016479 alpha
      packet₀ packet₁ weight₀ weight₁ halpha₀ halpha₁
      hweight₀ hweight₁ omega
  rw [hrepr]
  exact ((hcorr₀.const_mul alpha).add
    (hcorr₁.const_mul (1 - alpha))).sub hcorrMix



theorem d016490
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (hweight₀ : ∀ i, 0 ≤ weight₀ i) (hweight₁ : ∀ j, 0 ≤ weight₁ j) :
    (1 / 4 : ℝ) *
        (∫ omega,
          (_root_.GD.N0232.N0720.N1126.d016416 packet₀ weight₀ omega -
            _root_.GD.N0232.N0720.N1126.d016416 packet₁ weight₁ omega) ^ 2
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n) ≤
      _root_.GD.N0232.N0720.N1118.d016477
        (m := m) (n := n) packet₀ packet₁ weight₀ weight₁ := by
  have hdiff : MemLp
      (fun omega ↦ _root_.GD.N0232.N0720.N1126.d016416 packet₀ weight₀ omega -
        _root_.GD.N0232.N0720.N1126.d016416 packet₁ weight₁ omega) 2
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    (_root_.GD.N0232.N0720.N1126.d016425 packet₀ weight₀ hweight₀).sub
      (_root_.GD.N0232.N0720.N1126.d016425 packet₁ weight₁ hweight₁)
  have hleft : Integrable
      (fun omega ↦ (1 / 4 : ℝ) *
        (_root_.GD.N0232.N0720.N1126.d016416 packet₀ weight₀ omega -
          _root_.GD.N0232.N0720.N1126.d016416 packet₁ weight₁ omega) ^ 2)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := hdiff.integrable_sq.const_mul (1 / 4 : ℝ)
  have hright := _root_.GD.N0232.N0720.N1118.d016488
    (m := m) (n := n) packet₀ packet₁ weight₀ weight₁ hweight₀ hweight₁
  unfold _root_.GD.N0232.N0720.N1118.d016477
  rw [← integral_const_mul]
  exact integral_mono hleft hright fun omega ↦
    _root_.GD.N0232.N0720.N1118.d016484
      packet₀ packet₁ weight₀ weight₁ hweight₀ hweight₁ omega




theorem d016491
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (hweight₀ : ∀ i, 0 ≤ weight₀ i) (hweight₁ : ∀ j, 0 ≤ weight₁ j) :
    _root_.GD.N0232.N0720.N1126.d016432 s (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
        (_root_.GD.N0232.N0720.N1118.d016466 weight₀ weight₁) =
      (_root_.GD.N0232.N0720.N1126.d016432 s packet₀ weight₀ +
        _root_.GD.N0232.N0720.N1126.d016432 s packet₁ weight₁) / 2 +
      _root_.GD.N0232.N0720.N1118.d016477 (m := m) (n := n)
        packet₀ packet₁ weight₀ weight₁ := by
  have hcorr₀ := _root_.GD.N0232.N0720.N1118.d016487
    (m := m) (n := n) packet₀ weight₀ hweight₀
  have hcorr₁ := _root_.GD.N0232.N0720.N1118.d016487
    (m := m) (n := n) packet₁ weight₁ hweight₁
  have hmidWeight := _root_.GD.N0232.N0720.N1118.d016469
    weight₀ weight₁ hweight₀ hweight₁
  have hcorrMid := _root_.GD.N0232.N0720.N1118.d016487
    (m := m) (n := n) (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
      (_root_.GD.N0232.N0720.N1118.d016466 weight₀ weight₁) hmidWeight
  have htax := _root_.GD.N0232.N0720.N1118.d016488
    (m := m) (n := n) packet₀ packet₁ weight₀ weight₁ hweight₀ hweight₁
  have hcorrIntegral :
      (∫ omega, _root_.GD.N0232.N0720.N1126.d016417
          (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
          (_root_.GD.N0232.N0720.N1118.d016466 weight₀ weight₁) omega
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
        ((∫ omega, _root_.GD.N0232.N0720.N1126.d016417 packet₀ weight₀ omega
            ∂_root_.GD.N0232.N0720.N1080.d014172 m n) +
          ∫ omega, _root_.GD.N0232.N0720.N1126.d016417 packet₁ weight₁ omega
            ∂_root_.GD.N0232.N0720.N1080.d014172 m n) / 2 -
        ∫ omega, _root_.GD.N0232.N0720.N1118.d016476
          packet₀ packet₁ weight₀ weight₁ omega
            ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    calc
      (∫ omega, _root_.GD.N0232.N0720.N1126.d016417
          (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
          (_root_.GD.N0232.N0720.N1118.d016466 weight₀ weight₁) omega
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
          ∫ omega,
            (_root_.GD.N0232.N0720.N1126.d016417 packet₀ weight₀ omega +
              _root_.GD.N0232.N0720.N1126.d016417 packet₁ weight₁ omega) / 2 -
            _root_.GD.N0232.N0720.N1118.d016476
              packet₀ packet₁ weight₀ weight₁ omega
              ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
        apply integral_congr_ae
        filter_upwards with omega
        have hgap := _root_.GD.N0232.N0720.N1118.d016478
          packet₀ packet₁ weight₀ weight₁ hweight₀ hweight₁ omega
        linarith
      _ = _ := by
        calc
          (∫ omega,
              (_root_.GD.N0232.N0720.N1126.d016417 packet₀ weight₀ omega +
                _root_.GD.N0232.N0720.N1126.d016417 packet₁ weight₁ omega) / 2 -
              _root_.GD.N0232.N0720.N1118.d016476
                packet₀ packet₁ weight₀ weight₁ omega
              ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
              (∫ omega,
                (_root_.GD.N0232.N0720.N1126.d016417 packet₀ weight₀ omega +
                  _root_.GD.N0232.N0720.N1126.d016417 packet₁ weight₁ omega) / 2
                ∂_root_.GD.N0232.N0720.N1080.d014172 m n) -
              ∫ omega, _root_.GD.N0232.N0720.N1118.d016476
                packet₀ packet₁ weight₀ weight₁ omega
                ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
            exact integral_sub ((hcorr₀.add hcorr₁).div_const 2) htax
          _ = _ := by
            rw [integral_div, integral_add hcorr₀ hcorr₁]
  unfold _root_.GD.N0232.N0720.N1126.d016417 at hcorrIntegral
  unfold _root_.GD.N0232.N0720.N1126.d016432 _root_.GD.N0230.N0617.d000186
  rw [_root_.GD.N0232.N0720.N1118.d016485, hcorrIntegral]
  unfold _root_.GD.N0232.N0720.N1118.d016477
  ring




theorem d016492
    (alpha : ℝ) (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (halpha₀ : 0 ≤ alpha) (halpha₁ : alpha ≤ 1)
    (hweight₀ : ∀ i, 0 ≤ weight₀ i) (hweight₁ : ∀ j, 0 ≤ weight₁ j) :
    _root_.GD.N0232.N0720.N1126.d016432 s (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
        (_root_.GD.N0232.N0720.N1118.d016467 alpha weight₀ weight₁) =
      alpha * _root_.GD.N0232.N0720.N1126.d016432 s packet₀ weight₀ +
        (1 - alpha) * _root_.GD.N0232.N0720.N1126.d016432 s packet₁ weight₁ +
      _root_.GD.N0232.N0720.N1118.d016475 alpha
        (m := m) (n := n) packet₀ packet₁ weight₀ weight₁ := by
  have hcorr₀ := _root_.GD.N0232.N0720.N1118.d016487
    (m := m) (n := n) packet₀ weight₀ hweight₀
  have hcorr₁ := _root_.GD.N0232.N0720.N1118.d016487
    (m := m) (n := n) packet₁ weight₁ hweight₁
  have hconvexWeight := _root_.GD.N0232.N0720.N1118.d016468 alpha
    weight₀ weight₁ halpha₀ halpha₁ hweight₀ hweight₁
  have hcorrMix := _root_.GD.N0232.N0720.N1118.d016487
    (m := m) (n := n) (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
      (_root_.GD.N0232.N0720.N1118.d016467 alpha weight₀ weight₁) hconvexWeight
  have htax := _root_.GD.N0232.N0720.N1118.d016489 alpha
    (m := m) (n := n) packet₀ packet₁ weight₀ weight₁
      halpha₀ halpha₁ hweight₀ hweight₁
  have hcorrIntegral :
      (∫ omega, _root_.GD.N0232.N0720.N1126.d016417
          (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
          (_root_.GD.N0232.N0720.N1118.d016467 alpha weight₀ weight₁) omega
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
        alpha * (∫ omega, _root_.GD.N0232.N0720.N1126.d016417 packet₀ weight₀ omega
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n) +
        (1 - alpha) * (∫ omega,
          _root_.GD.N0232.N0720.N1126.d016417 packet₁ weight₁ omega
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n) -
        ∫ omega, _root_.GD.N0232.N0720.N1118.d016474 alpha
          packet₀ packet₁ weight₀ weight₁ omega
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    calc
      (∫ omega, _root_.GD.N0232.N0720.N1126.d016417
          (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
          (_root_.GD.N0232.N0720.N1118.d016467 alpha weight₀ weight₁) omega
          ∂_root_.GD.N0232.N0720.N1080.d014172 m n) =
          ∫ omega,
            (alpha * _root_.GD.N0232.N0720.N1126.d016417 packet₀ weight₀ omega +
              (1 - alpha) *
                _root_.GD.N0232.N0720.N1126.d016417 packet₁ weight₁ omega) -
            _root_.GD.N0232.N0720.N1118.d016474 alpha
              packet₀ packet₁ weight₀ weight₁ omega
            ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
        apply integral_congr_ae
        filter_upwards with omega
        have hgap := _root_.GD.N0232.N0720.N1118.d016479 alpha
          packet₀ packet₁ weight₀ weight₁ halpha₀ halpha₁
          hweight₀ hweight₁ omega
        linarith
      _ = (∫ omega,
              alpha * _root_.GD.N0232.N0720.N1126.d016417 packet₀ weight₀ omega +
                (1 - alpha) *
                  _root_.GD.N0232.N0720.N1126.d016417 packet₁ weight₁ omega
              ∂_root_.GD.N0232.N0720.N1080.d014172 m n) -
            ∫ omega, _root_.GD.N0232.N0720.N1118.d016474 alpha
              packet₀ packet₁ weight₀ weight₁ omega
              ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
        exact integral_sub
          ((hcorr₀.const_mul alpha).add
            (hcorr₁.const_mul (1 - alpha))) htax
      _ = _ := by
        rw [integral_add (hcorr₀.const_mul alpha)
          (hcorr₁.const_mul (1 - alpha)),
          integral_const_mul, integral_const_mul]
  unfold _root_.GD.N0232.N0720.N1126.d016417 at hcorrIntegral
  unfold _root_.GD.N0232.N0720.N1126.d016432 _root_.GD.N0230.N0617.d000186
  rw [_root_.GD.N0232.N0720.N1118.d016486, hcorrIntegral]
  unfold _root_.GD.N0232.N0720.N1118.d016475
  ring


theorem d016493
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (hweight₀ : ∀ i, 0 ≤ weight₀ i) (hweight₁ : ∀ j, 0 ≤ weight₁ j) :
    (_root_.GD.N0232.N0720.N1126.d016432 s packet₀ weight₀ +
        _root_.GD.N0232.N0720.N1126.d016432 s packet₁ weight₁) / 2 ≤
      _root_.GD.N0232.N0720.N1126.d016432 s (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
        (_root_.GD.N0232.N0720.N1118.d016466 weight₀ weight₁) := by
  rw [_root_.GD.N0232.N0720.N1118.d016491
    s packet₀ packet₁ weight₀ weight₁ hweight₀ hweight₁]
  exact le_add_of_nonneg_right
    (_root_.GD.N0232.N0720.N1118.d016483
      packet₀ packet₁ weight₀ weight₁ hweight₀ hweight₁)



theorem d016494
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet₀ : iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : iota → ℝ) (weight₁ : kappa → ℝ)
    (hweight₀ : ∀ i, 0 ≤ weight₀ i) (hweight₁ : ∀ j, 0 ≤ weight₁ j) :
    (_root_.GD.N0232.N0720.N1126.d016432 s packet₀ weight₀ +
        _root_.GD.N0232.N0720.N1126.d016432 s packet₁ weight₁) / 2 +
        _root_.GD.N0232.N0720.N1118.d016477 (m := m) (n := n)
          packet₀ packet₁ weight₀ weight₁ ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 := by
  have hmidWeight := _root_.GD.N0232.N0720.N1118.d016469
    weight₀ weight₁ hweight₀ hweight₁
  have hbound := _root_.GD.N0232.N0720.N1126.d016437
    s (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
      (_root_.GD.N0232.N0720.N1118.d016466 weight₀ weight₁) hmidWeight
  rw [_root_.GD.N0232.N0720.N1118.d016491
    s packet₀ packet₁ weight₀ weight₁ hweight₀ hweight₁] at hbound
  exact le_trans (le_add_of_nonneg_right (sq_nonneg
    ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value -
      _root_.GD.N0232.N0720.N1126.d016426
        (_root_.GD.N0232.N0720.N1118.d016465 packet₀ packet₁)
        (_root_.GD.N0232.N0720.N1118.d016466 weight₀ weight₁) hmidWeight‖)) hbound





theorem d016495
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet₀ : ℕ → iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : ℕ → kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : ℕ → iota → ℝ) (weight₁ : ℕ → kappa → ℝ)
    (hweight₀ : ∀ j i, 0 ≤ weight₀ j i)
    (hweight₁ : ∀ j k, 0 ≤ weight₁ j k)
    (htight : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        (_root_.GD.N0232.N0720.N1126.d016432 s (packet₀ j) (weight₀ j) +
          _root_.GD.N0232.N0720.N1126.d016432 s (packet₁ j) (weight₁ j)) / 2)
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1118.d016477
        (m := m) (n := n) (packet₀ j) (packet₁ j)
          (weight₀ j) (weight₁ j))
      atTop (nhds 0) := by
  apply squeeze_zero (g := fun j ↦
    ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
      (_root_.GD.N0232.N0720.N1126.d016432 s (packet₀ j) (weight₀ j) +
        _root_.GD.N0232.N0720.N1126.d016432 s (packet₁ j) (weight₁ j)) / 2)
  · intro j
    exact _root_.GD.N0232.N0720.N1118.d016483
      (packet₀ j) (packet₁ j) (weight₀ j) (weight₁ j)
        (hweight₀ j) (hweight₁ j)
  · intro j
    have hbound := _root_.GD.N0232.N0720.N1118.d016494
      s (packet₀ j) (packet₁ j) (weight₀ j) (weight₁ j)
        (hweight₀ j) (hweight₁ j)
    linarith
  · exact htight



theorem d016496
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (packet₀ : ℕ → iota → _root_.GD.N0232.N0720.N1080.d014168) (packet₁ : ℕ → kappa → _root_.GD.N0232.N0720.N1080.d014168)
    (weight₀ : ℕ → iota → ℝ) (weight₁ : ℕ → kappa → ℝ)
    (hweight₀ : ∀ j i, 0 ≤ weight₀ j i)
    (hweight₁ : ∀ j k, 0 ≤ weight₁ j k)
    (htight : Tendsto
      (fun j ↦ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 -
        (_root_.GD.N0232.N0720.N1126.d016432 s (packet₀ j) (weight₀ j) +
          _root_.GD.N0232.N0720.N1126.d016432 s (packet₁ j) (weight₁ j)) / 2)
      atTop (nhds 0)) :
    Tendsto
      (fun j ↦ ∫ omega,
        (_root_.GD.N0232.N0720.N1126.d016416 (packet₀ j) (weight₀ j) omega -
          _root_.GD.N0232.N0720.N1126.d016416 (packet₁ j) (weight₁ j) omega) ^ 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 m n)
      atTop (nhds 0) := by
  have htax :=
    _root_.GD.N0232.N0720.N1118.d016495
      s packet₀ packet₁ weight₀ weight₁ hweight₀ hweight₁ htight
  have htaxFour := htax.mul_const (4 : ℝ)
  rw [zero_mul] at htaxFour
  apply squeeze_zero (g := fun j ↦
    _root_.GD.N0232.N0720.N1118.d016477
      (m := m) (n := n) (packet₀ j) (packet₁ j)
        (weight₀ j) (weight₁ j) * 4)
  · intro j
    exact integral_nonneg fun omega ↦ sq_nonneg
      (_root_.GD.N0232.N0720.N1126.d016416 (packet₀ j) (weight₀ j) omega -
        _root_.GD.N0232.N0720.N1126.d016416 (packet₁ j) (weight₁ j) omega)
  · intro j
    have hfloor :=
      _root_.GD.N0232.N0720.N1118.d016490
        (m := m) (n := n)
          (packet₀ j) (packet₁ j) (weight₀ j) (weight₁ j)
          (hweight₀ j) (hweight₁ j)
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mp
    simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using hfloor
  · exact htaxFour

end

end N1118
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1118.d016458
#print axioms _root_.GD.N0232.N0720.N1118.d016460
#print axioms _root_.GD.N0232.N0720.N1118.d016492
#print axioms _root_.GD.N0232.N0720.N1118.d016491
#print axioms _root_.GD.N0232.N0720.N1118.d016494
#print axioms _root_.GD.N0232.N0720.N1118.d016496
