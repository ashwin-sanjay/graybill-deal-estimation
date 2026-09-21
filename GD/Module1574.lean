import GD.Module1565

















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped BigOperators

namespace GD.N0106.N0428.N0770.N1728
noncomputable section

open _root_.GD.N0106.N0428.N0770.N1725


abbrev d024386 := Fin 4 × Fin 2

def d024387 : Fin 2 → ℝ := ![1, -1]
def d024388 (ell : ℝ) : Fin 2 → ℝ := ![ell, 1 - ell]

def d024389 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : ℝ × ℝ :=
  (_root_.GD.N0106.N0428.N0770.N1728.d024388 (_root_.GD.N0106.N0428.N0770.N1725.d024127 i.1) i.2, _root_.GD.N0106.N0428.N0770.N1725.d024128 i.1)

def d024390 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : ℝ := _root_.GD.N0106.N0428.N0770.N1728.d024387 i.2 * _root_.GD.N0106.N0428.N0770.N1725.d024129 i.1

theorem d024391 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) :
    _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 = _root_.GD.N0106.N0428.N0770.N1725.d024129 i.1 ^ 2 := by
  rcases i with ⟨r, s⟩
  fin_cases s <;> simp [_root_.GD.N0106.N0428.N0770.N1728.d024390, _root_.GD.N0106.N0428.N0770.N1728.d024387]

theorem d024392 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) :
    (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 ∈ Ioo (0 : ℝ) 1 ∧ 0 < (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).2 := by
  rcases i with ⟨r, s⟩
  fin_cases r <;> fin_cases s <;>
    norm_num [_root_.GD.N0106.N0428.N0770.N1728.d024389, _root_.GD.N0106.N0428.N0770.N1728.d024388, _root_.GD.N0106.N0428.N0770.N1725.d024127, _root_.GD.N0106.N0428.N0770.N1725.d024128]


theorem d024393 (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024130 p = ∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386,
      _root_.GD.N0106.N0428.N0770.N1728.d024390 i * _root_.GD.N0106.N0428.N0770.N1725.d024125 (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).2 _root_.GD.N0106.N0428.N0770.N1725.d024116 p := by
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024130
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  simp [Fin.sum_univ_succ, _root_.GD.N0106.N0428.N0770.N1728.d024390, _root_.GD.N0106.N0428.N0770.N1728.d024389, _root_.GD.N0106.N0428.N0770.N1728.d024387, _root_.GD.N0106.N0428.N0770.N1728.d024388,
    _root_.GD.N0106.N0428.N0770.N1725.d024125, _root_.GD.N0106.N0428.N0770.N1725.d024126]
  <;> ring


def d024394 (m q e c sign : ℝ) : ℝ :=
  2 * sign * c * (e - q) + (4 / 9) * m * _root_.GD.N0106.N0428.N0770.N1725.d024117 * c * c

def d024395 (m q e f c sign : ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0770.N1728.d024394 m q e c sign * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, f)

def d024396 (m q : ℝ) : ℝ :=
  ∑ r : Fin 4, ∑ s : Fin 2,
    _root_.GD.N0106.N0428.N0770.N1728.d024395 m q (_root_.GD.N0106.N0428.N0770.N1728.d024388 (_root_.GD.N0106.N0428.N0770.N1725.d024127 r) s) (_root_.GD.N0106.N0428.N0770.N1725.d024128 r)
      (_root_.GD.N0106.N0428.N0770.N1725.d024129 r) (_root_.GD.N0106.N0428.N0770.N1728.d024387 s)

def d024397 (q : ℝ) : ℝ := _root_.GD.N0106.N0428.N0770.N1728.d024396 1 q
def d024398 (q : ℝ) : ℝ := _root_.GD.N0106.N0428.N0770.N1728.d024396 3 q


theorem d024399 (m q : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1728.d024396 m q = ∑ r : Fin 4, (
      (2 * _root_.GD.N0106.N0428.N0770.N1725.d024129 r * (_root_.GD.N0106.N0428.N0770.N1725.d024127 r - q) +
          4 * m * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1725.d024129 r ^ 2 / 9) *
        _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1725.d024127 r, _root_.GD.N0106.N0428.N0770.N1725.d024128 r) +
      (-2 * _root_.GD.N0106.N0428.N0770.N1725.d024129 r * (1 - _root_.GD.N0106.N0428.N0770.N1725.d024127 r - q) +
          4 * m * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1725.d024129 r ^ 2 / 9) *
        _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 - _root_.GD.N0106.N0428.N0770.N1725.d024127 r, _root_.GD.N0106.N0428.N0770.N1725.d024128 r)) := by
  unfold _root_.GD.N0106.N0428.N0770.N1728.d024396
  apply Finset.sum_congr rfl
  intro r _
  simp [Fin.sum_univ_succ, _root_.GD.N0106.N0428.N0770.N1728.d024395, _root_.GD.N0106.N0428.N0770.N1728.d024394, _root_.GD.N0106.N0428.N0770.N1728.d024387, _root_.GD.N0106.N0428.N0770.N1728.d024388]
  <;> ring

theorem d024400 (q : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1728.d024397 q = ∑ r : Fin 4, (
      (2 * _root_.GD.N0106.N0428.N0770.N1725.d024129 r * (_root_.GD.N0106.N0428.N0770.N1725.d024127 r - q) +
          4 * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1725.d024129 r ^ 2 / 9) *
        _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1725.d024127 r, _root_.GD.N0106.N0428.N0770.N1725.d024128 r) +
      (-2 * _root_.GD.N0106.N0428.N0770.N1725.d024129 r * (1 - _root_.GD.N0106.N0428.N0770.N1725.d024127 r - q) +
          4 * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1725.d024129 r ^ 2 / 9) *
        _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 - _root_.GD.N0106.N0428.N0770.N1725.d024127 r, _root_.GD.N0106.N0428.N0770.N1725.d024128 r)) := by
  simpa only [_root_.GD.N0106.N0428.N0770.N1728.d024397, mul_one] using _root_.GD.N0106.N0428.N0770.N1728.d024399 1 q



def d024401 (m q : ℝ) (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : ℝ :=
  (_root_.GD.N0106.N0428.N0770.N1725.d024116 ^ 2)⁻¹ * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i) *
    (2 * ((_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 - q) * _root_.GD.N0106.N0428.N0770.N1728.d024390 i *
        (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024125 (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).2 _root_.GD.N0106.N0428.N0770.N1725.d024116 p
          ∂(volume.prod volume)) +
      m * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 *
        (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024125 (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 (_root_.GD.N0106.N0428.N0770.N1728.d024389 i).2 _root_.GD.N0106.N0428.N0770.N1725.d024116 p ^ 2
          ∂(volume.prod volume)))

def d024402 (m q : ℝ) : ℝ := ∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, _root_.GD.N0106.N0428.N0770.N1728.d024401 m q i

theorem d024403 (m q : ℝ) (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) :
    _root_.GD.N0106.N0428.N0770.N1728.d024401 m q i =
      (2 * ((_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 - q) * _root_.GD.N0106.N0428.N0770.N1728.d024390 i +
        (4 / 9) * m * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i) := by
  unfold _root_.GD.N0106.N0428.N0770.N1728.d024401
  rw [_root_.GD.N0106.N0428.N0770.N1725.d024152 _ _ _ _root_.GD.N0106.N0428.N0770.N1725.d024120, _root_.GD.N0106.N0428.N0770.N1725.d024153 _ _ _ _root_.GD.N0106.N0428.N0770.N1725.d024120]
  field_simp [_root_.GD.N0106.N0428.N0770.N1725.d024120.ne']
  <;> ring

theorem d024404 (m q : ℝ) (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) :
    _root_.GD.N0106.N0428.N0770.N1728.d024401 m q i =
      _root_.GD.N0106.N0428.N0770.N1728.d024395 m q (_root_.GD.N0106.N0428.N0770.N1728.d024388 (_root_.GD.N0106.N0428.N0770.N1725.d024127 i.1) i.2) (_root_.GD.N0106.N0428.N0770.N1725.d024128 i.1)
        (_root_.GD.N0106.N0428.N0770.N1725.d024129 i.1) (_root_.GD.N0106.N0428.N0770.N1728.d024387 i.2) := by
  rw [_root_.GD.N0106.N0428.N0770.N1728.d024403, _root_.GD.N0106.N0428.N0770.N1728.d024391]
  unfold _root_.GD.N0106.N0428.N0770.N1728.d024390 _root_.GD.N0106.N0428.N0770.N1728.d024389 _root_.GD.N0106.N0428.N0770.N1728.d024395 _root_.GD.N0106.N0428.N0770.N1728.d024394
  ring

theorem d024405 (m q : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1728.d024396 m q = _root_.GD.N0106.N0428.N0770.N1728.d024402 m q := by
  unfold _root_.GD.N0106.N0428.N0770.N1728.d024396 _root_.GD.N0106.N0428.N0770.N1728.d024402
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  exact (_root_.GD.N0106.N0428.N0770.N1728.d024404 m q (r, s)).symm

theorem d024406 (q : ℝ) : _root_.GD.N0106.N0428.N0770.N1728.d024397 q = _root_.GD.N0106.N0428.N0770.N1728.d024402 1 q :=
  _root_.GD.N0106.N0428.N0770.N1728.d024405 1 q

theorem d024407 (m q : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1728.d024396 m q = ∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386,
      (2 * ((_root_.GD.N0106.N0428.N0770.N1728.d024389 i).1 - q) * _root_.GD.N0106.N0428.N0770.N1728.d024390 i +
        (4 / 9) * m * _root_.GD.N0106.N0428.N0770.N1725.d024117 * _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i) := by
  rw [_root_.GD.N0106.N0428.N0770.N1728.d024405]
  simp only [_root_.GD.N0106.N0428.N0770.N1728.d024402, _root_.GD.N0106.N0428.N0770.N1728.d024403]



def d024408 (q : ℝ) : ℝ :=
  ∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, _root_.GD.N0106.N0428.N0770.N1728.d024390 i ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i)

theorem d024409 (m₁ m₂ q : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1728.d024396 m₂ q - _root_.GD.N0106.N0428.N0770.N1728.d024396 m₁ q =
      ((4 / 9) * _root_.GD.N0106.N0428.N0770.N1725.d024117 * (m₂ - m₁)) * _root_.GD.N0106.N0428.N0770.N1728.d024408 q := by
  rw [_root_.GD.N0106.N0428.N0770.N1728.d024407, _root_.GD.N0106.N0428.N0770.N1728.d024407]
  unfold _root_.GD.N0106.N0428.N0770.N1728.d024408
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem d024410 (q : ℝ) : _root_.GD.N0106.N0428.N0770.N1728.d024398 q = _root_.GD.N0106.N0428.N0770.N1728.d024397 q + (4 / 1125) * _root_.GD.N0106.N0428.N0770.N1728.d024408 q := by
  have h := _root_.GD.N0106.N0428.N0770.N1728.d024409 1 3 q
  norm_num only [_root_.GD.N0106.N0428.N0770.N1725.d024117] at h
  dsimp only [_root_.GD.N0106.N0428.N0770.N1728.d024398, _root_.GD.N0106.N0428.N0770.N1728.d024397]
  linarith

theorem d024411 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    0 ≤ _root_.GD.N0106.N0428.N0770.N1728.d024408 q := by
  unfold _root_.GD.N0106.N0428.N0770.N1728.d024408
  apply Finset.sum_nonneg
  intro i _
  have hi := _root_.GD.N0106.N0428.N0770.N1728.d024392 i
  have hN := _root_.GD.N0106.N0428.N0770.N1725.d024172 hq hi.1 hi.2
  have hW : 0 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024170 q (_root_.GD.N0106.N0428.N0770.N1728.d024389 i) := by
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hN.le _)
  exact mul_nonneg (sq_nonneg _) hW

theorem d024412 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : _root_.GD.N0106.N0428.N0770.N1728.d024397 q ≤ _root_.GD.N0106.N0428.N0770.N1728.d024398 q := by
  rw [_root_.GD.N0106.N0428.N0770.N1728.d024410]
  exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (_root_.GD.N0106.N0428.N0770.N1728.d024411 hq))


theorem d024413 (e q z : ℝ) :
    (e + 2 * _root_.GD.N0106.N0428.N0770.N1725.d024117 * z - q) ^ 2 - (e + _root_.GD.N0106.N0428.N0770.N1725.d024117 * z - q) ^ 2 =
      _root_.GD.N0106.N0428.N0770.N1725.d024117 * (2 * (e - q) * z + 3 * _root_.GD.N0106.N0428.N0770.N1725.d024117 * z ^ 2) := by
  ring

theorem d024414 (e q z : ℝ) :
    (e + _root_.GD.N0106.N0428.N0770.N1725.d024117 * z - q) ^ 2 - (e - q) ^ 2 =
      _root_.GD.N0106.N0428.N0770.N1725.d024117 * (2 * (e - q) * z + _root_.GD.N0106.N0428.N0770.N1725.d024117 * z ^ 2) := by
  ring



theorem d024415 :
    -(47 / 200 : ℝ) + 1 / 1000 = -(117 / 500 : ℝ) := by norm_num

theorem d024416 :
    (3 / 4 : ℝ) * _root_.GD.N0106.N0428.N0770.N1725.d024117 * (117 / 500) = 351 / 500000 := by
  norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024117]

theorem d024417 :
    (7403 / 10000 : ℝ) - 718 / 1000000 > 739 / 1000 := by norm_num

theorem d024418 :
    (1 : ℝ) ^ 2 / ((19 : ℝ) ^ 2 + 1 ^ 2) = 1 / 362 := by norm_num

end
end GD.N0106.N0428.N0770.N1728

#print axioms _root_.GD.N0106.N0428.N0770.N1728.d024400
#print axioms _root_.GD.N0106.N0428.N0770.N1728.d024406
