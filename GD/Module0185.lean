import GD.Module0184























namespace GD.N0232.N0720.N1249

open scoped BigOperators


noncomputable def d002197 (k : ℕ) (h : ℝ) : ℝ :=
  h * (1 - h) * (h - 1 / 2) ^ k


theorem d002198 (k : ℕ) (h : ℝ) :
    _root_.GD.N0232.N0720.N1249.d002197 k (1 - h) =
      (-1 : ℝ) ^ k * _root_.GD.N0232.N0720.N1249.d002197 k h := by
  unfold _root_.GD.N0232.N0720.N1249.d002197
  rw [show (1 - h) - 1 / 2 = -(h - 1 / 2) by ring, neg_pow]
  ring

theorem d002199 (h : ℝ) :
    _root_.GD.N0232.N0720.N1249.d002197 0 (1 - h) = _root_.GD.N0232.N0720.N1249.d002197 0 h := by
  simp [_root_.GD.N0232.N0720.N1249.d002197]
  ring

theorem d002200 (h : ℝ) :
    _root_.GD.N0232.N0720.N1249.d002197 1 (1 - h) = -_root_.GD.N0232.N0720.N1249.d002197 1 h := by
  simp [_root_.GD.N0232.N0720.N1249.d002197]
  ring

theorem d002201 (h : ℝ) :
    _root_.GD.N0232.N0720.N1249.d002197 2 (1 - h) = _root_.GD.N0232.N0720.N1249.d002197 2 h := by
  simp [_root_.GD.N0232.N0720.N1249.d002197]
  ring

theorem d002202 (h : ℝ) :
    _root_.GD.N0232.N0720.N1249.d002197 3 (1 - h) = -_root_.GD.N0232.N0720.N1249.d002197 3 h := by
  simp [_root_.GD.N0232.N0720.N1249.d002197]
  ring

theorem d002203 (h : ℝ) :
    _root_.GD.N0232.N0720.N1249.d002197 4 (1 - h) = _root_.GD.N0232.N0720.N1249.d002197 4 h := by
  simp [_root_.GD.N0232.N0720.N1249.d002197]
  ring

abbrev d002204 := _root_.GD.N0232.N0720.N1250.d002191




theorem d002205 (h : ℝ) :
    _root_.GD.N0232.N0720.N1249.d002197 0 h = _root_.GD.N0232.N0720.N1249.d002204 0 h := by
  simp [_root_.GD.N0232.N0720.N1249.d002197, _root_.GD.N0232.N0720.N1249.d002204, _root_.GD.N0232.N0720.N1250.d002191]

theorem d002206 (h : ℝ) :
    _root_.GD.N0232.N0720.N1249.d002197 1 h =
      _root_.GD.N0232.N0720.N1249.d002204 1 h - (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1249.d002204 0 h := by
  simp [_root_.GD.N0232.N0720.N1249.d002197, _root_.GD.N0232.N0720.N1249.d002204, _root_.GD.N0232.N0720.N1250.d002191]
  ring

theorem d002207 (h : ℝ) :
    _root_.GD.N0232.N0720.N1249.d002197 2 h =
      _root_.GD.N0232.N0720.N1249.d002204 2 h - _root_.GD.N0232.N0720.N1249.d002204 1 h +
        (1 / 4 : ℝ) * _root_.GD.N0232.N0720.N1249.d002204 0 h := by
  simp [_root_.GD.N0232.N0720.N1249.d002197, _root_.GD.N0232.N0720.N1249.d002204, _root_.GD.N0232.N0720.N1250.d002191]
  ring

theorem d002208 (h : ℝ) :
    _root_.GD.N0232.N0720.N1249.d002197 3 h =
      _root_.GD.N0232.N0720.N1249.d002204 3 h - (3 / 2 : ℝ) * _root_.GD.N0232.N0720.N1249.d002204 2 h +
        (3 / 4 : ℝ) * _root_.GD.N0232.N0720.N1249.d002204 1 h -
          (1 / 8 : ℝ) * _root_.GD.N0232.N0720.N1249.d002204 0 h := by
  simp [_root_.GD.N0232.N0720.N1249.d002197, _root_.GD.N0232.N0720.N1249.d002204, _root_.GD.N0232.N0720.N1250.d002191]
  ring

theorem d002209 (h : ℝ) :
    _root_.GD.N0232.N0720.N1249.d002197 4 h =
      _root_.GD.N0232.N0720.N1249.d002204 4 h - 2 * _root_.GD.N0232.N0720.N1249.d002204 3 h +
        (3 / 2 : ℝ) * _root_.GD.N0232.N0720.N1249.d002204 2 h -
          (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1249.d002204 1 h +
            (1 / 16 : ℝ) * _root_.GD.N0232.N0720.N1249.d002204 0 h := by
  simp [_root_.GD.N0232.N0720.N1249.d002197, _root_.GD.N0232.N0720.N1249.d002204, _root_.GD.N0232.N0720.N1250.d002191]
  ring

theorem d002210 (h : ℝ) :
    _root_.GD.N0232.N0720.N1249.d002204 0 h = _root_.GD.N0232.N0720.N1249.d002197 0 h := by
  simp [_root_.GD.N0232.N0720.N1249.d002197, _root_.GD.N0232.N0720.N1249.d002204, _root_.GD.N0232.N0720.N1250.d002191]

theorem d002211 (h : ℝ) :
    _root_.GD.N0232.N0720.N1249.d002204 1 h =
      _root_.GD.N0232.N0720.N1249.d002197 1 h + (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1249.d002197 0 h := by
  simp [_root_.GD.N0232.N0720.N1249.d002197, _root_.GD.N0232.N0720.N1249.d002204, _root_.GD.N0232.N0720.N1250.d002191]
  ring

theorem d002212 (h : ℝ) :
    _root_.GD.N0232.N0720.N1249.d002204 2 h =
      _root_.GD.N0232.N0720.N1249.d002197 2 h + _root_.GD.N0232.N0720.N1249.d002197 1 h +
        (1 / 4 : ℝ) * _root_.GD.N0232.N0720.N1249.d002197 0 h := by
  simp [_root_.GD.N0232.N0720.N1249.d002197, _root_.GD.N0232.N0720.N1249.d002204, _root_.GD.N0232.N0720.N1250.d002191]
  ring

theorem d002213 (h : ℝ) :
    _root_.GD.N0232.N0720.N1249.d002204 3 h =
      _root_.GD.N0232.N0720.N1249.d002197 3 h + (3 / 2 : ℝ) * _root_.GD.N0232.N0720.N1249.d002197 2 h +
        (3 / 4 : ℝ) * _root_.GD.N0232.N0720.N1249.d002197 1 h +
          (1 / 8 : ℝ) * _root_.GD.N0232.N0720.N1249.d002197 0 h := by
  simp [_root_.GD.N0232.N0720.N1249.d002197, _root_.GD.N0232.N0720.N1249.d002204, _root_.GD.N0232.N0720.N1250.d002191]
  ring

theorem d002214 (h : ℝ) :
    _root_.GD.N0232.N0720.N1249.d002204 4 h =
      _root_.GD.N0232.N0720.N1249.d002197 4 h + 2 * _root_.GD.N0232.N0720.N1249.d002197 3 h +
        (3 / 2 : ℝ) * _root_.GD.N0232.N0720.N1249.d002197 2 h +
          (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1249.d002197 1 h +
            (1 / 16 : ℝ) * _root_.GD.N0232.N0720.N1249.d002197 0 h := by
  simp [_root_.GD.N0232.N0720.N1249.d002197, _root_.GD.N0232.N0720.N1249.d002204, _root_.GD.N0232.N0720.N1250.d002191]
  ring

variable {ι : Type*} [Fintype ι]



theorem d002215
    (eta alpha : ι → ℝ)
    (forward reciprocal : ι → Fin 5 → Fin 2 → ℝ)
    (hswap : ∀ i k j,
      eta i * reciprocal i k j =
        -((-1 : ℝ) ^ (k : ℕ)) * forward i k j)
    (k : Fin 5) (j : Fin 2) :
    ∑ i, (alpha i * forward i k j +
        (alpha i * eta i) * reciprocal i k j) =
      (1 - (-1 : ℝ) ^ (k : ℕ)) *
        ∑ i, alpha i * forward i k j := by
  calc
    ∑ i, (alpha i * forward i k j +
        (alpha i * eta i) * reciprocal i k j) =
        ∑ i, (alpha i * forward i k j +
          alpha i * (eta i * reciprocal i k j)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = ∑ i, (alpha i * forward i k j +
          alpha i * (-((-1 : ℝ) ^ (k : ℕ)) * forward i k j)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hswap i k j]
    _ = (1 - (-1 : ℝ) ^ (k : ℕ)) *
          ∑ i, alpha i * forward i k j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring




theorem d002216
    (eta alpha : ι → ℝ)
    (forward reciprocal : ι → Fin 5 → Fin 2 → ℝ)
    (hswap : ∀ i k j,
      eta i * reciprocal i k j =
        -((-1 : ℝ) ^ (k : ℕ)) * forward i k j)
    (hoddOne : ∀ j,
      ∑ i, alpha i * forward i (1 : Fin 5) j = 0)
    (hoddThree : ∀ j,
      ∑ i, alpha i * forward i (3 : Fin 5) j = 0) :
    ∀ k j,
      ∑ i, (alpha i * forward i k j +
        (alpha i * eta i) * reciprocal i k j) = 0 := by
  intro k j
  rw [_root_.GD.N0232.N0720.N1249.d002215 eta alpha forward reciprocal hswap k j]
  fin_cases k <;> norm_num [hoddOne j, hoddThree j]
  simpa using hoddThree j



def d002217 (eta alpha : ι → ℝ) : Sum ι ι → ℝ
  | Sum.inl i => alpha i
  | Sum.inr i => alpha i * eta i


def d002218
    (forward reciprocal : ι → Fin 5 → Fin 2 → ℝ) :
    Sum ι ι → Fin 5 → Fin 2 → ℝ
  | Sum.inl i => forward i
  | Sum.inr i => reciprocal i

omit [Fintype ι] in
theorem d002219
    (eta alpha : ι → ℝ)
    (heta : ∀ i, 0 < eta i)
    (halpha : ∀ i, 0 < alpha i) :
    ∀ atom, 0 < _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom := by
  intro atom
  cases atom with
  | inl i => exact halpha i
  | inr i => exact mul_pos (halpha i) (heta i)



theorem d002220
    (eta alpha : ι → ℝ)
    (forward reciprocal : ι → Fin 5 → Fin 2 → ℝ)
    (hswap : ∀ i k j,
      eta i * reciprocal i k j =
        -((-1 : ℝ) ^ (k : ℕ)) * forward i k j)
    (hoddOne : ∀ j,
      ∑ i, alpha i * forward i (1 : Fin 5) j = 0)
    (hoddThree : ∀ j,
      ∑ i, alpha i * forward i (3 : Fin 5) j = 0) :
    ∀ k j,
      ∑ atom, _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom *
        _root_.GD.N0232.N0720.N1249.d002218 forward reciprocal atom k j = 0 := by
  intro k j
  rw [Fintype.sum_sum_type]
  rw [← Finset.sum_add_distrib]
  simpa [_root_.GD.N0232.N0720.N1249.d002217, _root_.GD.N0232.N0720.N1249.d002218] using
    _root_.GD.N0232.N0720.N1249.d002216 eta alpha forward reciprocal
      hswap hoddOne hoddThree k j



noncomputable def d002221
    (forward reciprocal : ι → Fin 5 → Fin 2 → ℝ)
    (coefficient : Fin 5 → Fin 2 → ℝ)
    (atom : Sum ι ι) : ℝ :=
  ∑ k, ∑ j, coefficient k j * _root_.GD.N0232.N0720.N1249.d002218 forward reciprocal atom k j



theorem d002222
    (eta alpha : ι → ℝ)
    (forward reciprocal : ι → Fin 5 → Fin 2 → ℝ)
    (coefficient : Fin 5 → Fin 2 → ℝ)
    (hswap : ∀ i k j,
      eta i * reciprocal i k j =
        -((-1 : ℝ) ^ (k : ℕ)) * forward i k j)
    (hoddOne : ∀ j,
      ∑ i, alpha i * forward i (1 : Fin 5) j = 0)
    (hoddThree : ∀ j,
      ∑ i, alpha i * forward i (3 : Fin 5) j = 0) :
    ∑ atom, _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom *
      _root_.GD.N0232.N0720.N1249.d002221 forward reciprocal coefficient atom = 0 := by
  simp only [_root_.GD.N0232.N0720.N1249.d002221, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  calc
    ∑ atom, _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom *
        (coefficient k j * _root_.GD.N0232.N0720.N1249.d002218 forward reciprocal atom k j) =
        coefficient k j * ∑ atom, _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom *
          _root_.GD.N0232.N0720.N1249.d002218 forward reciprocal atom k j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro atom hatom
            ring
    _ = 0 := by
      rw [_root_.GD.N0232.N0720.N1249.d002220 eta alpha forward reciprocal hswap hoddOne
        hoddThree k j]
      ring






theorem d002223
    [Nonempty ι]
    (eta alpha : ι → ℝ)
    (forward reciprocal : ι → Fin 5 → Fin 2 → ℝ)
    (zero : Fin 5 → Fin 2 → ℝ)
    (energy : Sum ι ι → (Fin 5 → Fin 2 → ℝ) → ℝ)
    (heta : ∀ i, 0 < eta i)
    (halpha : ∀ i, 0 < alpha i)
    (hswap : ∀ i k j,
      eta i * reciprocal i k j =
        -((-1 : ℝ) ^ (k : ℕ)) * forward i k j)
    (hoddOne : ∀ j,
      ∑ i, alpha i * forward i (1 : Fin 5) j = 0)
    (hoddThree : ∀ j,
      ∑ i, alpha i * forward i (3 : Fin 5) j = 0)
    (henergy : ∀ atom c, 0 ≤ energy atom c)
    (henergyStrict : ∀ atom c, c ≠ zero → 0 < energy atom c) :
    ¬ ∃ c, c ≠ zero ∧ ∀ atom,
      2 * _root_.GD.N0232.N0720.N1249.d002221 forward reciprocal c atom + energy atom c ≤ 0 := by
  rintro ⟨c, hc, hall⟩
  have hw : ∀ atom, 0 < _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom :=
    _root_.GD.N0232.N0720.N1249.d002219 eta alpha heta halpha
  have henergySum :
      0 < ∑ atom, _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom * energy atom c := by
    apply Finset.sum_pos'
    · intro atom hatom
      exact mul_nonneg (hw atom).le (henergy atom c)
    · let i : ι := Classical.choice (inferInstance : Nonempty ι)
      exact ⟨Sum.inl i, Finset.mem_univ _,
        mul_pos (hw (Sum.inl i)) (henergyStrict (Sum.inl i) c hc)⟩
  have hincrementSum :
      (∑ atom, _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom *
        (2 * _root_.GD.N0232.N0720.N1249.d002221 forward reciprocal c atom + energy atom c)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro atom hatom
    exact mul_nonpos_of_nonneg_of_nonpos (hw atom).le (hall atom)
  have hbalance := _root_.GD.N0232.N0720.N1249.d002222 eta alpha forward reciprocal c
    hswap hoddOne hoddThree
  have hid :
      (∑ atom, _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom *
        (2 * _root_.GD.N0232.N0720.N1249.d002221 forward reciprocal c atom + energy atom c)) =
        ∑ atom, _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom * energy atom c := by
    calc
      _ = 2 * (∑ atom, _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom *
              _root_.GD.N0232.N0720.N1249.d002221 forward reciprocal c atom) +
            ∑ atom, _root_.GD.N0232.N0720.N1249.d002217 eta alpha atom * energy atom c := by
              simp_rw [mul_add]
              rw [Finset.sum_add_distrib]
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro atom hatom
              ring
      _ = _ := by rw [hbalance]; ring
  rw [hid] at hincrementSum
  exact (not_lt_of_ge hincrementSum) henergySum


theorem d002224 :
    Fintype.card (Sum (Fin 5) (Fin 5)) = 10 := by
  simp




noncomputable def d002225 : Fin 5 → ℝ
  | 0 => 13 / 10
  | 1 => 23 / 10
  | 2 => 27 / 4
  | 3 => 42 / 5
  | 4 => 273 / 2

theorem d002226 (i : Fin 5) : 1 < _root_.GD.N0232.N0720.N1249.d002225 i := by
  fin_cases i <;> norm_num [_root_.GD.N0232.N0720.N1249.d002225]




noncomputable def d002227 : Fin 5 → ℝ
  | 0 => 11 / 10
  | 1 => 2
  | 2 => 11 / 2
  | 3 => 18
  | 4 => 145

theorem d002228 (i : Fin 5) :
    1 < _root_.GD.N0232.N0720.N1249.d002227 i := by
  fin_cases i <;> norm_num [_root_.GD.N0232.N0720.N1249.d002227]



noncomputable def d002229 : Fin 4 → ℝ
  | 0 => 1 / 7
  | 1 => 4 / 7
  | 2 => 7 / 4
  | 3 => 7

theorem d002230 (i : Fin 4) : 0 < _root_.GD.N0232.N0720.N1249.d002229 i := by
  fin_cases i <;> norm_num [_root_.GD.N0232.N0720.N1249.d002229]

end GD.N0232.N0720.N1249
