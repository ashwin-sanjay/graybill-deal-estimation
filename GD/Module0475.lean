import GD.Module0472









set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators

namespace GD.N0193
noncomputable section

open _root_.GD.N0181

def d007343 (N : ℕ) : ℕ := N ^ 3 - N ^ 2


abbrev d007344 (N : ℕ) := Fin (_root_.GD.N0193.d007343 N) × Fin 2

def d007345 (N : ℕ) (i : Fin (_root_.GD.N0193.d007343 N)) : ℕ := N ^ 2 + i.val

def d007346 (N : ℕ) (i : Fin (_root_.GD.N0193.d007343 N)) : ℝ := _root_.GD.N0181.d007268 N ^ _root_.GD.N0193.d007345 N i

def d007347 (N : ℕ) (i : _root_.GD.N0193.d007344 N) : ℝ :=
  if i.2 = 0 then _root_.GD.N0193.d007346 N i.1 else 1 - _root_.GD.N0193.d007346 N i.1

def d007348 (N : ℕ) : ℝ := 1 / (2 * (_root_.GD.N0193.d007343 N : ℝ))


def d007349 (N : ℕ) (i : _root_.GD.N0193.d007344 N) : ℚ :=
  if i.2 = 0 then (1 - 1 / (N : ℚ)) ^ _root_.GD.N0193.d007345 N i.1
    else 1 - (1 - 1 / (N : ℚ)) ^ _root_.GD.N0193.d007345 N i.1

def d007350 (N : ℕ) : ℚ := 1 / (2 * (_root_.GD.N0193.d007343 N : ℚ))


def d007351 (N : ℕ) : Measure ℝ :=
  Measure.sum fun i : _root_.GD.N0193.d007344 N =>
    ENNReal.ofReal (_root_.GD.N0193.d007348 N) • Measure.dirac (_root_.GD.N0193.d007347 N i)

theorem d007352 (N : ℕ) : _root_.GD.N0193.d007343 N = N ^ 2 * (N - 1) := by
  simp only [_root_.GD.N0193.d007343, Nat.mul_sub_left_distrib, mul_one] <;> ring

theorem d007353 {N : ℕ} (hN : 2 ≤ N) : 0 < _root_.GD.N0193.d007343 N := by
  rw [_root_.GD.N0193.d007352]
  exact Nat.mul_pos (pow_pos (by omega : 0 < N) _) (by omega)

theorem d007354 {N : ℕ} (hN : 2 ≤ N) : N ^ 2 ≤ N ^ 3 := by
  have hk := _root_.GD.N0193.d007353 hN
  unfold _root_.GD.N0193.d007343 at hk
  omega

theorem d007355 {N : ℕ} (hN : 2 ≤ N) (i : Fin (_root_.GD.N0193.d007343 N)) :
    _root_.GD.N0193.d007345 N i ∈ Ico (N ^ 2) (N ^ 3) := by
  have hi := i.isLt
  have hpow := _root_.GD.N0193.d007354 hN
  unfold _root_.GD.N0193.d007343 at hi
  simp only [_root_.GD.N0193.d007345, mem_Ico]
  omega


theorem d007356 {N : ℕ} (hN : 2 ≤ N) :
    Set.range (_root_.GD.N0193.d007345 N) = Ico (N ^ 2) (N ^ 3) := by
  ext j
  constructor
  · rintro ⟨i, rfl⟩
    exact _root_.GD.N0193.d007355 hN i
  · intro hj
    have hj0 := hj.1
    have hj1 := hj.2
    let i : Fin (_root_.GD.N0193.d007343 N) := ⟨j - N ^ 2, by unfold _root_.GD.N0193.d007343; omega⟩
    refine ⟨i, ?_⟩
    dsimp [_root_.GD.N0193.d007345, i]
    omega

theorem d007357 {N : ℕ} (hN : 2 ≤ N) (i : Fin (_root_.GD.N0193.d007343 N)) :
    0 < _root_.GD.N0193.d007345 N i :=
  lt_of_lt_of_le (pow_pos (by omega : 0 < N) _) (_root_.GD.N0193.d007355 hN i).1

theorem d007358 {N : ℕ} (hN : 2 ≤ N) (i : Fin (_root_.GD.N0193.d007343 N)) :
    0 < _root_.GD.N0193.d007346 N i := pow_pos (_root_.GD.N0181.d007276 hN) _

theorem d007359 {N : ℕ} (hN : 2 ≤ N) (i : Fin (_root_.GD.N0193.d007343 N)) :
    _root_.GD.N0193.d007346 N i < 1 := by
  simpa only [_root_.GD.N0193.d007346, pow_zero] using
    pow_lt_pow_right_of_lt_one₀ (_root_.GD.N0181.d007276 hN) (_root_.GD.N0181.d007277 hN) (_root_.GD.N0193.d007357 hN i)

theorem d007360 {N : ℕ} (hN : 2 ≤ N) (i : Fin (_root_.GD.N0193.d007343 N)) :
    _root_.GD.N0193.d007346 N i ≤ _root_.GD.N0181.d007269 N :=
  pow_le_pow_of_le_one (_root_.GD.N0181.d007276 hN).le (_root_.GD.N0181.d007277 hN).le (_root_.GD.N0193.d007355 hN i).1


theorem d007361 {N : ℕ} (hN : 2 ≤ N) (i : Fin (_root_.GD.N0193.d007343 N)) :
    _root_.GD.N0193.d007346 N i < 1 / 2 := by
  have hNsq : N ≤ N ^ 2 := le_self_pow₀ (by omega : 1 ≤ N) (by decide : 2 ≠ 0)
  have hNexp : N ≤ _root_.GD.N0193.d007345 N i := hNsq.trans (_root_.GD.N0193.d007355 hN i).1
  exact (pow_le_pow_of_le_one (_root_.GD.N0181.d007276 hN).le (_root_.GD.N0181.d007277 hN).le hNexp).trans_lt
    (_root_.GD.N0181.d007279 hN)

theorem d007362 {N : ℕ} (hN : 2 ≤ N) (i : Fin (_root_.GD.N0193.d007343 N)) :
    1 / 2 < 1 - _root_.GD.N0193.d007346 N i := by
  have h := _root_.GD.N0193.d007361 hN i
  linarith

theorem d007363 {N : ℕ} (hN : 2 ≤ N) (i : _root_.GD.N0193.d007344 N) :
    _root_.GD.N0193.d007347 N i ∈ Ioo (0 : ℝ) 1 := by
  have h0 := _root_.GD.N0193.d007358 hN i.1
  have h1 := _root_.GD.N0193.d007359 hN i.1
  unfold _root_.GD.N0193.d007347
  split_ifs <;> constructor <;> linarith

theorem d007364 (N : ℕ) (i : _root_.GD.N0193.d007344 N) :
    (_root_.GD.N0193.d007349 N i : ℝ) = _root_.GD.N0193.d007347 N i := by
  unfold _root_.GD.N0193.d007349 _root_.GD.N0193.d007347 _root_.GD.N0193.d007346
  split_ifs <;> simp [_root_.GD.N0181.d007268]

theorem d007365 {N : ℕ} (hN : 2 ≤ N) (i : _root_.GD.N0193.d007344 N) :
    _root_.GD.N0193.d007349 N i ∈ Ioo (0 : ℚ) 1 := by
  have h := _root_.GD.N0193.d007363 hN i
  rw [← _root_.GD.N0193.d007364] at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

theorem d007366 (N : ℕ) : (_root_.GD.N0193.d007350 N : ℝ) = _root_.GD.N0193.d007348 N := by
  simp [_root_.GD.N0193.d007350, _root_.GD.N0193.d007348]

theorem d007367 {N : ℕ} (hN : 2 ≤ N) : 0 < _root_.GD.N0193.d007348 N := by
  have hk : 0 < (_root_.GD.N0193.d007343 N : ℝ) := Nat.cast_pos.mpr (_root_.GD.N0193.d007353 hN)
  unfold _root_.GD.N0193.d007348
  positivity

theorem d007368 {N : ℕ} (hN : 2 ≤ N) : 0 < _root_.GD.N0193.d007350 N := by
  have h := _root_.GD.N0193.d007367 hN
  rw [← _root_.GD.N0193.d007366] at h
  exact_mod_cast h

theorem d007369 (N : ℕ) : Fintype.card (Fin (_root_.GD.N0193.d007343 N)) = _root_.GD.N0193.d007343 N := Fintype.card_fin _

theorem d007370 (N : ℕ) : Fintype.card (_root_.GD.N0193.d007344 N) = 2 * _root_.GD.N0193.d007343 N := by
  simp only [_root_.GD.N0193.d007344, Fintype.card_prod, Fintype.card_fin]
  omega

theorem d007371 {N : ℕ} (hN : 2 ≤ N) : Function.Injective (_root_.GD.N0193.d007346 N) := by
  intro i j hij
  have he := pow_right_injective₀ (_root_.GD.N0181.d007276 hN) (_root_.GD.N0181.d007277 hN).ne hij
  apply Fin.ext
  change N ^ 2 + i.val = N ^ 2 + j.val at he
  omega

theorem d007372 {N : ℕ} (hN : 2 ≤ N) : Function.Injective (_root_.GD.N0193.d007347 N) := by
  rintro ⟨i, side⟩ ⟨j, side'⟩ hij
  fin_cases side <;> fin_cases side'
  · change _root_.GD.N0193.d007346 N i = _root_.GD.N0193.d007346 N j at hij
    have h := _root_.GD.N0193.d007371 hN hij
    subst j
    rfl
  · change _root_.GD.N0193.d007346 N i = 1 - _root_.GD.N0193.d007346 N j at hij
    have hi := _root_.GD.N0193.d007361 hN i
    have hj := _root_.GD.N0193.d007362 hN j
    linarith
  · change 1 - _root_.GD.N0193.d007346 N i = _root_.GD.N0193.d007346 N j at hij
    have hi := _root_.GD.N0193.d007362 hN i
    have hj := _root_.GD.N0193.d007361 hN j
    linarith
  · change 1 - _root_.GD.N0193.d007346 N i = 1 - _root_.GD.N0193.d007346 N j at hij
    have he : _root_.GD.N0193.d007346 N i = _root_.GD.N0193.d007346 N j := by linarith
    have h := _root_.GD.N0193.d007371 hN he
    subst j
    rfl

theorem d007373 {N : ℕ} (hN : 2 ≤ N) :
    (Finset.univ.image (_root_.GD.N0193.d007347 N)).card = 2 * _root_.GD.N0193.d007343 N := by
  classical
  rw [Finset.card_image_of_injective _ (_root_.GD.N0193.d007372 hN), Finset.card_univ,
    _root_.GD.N0193.d007370]

theorem d007374 {N : ℕ} (hN : 2 ≤ N) :
    (∑ _i : _root_.GD.N0193.d007344 N, _root_.GD.N0193.d007348 N) = 1 := by
  have hk : (_root_.GD.N0193.d007343 N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (_root_.GD.N0193.d007353 hN).ne'
  rw [Finset.sum_const, Finset.card_univ, _root_.GD.N0193.d007370, nsmul_eq_mul]
  unfold _root_.GD.N0193.d007348
  push_cast
  field_simp [hk]

theorem d007375 (N : ℕ) :
    _root_.GD.N0193.d007351 N = ENNReal.ofReal (_root_.GD.N0193.d007348 N) •
      ∑ i : Fin (_root_.GD.N0193.d007343 N),
        (Measure.dirac (_root_.GD.N0193.d007346 N i) + Measure.dirac (1 - _root_.GD.N0193.d007346 N i)) := by
  rw [_root_.GD.N0193.d007351, Measure.sum_fintype, Fintype.sum_prod_type]
  simp only [Finset.smul_sum, smul_add]
  apply Finset.sum_congr rfl
  intro i _
  simp [_root_.GD.N0193.d007347, Fin.sum_univ_succ]

theorem d007376 {N : ℕ} (hN : 2 ≤ N) :
    IsProbabilityMeasure (_root_.GD.N0193.d007351 N) := by
  have hsum : HasSum (fun _i : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) 1 := by
    simpa only [_root_.GD.N0193.d007374 hN] using (hasSum_fintype (fun _i : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N))
  exact HasSum.isProbabilityMeasure_sum_dirac (d := _root_.GD.N0193.d007347 N)
    (fun _i => (_root_.GD.N0193.d007367 hN).le) hsum

theorem d007377 {N : ℕ} (hN : 2 ≤ N) : _root_.GD.N0193.d007351 N univ = 1 := by
  letI := _root_.GD.N0193.d007376 hN
  exact measure_univ


theorem d007378 {N : ℕ} (hN : 2 ≤ N) (i : _root_.GD.N0193.d007344 N) :
    _root_.GD.N0193.d007351 N {_root_.GD.N0193.d007347 N i} = ENNReal.ofReal (_root_.GD.N0193.d007348 N) := by
  rw [_root_.GD.N0193.d007351, Measure.sum_apply _ (measurableSet_singleton _), tsum_eq_single i]
  · simp
  · intro j hji
    have hne : _root_.GD.N0193.d007347 N j ≠ _root_.GD.N0193.d007347 N i := fun h => hji (_root_.GD.N0193.d007372 hN h)
    simp [Measure.smul_apply, Measure.dirac_apply, hne]

end
end GD.N0193

#print axioms _root_.GD.N0193.d007356
#print axioms _root_.GD.N0193.d007363
#print axioms _root_.GD.N0193.d007365
#print axioms _root_.GD.N0193.d007368
#print axioms _root_.GD.N0193.d007361
#print axioms _root_.GD.N0193.d007372
#print axioms _root_.GD.N0193.d007373
#print axioms _root_.GD.N0193.d007374
#print axioms _root_.GD.N0193.d007375
#print axioms _root_.GD.N0193.d007376
#print axioms _root_.GD.N0193.d007377
#print axioms _root_.GD.N0193.d007378
