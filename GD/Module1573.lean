import GD.Module1565











set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set
open scoped BigOperators

namespace GD.N0106.N0428.N0770.N1726
noncomputable section

open _root_.GD.N0106.N0428.N0770.N1725


def d024360 : Fin 12 → ℕ :=
  ![300, 5700, 900, 5100, 120, 5880, 600, 5400, 12, 5988, 50, 5950]

def d024361 (i : Fin 12) : ℝ := (_root_.GD.N0106.N0428.N0770.N1726.d024360 i : ℝ) / 6000

def d024362 : Fin 12 → ℝ :=
  ![2, 2, 1 / 50, 1 / 50, 1 / 50, 1 / 50, 1 / 50, 1 / 50,
    1 / 1000, 1 / 1000, 20, 20]

def d024363 : Fin 12 → ℝ :=
  ![_root_.GD.N0106.N0428.N0770.N1725.d024116, _root_.GD.N0106.N0428.N0770.N1725.d024116, _root_.GD.N0106.N0428.N0770.N1725.d024116, _root_.GD.N0106.N0428.N0770.N1725.d024116, _root_.GD.N0106.N0428.N0770.N1725.d024116, _root_.GD.N0106.N0428.N0770.N1725.d024116, _root_.GD.N0106.N0428.N0770.N1725.d024116, _root_.GD.N0106.N0428.N0770.N1725.d024116, _root_.GD.N0106.N0428.N0770.N1725.d024118, _root_.GD.N0106.N0428.N0770.N1725.d024118, _root_.GD.N0106.N0428.N0770.N1725.d024118, _root_.GD.N0106.N0428.N0770.N1725.d024118]

def d024364 (i : Fin 12) : (ℝ × ℝ) → ℝ :=
  _root_.GD.N0106.N0428.N0770.N1725.d024125 (_root_.GD.N0106.N0428.N0770.N1726.d024361 i) (_root_.GD.N0106.N0428.N0770.N1726.d024362 i) (_root_.GD.N0106.N0428.N0770.N1726.d024363 i)


def d024365 (i : Fin 12) : Set (ℝ × ℝ) :=
  Icc (_root_.GD.N0106.N0428.N0770.N1726.d024361 i - _root_.GD.N0106.N0428.N0770.N1726.d024363 i) (_root_.GD.N0106.N0428.N0770.N1726.d024361 i + _root_.GD.N0106.N0428.N0770.N1726.d024363 i) ×ˢ
    Icc (_root_.GD.N0106.N0428.N0770.N1726.d024362 i - _root_.GD.N0106.N0428.N0770.N1726.d024363 i) (_root_.GD.N0106.N0428.N0770.N1726.d024362 i + _root_.GD.N0106.N0428.N0770.N1726.d024363 i)

def d024366 : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioi 0

def d024367 : Fin 12 → ℝ :=
  ![-46233 / 500000, 46233 / 500000,
    294569 / 500000, -294569 / 500000,
    131993 / 1000000, -131993 / 1000000,
    70711 / 1000000, -70711 / 1000000, 0, 0, 0, 0]

def d024368 : Fin 12 → ℝ := ![0, 0, 0, 0, 0, 0, 0, 0, 3, -3, -4, 4]

theorem d024369 (i : Fin 12) : 0 < _root_.GD.N0106.N0428.N0770.N1726.d024363 i := by
  fin_cases i <;> norm_num [_root_.GD.N0106.N0428.N0770.N1726.d024363, _root_.GD.N0106.N0428.N0770.N1725.d024116, _root_.GD.N0106.N0428.N0770.N1725.d024118]

theorem d024370 (i : Fin 12) : _root_.GD.N0106.N0428.N0770.N1726.d024363 i ≤ _root_.GD.N0106.N0428.N0770.N1725.d024116 := by
  fin_cases i <;> norm_num [_root_.GD.N0106.N0428.N0770.N1726.d024363, _root_.GD.N0106.N0428.N0770.N1725.d024116, _root_.GD.N0106.N0428.N0770.N1725.d024118]

theorem d024371 (i : Fin 12) :
    0 < _root_.GD.N0106.N0428.N0770.N1726.d024361 i - _root_.GD.N0106.N0428.N0770.N1726.d024363 i ∧ _root_.GD.N0106.N0428.N0770.N1726.d024361 i + _root_.GD.N0106.N0428.N0770.N1726.d024363 i < 1 ∧
      0 < _root_.GD.N0106.N0428.N0770.N1726.d024362 i - _root_.GD.N0106.N0428.N0770.N1726.d024363 i := by
  fin_cases i <;> norm_num [_root_.GD.N0106.N0428.N0770.N1726.d024361, _root_.GD.N0106.N0428.N0770.N1726.d024360, _root_.GD.N0106.N0428.N0770.N1726.d024362, _root_.GD.N0106.N0428.N0770.N1726.d024363, _root_.GD.N0106.N0428.N0770.N1725.d024116, _root_.GD.N0106.N0428.N0770.N1725.d024118]

theorem d024372 {c w x : ℝ} (hw : 0 < w) :
    _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x ≠ 0 ↔ x ∈ Ioo (c - w) (c + w) := by
  have hpos : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x ↔ |x - c| < w := by
    change 0 < max (1 - |x - c| / w) 0 ↔ |x - c| < w
    rw [lt_max_iff]
    constructor
    · rintro (h | h)
      · have hd := (div_lt_iff₀ hw).mp (by linarith : |x - c| / w < 1)
        simpa only [one_mul] using hd
      · exact False.elim (lt_irrefl _ h)
    · intro h
      left
      have hd : |x - c| / w < 1 :=
        (div_lt_iff₀ hw).mpr (by simpa only [one_mul] using h)
      linarith
  have hn : _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x ≠ 0 ↔ 0 < _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x :=
    ⟨fun h => lt_of_le_of_ne (_root_.GD.N0106.N0428.N0770.N1725.d024139 c w x) (Ne.symm h), ne_of_gt⟩
  rw [hn, hpos, abs_lt]
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hlo, hhi⟩
    exact ⟨by linarith, by linarith⟩

theorem d024373 (i : Fin 12) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1726.d024364 i p ≠ 0 ↔
      p ∈ Ioo (_root_.GD.N0106.N0428.N0770.N1726.d024361 i - _root_.GD.N0106.N0428.N0770.N1726.d024363 i) (_root_.GD.N0106.N0428.N0770.N1726.d024361 i + _root_.GD.N0106.N0428.N0770.N1726.d024363 i) ×ˢ
        Ioo (_root_.GD.N0106.N0428.N0770.N1726.d024362 i - _root_.GD.N0106.N0428.N0770.N1726.d024363 i) (_root_.GD.N0106.N0428.N0770.N1726.d024362 i + _root_.GD.N0106.N0428.N0770.N1726.d024363 i) := by
  simp only [_root_.GD.N0106.N0428.N0770.N1726.d024364, _root_.GD.N0106.N0428.N0770.N1725.d024125, mul_ne_zero_iff, _root_.GD.N0106.N0428.N0770.N1726.d024372 (_root_.GD.N0106.N0428.N0770.N1726.d024369 i),
    Set.mem_prod]

theorem d024374 (i : Fin 12) :
    Function.support (_root_.GD.N0106.N0428.N0770.N1726.d024364 i) =
      Ioo (_root_.GD.N0106.N0428.N0770.N1726.d024361 i - _root_.GD.N0106.N0428.N0770.N1726.d024363 i) (_root_.GD.N0106.N0428.N0770.N1726.d024361 i + _root_.GD.N0106.N0428.N0770.N1726.d024363 i) ×ˢ
        Ioo (_root_.GD.N0106.N0428.N0770.N1726.d024362 i - _root_.GD.N0106.N0428.N0770.N1726.d024363 i) (_root_.GD.N0106.N0428.N0770.N1726.d024362 i + _root_.GD.N0106.N0428.N0770.N1726.d024363 i) := by
  ext p
  exact _root_.GD.N0106.N0428.N0770.N1726.d024373 i p

theorem d024375 (i : Fin 12) : tsupport (_root_.GD.N0106.N0428.N0770.N1726.d024364 i) = _root_.GD.N0106.N0428.N0770.N1726.d024365 i := by
  have hw := _root_.GD.N0106.N0428.N0770.N1726.d024369 i
  have he : _root_.GD.N0106.N0428.N0770.N1726.d024361 i - _root_.GD.N0106.N0428.N0770.N1726.d024363 i ≠ _root_.GD.N0106.N0428.N0770.N1726.d024361 i + _root_.GD.N0106.N0428.N0770.N1726.d024363 i := by linarith
  have hf : _root_.GD.N0106.N0428.N0770.N1726.d024362 i - _root_.GD.N0106.N0428.N0770.N1726.d024363 i ≠ _root_.GD.N0106.N0428.N0770.N1726.d024362 i + _root_.GD.N0106.N0428.N0770.N1726.d024363 i := by linarith
  rw [tsupport, _root_.GD.N0106.N0428.N0770.N1726.d024374, closure_prod_eq, closure_Ioo he, closure_Ioo hf]
  rfl

theorem d024376 (i : Fin 12) : _root_.GD.N0106.N0428.N0770.N1726.d024365 i ⊆ _root_.GD.N0106.N0428.N0770.N1726.d024366 := by
  intro p hp
  obtain ⟨he0, he1, hf0⟩ := _root_.GD.N0106.N0428.N0770.N1726.d024371 i
  rcases hp with ⟨⟨hel, heu⟩, hfl, hfu⟩
  exact ⟨⟨lt_of_lt_of_le he0 hel, lt_of_le_of_lt heu he1⟩,
    lt_of_lt_of_le hf0 hfl⟩

theorem d024377 : ∀ i j : Fin 12, i ≠ j →
    _root_.GD.N0106.N0428.N0770.N1726.d024360 i + 1 ≤ _root_.GD.N0106.N0428.N0770.N1726.d024360 j ∨ _root_.GD.N0106.N0428.N0770.N1726.d024360 j + 1 ≤ _root_.GD.N0106.N0428.N0770.N1726.d024360 i := by
  decide


theorem d024378 (i j : Fin 12) (hij : i ≠ j) :
    Disjoint (_root_.GD.N0106.N0428.N0770.N1726.d024365 i) (_root_.GD.N0106.N0428.N0770.N1726.d024365 j) := by
  apply Set.disjoint_left.mpr
  intro p hi hj
  have hiL := hi.1.1
  have hiU := hi.1.2
  have hjL := hj.1.1
  have hjU := hj.1.2
  have hwi := _root_.GD.N0106.N0428.N0770.N1726.d024370 i
  have hwj := _root_.GD.N0106.N0428.N0770.N1726.d024370 j
  change (_root_.GD.N0106.N0428.N0770.N1726.d024360 i : ℝ) / 6000 - _root_.GD.N0106.N0428.N0770.N1726.d024363 i ≤ p.1 at hiL
  change p.1 ≤ (_root_.GD.N0106.N0428.N0770.N1726.d024360 i : ℝ) / 6000 + _root_.GD.N0106.N0428.N0770.N1726.d024363 i at hiU
  change (_root_.GD.N0106.N0428.N0770.N1726.d024360 j : ℝ) / 6000 - _root_.GD.N0106.N0428.N0770.N1726.d024363 j ≤ p.1 at hjL
  change p.1 ≤ (_root_.GD.N0106.N0428.N0770.N1726.d024360 j : ℝ) / 6000 + _root_.GD.N0106.N0428.N0770.N1726.d024363 j at hjU
  norm_num only [_root_.GD.N0106.N0428.N0770.N1725.d024116] at hwi hwj
  rcases _root_.GD.N0106.N0428.N0770.N1726.d024377 i j hij with hsep | hsep
  · have hs : (_root_.GD.N0106.N0428.N0770.N1726.d024360 i : ℝ) + 1 ≤ (_root_.GD.N0106.N0428.N0770.N1726.d024360 j : ℝ) := by exact_mod_cast hsep
    linarith
  · have hs : (_root_.GD.N0106.N0428.N0770.N1726.d024360 j : ℝ) + 1 ≤ (_root_.GD.N0106.N0428.N0770.N1726.d024360 i : ℝ) := by exact_mod_cast hsep
    linarith

theorem d024379 :
    Pairwise fun i j : Fin 12 => Disjoint (tsupport (_root_.GD.N0106.N0428.N0770.N1726.d024364 i)) (tsupport (_root_.GD.N0106.N0428.N0770.N1726.d024364 j)) := by
  intro i j hij
  simpa only [_root_.GD.N0106.N0428.N0770.N1726.d024375] using _root_.GD.N0106.N0428.N0770.N1726.d024378 i j hij

theorem d024380 (i : Fin 12) : tsupport (_root_.GD.N0106.N0428.N0770.N1726.d024364 i) ⊆ _root_.GD.N0106.N0428.N0770.N1726.d024366 := by
  rw [_root_.GD.N0106.N0428.N0770.N1726.d024375]
  exact _root_.GD.N0106.N0428.N0770.N1726.d024376 i

theorem d024381 (i j : Fin 12) (hij : i ≠ j) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1726.d024364 i p * _root_.GD.N0106.N0428.N0770.N1726.d024364 j p = 0 := by
  by_cases hi : _root_.GD.N0106.N0428.N0770.N1726.d024364 i p = 0
  · simp [hi]
  by_cases hj : _root_.GD.N0106.N0428.N0770.N1726.d024364 j p = 0
  · simp [hj]
  have him : p ∈ _root_.GD.N0106.N0428.N0770.N1726.d024365 i := by
    rw [← _root_.GD.N0106.N0428.N0770.N1726.d024375]
    exact subset_tsupport _ hi
  have hjm : p ∈ _root_.GD.N0106.N0428.N0770.N1726.d024365 j := by
    rw [← _root_.GD.N0106.N0428.N0770.N1726.d024375]
    exact subset_tsupport _ hj
  exact False.elim ((Set.disjoint_left.mp (_root_.GD.N0106.N0428.N0770.N1726.d024378 i j hij)) him hjm)


theorem d024382 (p : ℝ × ℝ) : _root_.GD.N0106.N0428.N0770.N1725.d024130 p = ∑ i : Fin 12, _root_.GD.N0106.N0428.N0770.N1726.d024367 i * _root_.GD.N0106.N0428.N0770.N1726.d024364 i p := by
  rw [_root_.GD.N0106.N0428.N0770.N1725.d024132]
  norm_num [_root_.GD.N0106.N0428.N0770.N1726.d024367, _root_.GD.N0106.N0428.N0770.N1726.d024364, _root_.GD.N0106.N0428.N0770.N1725.d024125, _root_.GD.N0106.N0428.N0770.N1725.d024126, _root_.GD.N0106.N0428.N0770.N1726.d024361, _root_.GD.N0106.N0428.N0770.N1726.d024360, _root_.GD.N0106.N0428.N0770.N1726.d024362,
    _root_.GD.N0106.N0428.N0770.N1726.d024363, Fin.sum_univ_succ]
  <;> ring

theorem d024383 (p : ℝ × ℝ) : _root_.GD.N0106.N0428.N0770.N1725.d024131 p = ∑ i : Fin 12, _root_.GD.N0106.N0428.N0770.N1726.d024368 i * _root_.GD.N0106.N0428.N0770.N1726.d024364 i p := by
  norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024131, _root_.GD.N0106.N0428.N0770.N1726.d024368, _root_.GD.N0106.N0428.N0770.N1726.d024364, _root_.GD.N0106.N0428.N0770.N1725.d024125, _root_.GD.N0106.N0428.N0770.N1725.d024126, _root_.GD.N0106.N0428.N0770.N1726.d024361, _root_.GD.N0106.N0428.N0770.N1726.d024360, _root_.GD.N0106.N0428.N0770.N1726.d024362,
    _root_.GD.N0106.N0428.N0770.N1726.d024363, Fin.sum_univ_succ]
  <;> ring

theorem d024384 (i : Fin 12) : _root_.GD.N0106.N0428.N0770.N1726.d024367 i * _root_.GD.N0106.N0428.N0770.N1726.d024368 i = 0 := by
  fin_cases i <;> norm_num [_root_.GD.N0106.N0428.N0770.N1726.d024367, _root_.GD.N0106.N0428.N0770.N1726.d024368]


theorem d024385 (p : ℝ × ℝ) : _root_.GD.N0106.N0428.N0770.N1725.d024130 p * _root_.GD.N0106.N0428.N0770.N1725.d024131 p = 0 := by
  classical
  rw [_root_.GD.N0106.N0428.N0770.N1726.d024382, _root_.GD.N0106.N0428.N0770.N1726.d024383, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : i = j
  · subst j
    calc
      _ = (_root_.GD.N0106.N0428.N0770.N1726.d024367 i * _root_.GD.N0106.N0428.N0770.N1726.d024368 i) * (_root_.GD.N0106.N0428.N0770.N1726.d024364 i p * _root_.GD.N0106.N0428.N0770.N1726.d024364 i p) := by ring
      _ = 0 := by rw [_root_.GD.N0106.N0428.N0770.N1726.d024384, zero_mul]
  · calc
      _ = (_root_.GD.N0106.N0428.N0770.N1726.d024367 i * _root_.GD.N0106.N0428.N0770.N1726.d024368 j) * (_root_.GD.N0106.N0428.N0770.N1726.d024364 i p * _root_.GD.N0106.N0428.N0770.N1726.d024364 j p) := by ring
      _ = 0 := by rw [_root_.GD.N0106.N0428.N0770.N1726.d024381 i j hij p, mul_zero]

end
end GD.N0106.N0428.N0770.N1726

#print axioms _root_.GD.N0106.N0428.N0770.N1726.d024375
#print axioms _root_.GD.N0106.N0428.N0770.N1726.d024379
#print axioms _root_.GD.N0106.N0428.N0770.N1726.d024380
#print axioms _root_.GD.N0106.N0428.N0770.N1726.d024382
#print axioms _root_.GD.N0106.N0428.N0770.N1726.d024383
#print axioms _root_.GD.N0106.N0428.N0770.N1726.d024385
