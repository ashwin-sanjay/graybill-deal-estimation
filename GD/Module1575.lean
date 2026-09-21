import GD.Module1568
import GD.Module1574











set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open Set
open scoped BigOperators
open _root_.GD.N0232.N0720.N1164
open _root_.GD.N0106.N0428.N0770.N1725
open _root_.GD.N0106.N0428.N0770.N1719
open _root_.GD.N0106.N0428.N0770.N1728

namespace GD.N0106.N0428.N0770.N1727
noncomputable section

def d024419 {ι : Type*} [Fintype ι] (b : ι → _root_.GD.N0232.N0720.N1164.d006809) : _root_.GD.N0232.N0720.N1164.d006809 :=
  ⟨∑ i, (b i).lo, ∑ i, (b i).hi⟩

theorem d024420 {ι : Type*} [Fintype ι] {b : ι → _root_.GD.N0232.N0720.N1164.d006809}
    {v : ι → ℝ} (h : ∀ i, (b i).d006810 (v i)) :
    (_root_.GD.N0106.N0428.N0770.N1727.d024419 b).d006810 (∑ i, v i) := by
  constructor
  · change ((∑ i, (b i).lo : ℚ) : ℝ) ≤ _
    push_cast
    exact Finset.sum_le_sum (fun i _ => (h i).1)
  · change _ ≤ ((∑ i, (b i).hi : ℚ) : ℝ)
    push_cast
    exact Finset.sum_le_sum (fun i _ => (h i).2)



def d024421 (I : _root_.GD.N0232.N0720.N1164.d006809) (e c sign m : ℚ) : _root_.GD.N0232.N0720.N1164.d006809 :=
  (((_root_.GD.N0106.N0428.N0770.N1719.d024260 e).d006813 I).d006817 (2 * sign * c)).d006812
    (_root_.GD.N0106.N0428.N0770.N1719.d024260 ((4 / 9) * m * (1 / 250) * c * c))

theorem d024422 {I : _root_.GD.N0232.N0720.N1164.d006809} {q : ℝ}
    (e c sign m : ℚ) (hq : I.d006810 q) :
    (_root_.GD.N0106.N0428.N0770.N1727.d024421 I e c sign m).d006810
      (_root_.GD.N0106.N0428.N0770.N1728.d024394 (m : ℝ) q (e : ℝ) (c : ℝ) (sign : ℝ)) := by
  have hdiff := _root_.GD.N0232.N0720.N1164.d006809.d006820 (_root_.GD.N0106.N0428.N0770.N1719.d024262 e) hq
  have hlinear := _root_.GD.N0232.N0720.N1164.d006809.d006824 (2 * sign * c) hdiff
  have hs := _root_.GD.N0232.N0720.N1164.d006809.d006819 hlinear
    (_root_.GD.N0106.N0428.N0770.N1719.d024262 ((4 / 9) * m * (1 / 250) * c * c))
  have heq : ((2 * sign * c : ℚ) : ℝ) * ((e : ℝ) - q) +
      (((4 / 9) * m * (1 / 250) * c * c : ℚ) : ℝ) =
      _root_.GD.N0106.N0428.N0770.N1728.d024394 (m : ℝ) q (e : ℝ) (c : ℝ) (sign : ℝ) := by
    norm_num [_root_.GD.N0106.N0428.N0770.N1728.d024394, _root_.GD.N0106.N0428.N0770.N1725.d024117]
  simpa only [_root_.GD.N0106.N0428.N0770.N1727.d024421, heq] using hs

def d024423 (I : _root_.GD.N0232.N0720.N1164.d006809) (e F c sign m : ℚ) (R : _root_.GD.N0106.N0428.N0770.N1719.d024281) : _root_.GD.N0232.N0720.N1164.d006809 :=
  (_root_.GD.N0106.N0428.N0770.N1727.d024421 I e c sign m).d006816
    (_root_.GD.N0106.N0428.N0770.N1719.d024283 (_root_.GD.N0106.N0428.N0770.N1719.d024266 I e F) R)

theorem d024424 {I : _root_.GD.N0232.N0720.N1164.d006809} {q : ℝ}
    (e F c sign m : ℚ) (hq : q ∈ Icc (0 : ℝ) 1) (hI : I.d006810 q)
    (he0 : 0 < e) (he1 : e < 1) (hf : 0 < F)
    {R : _root_.GD.N0106.N0428.N0770.N1719.d024281} (hR : R.d024282 (_root_.GD.N0106.N0428.N0770.N1719.d024266 I e F)
      (_root_.GD.N0106.N0428.N0770.N1719.d024260 (F / (e * (1 - e))))) :
    (_root_.GD.N0106.N0428.N0770.N1727.d024423 I e F c sign m R).d006810
      (_root_.GD.N0106.N0428.N0770.N1728.d024395 (m : ℝ) q (e : ℝ) (F : ℝ) (c : ℝ) (sign : ℝ)) := by
  exact _root_.GD.N0232.N0720.N1164.d006809.d006823 (_root_.GD.N0106.N0428.N0770.N1719.d024284 hR)
    (_root_.GD.N0106.N0428.N0770.N1727.d024422 e c sign m hI)
    (_root_.GD.N0106.N0428.N0770.N1719.d024287 e F hq hI he0 he1 hf hR)

def d024425 : Fin 4 → ℚ := ![1 / 20, 3 / 20, 1 / 50, 1 / 10]
def d024426 : Fin 4 → ℚ := ![2, 1 / 50, 1 / 50, 1 / 50]
def d024427 : Fin 4 → ℚ :=
  ![-46233 / 500000, 294569 / 500000, 131993 / 1000000, 70711 / 1000000]
def d024428 : Fin 2 → ℚ := ![1, -1]
def d024429 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : ℚ :=
  (![_root_.GD.N0106.N0428.N0770.N1727.d024425 i.1, 1 - _root_.GD.N0106.N0428.N0770.N1727.d024425 i.1] : Fin 2 → ℚ) i.2
def d024430 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : ℚ := _root_.GD.N0106.N0428.N0770.N1727.d024426 i.1

theorem d024431 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) :
    (_root_.GD.N0106.N0428.N0770.N1727.d024429 i : ℝ) = _root_.GD.N0106.N0428.N0770.N1728.d024388 (_root_.GD.N0106.N0428.N0770.N1725.d024127 i.1) i.2 ∧
    (_root_.GD.N0106.N0428.N0770.N1727.d024430 i : ℝ) = _root_.GD.N0106.N0428.N0770.N1725.d024128 i.1 ∧
    (_root_.GD.N0106.N0428.N0770.N1727.d024427 i.1 : ℝ) = _root_.GD.N0106.N0428.N0770.N1725.d024129 i.1 ∧
    (_root_.GD.N0106.N0428.N0770.N1727.d024428 i.2 : ℝ) = _root_.GD.N0106.N0428.N0770.N1728.d024387 i.2 := by
  rcases i with ⟨r, s⟩
  fin_cases r <;> fin_cases s <;>
    norm_num [_root_.GD.N0106.N0428.N0770.N1727.d024429, _root_.GD.N0106.N0428.N0770.N1727.d024430, _root_.GD.N0106.N0428.N0770.N1727.d024425, _root_.GD.N0106.N0428.N0770.N1727.d024426,
      _root_.GD.N0106.N0428.N0770.N1727.d024427, _root_.GD.N0106.N0428.N0770.N1727.d024428, _root_.GD.N0106.N0428.N0770.N1728.d024388, _root_.GD.N0106.N0428.N0770.N1728.d024387,
      _root_.GD.N0106.N0428.N0770.N1725.d024127, _root_.GD.N0106.N0428.N0770.N1725.d024128, _root_.GD.N0106.N0428.N0770.N1725.d024129]

theorem d024432 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) :
    0 < _root_.GD.N0106.N0428.N0770.N1727.d024429 i ∧ _root_.GD.N0106.N0428.N0770.N1727.d024429 i < 1 ∧ 0 < _root_.GD.N0106.N0428.N0770.N1727.d024430 i := by
  rcases i with ⟨r, s⟩
  fin_cases r <;> fin_cases s <;>
    norm_num [_root_.GD.N0106.N0428.N0770.N1727.d024429, _root_.GD.N0106.N0428.N0770.N1727.d024430, _root_.GD.N0106.N0428.N0770.N1727.d024425, _root_.GD.N0106.N0428.N0770.N1727.d024426]

def d024433 (I : _root_.GD.N0232.N0720.N1164.d006809) (m : ℚ) (R : _root_.GD.N0106.N0428.N0770.N1728.d024386 → _root_.GD.N0106.N0428.N0770.N1719.d024281) : _root_.GD.N0232.N0720.N1164.d006809 :=
  _root_.GD.N0106.N0428.N0770.N1727.d024419 fun i => _root_.GD.N0106.N0428.N0770.N1727.d024423 I (_root_.GD.N0106.N0428.N0770.N1727.d024429 i) (_root_.GD.N0106.N0428.N0770.N1727.d024430 i)
    (_root_.GD.N0106.N0428.N0770.N1727.d024427 i.1) (_root_.GD.N0106.N0428.N0770.N1727.d024428 i.2) m (R i)

theorem d024434 {I : _root_.GD.N0232.N0720.N1164.d006809} {q : ℝ} (m : ℚ)
    (hq : q ∈ Icc (0 : ℝ) 1) (hI : I.d006810 q) {R : _root_.GD.N0106.N0428.N0770.N1728.d024386 → _root_.GD.N0106.N0428.N0770.N1719.d024281}
    (hR : ∀ i, (R i).d024282 (_root_.GD.N0106.N0428.N0770.N1719.d024266 I (_root_.GD.N0106.N0428.N0770.N1727.d024429 i) (_root_.GD.N0106.N0428.N0770.N1727.d024430 i))
      (_root_.GD.N0106.N0428.N0770.N1719.d024260 (_root_.GD.N0106.N0428.N0770.N1727.d024430 i / (_root_.GD.N0106.N0428.N0770.N1727.d024429 i * (1 - _root_.GD.N0106.N0428.N0770.N1727.d024429 i))))) :
    (_root_.GD.N0106.N0428.N0770.N1727.d024433 I m R).d006810 (_root_.GD.N0106.N0428.N0770.N1728.d024396 (m : ℝ) q) := by
  have hs := _root_.GD.N0106.N0428.N0770.N1727.d024420 (fun i : _root_.GD.N0106.N0428.N0770.N1728.d024386 =>
    _root_.GD.N0106.N0428.N0770.N1727.d024424 (_root_.GD.N0106.N0428.N0770.N1727.d024429 i) (_root_.GD.N0106.N0428.N0770.N1727.d024430 i)
      (_root_.GD.N0106.N0428.N0770.N1727.d024427 i.1) (_root_.GD.N0106.N0428.N0770.N1727.d024428 i.2) m hq hI
      (_root_.GD.N0106.N0428.N0770.N1727.d024432 i).1 (_root_.GD.N0106.N0428.N0770.N1727.d024432 i).2.1
      (_root_.GD.N0106.N0428.N0770.N1727.d024432 i).2.2 (hR i))
  have heq : (∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386,
      _root_.GD.N0106.N0428.N0770.N1728.d024395 (m : ℝ) q (_root_.GD.N0106.N0428.N0770.N1727.d024429 i : ℝ) (_root_.GD.N0106.N0428.N0770.N1727.d024430 i : ℝ)
        (_root_.GD.N0106.N0428.N0770.N1727.d024427 i.1 : ℝ) (_root_.GD.N0106.N0428.N0770.N1727.d024428 i.2 : ℝ)) =
      _root_.GD.N0106.N0428.N0770.N1728.d024396 (m : ℝ) q := by
    calc
      _ = ∑ i : _root_.GD.N0106.N0428.N0770.N1728.d024386,
          _root_.GD.N0106.N0428.N0770.N1728.d024395 (m : ℝ) q (_root_.GD.N0106.N0428.N0770.N1728.d024388 (_root_.GD.N0106.N0428.N0770.N1725.d024127 i.1) i.2)
            (_root_.GD.N0106.N0428.N0770.N1725.d024128 i.1) (_root_.GD.N0106.N0428.N0770.N1725.d024129 i.1) (_root_.GD.N0106.N0428.N0770.N1728.d024387 i.2) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [(_root_.GD.N0106.N0428.N0770.N1727.d024431 i).1, (_root_.GD.N0106.N0428.N0770.N1727.d024431 i).2.1,
          (_root_.GD.N0106.N0428.N0770.N1727.d024431 i).2.2.1, (_root_.GD.N0106.N0428.N0770.N1727.d024431 i).2.2.2]
      _ = _root_.GD.N0106.N0428.N0770.N1728.d024396 (m : ℝ) q := by
        simp only [_root_.GD.N0106.N0428.N0770.N1728.d024396, Fintype.sum_prod_type]
  simpa only [_root_.GD.N0106.N0428.N0770.N1727.d024433, heq] using hs

theorem d024435 {I : _root_.GD.N0232.N0720.N1164.d006809} {q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (hI : I.d006810 q) {R : _root_.GD.N0106.N0428.N0770.N1728.d024386 → _root_.GD.N0106.N0428.N0770.N1719.d024281}
    (hR : ∀ i, (R i).d024282 (_root_.GD.N0106.N0428.N0770.N1719.d024266 I (_root_.GD.N0106.N0428.N0770.N1727.d024429 i) (_root_.GD.N0106.N0428.N0770.N1727.d024430 i))
      (_root_.GD.N0106.N0428.N0770.N1719.d024260 (_root_.GD.N0106.N0428.N0770.N1727.d024430 i / (_root_.GD.N0106.N0428.N0770.N1727.d024429 i * (1 - _root_.GD.N0106.N0428.N0770.N1727.d024429 i))))) :
    (_root_.GD.N0106.N0428.N0770.N1727.d024433 I 1 R).d006810 (_root_.GD.N0106.N0428.N0770.N1728.d024397 q) := by
  simpa only [Rat.cast_one, _root_.GD.N0106.N0428.N0770.N1728.d024397] using _root_.GD.N0106.N0428.N0770.N1727.d024434 1 hq hI hR

theorem d024436 {I : _root_.GD.N0232.N0720.N1164.d006809} {q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (hI : I.d006810 q) {R : _root_.GD.N0106.N0428.N0770.N1728.d024386 → _root_.GD.N0106.N0428.N0770.N1719.d024281}
    (hR : ∀ i, (R i).d024282 (_root_.GD.N0106.N0428.N0770.N1719.d024266 I (_root_.GD.N0106.N0428.N0770.N1727.d024429 i) (_root_.GD.N0106.N0428.N0770.N1727.d024430 i))
      (_root_.GD.N0106.N0428.N0770.N1719.d024260 (_root_.GD.N0106.N0428.N0770.N1727.d024430 i / (_root_.GD.N0106.N0428.N0770.N1727.d024429 i * (1 - _root_.GD.N0106.N0428.N0770.N1727.d024429 i))))) :
    (_root_.GD.N0106.N0428.N0770.N1727.d024433 I 3 R).d006810 (_root_.GD.N0106.N0428.N0770.N1728.d024398 q) := by
  simpa only [Rat.cast_ofNat, _root_.GD.N0106.N0428.N0770.N1728.d024398] using _root_.GD.N0106.N0428.N0770.N1727.d024434 3 hq hI hR



def d024437 (q e F : ℝ) : ℝ :=
  (e - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) + (q + e - 1) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 - e, F)

def d024438 (q e F : ℝ) : ℝ := _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) + _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 - e, F)


def d024439 (q ea Fa eb Fb : ℝ) : ℝ :=
  4 * _root_.GD.N0106.N0428.N0770.N1727.d024437 q eb Fb - 3 * _root_.GD.N0106.N0428.N0770.N1727.d024437 q ea Fa -
    (_root_.GD.N0106.N0428.N0770.N1725.d024119 / 2) * (9 * _root_.GD.N0106.N0428.N0770.N1727.d024438 q ea Fa + 16 * _root_.GD.N0106.N0428.N0770.N1727.d024438 q eb Fb) -
    (1 / 1000) * (_root_.GD.N0106.N0428.N0770.N1727.d024438 q ea Fa + _root_.GD.N0106.N0428.N0770.N1727.d024438 q eb Fb)

def d024440 (q ea eb : ℝ) : Fin 4 → ℝ :=
  ![3 * (q - ea) - ((9 / 2) * _root_.GD.N0106.N0428.N0770.N1725.d024119 + 1 / 1000),
    3 * (1 - ea - q) - ((9 / 2) * _root_.GD.N0106.N0428.N0770.N1725.d024119 + 1 / 1000),
    4 * (eb - q) - (8 * _root_.GD.N0106.N0428.N0770.N1725.d024119 + 1 / 1000),
    4 * (q + eb - 1) - (8 * _root_.GD.N0106.N0428.N0770.N1725.d024119 + 1 / 1000)]

def d024441 (I EA EB : _root_.GD.N0232.N0720.N1164.d006809) : Fin 4 → _root_.GD.N0232.N0720.N1164.d006809 :=
  ![((I.d006813 EA).d006817 3).d006813 (_root_.GD.N0106.N0428.N0770.N1719.d024260 ((9 / 2) * (1 / 10000) + 1 / 1000)),
    (((_root_.GD.N0106.N0428.N0770.N1719.d024261 EA).d006813 I).d006817 3).d006813
      (_root_.GD.N0106.N0428.N0770.N1719.d024260 ((9 / 2) * (1 / 10000) + 1 / 1000)),
    ((EB.d006813 I).d006817 4).d006813 (_root_.GD.N0106.N0428.N0770.N1719.d024260 (8 * (1 / 10000) + 1 / 1000)),
    (((I.d006812 EB).d006813 _root_.GD.N0232.N0720.N1164.d006809.d006811).d006817 4).d006813
      (_root_.GD.N0106.N0428.N0770.N1719.d024260 (8 * (1 / 10000) + 1 / 1000))]

theorem d024442 {I EA EB : _root_.GD.N0232.N0720.N1164.d006809}
    {q ea eb : ℝ} (hq : I.d006810 q) (ha : EA.d006810 ea) (hb : EB.d006810 eb)
    (j : Fin 4) :
    (_root_.GD.N0106.N0428.N0770.N1727.d024441 I EA EB j).d006810 (_root_.GD.N0106.N0428.N0770.N1727.d024440 q ea eb j) := by
  fin_cases j
  · have h := _root_.GD.N0232.N0720.N1164.d006809.d006820
      (_root_.GD.N0232.N0720.N1164.d006809.d006824 3 (_root_.GD.N0232.N0720.N1164.d006809.d006820 hq ha))
      (_root_.GD.N0106.N0428.N0770.N1719.d024262 ((9 / 2) * (1 / 10000) + 1 / 1000))
    simpa [_root_.GD.N0106.N0428.N0770.N1727.d024441, _root_.GD.N0106.N0428.N0770.N1727.d024440, _root_.GD.N0106.N0428.N0770.N1725.d024119] using h
  · have h := _root_.GD.N0232.N0720.N1164.d006809.d006820
      (_root_.GD.N0232.N0720.N1164.d006809.d006824 3 (_root_.GD.N0232.N0720.N1164.d006809.d006820 (_root_.GD.N0106.N0428.N0770.N1719.d024263 ha) hq))
      (_root_.GD.N0106.N0428.N0770.N1719.d024262 ((9 / 2) * (1 / 10000) + 1 / 1000))
    simpa [_root_.GD.N0106.N0428.N0770.N1727.d024441, _root_.GD.N0106.N0428.N0770.N1727.d024440, _root_.GD.N0106.N0428.N0770.N1725.d024119] using h
  · have h := _root_.GD.N0232.N0720.N1164.d006809.d006820
      (_root_.GD.N0232.N0720.N1164.d006809.d006824 4 (_root_.GD.N0232.N0720.N1164.d006809.d006820 hb hq))
      (_root_.GD.N0106.N0428.N0770.N1719.d024262 (8 * (1 / 10000) + 1 / 1000))
    simpa [_root_.GD.N0106.N0428.N0770.N1727.d024441, _root_.GD.N0106.N0428.N0770.N1727.d024440, _root_.GD.N0106.N0428.N0770.N1725.d024119] using h
  · have h := _root_.GD.N0232.N0720.N1164.d006809.d006820
      (_root_.GD.N0232.N0720.N1164.d006809.d006824 4 (_root_.GD.N0232.N0720.N1164.d006809.d006820
        (_root_.GD.N0232.N0720.N1164.d006809.d006819 hq hb) _root_.GD.N0232.N0720.N1164.d006809.d006818))
      (_root_.GD.N0106.N0428.N0770.N1719.d024262 (8 * (1 / 10000) + 1 / 1000))
    simpa [_root_.GD.N0106.N0428.N0770.N1727.d024441, _root_.GD.N0106.N0428.N0770.N1727.d024440, _root_.GD.N0106.N0428.N0770.N1725.d024119] using h

def d024443 (I EA FA EB FB : _root_.GD.N0232.N0720.N1164.d006809) : Fin 4 → _root_.GD.N0106.N0428.N0770.N1719.d024274 :=
  ![⟨I, EA, FA⟩, ⟨I, _root_.GD.N0106.N0428.N0770.N1719.d024261 EA, FA⟩,
    ⟨I, EB, FB⟩, ⟨I, _root_.GD.N0106.N0428.N0770.N1719.d024261 EB, FB⟩]

def d024444 (q ea Fa eb Fb : ℝ) : Fin 4 → ℝ :=
  ![_root_.GD.N0106.N0428.N0770.N1725.d024170 q (ea, Fa), _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 - ea, Fa), _root_.GD.N0106.N0428.N0770.N1725.d024170 q (eb, Fb), _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 - eb, Fb)]

theorem d024445 {I EA FA EB FB : _root_.GD.N0232.N0720.N1164.d006809}
    (hD : ∀ j, (_root_.GD.N0106.N0428.N0770.N1727.d024443 I EA FA EB FB j).d024275)
    {R : Fin 4 → _root_.GD.N0106.N0428.N0770.N1719.d024281}
    (hR : ∀ j, (R j).d024282 (_root_.GD.N0106.N0428.N0770.N1719.d024276 (_root_.GD.N0106.N0428.N0770.N1727.d024443 I EA FA EB FB j))
      (_root_.GD.N0106.N0428.N0770.N1719.d024277 (_root_.GD.N0106.N0428.N0770.N1727.d024443 I EA FA EB FB j)))
    {q ea Fa eb Fb : ℝ} (hq : I.d006810 q) (hea : EA.d006810 ea)
    (hFa : FA.d006810 Fa) (heb : EB.d006810 eb) (hFb : FB.d006810 Fb)
    (j : Fin 4) :
    (_root_.GD.N0106.N0428.N0770.N1719.d024283 (_root_.GD.N0106.N0428.N0770.N1719.d024276 (_root_.GD.N0106.N0428.N0770.N1727.d024443 I EA FA EB FB j)) (R j)).d006810
      (_root_.GD.N0106.N0428.N0770.N1727.d024444 q ea Fa eb Fb j) := by
  fin_cases j
  · exact _root_.GD.N0106.N0428.N0770.N1719.d024286 (hD 0) (hR 0) hq hea hFa
  · exact _root_.GD.N0106.N0428.N0770.N1719.d024286 (hD 1) (hR 1) hq (_root_.GD.N0106.N0428.N0770.N1719.d024263 hea) hFa
  · exact _root_.GD.N0106.N0428.N0770.N1719.d024286 (hD 2) (hR 2) hq heb hFb
  · exact _root_.GD.N0106.N0428.N0770.N1719.d024286 (hD 3) (hR 3) hq (_root_.GD.N0106.N0428.N0770.N1719.d024263 heb) hFb

theorem d024446 (q ea Fa eb Fb : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1727.d024439 q ea Fa eb Fb =
      ∑ j : Fin 4, _root_.GD.N0106.N0428.N0770.N1727.d024440 q ea eb j * _root_.GD.N0106.N0428.N0770.N1727.d024444 q ea Fa eb Fb j := by
  simp [Fin.sum_univ_succ, _root_.GD.N0106.N0428.N0770.N1727.d024439, _root_.GD.N0106.N0428.N0770.N1727.d024437, _root_.GD.N0106.N0428.N0770.N1727.d024438,
    _root_.GD.N0106.N0428.N0770.N1727.d024440, _root_.GD.N0106.N0428.N0770.N1727.d024444]
  <;> ring

def d024447 (I EA FA EB FB : _root_.GD.N0232.N0720.N1164.d006809) (R : Fin 4 → _root_.GD.N0106.N0428.N0770.N1719.d024281) : _root_.GD.N0232.N0720.N1164.d006809 :=
  _root_.GD.N0106.N0428.N0770.N1727.d024419 fun j => (_root_.GD.N0106.N0428.N0770.N1727.d024441 I EA EB j).d006816
    (_root_.GD.N0106.N0428.N0770.N1719.d024283 (_root_.GD.N0106.N0428.N0770.N1719.d024276 (_root_.GD.N0106.N0428.N0770.N1727.d024443 I EA FA EB FB j)) (R j))

theorem d024448 {I EA FA EB FB : _root_.GD.N0232.N0720.N1164.d006809}
    (hD : ∀ j, (_root_.GD.N0106.N0428.N0770.N1727.d024443 I EA FA EB FB j).d024275)
    {R : Fin 4 → _root_.GD.N0106.N0428.N0770.N1719.d024281}
    (hR : ∀ j, (R j).d024282 (_root_.GD.N0106.N0428.N0770.N1719.d024276 (_root_.GD.N0106.N0428.N0770.N1727.d024443 I EA FA EB FB j))
      (_root_.GD.N0106.N0428.N0770.N1719.d024277 (_root_.GD.N0106.N0428.N0770.N1727.d024443 I EA FA EB FB j)))
    {q ea Fa eb Fb : ℝ} (hq : I.d006810 q) (hea : EA.d006810 ea)
    (hFa : FA.d006810 Fa) (heb : EB.d006810 eb) (hFb : FB.d006810 Fb) :
    (_root_.GD.N0106.N0428.N0770.N1727.d024447 I EA FA EB FB R).d006810 (_root_.GD.N0106.N0428.N0770.N1727.d024439 q ea Fa eb Fb) := by
  have hs := _root_.GD.N0106.N0428.N0770.N1727.d024420 (fun j : Fin 4 =>
    _root_.GD.N0232.N0720.N1164.d006809.d006823 (_root_.GD.N0106.N0428.N0770.N1719.d024284 (hR j))
      (_root_.GD.N0106.N0428.N0770.N1727.d024442 hq hea heb j)
      (_root_.GD.N0106.N0428.N0770.N1727.d024445 hD hR hq hea hFa heb hFb j))
  simpa only [_root_.GD.N0106.N0428.N0770.N1727.d024447, _root_.GD.N0106.N0428.N0770.N1727.d024446] using hs



def d024449 : ℚ := 1 / 10 ^ 12
def d024450 : _root_.GD.N0232.N0720.N1164.d006809 := ⟨1 / 500 - _root_.GD.N0106.N0428.N0770.N1727.d024449, 1 / 500 + _root_.GD.N0106.N0428.N0770.N1727.d024449⟩
def d024451 : _root_.GD.N0232.N0720.N1164.d006809 := ⟨1 / 1000 - _root_.GD.N0106.N0428.N0770.N1727.d024449, 1 / 1000 + _root_.GD.N0106.N0428.N0770.N1727.d024449⟩
def d024452 : _root_.GD.N0232.N0720.N1164.d006809 := ⟨1 / 120 - _root_.GD.N0106.N0428.N0770.N1727.d024449, 1 / 120 + _root_.GD.N0106.N0428.N0770.N1727.d024449⟩
def d024453 : _root_.GD.N0232.N0720.N1164.d006809 := ⟨20 - _root_.GD.N0106.N0428.N0770.N1727.d024449, 20 + _root_.GD.N0106.N0428.N0770.N1727.d024449⟩

theorem d024454 : (_root_.GD.N0106.N0428.N0770.N1727.d024449 : ℝ) = _root_.GD.N0106.N0428.N0770.N1725.d024118 := by
  norm_num [_root_.GD.N0106.N0428.N0770.N1727.d024449, _root_.GD.N0106.N0428.N0770.N1725.d024118]

theorem d024455 {I : _root_.GD.N0232.N0720.N1164.d006809}
    (hlo : 0 ≤ I.lo) (horder : I.lo ≤ I.hi) (hhi : I.hi ≤ 1 / 2) (j : Fin 4) :
    (_root_.GD.N0106.N0428.N0770.N1727.d024443 I _root_.GD.N0106.N0428.N0770.N1727.d024450 _root_.GD.N0106.N0428.N0770.N1727.d024451 _root_.GD.N0106.N0428.N0770.N1727.d024452 _root_.GD.N0106.N0428.N0770.N1727.d024453 j).d024275 := by
  fin_cases j <;> constructor
  all_goals first
    | exact hlo
    | exact horder
    | exact hhi
    | norm_num [_root_.GD.N0106.N0428.N0770.N1727.d024443, _root_.GD.N0106.N0428.N0770.N1727.d024450, _root_.GD.N0106.N0428.N0770.N1727.d024451, _root_.GD.N0106.N0428.N0770.N1727.d024452, _root_.GD.N0106.N0428.N0770.N1727.d024453,
        _root_.GD.N0106.N0428.N0770.N1719.d024261, _root_.GD.N0106.N0428.N0770.N1727.d024449, _root_.GD.N0232.N0720.N1164.d006809.d006811, _root_.GD.N0232.N0720.N1164.d006809.d006813]

theorem d024456 {ea Fa eb Fb : ℝ}
    (hea : ea ∈ Icc (1 / 500 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (1 / 500 + _root_.GD.N0106.N0428.N0770.N1725.d024118))
    (hFa : Fa ∈ Icc (1 / 1000 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (1 / 1000 + _root_.GD.N0106.N0428.N0770.N1725.d024118))
    (heb : eb ∈ Icc (1 / 120 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (1 / 120 + _root_.GD.N0106.N0428.N0770.N1725.d024118))
    (hFb : Fb ∈ Icc (20 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (20 + _root_.GD.N0106.N0428.N0770.N1725.d024118)) :
    _root_.GD.N0106.N0428.N0770.N1727.d024450.d006810 ea ∧ _root_.GD.N0106.N0428.N0770.N1727.d024451.d006810 Fa ∧
      _root_.GD.N0106.N0428.N0770.N1727.d024452.d006810 eb ∧ _root_.GD.N0106.N0428.N0770.N1727.d024453.d006810 Fb := by
  norm_num [_root_.GD.N0106.N0428.N0770.N1727.d024450, _root_.GD.N0106.N0428.N0770.N1727.d024451, _root_.GD.N0106.N0428.N0770.N1727.d024452, _root_.GD.N0106.N0428.N0770.N1727.d024453, _root_.GD.N0232.N0720.N1164.d006809.d006810,
    _root_.GD.N0106.N0428.N0770.N1727.d024449, _root_.GD.N0106.N0428.N0770.N1725.d024118, Set.mem_Icc] at hea hFa heb hFb ⊢
  exact ⟨hea, hFa, heb, hFb⟩



theorem d024457 {I : _root_.GD.N0232.N0720.N1164.d006809}
    (hlo : 0 ≤ I.lo) (horder : I.lo ≤ I.hi) (hhi : I.hi ≤ 1 / 2)
    {R : Fin 4 → _root_.GD.N0106.N0428.N0770.N1719.d024281}
    (hR : ∀ j, (R j).d024282
      (_root_.GD.N0106.N0428.N0770.N1719.d024276 (_root_.GD.N0106.N0428.N0770.N1727.d024443 I _root_.GD.N0106.N0428.N0770.N1727.d024450 _root_.GD.N0106.N0428.N0770.N1727.d024451 _root_.GD.N0106.N0428.N0770.N1727.d024452 _root_.GD.N0106.N0428.N0770.N1727.d024453 j))
      (_root_.GD.N0106.N0428.N0770.N1719.d024277 (_root_.GD.N0106.N0428.N0770.N1727.d024443 I _root_.GD.N0106.N0428.N0770.N1727.d024450 _root_.GD.N0106.N0428.N0770.N1727.d024451 _root_.GD.N0106.N0428.N0770.N1727.d024452 _root_.GD.N0106.N0428.N0770.N1727.d024453 j)))
    {q ea Fa eb Fb : ℝ} (hq : I.d006810 q)
    (hea : ea ∈ Icc (1 / 500 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (1 / 500 + _root_.GD.N0106.N0428.N0770.N1725.d024118))
    (hFa : Fa ∈ Icc (1 / 1000 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (1 / 1000 + _root_.GD.N0106.N0428.N0770.N1725.d024118))
    (heb : eb ∈ Icc (1 / 120 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (1 / 120 + _root_.GD.N0106.N0428.N0770.N1725.d024118))
    (hFb : Fb ∈ Icc (20 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (20 + _root_.GD.N0106.N0428.N0770.N1725.d024118)) :
    (_root_.GD.N0106.N0428.N0770.N1727.d024447 I _root_.GD.N0106.N0428.N0770.N1727.d024450 _root_.GD.N0106.N0428.N0770.N1727.d024451 _root_.GD.N0106.N0428.N0770.N1727.d024452 _root_.GD.N0106.N0428.N0770.N1727.d024453 R).d006810
      (_root_.GD.N0106.N0428.N0770.N1727.d024439 q ea Fa eb Fb) := by
  have hs := _root_.GD.N0106.N0428.N0770.N1727.d024456 hea hFa heb hFb
  exact _root_.GD.N0106.N0428.N0770.N1727.d024448 (_root_.GD.N0106.N0428.N0770.N1727.d024455 hlo horder hhi) hR hq
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2

end
end GD.N0106.N0428.N0770.N1727

#print axioms _root_.GD.N0106.N0428.N0770.N1727.d024420
#print axioms _root_.GD.N0106.N0428.N0770.N1727.d024422
#print axioms _root_.GD.N0106.N0428.N0770.N1727.d024424
#print axioms _root_.GD.N0106.N0428.N0770.N1727.d024431
#print axioms _root_.GD.N0106.N0428.N0770.N1727.d024432
#print axioms _root_.GD.N0106.N0428.N0770.N1727.d024434
#print axioms _root_.GD.N0106.N0428.N0770.N1727.d024435
#print axioms _root_.GD.N0106.N0428.N0770.N1727.d024436
#print axioms _root_.GD.N0106.N0428.N0770.N1727.d024442
#print axioms _root_.GD.N0106.N0428.N0770.N1727.d024445
#print axioms _root_.GD.N0106.N0428.N0770.N1727.d024446
#print axioms _root_.GD.N0106.N0428.N0770.N1727.d024448
#print axioms _root_.GD.N0106.N0428.N0770.N1727.d024454
#print axioms _root_.GD.N0106.N0428.N0770.N1727.d024455
#print axioms _root_.GD.N0106.N0428.N0770.N1727.d024456
#print axioms _root_.GD.N0106.N0428.N0770.N1727.d024457
