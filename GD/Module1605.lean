import GD.Module1575
























set_option autoImplicit false
set_option warningAsError true

open Set
open _root_.GD.N0232.N0720.N1164
open _root_.GD.N0106.N0428.N0770.N1725
open _root_.GD.N0106.N0428.N0770.N1719
open _root_.GD.N0106.N0428.N0770.N1728
open _root_.GD.N0106.N0428.N0770.N1727

namespace GD.N0106.N0428.N0770.N1708
noncomputable section


def d027367 : ℚ := 1 / 362


def d027368 : _root_.GD.N0232.N0720.N1164.d006809 := _root_.GD.N0106.N0428.N0770.N1719.d024260 _root_.GD.N0106.N0428.N0770.N1708.d027367


def d027369 : ℚ := 7403 / 10000




def d027370 : Fin 4 → Fin 2 → _root_.GD.N0106.N0428.N0770.N1719.d024281 :=
  ![![⟨⟨162221421 / 25000000, 129777137 / 20000000⟩, ⟨12041157 / 50000000, 4816463 / 20000000⟩⟩,
      ⟨⟨162221421 / 25000000, 129777137 / 20000000⟩, ⟨48811459 / 50000000, 97622919 / 100000000⟩⟩],
    ![⟨⟨39605901 / 100000000, 19802951 / 50000000⟩, ⟨1949287 / 5000000, 38985741 / 100000000⟩⟩,
      ⟨⟨39605901 / 100000000, 19802951 / 50000000⟩, ⟨46046753 / 50000000, 92093507 / 100000000⟩⟩],
    ![⟨⟨50507627 / 50000000, 20203051 / 20000000⟩, ⟨15068851 / 100000000, 3767213 / 25000000⟩⟩,
      ⟨⟨50507627 / 50000000, 20203051 / 20000000⟩, ⟨49431851 / 50000000, 98863703 / 100000000⟩⟩],
    ![⟨⟨11785113 / 25000000, 47140453 / 100000000⟩, ⟨6395781 / 20000000, 15989453 / 50000000⟩⟩,
      ⟨⟨11785113 / 25000000, 47140453 / 100000000⟩, ⟨94754691 / 100000000, 23688673 / 25000000⟩⟩]]


def d027371 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : _root_.GD.N0106.N0428.N0770.N1719.d024281 := _root_.GD.N0106.N0428.N0770.N1708.d027370 i.1 i.2


def d027372 : List _root_.GD.N0106.N0428.N0770.N1728.d024386 :=
  [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1)]


theorem d027373 : ∀ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, i ∈ _root_.GD.N0106.N0428.N0770.N1708.d027372 := by
  first
  | decide +kernel
  | (rintro ⟨r, s⟩; fin_cases r <;> fin_cases s <;> decide +kernel)
  | (rintro ⟨r, s⟩; fin_cases r <;> fin_cases s <;> simp [_root_.GD.N0106.N0428.N0770.N1708.d027372])




def d027374 (R : _root_.GD.N0106.N0428.N0770.N1719.d024281) (J K : _root_.GD.N0232.N0720.N1164.d006809) : Decidable (R.d024282 J K) := by
  letI (a b : ℚ) : Decidable (a < b) := _root_.GD.N0232.N0720.N1164.d006825 a b
  letI (a b : ℚ) : Decidable (a ≤ b) := _root_.GD.N0232.N0720.N1164.d006826 a b
  exact decidable_of_iff
    (0 < J.lo ∧ J.lo ≤ J.hi ∧ 0 ≤ R.ratioRoot.lo ∧ R.ratioRoot.lo ≤ R.ratioRoot.hi ∧
      R.ratioRoot.lo ^ 2 ≤ K.lo ∧ K.hi ≤ R.ratioRoot.hi ^ 2 ∧ 0 < R.nRoot.lo ∧
      R.nRoot.lo ≤ R.nRoot.hi ∧ R.nRoot.lo ^ 2 ≤ J.lo ∧ J.hi ≤ R.nRoot.hi ^ 2)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ =>
        ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩,
      fun h => ⟨h.nlo, h.norder, h.ratioLo, h.ratioOrder, h.ratioLower, h.ratioUpper,
        h.rootLo, h.rootOrder, h.rootLower, h.rootUpper⟩⟩


def d027375 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : _root_.GD.N0232.N0720.N1164.d006809 := _root_.GD.N0106.N0428.N0770.N1719.d024266 _root_.GD.N0106.N0428.N0770.N1708.d027368 (_root_.GD.N0106.N0428.N0770.N1727.d024429 i) (_root_.GD.N0106.N0428.N0770.N1727.d024430 i)


def d027376 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : _root_.GD.N0232.N0720.N1164.d006809 :=
  _root_.GD.N0106.N0428.N0770.N1719.d024260 (_root_.GD.N0106.N0428.N0770.N1727.d024430 i / (_root_.GD.N0106.N0428.N0770.N1727.d024429 i * (1 - _root_.GD.N0106.N0428.N0770.N1727.d024429 i)))


def d027377 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : Bool :=
  @decide ((_root_.GD.N0106.N0428.N0770.N1708.d027371 i).d024282 (_root_.GD.N0106.N0428.N0770.N1708.d027375 i) (_root_.GD.N0106.N0428.N0770.N1708.d027376 i))
    (_root_.GD.N0106.N0428.N0770.N1708.d027374 (_root_.GD.N0106.N0428.N0770.N1708.d027371 i) (_root_.GD.N0106.N0428.N0770.N1708.d027375 i) (_root_.GD.N0106.N0428.N0770.N1708.d027376 i))

theorem d027378 {i : _root_.GD.N0106.N0428.N0770.N1728.d024386} (h : _root_.GD.N0106.N0428.N0770.N1708.d027377 i = true) :
    (_root_.GD.N0106.N0428.N0770.N1708.d027371 i).d024282 (_root_.GD.N0106.N0428.N0770.N1708.d027375 i) (_root_.GD.N0106.N0428.N0770.N1708.d027376 i) :=
  @of_decide_eq_true _ (_root_.GD.N0106.N0428.N0770.N1708.d027374 (_root_.GD.N0106.N0428.N0770.N1708.d027371 i) (_root_.GD.N0106.N0428.N0770.N1708.d027375 i) (_root_.GD.N0106.N0428.N0770.N1708.d027376 i)) h


def d027379 : Bool :=
  @decide (_root_.GD.N0106.N0428.N0770.N1708.d027369 < (_root_.GD.N0106.N0428.N0770.N1727.d024433 _root_.GD.N0106.N0428.N0770.N1708.d027368 3 _root_.GD.N0106.N0428.N0770.N1708.d027371).lo)
    (_root_.GD.N0232.N0720.N1164.d006825 _root_.GD.N0106.N0428.N0770.N1708.d027369 (_root_.GD.N0106.N0428.N0770.N1727.d024433 _root_.GD.N0106.N0428.N0770.N1708.d027368 3 _root_.GD.N0106.N0428.N0770.N1708.d027371).lo)

theorem d027380 (h : _root_.GD.N0106.N0428.N0770.N1708.d027379 = true) : _root_.GD.N0106.N0428.N0770.N1708.d027369 < (_root_.GD.N0106.N0428.N0770.N1727.d024433 _root_.GD.N0106.N0428.N0770.N1708.d027368 3 _root_.GD.N0106.N0428.N0770.N1708.d027371).lo :=
  @of_decide_eq_true _ (_root_.GD.N0232.N0720.N1164.d006825 _root_.GD.N0106.N0428.N0770.N1708.d027369 (_root_.GD.N0106.N0428.N0770.N1727.d024433 _root_.GD.N0106.N0428.N0770.N1708.d027368 3 _root_.GD.N0106.N0428.N0770.N1708.d027371).lo) h



theorem d027381 : (_root_.GD.N0106.N0428.N0770.N1708.d027372.all _root_.GD.N0106.N0428.N0770.N1708.d027377 && _root_.GD.N0106.N0428.N0770.N1708.d027379) = true := by decide +kernel



theorem d027382 : ((_root_.GD.N0106.N0428.N0770.N1708.d027369 : ℚ) : ℝ) < _root_.GD.N0106.N0428.N0770.N1728.d024398 ((_root_.GD.N0106.N0428.N0770.N1708.d027367 : ℚ) : ℝ) := by
  have hk : (_root_.GD.N0106.N0428.N0770.N1708.d027372.all _root_.GD.N0106.N0428.N0770.N1708.d027377 && _root_.GD.N0106.N0428.N0770.N1708.d027379) = true := _root_.GD.N0106.N0428.N0770.N1708.d027381
  obtain ⟨hall, hcap⟩ := Bool.and_eq_true_iff.mp hk
  have hR : ∀ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, (_root_.GD.N0106.N0428.N0770.N1708.d027371 i).d024282
      (_root_.GD.N0106.N0428.N0770.N1719.d024266 _root_.GD.N0106.N0428.N0770.N1708.d027368 (_root_.GD.N0106.N0428.N0770.N1727.d024429 i) (_root_.GD.N0106.N0428.N0770.N1727.d024430 i))
      (_root_.GD.N0106.N0428.N0770.N1719.d024260 (_root_.GD.N0106.N0428.N0770.N1727.d024430 i / (_root_.GD.N0106.N0428.N0770.N1727.d024429 i * (1 - _root_.GD.N0106.N0428.N0770.N1727.d024429 i)))) :=
    fun i => _root_.GD.N0106.N0428.N0770.N1708.d027378 (List.all_eq_true.mp hall i (_root_.GD.N0106.N0428.N0770.N1708.d027373 i))
  have hq : ((_root_.GD.N0106.N0428.N0770.N1708.d027367 : ℚ) : ℝ) ∈ Icc (0 : ℝ) 1 := by
    rw [show ((_root_.GD.N0106.N0428.N0770.N1708.d027367 : ℚ) : ℝ) = 1 / 362 by norm_num [_root_.GD.N0106.N0428.N0770.N1708.d027367]]
    constructor <;> norm_num
  have hbox := _root_.GD.N0106.N0428.N0770.N1727.d024436 hq (_root_.GD.N0106.N0428.N0770.N1719.d024262 _root_.GD.N0106.N0428.N0770.N1708.d027367) hR
  have hlt : ((_root_.GD.N0106.N0428.N0770.N1708.d027369 : ℚ) : ℝ) < (((_root_.GD.N0106.N0428.N0770.N1727.d024433 _root_.GD.N0106.N0428.N0770.N1708.d027368 3 _root_.GD.N0106.N0428.N0770.N1708.d027371).lo : ℚ) : ℝ) :=
    Rat.cast_lt.mpr (_root_.GD.N0106.N0428.N0770.N1708.d027380 hcap)
  exact hlt.trans_le hbox.1


theorem d027383 : (7403 / 10000 : ℝ) < _root_.GD.N0106.N0428.N0770.N1728.d024398 (1 / 362) := by
  have h := _root_.GD.N0106.N0428.N0770.N1708.d027382
  rw [show ((_root_.GD.N0106.N0428.N0770.N1708.d027367 : ℚ) : ℝ) = 1 / 362 by norm_num [_root_.GD.N0106.N0428.N0770.N1708.d027367],
    show ((_root_.GD.N0106.N0428.N0770.N1708.d027369 : ℚ) : ℝ) = 7403 / 10000 by norm_num [_root_.GD.N0106.N0428.N0770.N1708.d027369]] at h
  exact h




theorem d027384 {T3 : ℝ}
    (hrem : |T3 - _root_.GD.N0106.N0428.N0770.N1728.d024398 (1 / 362)| ≤ 718 / 1000000) : (739 / 1000 : ℝ) < T3 := by
  have h1 := _root_.GD.N0106.N0428.N0770.N1708.d027383
  have h2 := _root_.GD.N0106.N0428.N0770.N1728.d024417
  have h3 := (abs_sub_le_iff.mp hrem).2
  linarith

end
end GD.N0106.N0428.N0770.N1708

#print axioms _root_.GD.N0106.N0428.N0770.N1708.d027373
#print axioms _root_.GD.N0106.N0428.N0770.N1708.d027381
#print axioms _root_.GD.N0106.N0428.N0770.N1708.d027382
#print axioms _root_.GD.N0106.N0428.N0770.N1708.d027383
#print axioms _root_.GD.N0106.N0428.N0770.N1708.d027384
