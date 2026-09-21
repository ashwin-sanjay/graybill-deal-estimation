import GD.Module0671
import GD.Module0655
































open scoped BigOperators
open MeasureTheory Set

namespace GD
namespace N0232
namespace N0719
namespace N1008

noncomputable section

open _root_.GD.N0232.N0719.N1007
open _root_.GD.N0232.N0719.N0928
open _root_.GD.N0232.N0719.N0929
open _root_.GD.N0232.N0719.N0866





def d009989 {k : ℕ} (sizes : Fin k → ℕ) : ℝ :=
  (∑ i, (sizes i : ℝ) / 2) + 1





def d009990 {k : ℕ}
    (sizes : Fin k → ℕ) (face : Finset (Fin k)) (j : Fin k) : ℝ :=
  (∑ i ∈ face.erase j, (sizes i : ℝ) / 2) + (face.card : ℝ) - 2



def d009991 {k : ℕ}
    (sizes : Fin k → ℕ) (face : Finset (Fin k)) (j : Fin k) : ℝ :=
  _root_.GD.N0232.N0719.N1008.d009989 sizes -
    (_root_.GD.N0232.N0719.N1008.d009990 sizes face j + 1)


def d009992 {k : ℕ}
    (sizes : Fin k → ℕ) (face : Finset (Fin k)) (j : Fin k) : ℝ :=
  _root_.GD.N0232.N0719.N1008.d009989 sizes -
    _root_.GD.N0232.N0719.N1008.d009991 sizes face j



def d009993 {k : ℕ}
    (sizes : Fin k → ℕ) (face : Finset (Fin k)) (j : Fin k) : ℝ :=
  _root_.GD.N0232.N0719.N1008.d009991 sizes face j - 1


def d009994 {k : ℕ}
    (sizes : Fin k → ℕ) (face : Finset (Fin k)) (j : Fin k) : ℝ :=
  _root_.GD.N0232.N0719.N1008.d009989 sizes -
    _root_.GD.N0232.N0719.N1008.d009993 sizes face j


@[simp]
theorem d009995
    {k : ℕ} (sizes : Fin k → ℕ) (j : Fin k) :
    _root_.GD.N0232.N0719.N1008.d009991 sizes {j} j =
      _root_.GD.N0232.N0719.N1008.d009989 sizes := by
  norm_num [_root_.GD.N0232.N0719.N1008.d009991,
    _root_.GD.N0232.N0719.N1008.d009990]



theorem d009996
    {k : ℕ} (sizes : Fin k → ℕ) (face : Finset (Fin k))
    {j : Fin k} (hj : j ∈ face) :
    _root_.GD.N0232.N0719.N1008.d009992 sizes face j =
      ∑ i ∈ face.erase j, ((sizes i : ℝ) / 2 + 1) := by
  have hcardNat : (face.erase j).card + 1 = face.card :=
    Finset.card_erase_add_one hj
  have hcardReal : ((face.erase j).card : ℝ) + 1 = (face.card : ℝ) := by
    exact_mod_cast hcardNat
  unfold _root_.GD.N0232.N0719.N1008.d009992
    _root_.GD.N0232.N0719.N1008.d009991 _root_.GD.N0232.N0719.N1008.d009990
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  linarith



theorem d009997
    {k : ℕ} (sizes : Fin k → ℕ) (face : Finset (Fin k)) (j : Fin k) :
    _root_.GD.N0232.N0719.N1008.d009994 sizes face j =
      _root_.GD.N0232.N0719.N1008.d009992 sizes face j + 1 := by
  unfold _root_.GD.N0232.N0719.N1008.d009994 _root_.GD.N0232.N0719.N1008.d009993
    _root_.GD.N0232.N0719.N1008.d009992
  ring


theorem d009998
    {k : ℕ} (sizes : Fin k → ℕ) (face : Finset (Fin k))
    {j : Fin k} (hj : j ∈ face) :
    _root_.GD.N0232.N0719.N1008.d009994 sizes face j =
      (∑ i ∈ face.erase j, ((sizes i : ℝ) / 2 + 1)) + 1 := by
  rw [_root_.GD.N0232.N0719.N1008.d009997,
    _root_.GD.N0232.N0719.N1008.d009996 sizes face hj]



theorem d009999
    {k : ℕ} (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (face : Finset (Fin k)) {j : Fin k} (hj : j ∈ face) :
    2 * ((face.erase j).card : ℝ) ≤
      _root_.GD.N0232.N0719.N1008.d009992 sizes face j := by
  rw [_root_.GD.N0232.N0719.N1008.d009996 sizes face hj]
  calc
    2 * ((face.erase j).card : ℝ) =
        ∑ _i ∈ face.erase j, (2 : ℝ) := by simp [mul_comm]
    _ ≤ ∑ i ∈ face.erase j, ((sizes i : ℝ) / 2 + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      have hsizeR : (2 : ℝ) ≤ sizes i := by exact_mod_cast hsizes i
      linarith



theorem d010000
    {k : ℕ} (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (face : Finset (Fin k)) {j : Fin k} (hj : j ∈ face)
    (hcard : 1 < face.card) :
    2 ≤ _root_.GD.N0232.N0719.N1008.d009992 sizes face j := by
  have herase : 1 ≤ (face.erase j).card := by
    have hcardEq := Finset.card_erase_add_one hj
    omega
  have hbound := _root_.GD.N0232.N0719.N1008.d009999
    sizes hsizes face hj
  have heraseR : (1 : ℝ) ≤ (face.erase j).card := by exact_mod_cast herase
  linarith



theorem d010001
    {k : ℕ} (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (face : Finset (Fin k)) {j : Fin k} (hj : j ∈ face)
    (hcard : 1 < face.card) :
    3 ≤ _root_.GD.N0232.N0719.N1008.d009994 sizes face j := by
  rw [_root_.GD.N0232.N0719.N1008.d009997]
  linarith [_root_.GD.N0232.N0719.N1008.d010000
    sizes hsizes face hj hcard]



theorem d010002
    {k : ℕ} (sizes : Fin k → ℕ) (j : Fin k) :
    _root_.GD.N0232.N0719.N1008.d009991 sizes Finset.univ j =
      (sizes j : ℝ) / 2 + 2 - k := by
  have hsum := Finset.sum_erase_add
    (s := Finset.univ) (f := fun i : Fin k ↦ (sizes i : ℝ) / 2)
    (Finset.mem_univ j)
  unfold _root_.GD.N0232.N0719.N1008.d009991
    _root_.GD.N0232.N0719.N1008.d009990 _root_.GD.N0232.N0719.N1008.d009989
  simp only [Finset.card_univ, Fintype.card_fin]
  linarith



theorem d010003
    (sizes : Fin 3 → ℕ) (j : Fin 3) (hsize : sizes j = 2) :
    _root_.GD.N0232.N0719.N1008.d009991 sizes Finset.univ j = 0 := by
  rw [_root_.GD.N0232.N0719.N1008.d010002, hsize]
  norm_num



theorem d010004
    (sizes : Fin 3 → ℕ) (j : Fin 3) (hsize : sizes j = 2) :
    _root_.GD.N0232.N0719.N1008.d009992 sizes Finset.univ j =
      _root_.GD.N0232.N0719.N1008.d009989 sizes := by
  unfold _root_.GD.N0232.N0719.N1008.d009992
  rw [_root_.GD.N0232.N0719.N1008.d010003 sizes j hsize]
  ring





theorem d010005
    (p y : Fin 1 → ℝ) (hsum : ∑ i, p i = 1) :
    _root_.GD.N0232.N0719.N0928.d009405 p y = y 0 := by
  unfold _root_.GD.N0232.N0719.N0928.d009405
  simp only [Fin.sum_univ_one]
  have hp : p 0 = 1 := by simpa using hsum
  rw [hp, one_mul]



theorem d010006
    (shape y t : Fin 1 → ℝ) (s : ℝ) :
    _root_.GD.N0232.N0719.N0929.d009652 Nat.zero_lt_one shape y t s =
      y 0 * _root_.GD.N0232.N0719.N0929.d009647 Nat.zero_lt_one shape y t s := by
  unfold _root_.GD.N0232.N0719.N0929.d009652 _root_.GD.N0232.N0719.N0929.d009647
  rw [← integral_const_mul]
  apply setIntegral_congr_fun
    (_root_.GD.N0232.N0719.N0955.d009608 1)
  intro q hq
  change
    _root_.GD.N0232.N0719.N0928.d009437 shape
          (_root_.GD.N0232.N0719.N0853.d009567 Nat.zero_lt_one q)
          y t s *
        _root_.GD.N0232.N0719.N0928.d009405
          (_root_.GD.N0232.N0719.N0853.d009567 Nat.zero_lt_one q) y =
      y 0 * _root_.GD.N0232.N0719.N0928.d009437 shape
        (_root_.GD.N0232.N0719.N0853.d009567 Nat.zero_lt_one q) y t s
  rw [_root_.GD.N0232.N0719.N1008.d010005]
  · ring
  · exact _root_.GD.N0232.N0719.N0853.d009570
      Nat.zero_lt_one q



theorem d010007
    (shape y t : Fin 1 → ℝ) (s : ℝ)
    (hshape : ∀ i, 0 < shape i) (ht : ∀ i, 0 < t i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    _root_.GD.N0232.N0719.N0929.d009653 Nat.zero_lt_one shape y t s = y 0 := by
  unfold _root_.GD.N0232.N0719.N0929.d009653
  rw [_root_.GD.N0232.N0719.N1008.d010006]
  field_simp [_root_.GD.N0232.N0719.N0929.d009654 Nat.zero_lt_one shape y t s
    hshape ht hpower]




theorem d010008
    (shape y t : Fin 1 → ℝ) (s : ℝ)
    (hshape : ∀ i, 0 < shape i) (ht : 0 < t 0)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    _root_.GD.N0232.N0719.N0929.d009647 Nat.zero_lt_one shape y t s =
      (t 0) ^ (-_root_.GD.N0232.N0719.N0928.d009415 shape s) *
        _root_.GD.N0232.N0719.N0929.d009647 Nat.zero_lt_one shape (fun _ ↦ 0) (fun _ ↦ 1) s := by
  let l := Real.sqrt (t 0)
  have hl : 0 < l := Real.sqrt_pos.2 ht
  have hl2 : l ^ 2 = t 0 := by
    exact Real.sq_sqrt ht.le
  have hy : _root_.GD.N0232.N0719.N0866.d009655 (y 0) l (fun _ : Fin 1 ↦ 0) = y := by
    funext i
    fin_cases i
    simp [_root_.GD.N0232.N0719.N0866.d009655]
  have ht' : _root_.GD.N0232.N0719.N0866.d009656 l (fun _ : Fin 1 ↦ 1) = t := by
    funext i
    fin_cases i
    simp [_root_.GD.N0232.N0719.N0866.d009656, hl2]
  have hbaseT : ∀ i : Fin 1, 0 < (1 : ℝ) := fun _ ↦ by norm_num
  have hcov := _root_.GD.N0232.N0719.N0866.d009661 Nat.zero_lt_one shape
    (fun _ : Fin 1 ↦ 0) (fun _ : Fin 1 ↦ 1) s (y 0) l
    hshape hbaseT hpower hl
  rw [hy, ht', hl2] at hcov
  exact hcov



variable {J : Type*} [Fintype J]


theorem d010009
    (weight evidence action : J → ℝ) (center : ℝ)
    (hdenom : _root_.GD.N0232.N0719.N1007.d009826 weight evidence ≠ 0) :
    _root_.GD.N0232.N0719.N1007.d009828 weight evidence action - center =
      (∑ j, weight j * evidence j * (action j - center)) /
        _root_.GD.N0232.N0719.N1007.d009826 weight evidence := by
  have hdenom' : (∑ j, weight j * evidence j) ≠ 0 := by
    simpa [_root_.GD.N0232.N0719.N1007.d009826] using hdenom
  unfold _root_.GD.N0232.N0719.N1007.d009828 _root_.GD.N0232.N0719.N1007.d009827 _root_.GD.N0232.N0719.N1007.d009826
  field_simp [hdenom']
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

variable [DecidableEq J]



theorem d010010
    (weight evidence action : J → ℝ) (center : ℝ) (j0 : J)
    (haction : action j0 = center)
    (hdenom : _root_.GD.N0232.N0719.N1007.d009826 weight evidence ≠ 0) :
    _root_.GD.N0232.N0719.N1007.d009828 weight evidence action - center =
      (∑ j ∈ Finset.univ.erase j0,
          weight j * evidence j * (action j - center)) /
        _root_.GD.N0232.N0719.N1007.d009826 weight evidence := by
  rw [_root_.GD.N0232.N0719.N1008.d010009 weight evidence action center hdenom]
  congr 1
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j0)]
  simp [haction]





theorem d010011
    (weight evidence action : J → ℝ) (center : ℝ) (j0 : J)
    (hmass : ∀ j, 0 ≤ weight j * evidence j)
    (hmass0 : 0 < weight j0 * evidence j0)
    (haction : action j0 = center) :
    |_root_.GD.N0232.N0719.N1007.d009828 weight evidence action - center| ≤
      (∑ j ∈ Finset.univ.erase j0,
          weight j * evidence j * |action j - center|) /
        (weight j0 * evidence j0) := by
  let D := _root_.GD.N0232.N0719.N1007.d009826 weight evidence
  let M := weight j0 * evidence j0
  let B := ∑ j ∈ Finset.univ.erase j0,
    weight j * evidence j * |action j - center|
  have hDsum : D = ∑ j, weight j * evidence j := rfl
  have hMD : M ≤ D := by
    rw [hDsum, ← Finset.sum_erase_add _ _ (Finset.mem_univ j0)]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun j hj ↦ hmass j)
  have hDpos : 0 < D := lt_of_lt_of_le hmass0 hMD
  have hBnonneg : 0 ≤ B := Finset.sum_nonneg fun j hj ↦
    mul_nonneg (hmass j) (abs_nonneg _)
  have hnumAbs :
      |∑ j ∈ Finset.univ.erase j0,
          weight j * evidence j * (action j - center)| ≤ B := by
    calc
      |∑ j ∈ Finset.univ.erase j0,
          weight j * evidence j * (action j - center)| ≤
          ∑ j ∈ Finset.univ.erase j0,
            |weight j * evidence j * (action j - center)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = B := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [abs_mul, abs_of_nonneg (hmass j)]
  rw [_root_.GD.N0232.N0719.N1008.d010010 weight evidence action center j0
    haction hDpos.ne', abs_div, abs_of_pos hDpos]
  change
    |∑ j ∈ Finset.univ.erase j0,
        weight j * evidence j * (action j - center)| / D ≤ B / M
  calc
    |∑ j ∈ Finset.univ.erase j0,
        weight j * evidence j * (action j - center)| / D ≤ B / D :=
      (div_le_div_iff_of_pos_right hDpos).2 hnumAbs
    _ ≤ B / M := by
      exact div_le_div_of_nonneg_left hBnonneg hmass0 hMD

end

end N1008
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N1008.d009996
#print axioms _root_.GD.N0232.N0719.N1008.d010001
#print axioms _root_.GD.N0232.N0719.N1008.d010003
#print axioms _root_.GD.N0232.N0719.N1008.d010011
