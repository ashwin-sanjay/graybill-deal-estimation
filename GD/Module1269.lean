import GD.Module1223
import GD.Module0754
import GD.Module1262
import GD.Module0664
import GD.Module1230

set_option autoImplicit false
set_option warningAsError true











open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace GD.N0232.N0719.N0990

open _root_.GD.N0232.N0720.N1341
open _root_.GD.N0232.N0720.N1316
open _root_.GD.N0232.N0720.N1377
open _root_.GD.N0232.N0720.N1379
open _root_.GD.N0232.N0720.N1330
  (d020031 d020030 d020032)
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0988
open _root_.GD.N0232.N0719.N0989 _root_.GD.N0232.N0719.N0986
open _root_.GD.N0232.N0719.N0983
open _root_.GD.N0107

noncomputable section

variable {k d : ℕ} (sizes : Fin k → ℕ)

abbrev d020496 (k : ℕ) := ℝ × _root_.GD.N0232.N0719.N0983.d009709 k
abbrev d020497 (k : ℕ) := _root_.GD.N0232.N0719.N0873.d011295 (Fin k)

def d020498 (q : _root_.GD.N0232.N0719.N0988.d019777 k) (i : Fin k) : ℝ := (sizes i : ℝ) / (q.2 i : ℝ)
def d020499 (q : _root_.GD.N0232.N0719.N0988.d019777 k) : ℝ := ∑ i, _root_.GD.N0232.N0719.N0990.d020498 sizes q i

def d020500 (q : _root_.GD.N0232.N0719.N0988.d019777 k) (i : Fin k) : ℝ :=
  _root_.GD.N0232.N0719.N0990.d020498 sizes q i / _root_.GD.N0232.N0719.N0990.d020499 sizes q

def d020501 (q : _root_.GD.N0232.N0719.N0988.d019777 k) : ℝ := Real.sqrt (_root_.GD.N0232.N0719.N0990.d020499 sizes q)
def d020502 (q : _root_.GD.N0232.N0719.N0988.d019777 k) : ℝ := q.1 * _root_.GD.N0232.N0719.N0990.d020501 sizes q

theorem d020503 (hn : ∀ i, 0 < sizes i) (q : _root_.GD.N0232.N0719.N0988.d019777 k) (i : Fin k) :
    0 < _root_.GD.N0232.N0719.N0990.d020498 sizes q i := div_pos (by exact_mod_cast hn i) (q.2 i).property.1

variable (hdim : (∑ i, sizes i) = d + 1) (hn : ∀ i, 0 < sizes i)


include hdim hn in
theorem d020504 (q : _root_.GD.N0232.N0719.N0988.d019777 k) : 0 < _root_.GD.N0232.N0719.N0990.d020499 sizes q := by
  let i : Fin k := ((_root_.GD.N0232.N0719.N0997.d019805 sizes hdim).symm (0 : Fin (d + 1))).1
  exact Finset.sum_pos' (fun j _ => (_root_.GD.N0232.N0719.N0990.d020503 sizes hn q j).le)
    ⟨i, Finset.mem_univ i, _root_.GD.N0232.N0719.N0990.d020503 sizes hn q i⟩

include hdim hn in
theorem d020505 (q : _root_.GD.N0232.N0719.N0988.d019777 k) (i : Fin k) :
    _root_.GD.N0232.N0719.N0990.d020500 sizes q i ∈ Icc (0 : ℝ) 1 := by
  have hT := _root_.GD.N0232.N0719.N0990.d020504 sizes hdim hn q
  refine ⟨(div_pos (_root_.GD.N0232.N0719.N0990.d020503 sizes hn q i) hT).le, ?_⟩
  apply (div_le_one hT).mpr
  exact Finset.single_le_sum (fun j _ => (_root_.GD.N0232.N0719.N0990.d020503 sizes hn q j).le)
    (Finset.mem_univ i)

include hdim hn in
theorem d020506 (q : _root_.GD.N0232.N0719.N0988.d019777 k) : ∑ i, _root_.GD.N0232.N0719.N0990.d020500 sizes q i = 1 := by
  simp only [_root_.GD.N0232.N0719.N0990.d020500, ← Finset.sum_div]
  exact div_self (_root_.GD.N0232.N0719.N0990.d020504 sizes hdim hn q).ne'

def d020507 (q : _root_.GD.N0232.N0719.N0988.d019777 k) : _root_.GD.N0232.N0719.N0990.d020496 k :=
  (_root_.GD.N0232.N0719.N0990.d020502 sizes q,
    ⟨fun i => ⟨_root_.GD.N0232.N0719.N0990.d020500 sizes q i, _root_.GD.N0232.N0719.N0990.d020505 sizes hdim hn q i⟩,
      _root_.GD.N0232.N0719.N0990.d020506 sizes hdim hn q⟩)

include hdim hn in
theorem d020508 (q : _root_.GD.N0232.N0719.N0988.d019777 k) : 0 < _root_.GD.N0232.N0719.N0990.d020501 sizes q :=
  Real.sqrt_pos.mpr (_root_.GD.N0232.N0719.N0990.d020504 sizes hdim hn q)

include hdim hn in
theorem d020509 (q : _root_.GD.N0232.N0719.N0988.d019777 k) :
    _root_.GD.N0232.N0719.N0990.d020501 sizes q ^ 2 = _root_.GD.N0232.N0719.N0990.d020499 sizes q :=
  Real.sq_sqrt (_root_.GD.N0232.N0719.N0990.d020504 sizes hdim hn q).le

omit hdim hn in
def d020510 (p : _root_.GD.N0232.N0719.N0990.d020496 k) (x : _root_.GD.N0232.N0719.N0990.d020497 k) : ℝ :=
  _root_.GD.N0232.N0719.N0989.d011346 (d + 2) p.1 (fun i => (_root_.GD.N0232.N0719.N0983.d009710 i p.2 : ℝ)) x

omit hdim hn in
def d020511 (p : _root_.GD.N0232.N0719.N0990.d020496 k) (x : _root_.GD.N0232.N0719.N0990.d020497 k) : ℝ :=
  p.1 * _root_.GD.N0232.N0719.N0989.d011346 (d + 1) p.1 (fun i => (_root_.GD.N0232.N0719.N0983.d009710 i p.2 : ℝ)) x

omit hn in
def d020512 (x : _root_.GD.N0232.N0720.N1341.d004414 d) : _root_.GD.N0232.N0719.N0990.d020497 k :=
  _root_.GD.N0232.N0719.N0986.d020362 sizes ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x)

private theorem d020513 (f : Fin (d + 1) → ℝ) :
    (∑ j, f j) = ∑ i, ∑ j : Fin (sizes i), f (_root_.GD.N0232.N0719.N0997.d019805 sizes hdim ⟨i,j⟩) := by
  rw [← (_root_.GD.N0232.N0719.N0997.d019805 sizes hdim).sum_comp f, Fintype.sum_sigma]

private theorem d020514 (q : _root_.GD.N0232.N0719.N0988.d019777 k) (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    _root_.GD.N0232.N0720.N1316.d004441 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q) x =
      ∑ i, (∑ j : Fin (sizes i), ((_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x i j) ^ 2) / (q.2 i : ℝ) := by
  unfold _root_.GD.N0232.N0720.N1316.d004441
  rw [_root_.GD.N0232.N0719.N0990.d020513 sizes hdim]
  simp only [_root_.GD.N0232.N0719.N0988.d019779, _root_.GD.N0232.N0719.N0997.d019806, Equiv.symm_apply_apply,
    ← Finset.sum_div, _root_.GD.N0232.N0719.N0997.d019808]

private theorem d020515 (q : _root_.GD.N0232.N0719.N0988.d019777 k) (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    _root_.GD.N0232.N0720.N1316.d004442 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q) x =
      ∑ i, ((∑ j : Fin (sizes i), (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).symm x i j) * q.1) / (q.2 i : ℝ) := by
  unfold _root_.GD.N0232.N0720.N1316.d004442
  rw [_root_.GD.N0232.N0719.N0990.d020513 sizes hdim]
  simp only [_root_.GD.N0232.N0719.N0988.d019779, _root_.GD.N0232.N0719.N0997.d019806, Equiv.symm_apply_apply,
    ← Finset.sum_div, ← Finset.sum_mul, _root_.GD.N0232.N0719.N0997.d019808]

private theorem d020516 {j : ℕ} (hj : 0 < j)
    (x : _root_.GD.N0137.d008894 j) :
    (∑ i, x i ^ 2) = (j : ℝ) *
      (_root_.GD.N0107.d009084 x ^ 2 + 2 * (_root_.GD.N0126.d006422 x / (2 * j))) := by
  letI : NeZero j := ⟨hj.ne'⟩
  rw [_root_.GD.N0126.d006428]
  simp only [_root_.GD.N0126.d006419, Fintype.card_fin, _root_.GD.N0107.d009084]
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  field_simp [hjR]
  ring

private theorem d020517 {j : ℕ} (hj : 0 < j)
    (x : _root_.GD.N0137.d008894 j) :
    (∑ i, x i) = (j : ℝ) * _root_.GD.N0107.d009084 x := by
  unfold _root_.GD.N0107.d009084 _root_.GD.N0126.d006420 _root_.GD.N0126.d006419
  simp only [Fintype.card_fin]
  exact (mul_div_cancel₀ _ (by exact_mod_cast hj.ne' : (j : ℝ) ≠ 0)).symm

include hn in
theorem d020518 (q : _root_.GD.N0232.N0719.N0988.d019777 k) (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    _root_.GD.N0232.N0720.N1316.d004441 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q) x =
      ∑ i, _root_.GD.N0232.N0719.N0990.d020498 sizes q i *
        (((_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x).1 i) ^ 2 + 2 * (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x).2 i) := by
  rw [_root_.GD.N0232.N0719.N0990.d020514 sizes hdim]
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.GD.N0232.N0719.N0990.d020516 (hn i)]
  simp only [_root_.GD.N0232.N0719.N0990.d020512, _root_.GD.N0232.N0719.N0986.d020362, _root_.GD.N0232.N0719.N0986.d020363, _root_.GD.N0232.N0719.N0986.d020364,
    _root_.GD.N0232.N0719.N0900.d009102, _root_.GD.N0232.N0719.N0990.d020498]
  ring

include hn in
theorem d020519 (q : _root_.GD.N0232.N0719.N0988.d019777 k) (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    _root_.GD.N0232.N0720.N1316.d004442 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q) x =
      q.1 * ∑ i, _root_.GD.N0232.N0719.N0990.d020498 sizes q i * (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x).1 i := by
  rw [_root_.GD.N0232.N0719.N0990.d020515 sizes hdim, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.GD.N0232.N0719.N0990.d020517 (hn i)]
  simp only [_root_.GD.N0232.N0719.N0990.d020512, _root_.GD.N0232.N0719.N0986.d020362, _root_.GD.N0232.N0719.N0986.d020363, _root_.GD.N0232.N0719.N0900.d009102, _root_.GD.N0232.N0719.N0990.d020498]
  ring

omit hn in
def d020520 (q : _root_.GD.N0232.N0719.N0988.d019777 k) (x : _root_.GD.N0232.N0720.N1341.d004414 d) : ℝ :=
  _root_.GD.N0232.N0719.N0989.d011339 (_root_.GD.N0232.N0719.N0990.d020500 sizes q) (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x)

omit hn in
def d020521 (q : _root_.GD.N0232.N0719.N0988.d019777 k) (x : _root_.GD.N0232.N0720.N1341.d004414 d) : ℝ :=
  _root_.GD.N0232.N0719.N0989.d011340 (_root_.GD.N0232.N0719.N0990.d020500 sizes q) (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x)

include hn in
theorem d020522 (q : _root_.GD.N0232.N0719.N0988.d019777 k) (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    _root_.GD.N0232.N0720.N1316.d004441 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q) x =
      _root_.GD.N0232.N0719.N0990.d020501 sizes q ^ 2 * _root_.GD.N0232.N0719.N0990.d020520 sizes hdim q x := by
  rw [_root_.GD.N0232.N0719.N0990.d020518 sizes hdim hn, _root_.GD.N0232.N0719.N0990.d020509 sizes hdim hn]
  unfold _root_.GD.N0232.N0719.N0990.d020520 _root_.GD.N0232.N0719.N0989.d011339
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold _root_.GD.N0232.N0719.N0990.d020500
  field_simp [(_root_.GD.N0232.N0719.N0990.d020504 sizes hdim hn q).ne']

include hn in
theorem d020523 (q : _root_.GD.N0232.N0719.N0988.d019777 k) (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    _root_.GD.N0232.N0720.N1316.d004442 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q) x =
      _root_.GD.N0232.N0719.N0990.d020501 sizes q * (_root_.GD.N0232.N0719.N0990.d020521 sizes hdim q x * _root_.GD.N0232.N0719.N0990.d020502 sizes q) := by
  have hB : _root_.GD.N0232.N0719.N0990.d020499 sizes q * _root_.GD.N0232.N0719.N0990.d020521 sizes hdim q x =
      ∑ i, _root_.GD.N0232.N0719.N0990.d020498 sizes q i * (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x).1 i := by
    unfold _root_.GD.N0232.N0719.N0990.d020521 _root_.GD.N0232.N0719.N0989.d011340
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold _root_.GD.N0232.N0719.N0990.d020500
    field_simp [(_root_.GD.N0232.N0719.N0990.d020504 sizes hdim hn q).ne']
  rw [_root_.GD.N0232.N0719.N0990.d020519 sizes hdim hn, ← hB, ← _root_.GD.N0232.N0719.N0990.d020509 sizes hdim hn]
  unfold _root_.GD.N0232.N0719.N0990.d020502
  ring

omit hn in
def d020524 (q : _root_.GD.N0232.N0719.N0988.d019777 k) : ℝ :=
  _root_.GD.N0232.N0720.N1316.d004444 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q) *
    (_root_.GD.N0232.N0719.N0990.d020501 sizes q ^ (d + 3))⁻¹

include hn in
theorem d020525 (q : _root_.GD.N0232.N0719.N0988.d019777 k) :
    0 < _root_.GD.N0232.N0719.N0990.d020524 sizes hdim q :=
  mul_pos (_root_.GD.N0232.N0720.N1316.d004447 _)
    (inv_pos.mpr (pow_pos (_root_.GD.N0232.N0719.N0990.d020508 sizes hdim hn q) _))

theorem d020526 (q : _root_.GD.N0232.N0719.N0988.d019777 k) (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    _root_.GD.N0232.N0720.N1316.d004444 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q) *
      _root_.GD.N0232.N0720.N1377.d002852 (d + 2) (_root_.GD.N0232.N0720.N1316.d004441 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q) x)
        (_root_.GD.N0232.N0720.N1316.d004442 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q) x) =
      _root_.GD.N0232.N0719.N0990.d020524 sizes hdim q *
        _root_.GD.N0232.N0719.N0990.d020510 (d := d) (_root_.GD.N0232.N0719.N0990.d020507 sizes hdim hn q) (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x) := by
  rw [_root_.GD.N0232.N0719.N0990.d020522 sizes hdim hn, _root_.GD.N0232.N0719.N0990.d020523 sizes hdim hn,
    _root_.GD.N0232.N0720.N1377.d002866 (d + 2) (_root_.GD.N0232.N0719.N0990.d020520 sizes hdim q x)
      (_root_.GD.N0232.N0719.N0990.d020521 sizes hdim q x * _root_.GD.N0232.N0719.N0990.d020502 sizes q) (_root_.GD.N0232.N0719.N0990.d020508 sizes hdim hn q)]
  simp only [_root_.GD.N0232.N0719.N0990.d020524, _root_.GD.N0232.N0719.N0990.d020510, _root_.GD.N0232.N0719.N0990.d020507, _root_.GD.N0232.N0719.N0990.d020520, _root_.GD.N0232.N0719.N0990.d020521,
    _root_.GD.N0232.N0719.N0983.d009710, _root_.GD.N0232.N0719.N0989.d011346, Nat.add_assoc, Nat.reduceAdd]
  ring

theorem d020527 (q : _root_.GD.N0232.N0719.N0988.d019777 k) (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    _root_.GD.N0232.N0720.N1316.d004444 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q) * q.1 *
      _root_.GD.N0232.N0720.N1377.d002852 (d + 1) (_root_.GD.N0232.N0720.N1316.d004441 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q) x)
        (_root_.GD.N0232.N0720.N1316.d004442 (_root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q) x) =
      _root_.GD.N0232.N0719.N0990.d020524 sizes hdim q *
        _root_.GD.N0232.N0719.N0990.d020511 (d := d) (_root_.GD.N0232.N0719.N0990.d020507 sizes hdim hn q) (_root_.GD.N0232.N0719.N0990.d020512 sizes hdim x) := by
  rw [_root_.GD.N0232.N0719.N0990.d020522 sizes hdim hn, _root_.GD.N0232.N0719.N0990.d020523 sizes hdim hn,
    _root_.GD.N0232.N0720.N1377.d002866 (d + 1) (_root_.GD.N0232.N0719.N0990.d020520 sizes hdim q x)
      (_root_.GD.N0232.N0719.N0990.d020521 sizes hdim q x * _root_.GD.N0232.N0719.N0990.d020502 sizes q) (_root_.GD.N0232.N0719.N0990.d020508 sizes hdim hn q)]
  simp only [_root_.GD.N0232.N0719.N0990.d020524, _root_.GD.N0232.N0719.N0990.d020511, _root_.GD.N0232.N0719.N0990.d020507, _root_.GD.N0232.N0719.N0990.d020520, _root_.GD.N0232.N0719.N0990.d020521,
    _root_.GD.N0232.N0719.N0983.d009710, _root_.GD.N0232.N0719.N0989.d011346, Nat.add_assoc, Nat.reduceAdd, _root_.GD.N0232.N0719.N0990.d020502]
  have hpower : _root_.GD.N0232.N0719.N0990.d020501 sizes q ^ (d + 3) =
      _root_.GD.N0232.N0719.N0990.d020501 sizes q ^ (d + 2) * _root_.GD.N0232.N0719.N0990.d020501 sizes q := by
    rw [show d + 3 = (d + 2) + 1 by omega, pow_succ]
  rw [hpower]
  field_simp [(_root_.GD.N0232.N0719.N0990.d020508 sizes hdim hn q).ne']

end
end GD.N0232.N0719.N0990

#print axioms _root_.GD.N0232.N0719.N0990.d020522
#print axioms _root_.GD.N0232.N0719.N0990.d020527
