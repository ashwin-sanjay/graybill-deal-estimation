import GD.Module1217
import GD.Module0210
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure














open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace GD.N0232.N0720.N1315

open _root_.GD.N0232.N0720.N1341 _root_.GD.N0232.N0720.N1316
open _root_.GD.N0232.N0720.N1329 _root_.GD.N0232.N0720.N1314
open _root_.GD.N0232.N0720.N1377 _root_.GD.N0232.N0720.N1379
open _root_.GD.N0232.N0720.N1376 _root_.GD.N0107
open _root_.GD.N0230.N0556

noncomputable section

abbrev d019831 := Icc (0 : ℝ) 1
abbrev d019832 := ℝ × _root_.GD.N0232.N0720.N1315.d019831
abbrev d019833 := Fin 4 → ℝ

def d019834 (m : ℕ) (q : _root_.GD.N0232.N0720.N1329.d019646) : ℝ := m / q.2.1
def d019835 (n : ℕ) (q : _root_.GD.N0232.N0720.N1329.d019646) : ℝ := n / (1 - q.2.1)
def d019836 (m n : ℕ) (q : _root_.GD.N0232.N0720.N1329.d019646) : ℝ :=
  _root_.GD.N0232.N0720.N1315.d019834 m q + _root_.GD.N0232.N0720.N1315.d019835 n q

def d019837 (m n : ℕ) (q : _root_.GD.N0232.N0720.N1329.d019646) : ℝ :=
  _root_.GD.N0232.N0720.N1315.d019835 n q / _root_.GD.N0232.N0720.N1315.d019836 m n q

theorem d019838 {m : ℕ} (hm : 0 < m) (q : _root_.GD.N0232.N0720.N1329.d019646) :
    0 < _root_.GD.N0232.N0720.N1315.d019834 m q :=
  div_pos (by exact_mod_cast hm) q.2.2.1

theorem d019839 {n : ℕ} (hn : 0 < n) (q : _root_.GD.N0232.N0720.N1329.d019646) :
    0 < _root_.GD.N0232.N0720.N1315.d019835 n q :=
  div_pos (by exact_mod_cast hn) (sub_pos.mpr q.2.2.2)

theorem d019840 {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (q : _root_.GD.N0232.N0720.N1329.d019646) :
    0 < _root_.GD.N0232.N0720.N1315.d019836 m n q :=
  add_pos (_root_.GD.N0232.N0720.N1315.d019838 hm q) (_root_.GD.N0232.N0720.N1315.d019839 hn q)

theorem d019841 {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (q : _root_.GD.N0232.N0720.N1329.d019646) :
    _root_.GD.N0232.N0720.N1315.d019837 m n q ∈ Ioo (0 : ℝ) 1 := by
  have hT := _root_.GD.N0232.N0720.N1315.d019840 hm hn q
  constructor
  · exact div_pos (_root_.GD.N0232.N0720.N1315.d019839 hn q) hT
  · apply (div_lt_one hT).mpr
    exact lt_add_of_pos_left _ (_root_.GD.N0232.N0720.N1315.d019838 hm q)


theorem d019842 {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (q : _root_.GD.N0232.N0720.N1329.d019646) :
    _root_.GD.N0232.N0720.N1315.d019837 m n q = (n : ℝ) * q.2.1 /
      ((m : ℝ) * (1 - q.2.1) + (n : ℝ) * q.2.1) := by
  have hD : 0 < (m : ℝ) * (1 - q.2.1) + (n : ℝ) * q.2.1 :=
    add_pos (mul_pos (by exact_mod_cast hm) (sub_pos.mpr q.2.2.2))
      (mul_pos (by exact_mod_cast hn) q.2.2.1)
  have hT : (m : ℝ) / q.2.1 + (n : ℝ) / (1 - q.2.1) ≠ 0 :=
    (_root_.GD.N0232.N0720.N1315.d019840 hm hn q).ne'
  unfold _root_.GD.N0232.N0720.N1315.d019837 _root_.GD.N0232.N0720.N1315.d019836 _root_.GD.N0232.N0720.N1315.d019834 _root_.GD.N0232.N0720.N1315.d019835
  field_simp [q.2.2.1.ne', (sub_pos.mpr q.2.2.2).ne', hD.ne', hT]

def d019843 (m n : ℕ) (q : _root_.GD.N0232.N0720.N1329.d019646) : ℝ :=
  Real.sqrt (_root_.GD.N0232.N0720.N1315.d019836 m n q)

def d019844 (m n : ℕ) (q : _root_.GD.N0232.N0720.N1329.d019646) : ℝ := q.1 * _root_.GD.N0232.N0720.N1315.d019843 m n q

theorem d019845 {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (q : _root_.GD.N0232.N0720.N1329.d019646) :
    0 < _root_.GD.N0232.N0720.N1315.d019843 m n q := Real.sqrt_pos.mpr (_root_.GD.N0232.N0720.N1315.d019840 hm hn q)

theorem d019846 {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (q : _root_.GD.N0232.N0720.N1329.d019646) :
    _root_.GD.N0232.N0720.N1315.d019843 m n q ^ 2 = _root_.GD.N0232.N0720.N1315.d019836 m n q :=
  Real.sq_sqrt (_root_.GD.N0232.N0720.N1315.d019840 hm hn q).le

def d019847 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (q : _root_.GD.N0232.N0720.N1329.d019646) :
    _root_.GD.N0232.N0720.N1315.d019832 :=
  (_root_.GD.N0232.N0720.N1315.d019844 m n q,
    ⟨_root_.GD.N0232.N0720.N1315.d019837 m n q, (_root_.GD.N0232.N0720.N1315.d019841 hm hn q).1.le, (_root_.GD.N0232.N0720.N1315.d019841 hm hn q).2.le⟩)


def d019848 (d : ℕ) (p : _root_.GD.N0232.N0720.N1315.d019832) (x : _root_.GD.N0232.N0720.N1315.d019833) : ℝ :=
  _root_.GD.N0232.N0720.N1377.d002852 (d + 2) (_root_.GD.N0232.N0720.N1376.d002892 p.2.1 (x 0) (x 1) (x 2) (x 3))
    (_root_.GD.N0232.N0720.N1376.d002893 p.2.1 (x 0) (x 1) * p.1)

def d019849 (d : ℕ) (p : _root_.GD.N0232.N0720.N1315.d019832) (x : _root_.GD.N0232.N0720.N1315.d019833) : ℝ :=
  p.1 * _root_.GD.N0232.N0720.N1377.d002852 (d + 1) (_root_.GD.N0232.N0720.N1376.d002892 p.2.1 (x 0) (x 1) (x 2) (x 3))
    (_root_.GD.N0232.N0720.N1376.d002893 p.2.1 (x 0) (x 1) * p.1)


def d019850 (m n d : ℕ) (hdim : m + n = d + 1) (x : _root_.GD.N0232.N0720.N1341.d004414 d) : _root_.GD.N0232.N0720.N1315.d019833 :=
  ![_root_.GD.N0107.d009084 ((_root_.GD.N0232.N0720.N1329.d019648 m n d hdim).symm x).1,
    _root_.GD.N0107.d009084 ((_root_.GD.N0232.N0720.N1329.d019648 m n d hdim).symm x).2,
    _root_.GD.N0126.d006422 ((_root_.GD.N0232.N0720.N1329.d019648 m n d hdim).symm x).1 / (2 * m),
    _root_.GD.N0126.d006422 ((_root_.GD.N0232.N0720.N1329.d019648 m n d hdim).symm x).2 / (2 * n)]

section ActualCoordinates

variable {m n d : ℕ} (hdim : m + n = d + 1)

private theorem d019851 (f : Fin (d + 1) → ℝ) :
    (∑ i, f i) =
      (∑ i : Fin m, f (_root_.GD.N0232.N0720.N1329.d019647 m n d hdim (.inl i))) +
        ∑ i : Fin n, f (_root_.GD.N0232.N0720.N1329.d019647 m n d hdim (.inr i)) := by
  rw [← (_root_.GD.N0232.N0720.N1329.d019647 m n d hdim).sum_comp f, Fintype.sum_sum_type]

private theorem d019852 (q : _root_.GD.N0232.N0720.N1329.d019646) (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    _root_.GD.N0232.N0720.N1316.d004441 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim q) x =
      (∑ i : Fin m, ((_root_.GD.N0232.N0720.N1329.d019648 m n d hdim).symm x).1 i ^ 2) / q.2.1 +
        (∑ i : Fin n, ((_root_.GD.N0232.N0720.N1329.d019648 m n d hdim).symm x).2 i ^ 2) / (1 - q.2.1) := by
  unfold _root_.GD.N0232.N0720.N1316.d004441
  rw [_root_.GD.N0232.N0720.N1315.d019851 hdim]
  simp only [_root_.GD.N0232.N0720.N1329.d019661, _root_.GD.N0232.N0720.N1329.d019662, _root_.GD.N0232.N0720.N1329.d019659,
    ← Finset.sum_div, _root_.GD.N0232.N0720.N1329.d019649, _root_.GD.N0232.N0720.N1329.d019650]

private theorem d019853 (q : _root_.GD.N0232.N0720.N1329.d019646) (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    _root_.GD.N0232.N0720.N1316.d004442 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim q) x =
      ((∑ i : Fin m, ((_root_.GD.N0232.N0720.N1329.d019648 m n d hdim).symm x).1 i) * q.1) / q.2.1 +
        ((∑ i : Fin n, ((_root_.GD.N0232.N0720.N1329.d019648 m n d hdim).symm x).2 i) * q.1) / (1 - q.2.1) := by
  unfold _root_.GD.N0232.N0720.N1316.d004442
  change (∑ i, x i * q.1 / (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim q).2 i) = _
  rw [_root_.GD.N0232.N0720.N1315.d019851 hdim]
  simp only [_root_.GD.N0232.N0720.N1329.d019661, _root_.GD.N0232.N0720.N1329.d019662,
    _root_.GD.N0232.N0720.N1329.d019659, ← Finset.sum_div, ← Finset.sum_mul,
    _root_.GD.N0232.N0720.N1329.d019649, _root_.GD.N0232.N0720.N1329.d019650]

private theorem d019854 {j : ℕ} (hj : 0 < j) (x : _root_.GD.N0137.d008894 j) :
    (∑ i, x i ^ 2) = (j : ℝ) *
      (_root_.GD.N0107.d009084 x ^ 2 + 2 * (_root_.GD.N0126.d006422 x / (2 * j))) := by
  letI : NeZero j := ⟨hj.ne'⟩
  rw [_root_.GD.N0126.d006428]
  simp only [_root_.GD.N0126.d006419, Fintype.card_fin, _root_.GD.N0107.d009084]
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  field_simp [hjR]
  ring

private theorem d019855 {j : ℕ} (hj : 0 < j) (x : _root_.GD.N0137.d008894 j) :
    (∑ i, x i) = (j : ℝ) * _root_.GD.N0107.d009084 x := by
  unfold _root_.GD.N0107.d009084 _root_.GD.N0126.d006420 _root_.GD.N0126.d006419
  simp only [Fintype.card_fin]
  exact (mul_div_cancel₀ _ (by exact_mod_cast hj.ne' : (j : ℝ) ≠ 0)).symm

theorem d019856 (hm : 0 < m) (hn : 0 < n) (q : _root_.GD.N0232.N0720.N1329.d019646) (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    _root_.GD.N0232.N0720.N1316.d004441 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim q) x =
      _root_.GD.N0232.N0720.N1315.d019834 m q * ((_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 0) ^ 2 +
        2 * _root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 2) +
      _root_.GD.N0232.N0720.N1315.d019835 n q * ((_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 1) ^ 2 +
        2 * _root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 3) := by
  rw [_root_.GD.N0232.N0720.N1315.d019852 hdim, _root_.GD.N0232.N0720.N1315.d019854 hm, _root_.GD.N0232.N0720.N1315.d019854 hn]
  simp only [_root_.GD.N0232.N0720.N1315.d019850, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    _root_.GD.N0232.N0720.N1315.d019834, _root_.GD.N0232.N0720.N1315.d019835]
  ring

theorem d019857 (hm : 0 < m) (hn : 0 < n) (q : _root_.GD.N0232.N0720.N1329.d019646) (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    _root_.GD.N0232.N0720.N1316.d004442 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim q) x =
      q.1 * (_root_.GD.N0232.N0720.N1315.d019834 m q * _root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 0 +
        _root_.GD.N0232.N0720.N1315.d019835 n q * _root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 1) := by
  rw [_root_.GD.N0232.N0720.N1315.d019853 hdim, _root_.GD.N0232.N0720.N1315.d019855 hm, _root_.GD.N0232.N0720.N1315.d019855 hn]
  simp only [_root_.GD.N0232.N0720.N1315.d019850, Matrix.cons_val_zero, Matrix.cons_val_one,
    _root_.GD.N0232.N0720.N1315.d019834, _root_.GD.N0232.N0720.N1315.d019835]
  ring

def d019858 (q : _root_.GD.N0232.N0720.N1329.d019646) (x : _root_.GD.N0232.N0720.N1341.d004414 d) : ℝ :=
  _root_.GD.N0232.N0720.N1376.d002892 (_root_.GD.N0232.N0720.N1315.d019837 m n q) (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 0)
    (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 1) (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 2)
    (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 3)

def d019859 (q : _root_.GD.N0232.N0720.N1329.d019646) (x : _root_.GD.N0232.N0720.N1341.d004414 d) : ℝ :=
  _root_.GD.N0232.N0720.N1376.d002893 (_root_.GD.N0232.N0720.N1315.d019837 m n q) (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 0)
    (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 1)

theorem d019860 (hm : 0 < m) (hn : 0 < n) (q : _root_.GD.N0232.N0720.N1329.d019646) (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    _root_.GD.N0232.N0720.N1316.d004441 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim q) x =
      _root_.GD.N0232.N0720.N1315.d019843 m n q ^ 2 * _root_.GD.N0232.N0720.N1315.d019858 hdim q x := by
  rw [_root_.GD.N0232.N0720.N1315.d019856 hdim hm hn, _root_.GD.N0232.N0720.N1315.d019846 hm hn]
  unfold _root_.GD.N0232.N0720.N1315.d019858 _root_.GD.N0232.N0720.N1376.d002892 _root_.GD.N0232.N0720.N1315.d019837
  field_simp [(_root_.GD.N0232.N0720.N1315.d019840 hm hn q).ne']
  unfold _root_.GD.N0232.N0720.N1315.d019836
  ring

theorem d019861 (hm : 0 < m) (hn : 0 < n) (q : _root_.GD.N0232.N0720.N1329.d019646) (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    _root_.GD.N0232.N0720.N1316.d004442 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim q) x =
      _root_.GD.N0232.N0720.N1315.d019843 m n q * (_root_.GD.N0232.N0720.N1315.d019859 hdim q x * _root_.GD.N0232.N0720.N1315.d019844 m n q) := by
  have hB : _root_.GD.N0232.N0720.N1315.d019836 m n q * _root_.GD.N0232.N0720.N1315.d019859 hdim q x =
      _root_.GD.N0232.N0720.N1315.d019834 m q * _root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 0 +
        _root_.GD.N0232.N0720.N1315.d019835 n q * _root_.GD.N0232.N0720.N1315.d019850 m n d hdim x 1 := by
    unfold _root_.GD.N0232.N0720.N1315.d019859 _root_.GD.N0232.N0720.N1376.d002893 _root_.GD.N0232.N0720.N1315.d019837
    field_simp [(_root_.GD.N0232.N0720.N1315.d019840 hm hn q).ne']
    unfold _root_.GD.N0232.N0720.N1315.d019836
    ring
  rw [_root_.GD.N0232.N0720.N1315.d019857 hdim hm hn, ← hB, ← _root_.GD.N0232.N0720.N1315.d019846 hm hn]
  unfold _root_.GD.N0232.N0720.N1315.d019844
  ring

def d019862 (q : _root_.GD.N0232.N0720.N1329.d019646) : ℝ :=
  _root_.GD.N0232.N0720.N1316.d004444 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim q) * (_root_.GD.N0232.N0720.N1315.d019843 m n q ^ (d + 3))⁻¹

theorem d019863 (hm : 0 < m) (hn : 0 < n) (q : _root_.GD.N0232.N0720.N1329.d019646) :
    0 < _root_.GD.N0232.N0720.N1315.d019862 hdim q :=
  mul_pos (_root_.GD.N0232.N0720.N1316.d004447 _) (inv_pos.mpr (pow_pos (_root_.GD.N0232.N0720.N1315.d019845 hm hn q) _))

theorem d019864 (hm : 0 < m) (hn : 0 < n)
    (q : _root_.GD.N0232.N0720.N1329.d019646) (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    _root_.GD.N0232.N0720.N1316.d004444 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim q) *
      _root_.GD.N0232.N0720.N1377.d002852 (d + 2) (_root_.GD.N0232.N0720.N1316.d004441 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim q) x)
        (_root_.GD.N0232.N0720.N1316.d004442 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim q) x) =
      _root_.GD.N0232.N0720.N1315.d019862 hdim q *
        _root_.GD.N0232.N0720.N1315.d019848 d (_root_.GD.N0232.N0720.N1315.d019847 m n hm hn q) (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x) := by
  rw [_root_.GD.N0232.N0720.N1315.d019860 hdim hm hn, _root_.GD.N0232.N0720.N1315.d019861 hdim hm hn,
    _root_.GD.N0232.N0720.N1377.d002866 (d + 2) (_root_.GD.N0232.N0720.N1315.d019858 hdim q x)
      (_root_.GD.N0232.N0720.N1315.d019859 hdim q x * _root_.GD.N0232.N0720.N1315.d019844 m n q) (_root_.GD.N0232.N0720.N1315.d019845 hm hn q)]
  simp only [_root_.GD.N0232.N0720.N1315.d019862, _root_.GD.N0232.N0720.N1315.d019848, _root_.GD.N0232.N0720.N1315.d019847, _root_.GD.N0232.N0720.N1315.d019858, _root_.GD.N0232.N0720.N1315.d019859,
    Nat.add_assoc, Nat.reduceAdd]
  ring

theorem d019865 (hm : 0 < m) (hn : 0 < n)
    (q : _root_.GD.N0232.N0720.N1329.d019646) (x : _root_.GD.N0232.N0720.N1341.d004414 d) :
    _root_.GD.N0232.N0720.N1316.d004444 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim q) * q.1 *
      _root_.GD.N0232.N0720.N1377.d002852 (d + 1) (_root_.GD.N0232.N0720.N1316.d004441 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim q) x)
        (_root_.GD.N0232.N0720.N1316.d004442 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim q) x) =
      _root_.GD.N0232.N0720.N1315.d019862 hdim q *
        _root_.GD.N0232.N0720.N1315.d019849 d (_root_.GD.N0232.N0720.N1315.d019847 m n hm hn q) (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim x) := by
  rw [_root_.GD.N0232.N0720.N1315.d019860 hdim hm hn, _root_.GD.N0232.N0720.N1315.d019861 hdim hm hn,
    _root_.GD.N0232.N0720.N1377.d002866 (d + 1) (_root_.GD.N0232.N0720.N1315.d019858 hdim q x)
      (_root_.GD.N0232.N0720.N1315.d019859 hdim q x * _root_.GD.N0232.N0720.N1315.d019844 m n q) (_root_.GD.N0232.N0720.N1315.d019845 hm hn q)]
  simp only [_root_.GD.N0232.N0720.N1315.d019862, _root_.GD.N0232.N0720.N1315.d019849, _root_.GD.N0232.N0720.N1315.d019847, _root_.GD.N0232.N0720.N1315.d019858, _root_.GD.N0232.N0720.N1315.d019859,
    Nat.add_assoc, Nat.reduceAdd, _root_.GD.N0232.N0720.N1315.d019844]
  have hpower : _root_.GD.N0232.N0720.N1315.d019843 m n q ^ (d + 3) =
      _root_.GD.N0232.N0720.N1315.d019843 m n q ^ (d + 2) * _root_.GD.N0232.N0720.N1315.d019843 m n q := by
    rw [show d + 3 = (d + 2) + 1 by omega, pow_succ]
  rw [hpower]
  field_simp [(_root_.GD.N0232.N0720.N1315.d019845 hm hn q).ne']

end ActualCoordinates

section ProbabilityNormalization

variable {m n d : ℕ} (hdim : m + n = d + 1) (hm : 0 < m) (hn : 0 < n)
variable {I : Type*} [Fintype I]

def d019866 (q : I → _root_.GD.N0232.N0720.N1329.d019646) (w : I → ℝ) (i : I) : ℝ :=
  w i * _root_.GD.N0232.N0720.N1315.d019862 hdim (q i)

def d019867 (q : I → _root_.GD.N0232.N0720.N1329.d019646) (w : I → ℝ) : ℝ :=
  ∑ i, _root_.GD.N0232.N0720.N1315.d019866 hdim q w i

omit [Fintype I] in
include hm hn in
theorem d019868 (q : I → _root_.GD.N0232.N0720.N1329.d019646) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (i : I) : 0 ≤ _root_.GD.N0232.N0720.N1315.d019866 hdim q w i :=
  mul_nonneg (hw i) (_root_.GD.N0232.N0720.N1315.d019863 hdim hm hn _).le

include hm hn in
theorem d019869 (q : I → _root_.GD.N0232.N0720.N1329.d019646) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) : 0 < _root_.GD.N0232.N0720.N1315.d019867 hdim q w := by
  obtain ⟨j, hj⟩ := hp
  exact Finset.sum_pos' (fun i _ ↦ _root_.GD.N0232.N0720.N1315.d019868 hdim hm hn q w hw i)
    ⟨j, Finset.mem_univ j, mul_pos hj (_root_.GD.N0232.N0720.N1315.d019863 hdim hm hn _)⟩

def d019870 (q : I → _root_.GD.N0232.N0720.N1329.d019646) (w : I → ℝ) (i : I) : ℝ :=
  _root_.GD.N0232.N0720.N1315.d019866 hdim q w i / _root_.GD.N0232.N0720.N1315.d019867 hdim q w

include hm hn in
theorem d019871 (q : I → _root_.GD.N0232.N0720.N1329.d019646) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) (i : I) :
    0 ≤ _root_.GD.N0232.N0720.N1315.d019870 hdim q w i :=
  div_nonneg (_root_.GD.N0232.N0720.N1315.d019868 hdim hm hn q w hw i)
    (_root_.GD.N0232.N0720.N1315.d019869 hdim hm hn q w hw hp).le

include hm hn in
theorem d019872 (q : I → _root_.GD.N0232.N0720.N1329.d019646) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) : ∑ i, _root_.GD.N0232.N0720.N1315.d019870 hdim q w i = 1 := by
  simp only [_root_.GD.N0232.N0720.N1315.d019870, ← Finset.sum_div]
  exact div_self (_root_.GD.N0232.N0720.N1315.d019869 hdim hm hn q w hw hp).ne'



def d019873 (q : I → _root_.GD.N0232.N0720.N1329.d019646) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) : ProbabilityMeasure _root_.GD.N0232.N0720.N1315.d019832 :=
  ⟨∑ i, ENNReal.ofReal (_root_.GD.N0232.N0720.N1315.d019870 hdim q w i) •
      Measure.dirac (_root_.GD.N0232.N0720.N1315.d019847 m n hm hn (q i)), by
    refine ⟨?_⟩
    simp only [Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun i _ ↦ _root_.GD.N0232.N0720.N1315.d019871 hdim hm hn q w hw hp i),
      _root_.GD.N0232.N0720.N1315.d019872 hdim hm hn q w hw hp, ENNReal.ofReal_one]⟩

theorem d019874 (q : I → _root_.GD.N0232.N0720.N1329.d019646) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) (f : _root_.GD.N0232.N0720.N1315.d019832 → ℝ) :
    (∫ p, f p ∂(_root_.GD.N0232.N0720.N1315.d019873 hdim hm hn q w hw hp : Measure _root_.GD.N0232.N0720.N1315.d019832)) =
      ∑ i, _root_.GD.N0232.N0720.N1315.d019870 hdim q w i * f (_root_.GD.N0232.N0720.N1315.d019847 m n hm hn (q i)) := by
  change (∫ p, f p ∂(∑ i, ENNReal.ofReal (_root_.GD.N0232.N0720.N1315.d019870 hdim q w i) •
    Measure.dirac (_root_.GD.N0232.N0720.N1315.d019847 m n hm hn (q i)))) = _
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1315.d019871 hdim hm hn q w hw hp i), smul_eq_mul]
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure (by simp)

theorem d019875 (q : I → _root_.GD.N0232.N0720.N1329.d019646) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) (f : _root_.GD.N0232.N0720.N1315.d019832 → ℝ) :
    (∫ p, f p ∂(_root_.GD.N0232.N0720.N1315.d019873 hdim hm hn q w hw hp : Measure _root_.GD.N0232.N0720.N1315.d019832)) =
      (_root_.GD.N0232.N0720.N1315.d019867 hdim q w)⁻¹ *
        ∑ i, _root_.GD.N0232.N0720.N1315.d019866 hdim q w i * f (_root_.GD.N0232.N0720.N1315.d019847 m n hm hn (q i)) := by
  rw [_root_.GD.N0232.N0720.N1315.d019874, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold _root_.GD.N0232.N0720.N1315.d019870
  ring

theorem d019876 (q : I → _root_.GD.N0232.N0720.N1329.d019646) (w : I → ℝ) (u : _root_.GD.N0232.N0720.N1341.d004415 d) :
    _root_.GD.N0232.N0720.N1314.d019698 (fun i ↦ _root_.GD.N0232.N0720.N1329.d019660 m n d hdim (q i)) w u =
      ∑ i, _root_.GD.N0232.N0720.N1315.d019866 hdim q w i *
        _root_.GD.N0232.N0720.N1315.d019848 d (_root_.GD.N0232.N0720.N1315.d019847 m n hm hn (q i)) (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim u) := by
  rw [_root_.GD.N0232.N0720.N1314.d019702]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, _root_.GD.N0232.N0720.N1315.d019864 hdim hm hn]
  unfold _root_.GD.N0232.N0720.N1315.d019866
  ring

theorem d019877 (q : I → _root_.GD.N0232.N0720.N1329.d019646) (w : I → ℝ) (u : _root_.GD.N0232.N0720.N1341.d004415 d) :
    _root_.GD.N0232.N0720.N1314.d019699 (fun i ↦ _root_.GD.N0232.N0720.N1329.d019660 m n d hdim (q i)) w u =
      ∑ i, _root_.GD.N0232.N0720.N1315.d019866 hdim q w i *
        _root_.GD.N0232.N0720.N1315.d019849 d (_root_.GD.N0232.N0720.N1315.d019847 m n hm hn (q i)) (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim u) := by
  rw [_root_.GD.N0232.N0720.N1314.d019703]
  apply Finset.sum_congr rfl
  intro i _
  change w i * _root_.GD.N0232.N0720.N1316.d004444 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim (q i)) * (q i).1 *
    _root_.GD.N0232.N0720.N1377.d002852 (d + 1) (_root_.GD.N0232.N0720.N1316.d004441 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim (q i)) u)
      (_root_.GD.N0232.N0720.N1316.d004442 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim (q i)) u) = _
  calc
    _ = w i * (_root_.GD.N0232.N0720.N1316.d004444 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim (q i)) * (q i).1 *
        _root_.GD.N0232.N0720.N1377.d002852 (d + 1) (_root_.GD.N0232.N0720.N1316.d004441 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim (q i)) u)
          (_root_.GD.N0232.N0720.N1316.d004442 (_root_.GD.N0232.N0720.N1329.d019660 m n d hdim (q i)) u)) := by ring
    _ = _ := by
      rw [_root_.GD.N0232.N0720.N1315.d019865 hdim hm hn]
      unfold _root_.GD.N0232.N0720.N1315.d019866
      ring



theorem d019878 (q : I → _root_.GD.N0232.N0720.N1329.d019646) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∃ i, 0 < w i) (u : _root_.GD.N0232.N0720.N1341.d004415 d) :
    (∫ p, _root_.GD.N0232.N0720.N1315.d019849 d p (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim u)
      ∂(_root_.GD.N0232.N0720.N1315.d019873 hdim hm hn q w hw hp : Measure _root_.GD.N0232.N0720.N1315.d019832)) /
      (∫ p, _root_.GD.N0232.N0720.N1315.d019848 d p (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim u)
        ∂(_root_.GD.N0232.N0720.N1315.d019873 hdim hm hn q w hw hp : Measure _root_.GD.N0232.N0720.N1315.d019832)) =
      _root_.GD.N0232.N0720.N1314.d019699 (fun i ↦ _root_.GD.N0232.N0720.N1329.d019660 m n d hdim (q i)) w u /
        _root_.GD.N0232.N0720.N1314.d019698 (fun i ↦ _root_.GD.N0232.N0720.N1329.d019660 m n d hdim (q i)) w u := by
  rw [_root_.GD.N0232.N0720.N1315.d019875, _root_.GD.N0232.N0720.N1315.d019875,
    _root_.GD.N0232.N0720.N1315.d019877 hdim hm hn, _root_.GD.N0232.N0720.N1315.d019876 hdim hm hn]
  exact mul_div_mul_left _ _ (inv_ne_zero (_root_.GD.N0232.N0720.N1315.d019869 hdim hm hn q w hw hp).ne')

end ProbabilityNormalization

section Sequence

variable {m n d : ℕ} (hdim : m + n = d + 1) (hm : 0 < m) (hn : 0 < n)

def d019879 {I : Type*} (q : I → _root_.GD.N0232.N0720.N1329.d019646) : Option I → _root_.GD.N0232.N0720.N1329.d019646
  | none => _root_.GD.N0232.N0720.N1314.d019712
  | some i => q i

theorem d019880 {I : Type*} (q : I → _root_.GD.N0232.N0720.N1329.d019646) :
    _root_.GD.N0232.N0720.N1314.d019719 hdim q = fun i ↦ _root_.GD.N0232.N0720.N1329.d019660 m n d hdim (_root_.GD.N0232.N0720.N1315.d019879 q i) := by
  funext i
  cases i <;> rfl

include hm hn in


theorem d019881 (h : _root_.GD.N0232.N0720.N1341.d004417 d)
    (hadmissible : _root_.GD.N0230.N0556.d000031 (_root_.GD.N0232.N0720.N1314.d019711 m n d hdim) h) :
    ∃ ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1315.d019832, ∀ᵐ u : _root_.GD.N0232.N0720.N1341.d004415 d ∂_root_.GD.N0232.N0720.N1341.d004416 d,
      Tendsto (fun j ↦
        (∫ p, _root_.GD.N0232.N0720.N1315.d019849 d p (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim u) ∂(ν j : Measure _root_.GD.N0232.N0720.N1315.d019832)) /
          (∫ p, _root_.GD.N0232.N0720.N1315.d019848 d p (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim u) ∂(ν j : Measure _root_.GD.N0232.N0720.N1315.d019832)))
        atTop (𝓝 (h u)) := by
  obtain ⟨w, ns, hw, _hns, hlimit⟩ :=
    _root_.GD.N0232.N0720.N1314.d019732 hdim h hadmissible
  let ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1315.d019832 := fun j ↦
    _root_.GD.N0232.N0720.N1315.d019873 hdim hm hn
      (_root_.GD.N0232.N0720.N1315.d019879 (fun i : Fin (ns j) ↦ _root_.GD.N0232.N0720.N1314.d019725 i))
      (_root_.GD.N0232.N0720.N1314.d019720 (w (ns j)))
      (_root_.GD.N0232.N0720.N1314.d019721 _ (hw (ns j))) (_root_.GD.N0232.N0720.N1314.d019722 _)
  refine ⟨ν, ?_⟩
  filter_upwards [hlimit] with u hu
  have heq (j : ℕ) :
      (∫ p, _root_.GD.N0232.N0720.N1315.d019849 d p (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim u) ∂(ν j : Measure _root_.GD.N0232.N0720.N1315.d019832)) /
        (∫ p, _root_.GD.N0232.N0720.N1315.d019848 d p (_root_.GD.N0232.N0720.N1315.d019850 m n d hdim u) ∂(ν j : Measure _root_.GD.N0232.N0720.N1315.d019832)) =
      _root_.GD.N0232.N0720.N1314.d019699 (_root_.GD.N0232.N0720.N1314.d019719 hdim (fun i : Fin (ns j) ↦ _root_.GD.N0232.N0720.N1314.d019725 i))
          (_root_.GD.N0232.N0720.N1314.d019720 (w (ns j))) u /
        _root_.GD.N0232.N0720.N1314.d019698 (_root_.GD.N0232.N0720.N1314.d019719 hdim (fun i : Fin (ns j) ↦ _root_.GD.N0232.N0720.N1314.d019725 i))
          (_root_.GD.N0232.N0720.N1314.d019720 (w (ns j))) u := by
    simpa only [ν, _root_.GD.N0232.N0720.N1315.d019880] using
      _root_.GD.N0232.N0720.N1315.d019878 hdim hm hn
        (_root_.GD.N0232.N0720.N1315.d019879 (fun i : Fin (ns j) ↦ _root_.GD.N0232.N0720.N1314.d019725 i))
        (_root_.GD.N0232.N0720.N1314.d019720 (w (ns j)))
        (_root_.GD.N0232.N0720.N1314.d019721 _ (hw (ns j))) (_root_.GD.N0232.N0720.N1314.d019722 _) u
  simpa only [heq] using hu

end Sequence

end
end GD.N0232.N0720.N1315

#print axioms _root_.GD.N0232.N0720.N1315.d019842
#print axioms _root_.GD.N0232.N0720.N1315.d019860
#print axioms _root_.GD.N0232.N0720.N1315.d019861
#print axioms _root_.GD.N0232.N0720.N1315.d019865
#print axioms _root_.GD.N0232.N0720.N1315.d019878
#print axioms _root_.GD.N0232.N0720.N1315.d019881
