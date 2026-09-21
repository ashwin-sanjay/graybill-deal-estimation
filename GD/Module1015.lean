import GD.Module0653
import GD.Module0860
import GD.Module1014


























open Set
open scoped BigOperators

namespace GD
namespace N0232
namespace N0720
namespace N1151

noncomputable section

open _root_.GD.N0232.N0719.N0857
open _root_.GD.N0232.N0719.N0955
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1492



abbrev d016145 := _root_.GD.N0232.N0719.N0857.d009377 3


def d016146 : Set _root_.GD.N0232.N0720.N1151.d016145 :=
  _root_.GD.N0232.N0719.N0955.d009607 3


def d016147 (v : _root_.GD.N0232.N0720.N1151.d016145) : ℝ := v 0


def d016148 (v : _root_.GD.N0232.N0720.N1151.d016145) : ℝ := v 1


def d016149 (v : _root_.GD.N0232.N0720.N1151.d016145) : ℝ :=
  1 - _root_.GD.N0232.N0720.N1151.d016147 v - _root_.GD.N0232.N0720.N1151.d016148 v


def d016150 (q : ℝ) (v : _root_.GD.N0232.N0720.N1151.d016145) : ℝ :=
  q * _root_.GD.N0232.N0720.N1151.d016147 v + (1 - q) * _root_.GD.N0232.N0720.N1151.d016149 v


def d016151 (q : ℝ) (v : _root_.GD.N0232.N0720.N1151.d016145) : ℝ :=
  q * _root_.GD.N0232.N0720.N1151.d016147 v / _root_.GD.N0232.N0720.N1151.d016150 q v


def d016152 (q : ℝ) (v : _root_.GD.N0232.N0720.N1151.d016145) : ℝ :=
  _root_.GD.N0232.N0720.N1151.d016148 v / _root_.GD.N0232.N0720.N1151.d016150 q v


def d016153 (q : ℝ) (v : _root_.GD.N0232.N0720.N1151.d016145) : _root_.GD.N0232.N0720.N1436.d013217 :=
  (_root_.GD.N0232.N0720.N1151.d016151 q v, _root_.GD.N0232.N0720.N1151.d016152 q v)


def d016154 (q : ℝ) (p : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  p.1 * (1 - q) / _root_.GD.N0232.N0720.N1492.d016123 p.1 p.2 q


def d016155 (q : ℝ) (p : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  (1 - p.1) * q / _root_.GD.N0232.N0720.N1492.d016123 p.1 p.2 q


def d016156 (q : ℝ) (p : _root_.GD.N0232.N0720.N1436.d013217) : ℝ :=
  p.2 * q * (1 - q) / _root_.GD.N0232.N0720.N1492.d016123 p.1 p.2 q



def d016157 (q : ℝ) (p : _root_.GD.N0232.N0720.N1436.d013217) : _root_.GD.N0232.N0720.N1151.d016145 :=
  ![_root_.GD.N0232.N0720.N1151.d016154 q p, _root_.GD.N0232.N0720.N1151.d016156 q p]

@[simp] theorem d016158 (x z : ℝ) :
    _root_.GD.N0232.N0720.N1151.d016147 ![x, z] = x := rfl

@[simp] theorem d016159 (x z : ℝ) :
    _root_.GD.N0232.N0720.N1151.d016148 ![x, z] = z := rfl

theorem d016160 {v : _root_.GD.N0232.N0720.N1151.d016145} (hv : v ∈ _root_.GD.N0232.N0720.N1151.d016146) :
    0 < _root_.GD.N0232.N0720.N1151.d016147 v := by
  exact hv.1 0

theorem d016161 {v : _root_.GD.N0232.N0720.N1151.d016145} (hv : v ∈ _root_.GD.N0232.N0720.N1151.d016146) :
    0 < _root_.GD.N0232.N0720.N1151.d016148 v := by
  exact hv.1 1

theorem d016162 {v : _root_.GD.N0232.N0720.N1151.d016145} (hv : v ∈ _root_.GD.N0232.N0720.N1151.d016146) :
    0 < _root_.GD.N0232.N0720.N1151.d016149 v := by
  have hsum : _root_.GD.N0232.N0720.N1151.d016147 v + _root_.GD.N0232.N0720.N1151.d016148 v < 1 := by
    simpa [_root_.GD.N0232.N0720.N1151.d016146, _root_.GD.N0232.N0719.N0955.d009607, _root_.GD.N0232.N0720.N1151.d016147, _root_.GD.N0232.N0720.N1151.d016148,
      Fin.sum_univ_two] using hv.2
  unfold _root_.GD.N0232.N0720.N1151.d016149
  linarith

theorem d016163
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    {v : _root_.GD.N0232.N0720.N1151.d016145} (hv : v ∈ _root_.GD.N0232.N0720.N1151.d016146) :
    0 < _root_.GD.N0232.N0720.N1151.d016150 q v := by
  exact add_pos
    (mul_pos hq.1 (_root_.GD.N0232.N0720.N1151.d016160 hv))
    (mul_pos (sub_pos.mpr hq.2) (_root_.GD.N0232.N0720.N1151.d016162 hv))

theorem d016164
    {q : ℝ} {v : _root_.GD.N0232.N0720.N1151.d016145} (hL : _root_.GD.N0232.N0720.N1151.d016150 q v ≠ 0) :
    1 - _root_.GD.N0232.N0720.N1151.d016151 q v =
      (1 - q) * _root_.GD.N0232.N0720.N1151.d016149 v / _root_.GD.N0232.N0720.N1151.d016150 q v := by
  unfold _root_.GD.N0232.N0720.N1151.d016151
  field_simp [hL]
  simp only [_root_.GD.N0232.N0720.N1151.d016150]
  ring



def d016165 (p q : ℝ) (v : _root_.GD.N0232.N0720.N1151.d016145) : ℝ :=
  q * (1 - p) * _root_.GD.N0232.N0720.N1151.d016147 v +
    (1 - q) * p * _root_.GD.N0232.N0720.N1151.d016149 v +
      p * (1 - p) * _root_.GD.N0232.N0720.N1151.d016148 v

theorem d016166
    {p q : ℝ} {v : _root_.GD.N0232.N0720.N1151.d016145} (hL : _root_.GD.N0232.N0720.N1151.d016150 q v ≠ 0) :
    _root_.GD.N0232.N0720.N1492.d016123 (_root_.GD.N0232.N0720.N1151.d016153 q v).1 (_root_.GD.N0232.N0720.N1151.d016153 q v).2 p =
      _root_.GD.N0232.N0720.N1151.d016165 p q v / _root_.GD.N0232.N0720.N1151.d016150 q v := by
  unfold _root_.GD.N0232.N0720.N1151.d016153 _root_.GD.N0232.N0720.N1151.d016151 _root_.GD.N0232.N0720.N1151.d016152 _root_.GD.N0232.N0720.N1151.d016165
    _root_.GD.N0232.N0720.N1492.d016123
  field_simp [hL]
  simp only [_root_.GD.N0232.N0720.N1151.d016150]
  ring



theorem d016167
    {q : ℝ} {v : _root_.GD.N0232.N0720.N1151.d016145} (hL : _root_.GD.N0232.N0720.N1151.d016150 q v ≠ 0) :
    _root_.GD.N0232.N0720.N1492.d016123 (_root_.GD.N0232.N0720.N1151.d016153 q v).1 (_root_.GD.N0232.N0720.N1151.d016153 q v).2 q =
      q * (1 - q) / _root_.GD.N0232.N0720.N1151.d016150 q v := by
  rw [_root_.GD.N0232.N0720.N1151.d016166 hL]
  unfold _root_.GD.N0232.N0720.N1151.d016165 _root_.GD.N0232.N0720.N1151.d016150 _root_.GD.N0232.N0720.N1151.d016149
  ring

theorem d016168
    {q : ℝ} {v : _root_.GD.N0232.N0720.N1151.d016145} (hL : _root_.GD.N0232.N0720.N1151.d016150 q v ≠ 0) :
    _root_.GD.N0232.N0720.N1151.d016151 q v * (1 - _root_.GD.N0232.N0720.N1151.d016151 q v) * _root_.GD.N0232.N0720.N1151.d016152 q v =
      q * (1 - q) * _root_.GD.N0232.N0720.N1151.d016147 v * _root_.GD.N0232.N0720.N1151.d016149 v * _root_.GD.N0232.N0720.N1151.d016148 v /
        _root_.GD.N0232.N0720.N1151.d016150 q v ^ 3 := by
  rw [_root_.GD.N0232.N0720.N1151.d016164 hL]
  unfold _root_.GD.N0232.N0720.N1151.d016151 _root_.GD.N0232.N0720.N1151.d016152
  field_simp [hL]

theorem d016169
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    {v : _root_.GD.N0232.N0720.N1151.d016145} (hv : v ∈ _root_.GD.N0232.N0720.N1151.d016146) :
    _root_.GD.N0232.N0720.N1151.d016153 q v ∈ _root_.GD.N0232.N0720.N1436.d013218 := by
  have hL := _root_.GD.N0232.N0720.N1151.d016163 hq hv
  have hx := _root_.GD.N0232.N0720.N1151.d016160 hv
  have hy := _root_.GD.N0232.N0720.N1151.d016162 hv
  have hz := _root_.GD.N0232.N0720.N1151.d016161 hv
  have hqx : 0 < q * _root_.GD.N0232.N0720.N1151.d016147 v := mul_pos hq.1 hx
  have htail : 0 < (1 - q) * _root_.GD.N0232.N0720.N1151.d016149 v :=
    mul_pos (sub_pos.mpr hq.2) hy
  constructor
  · constructor
    · simpa [_root_.GD.N0232.N0720.N1151.d016153, _root_.GD.N0232.N0720.N1151.d016151] using div_pos hqx hL
    · change q * _root_.GD.N0232.N0720.N1151.d016147 v / _root_.GD.N0232.N0720.N1151.d016150 q v < 1
      rw [div_lt_one hL]
      unfold _root_.GD.N0232.N0720.N1151.d016150
      linarith
  · simpa [_root_.GD.N0232.N0720.N1151.d016153, _root_.GD.N0232.N0720.N1151.d016152] using div_pos hz hL

theorem d016170
    {q : ℝ} {p : _root_.GD.N0232.N0720.N1436.d013217}
    (hQ : _root_.GD.N0232.N0720.N1492.d016123 p.1 p.2 q ≠ 0) :
    _root_.GD.N0232.N0720.N1151.d016149 (_root_.GD.N0232.N0720.N1151.d016157 q p) = _root_.GD.N0232.N0720.N1151.d016155 q p := by
  unfold _root_.GD.N0232.N0720.N1151.d016149 _root_.GD.N0232.N0720.N1151.d016147 _root_.GD.N0232.N0720.N1151.d016148 _root_.GD.N0232.N0720.N1151.d016157 _root_.GD.N0232.N0720.N1151.d016154 _root_.GD.N0232.N0720.N1151.d016155 _root_.GD.N0232.N0720.N1151.d016156
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [hQ]
  simp only [_root_.GD.N0232.N0720.N1492.d016123]
  ring

theorem d016171
    {q : ℝ} {p : _root_.GD.N0232.N0720.N1436.d013217}
    (hQ : _root_.GD.N0232.N0720.N1492.d016123 p.1 p.2 q ≠ 0) :
    _root_.GD.N0232.N0720.N1151.d016150 q (_root_.GD.N0232.N0720.N1151.d016157 q p) =
      q * (1 - q) / _root_.GD.N0232.N0720.N1492.d016123 p.1 p.2 q := by
  unfold _root_.GD.N0232.N0720.N1151.d016150
  rw [_root_.GD.N0232.N0720.N1151.d016170 hQ]
  simp only [_root_.GD.N0232.N0720.N1151.d016147, _root_.GD.N0232.N0720.N1151.d016157, Matrix.cons_val_zero]
  unfold _root_.GD.N0232.N0720.N1151.d016154 _root_.GD.N0232.N0720.N1151.d016155
  field_simp [hQ]
  ring

theorem d016172
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    {p : _root_.GD.N0232.N0720.N1436.d013217} (hp : p ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0232.N0720.N1151.d016157 q p ∈ _root_.GD.N0232.N0720.N1151.d016146 := by
  have hQpos : 0 < _root_.GD.N0232.N0720.N1492.d016123 p.1 p.2 q :=
    _root_.GD.N0232.N0720.N1492.d016129 hp.1 hp.2 ⟨q, hq.1, hq.2⟩
  have hx : 0 < _root_.GD.N0232.N0720.N1151.d016154 q p := by
    exact div_pos (mul_pos hp.1.1 (sub_pos.mpr hq.2)) hQpos
  have hy : 0 < _root_.GD.N0232.N0720.N1151.d016155 q p := by
    exact div_pos (mul_pos (sub_pos.mpr hp.1.2) hq.1) hQpos
  have hz : 0 < _root_.GD.N0232.N0720.N1151.d016156 q p := by
    exact div_pos
      (mul_pos (mul_pos hp.2 hq.1) (sub_pos.mpr hq.2)) hQpos
  constructor
  · intro j
    fin_cases j
    · simpa [_root_.GD.N0232.N0720.N1151.d016157, _root_.GD.N0232.N0720.N1151.d016154] using hx
    · simpa [_root_.GD.N0232.N0720.N1151.d016157, _root_.GD.N0232.N0720.N1151.d016156] using hz
  · have hy' : 0 < _root_.GD.N0232.N0720.N1151.d016149 (_root_.GD.N0232.N0720.N1151.d016157 q p) := by
      rw [_root_.GD.N0232.N0720.N1151.d016170 hQpos.ne']
      exact hy
    change 0 < 1 - ∑ j, _root_.GD.N0232.N0720.N1151.d016157 q p j
    have hy'' : 0 < 1 - _root_.GD.N0232.N0720.N1151.d016157 q p 0 - _root_.GD.N0232.N0720.N1151.d016157 q p 1 := by
      simpa [_root_.GD.N0232.N0720.N1151.d016149, _root_.GD.N0232.N0720.N1151.d016147, _root_.GD.N0232.N0720.N1151.d016148] using hy'
    rw [Fin.sum_univ_two]
    linarith


theorem d016173
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    {v : _root_.GD.N0232.N0720.N1151.d016145} (hv : v ∈ _root_.GD.N0232.N0720.N1151.d016146) :
    _root_.GD.N0232.N0720.N1151.d016157 q (_root_.GD.N0232.N0720.N1151.d016153 q v) = v := by
  have hL := (_root_.GD.N0232.N0720.N1151.d016163 hq hv).ne'
  have hq0 : q ≠ 0 := hq.1.ne'
  have hq1 : 1 - q ≠ 0 := (sub_pos.mpr hq.2).ne'
  have hQ := _root_.GD.N0232.N0720.N1151.d016167 (q := q) (v := v) hL
  funext j
  fin_cases j
  · change _root_.GD.N0232.N0720.N1151.d016154 q (_root_.GD.N0232.N0720.N1151.d016153 q v) = _root_.GD.N0232.N0720.N1151.d016147 v
    unfold _root_.GD.N0232.N0720.N1151.d016154
    rw [hQ]
    simp only [_root_.GD.N0232.N0720.N1151.d016153, _root_.GD.N0232.N0720.N1151.d016151]
    field_simp [hL, hq0, hq1]
  · change _root_.GD.N0232.N0720.N1151.d016156 q (_root_.GD.N0232.N0720.N1151.d016153 q v) = _root_.GD.N0232.N0720.N1151.d016148 v
    unfold _root_.GD.N0232.N0720.N1151.d016156
    rw [hQ]
    simp only [_root_.GD.N0232.N0720.N1151.d016153, _root_.GD.N0232.N0720.N1151.d016152]
    field_simp [hL, hq0, hq1]


theorem d016174
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    {p : _root_.GD.N0232.N0720.N1436.d013217} (hp : p ∈ _root_.GD.N0232.N0720.N1436.d013218) :
    _root_.GD.N0232.N0720.N1151.d016153 q (_root_.GD.N0232.N0720.N1151.d016157 q p) = p := by
  have hQpos : 0 < _root_.GD.N0232.N0720.N1492.d016123 p.1 p.2 q :=
    _root_.GD.N0232.N0720.N1492.d016129 hp.1 hp.2 ⟨q, hq.1, hq.2⟩
  have hq0 : q ≠ 0 := hq.1.ne'
  have hq1 : 1 - q ≠ 0 := (sub_pos.mpr hq.2).ne'
  have hL := _root_.GD.N0232.N0720.N1151.d016171 (q := q) (p := p) hQpos.ne'
  apply Prod.ext
  · change _root_.GD.N0232.N0720.N1151.d016151 q (_root_.GD.N0232.N0720.N1151.d016157 q p) = p.1
    unfold _root_.GD.N0232.N0720.N1151.d016151
    rw [hL]
    simp only [_root_.GD.N0232.N0720.N1151.d016147, _root_.GD.N0232.N0720.N1151.d016157, Matrix.cons_val_zero]
    unfold _root_.GD.N0232.N0720.N1151.d016154
    field_simp [hQpos.ne', hq0, hq1]
  · change _root_.GD.N0232.N0720.N1151.d016152 q (_root_.GD.N0232.N0720.N1151.d016157 q p) = p.2
    unfold _root_.GD.N0232.N0720.N1151.d016152
    rw [hL]
    change _root_.GD.N0232.N0720.N1151.d016156 q p /
      (q * (1 - q) / _root_.GD.N0232.N0720.N1492.d016123 p.1 p.2 q) = p.2
    unfold _root_.GD.N0232.N0720.N1151.d016156
    field_simp [hQpos.ne', hq0, hq1]



def d016175 (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1151.d016146 ≃ _root_.GD.N0232.N0720.N1436.d013218 where
  toFun v := ⟨_root_.GD.N0232.N0720.N1151.d016153 q v, _root_.GD.N0232.N0720.N1151.d016169 hq v.property⟩
  invFun p := ⟨_root_.GD.N0232.N0720.N1151.d016157 q p, _root_.GD.N0232.N0720.N1151.d016172 hq p.property⟩
  left_inv v := Subtype.ext (_root_.GD.N0232.N0720.N1151.d016173 hq v.property)
  right_inv p := Subtype.ext (_root_.GD.N0232.N0720.N1151.d016174 hq p.property)


def d016176 (v : _root_.GD.N0232.N0720.N1151.d016145) : _root_.GD.N0232.N0720.N1151.d016145 :=
  ![_root_.GD.N0232.N0720.N1151.d016149 v, _root_.GD.N0232.N0720.N1151.d016148 v]

@[simp] theorem d016177 (v : _root_.GD.N0232.N0720.N1151.d016145) :
    _root_.GD.N0232.N0720.N1151.d016147 (_root_.GD.N0232.N0720.N1151.d016176 v) = _root_.GD.N0232.N0720.N1151.d016149 v := rfl

@[simp] theorem d016178 (v : _root_.GD.N0232.N0720.N1151.d016145) :
    _root_.GD.N0232.N0720.N1151.d016148 (_root_.GD.N0232.N0720.N1151.d016176 v) = _root_.GD.N0232.N0720.N1151.d016148 v := rfl

@[simp] theorem d016179 (v : _root_.GD.N0232.N0720.N1151.d016145) :
    _root_.GD.N0232.N0720.N1151.d016149 (_root_.GD.N0232.N0720.N1151.d016176 v) = _root_.GD.N0232.N0720.N1151.d016147 v := by
  simp only [_root_.GD.N0232.N0720.N1151.d016149, _root_.GD.N0232.N0720.N1151.d016176, _root_.GD.N0232.N0720.N1151.d016147, _root_.GD.N0232.N0720.N1151.d016148,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

@[simp] theorem d016180 (v : _root_.GD.N0232.N0720.N1151.d016145) :
    _root_.GD.N0232.N0720.N1151.d016176 (_root_.GD.N0232.N0720.N1151.d016176 v) = v := by
  funext j
  fin_cases j
  · simp [_root_.GD.N0232.N0720.N1151.d016176, _root_.GD.N0232.N0720.N1151.d016149, _root_.GD.N0232.N0720.N1151.d016147, _root_.GD.N0232.N0720.N1151.d016148]
    ring
  · simp [_root_.GD.N0232.N0720.N1151.d016176, _root_.GD.N0232.N0720.N1151.d016148]

theorem d016181
    {v : _root_.GD.N0232.N0720.N1151.d016145} (hv : v ∈ _root_.GD.N0232.N0720.N1151.d016146) :
    _root_.GD.N0232.N0720.N1151.d016176 v ∈ _root_.GD.N0232.N0720.N1151.d016146 := by
  constructor
  · intro j
    fin_cases j
    · change 0 < _root_.GD.N0232.N0720.N1151.d016149 v
      exact _root_.GD.N0232.N0720.N1151.d016162 hv
    · change 0 < _root_.GD.N0232.N0720.N1151.d016148 v
      exact _root_.GD.N0232.N0720.N1151.d016161 hv
  · change 0 < 1 - ∑ j, _root_.GD.N0232.N0720.N1151.d016176 v j
    rw [Fin.sum_univ_two]
    simp only [_root_.GD.N0232.N0720.N1151.d016176, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hx := _root_.GD.N0232.N0720.N1151.d016160 hv
    unfold _root_.GD.N0232.N0720.N1151.d016149
    linarith

@[simp] theorem d016182 (q : ℝ) (v : _root_.GD.N0232.N0720.N1151.d016145) :
    _root_.GD.N0232.N0720.N1151.d016150 (1 - q) (_root_.GD.N0232.N0720.N1151.d016176 v) = _root_.GD.N0232.N0720.N1151.d016150 q v := by
  unfold _root_.GD.N0232.N0720.N1151.d016150
  simp
  ring



theorem d016183
    {q : ℝ} {v : _root_.GD.N0232.N0720.N1151.d016145} (hL : _root_.GD.N0232.N0720.N1151.d016150 q v ≠ 0) :
    _root_.GD.N0232.N0720.N1151.d016153 (1 - q) (_root_.GD.N0232.N0720.N1151.d016176 v) =
      (1 - (_root_.GD.N0232.N0720.N1151.d016153 q v).1, (_root_.GD.N0232.N0720.N1151.d016153 q v).2) := by
  apply Prod.ext
  · change _root_.GD.N0232.N0720.N1151.d016151 (1 - q) (_root_.GD.N0232.N0720.N1151.d016176 v) = 1 - _root_.GD.N0232.N0720.N1151.d016151 q v
    rw [_root_.GD.N0232.N0720.N1151.d016164 hL]
    unfold _root_.GD.N0232.N0720.N1151.d016151
    rw [_root_.GD.N0232.N0720.N1151.d016182]
    simp
  · change _root_.GD.N0232.N0720.N1151.d016152 (1 - q) (_root_.GD.N0232.N0720.N1151.d016176 v) = _root_.GD.N0232.N0720.N1151.d016152 q v
    unfold _root_.GD.N0232.N0720.N1151.d016152
    rw [_root_.GD.N0232.N0720.N1151.d016182]
    simp

theorem d016184 (e F p : ℝ) :
    _root_.GD.N0232.N0720.N1492.d016123 (1 - e) F (1 - p) =
      _root_.GD.N0232.N0720.N1492.d016123 e F p := by
  unfold _root_.GD.N0232.N0720.N1492.d016123
  ring


theorem d016185
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    {v : _root_.GD.N0232.N0720.N1151.d016145} (hv : v ∈ _root_.GD.N0232.N0720.N1151.d016146) :
    3 * _root_.GD.N0232.N0720.N1151.d016152 q v * q * (1 - q) /
        _root_.GD.N0232.N0720.N1492.d016123 (_root_.GD.N0232.N0720.N1151.d016153 q v).1 (_root_.GD.N0232.N0720.N1151.d016153 q v).2 q =
      3 * _root_.GD.N0232.N0720.N1151.d016148 v := by
  have hL := (_root_.GD.N0232.N0720.N1151.d016163 hq hv).ne'
  have hq0 : q ≠ 0 := hq.1.ne'
  have hq1 : 1 - q ≠ 0 := (sub_pos.mpr hq.2).ne'
  rw [_root_.GD.N0232.N0720.N1151.d016167 hL]
  unfold _root_.GD.N0232.N0720.N1151.d016152
  field_simp [hL, hq0, hq1]




theorem d016186
    {q : ℝ} (hq : q ≠ 0) {v : _root_.GD.N0232.N0720.N1151.d016145}
    (hx : _root_.GD.N0232.N0720.N1151.d016147 v ≠ 0) (hy : _root_.GD.N0232.N0720.N1151.d016149 v = 0) :
    q * _root_.GD.N0232.N0720.N1151.d016152 q v = _root_.GD.N0232.N0720.N1151.d016148 v / _root_.GD.N0232.N0720.N1151.d016147 v := by
  unfold _root_.GD.N0232.N0720.N1151.d016152 _root_.GD.N0232.N0720.N1151.d016150
  rw [hy]
  field_simp [hq, hx]
  ring



theorem d016187
    {q : ℝ} (hq : q ≠ 0) {v : _root_.GD.N0232.N0720.N1151.d016145}
    (hx : _root_.GD.N0232.N0720.N1151.d016147 v ≠ 0) (hy : _root_.GD.N0232.N0720.N1151.d016149 v = 0) :
    _root_.GD.N0232.N0720.N1492.d016123 (_root_.GD.N0232.N0720.N1151.d016153 q v).1 (_root_.GD.N0232.N0720.N1151.d016153 q v).2 q =
      (1 - q) / _root_.GD.N0232.N0720.N1151.d016147 v := by
  have hL : _root_.GD.N0232.N0720.N1151.d016150 q v ≠ 0 := by
    unfold _root_.GD.N0232.N0720.N1151.d016150
    rw [hy]
    simpa using mul_ne_zero hq hx
  rw [_root_.GD.N0232.N0720.N1151.d016167 hL]
  unfold _root_.GD.N0232.N0720.N1151.d016150
  rw [hy]
  field_simp [hq, hx]
  ring



theorem d016188 (p F : ℝ) :
    _root_.GD.N0232.N0720.N1492.d016123 (1 / 2) F p =
      1 / 2 + p * (1 - p) * F := by
  unfold _root_.GD.N0232.N0720.N1492.d016123
  ring

end

end N1151
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1151.d016175
#print axioms _root_.GD.N0232.N0720.N1151.d016166
#print axioms _root_.GD.N0232.N0720.N1151.d016185
#print axioms _root_.GD.N0232.N0720.N1151.d016187
