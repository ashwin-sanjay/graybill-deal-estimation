import GD.Module1015











open Set

namespace GD
namespace N0232
namespace N0720
namespace N1153

noncomputable section

open _root_.GD.N0232.N0720.N1151
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1492


def d016204 (e F : ℝ) : ℝ :=
  Real.sqrt (F / (e * (1 - e)))


def d016205 (q e F : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1153.d016204 e F /
    _root_.GD.N0232.N0720.N1492.d016123 e F q ^ ((5 : ℝ) / 2)



theorem d016206
    {p q e F : ℝ}
    (hpN : 0 < _root_.GD.N0232.N0720.N1492.d016123 e F p)
    (hqN : 0 < _root_.GD.N0232.N0720.N1492.d016123 e F q)
    (hpref : _root_.GD.N0232.N0720.N1153.d016204 e F ≠ 0) :
    _root_.GD.N0232.N0720.N1153.d016205 p e F / _root_.GD.N0232.N0720.N1153.d016205 q e F =
      (_root_.GD.N0232.N0720.N1492.d016123 e F q /
        _root_.GD.N0232.N0720.N1492.d016123 e F p) ^ ((5 : ℝ) / 2) := by
  have hpPow :
      _root_.GD.N0232.N0720.N1492.d016123 e F p ^ ((5 : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hpN _)
  have hqPow :
      _root_.GD.N0232.N0720.N1492.d016123 e F q ^ ((5 : ℝ) / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hqN _)
  rw [_root_.GD.N0232.N0720.N1153.d016205]
  calc
    (_root_.GD.N0232.N0720.N1153.d016204 e F /
          _root_.GD.N0232.N0720.N1492.d016123 e F p ^ ((5 : ℝ) / 2)) /
        (_root_.GD.N0232.N0720.N1153.d016204 e F /
          _root_.GD.N0232.N0720.N1492.d016123 e F q ^ ((5 : ℝ) / 2)) =
      _root_.GD.N0232.N0720.N1492.d016123 e F q ^ ((5 : ℝ) / 2) /
        _root_.GD.N0232.N0720.N1492.d016123 e F p ^ ((5 : ℝ) / 2) := by
          field_simp [hpref, hpPow, hqPow]
    _ = (_root_.GD.N0232.N0720.N1492.d016123 e F q /
          _root_.GD.N0232.N0720.N1492.d016123 e F p) ^ ((5 : ℝ) / 2) := by
      rw [Real.div_rpow hqN.le hpN.le]

theorem d016207
    {p q : ℝ} {v : _root_.GD.N0232.N0720.N1151.d016145}
    (hL : _root_.GD.N0232.N0720.N1151.d016150 q v ≠ 0)
    (hD : _root_.GD.N0232.N0720.N1151.d016165 p q v ≠ 0) :
    _root_.GD.N0232.N0720.N1492.d016123 (_root_.GD.N0232.N0720.N1151.d016153 q v).1 (_root_.GD.N0232.N0720.N1151.d016153 q v).2 q /
        _root_.GD.N0232.N0720.N1492.d016123 (_root_.GD.N0232.N0720.N1151.d016153 q v).1 (_root_.GD.N0232.N0720.N1151.d016153 q v).2 p =
      q * (1 - q) / _root_.GD.N0232.N0720.N1151.d016165 p q v := by
  rw [_root_.GD.N0232.N0720.N1151.d016167 hL,
    _root_.GD.N0232.N0720.N1151.d016166 hL]
  field_simp [hL, hD]




theorem d016208
    {p q : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hq : q ∈ Ioo (0 : ℝ) 1)
    {v : _root_.GD.N0232.N0720.N1151.d016145} (hv : v ∈ _root_.GD.N0232.N0720.N1151.d016146) :
    _root_.GD.N0232.N0720.N1153.d016205 p (_root_.GD.N0232.N0720.N1151.d016153 q v).1 (_root_.GD.N0232.N0720.N1151.d016153 q v).2 /
        _root_.GD.N0232.N0720.N1153.d016205 q (_root_.GD.N0232.N0720.N1151.d016153 q v).1 (_root_.GD.N0232.N0720.N1151.d016153 q v).2 =
      (q * (1 - q) /
        _root_.GD.N0232.N0720.N1151.d016165 p q v) ^ ((5 : ℝ) / 2) := by
  have hobs : _root_.GD.N0232.N0720.N1151.d016153 q v ∈ _root_.GD.N0232.N0720.N1436.d013218 :=
    _root_.GD.N0232.N0720.N1151.d016169 hq hv
  have hNp :
      0 < _root_.GD.N0232.N0720.N1492.d016123
        (_root_.GD.N0232.N0720.N1151.d016153 q v).1 (_root_.GD.N0232.N0720.N1151.d016153 q v).2 p :=
    _root_.GD.N0232.N0720.N1492.d016129 hobs.1 hobs.2 ⟨p, hp.1, hp.2⟩
  have hNq :
      0 < _root_.GD.N0232.N0720.N1492.d016123
        (_root_.GD.N0232.N0720.N1151.d016153 q v).1 (_root_.GD.N0232.N0720.N1151.d016153 q v).2 q :=
    _root_.GD.N0232.N0720.N1492.d016129 hobs.1 hobs.2 ⟨q, hq.1, hq.2⟩
  have hpref :
      _root_.GD.N0232.N0720.N1153.d016204 (_root_.GD.N0232.N0720.N1151.d016153 q v).1 (_root_.GD.N0232.N0720.N1151.d016153 q v).2 ≠ 0 := by
    apply ne_of_gt
    rw [_root_.GD.N0232.N0720.N1153.d016204, Real.sqrt_pos]
    exact div_pos hobs.2
      (mul_pos hobs.1.1 (sub_pos.mpr hobs.1.2))
  have hD : 0 < _root_.GD.N0232.N0720.N1151.d016165 p q v := by
    unfold _root_.GD.N0232.N0720.N1151.d016165
    have hx := _root_.GD.N0232.N0720.N1151.d016160 hv
    have hy := _root_.GD.N0232.N0720.N1151.d016162 hv
    have hz := _root_.GD.N0232.N0720.N1151.d016161 hv
    exact add_pos
      (add_pos
        (mul_pos (mul_pos hq.1 (sub_pos.mpr hp.2)) hx)
        (mul_pos (mul_pos (sub_pos.mpr hq.2) hp.1) hy))
      (mul_pos (mul_pos hp.1 (sub_pos.mpr hp.2)) hz)
  rw [_root_.GD.N0232.N0720.N1153.d016206 hNp hNq hpref,
    _root_.GD.N0232.N0720.N1153.d016207 (_root_.GD.N0232.N0720.N1151.d016163 hq hv).ne' hD.ne']

end

end N1153
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1153.d016208
