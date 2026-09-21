import Mathlib










namespace GD.N0136

section Unbalanced

variable (h eta v0 v1 v2 vt : ℚ)

def d006564 : ℚ :=
  v1 / (2 * h) - v2 / h ^ 2

def d006565 : ℚ :=
  -v0 + 2 * v2 / h ^ 2 + vt / eta

def d006566 : ℚ :=
  -v1 / (2 * h) - v2 / h ^ 2

def d006567 : ℚ :=
  -vt / eta

theorem d006568
    (hh : h ≠ 0) (hη : eta ≠ 0)
    (gm g0 gp gt : ℚ) :
    _root_.GD.N0136.d006564 h v1 v2 * gm
      + _root_.GD.N0136.d006565 h eta v0 v2 vt * g0
      + _root_.GD.N0136.d006566 h v1 v2 * gp
      + _root_.GD.N0136.d006567 eta vt * gt
      =
      -v0 * g0
        - v1 * ((gp - gm) / (2 * h))
        - v2 * ((gp - 2 * g0 + gm) / h ^ 2)
        - vt * ((gt - g0) / eta) := by
  dsimp [_root_.GD.N0136.d006564, _root_.GD.N0136.d006565,
    _root_.GD.N0136.d006566, _root_.GD.N0136.d006567]
  field_simp [hh, hη] <;> ring

theorem d006569
    (hh : h ≠ 0) (hη : eta ≠ 0) :
    _root_.GD.N0136.d006564 h v1 v2
      + _root_.GD.N0136.d006565 h eta v0 v2 vt
      + _root_.GD.N0136.d006566 h v1 v2
      + _root_.GD.N0136.d006567 eta vt
      = -v0 := by
  dsimp [_root_.GD.N0136.d006564, _root_.GD.N0136.d006565,
    _root_.GD.N0136.d006566, _root_.GD.N0136.d006567]
  field_simp [hh, hη] <;> ring

theorem d006570
    (hh : h ≠ 0) (hη : eta ≠ 0) :
    _root_.GD.N0136.d006564 h v1 v2 * (-h)
      + _root_.GD.N0136.d006565 h eta v0 v2 vt * 0
      + _root_.GD.N0136.d006566 h v1 v2 * h
      + _root_.GD.N0136.d006567 eta vt * 0
      = -v1 := by
  dsimp [_root_.GD.N0136.d006564, _root_.GD.N0136.d006565,
    _root_.GD.N0136.d006566, _root_.GD.N0136.d006567]
  field_simp [hh, hη] <;> ring

theorem d006571
    (hh : h ≠ 0) (hη : eta ≠ 0) :
    _root_.GD.N0136.d006564 h v1 v2 * (-h) ^ 2
      + _root_.GD.N0136.d006565 h eta v0 v2 vt * 0 ^ 2
      + _root_.GD.N0136.d006566 h v1 v2 * h ^ 2
      + _root_.GD.N0136.d006567 eta vt * 0 ^ 2
      = -2 * v2 := by
  dsimp [_root_.GD.N0136.d006564, _root_.GD.N0136.d006565,
    _root_.GD.N0136.d006566, _root_.GD.N0136.d006567]
  field_simp [hh, hη] <;> ring

theorem d006572
    (hh : h ≠ 0) (hη : eta ≠ 0) :
    _root_.GD.N0136.d006564 h v1 (-v2)
        = -_root_.GD.N0136.d006566 h v1 v2
      ∧ _root_.GD.N0136.d006565 h eta (-v0) (-v2) (-vt)
        = -_root_.GD.N0136.d006565 h eta v0 v2 vt
      ∧ _root_.GD.N0136.d006566 h v1 (-v2)
        = -_root_.GD.N0136.d006564 h v1 v2
      ∧ _root_.GD.N0136.d006567 eta (-vt)
        = -_root_.GD.N0136.d006567 eta vt := by
  constructor
  · dsimp [_root_.GD.N0136.d006564, _root_.GD.N0136.d006566]
    field_simp [hh] <;> ring
  constructor
  · dsimp [_root_.GD.N0136.d006565]
    field_simp [hh, hη] <;> ring
  constructor
  · dsimp [_root_.GD.N0136.d006564, _root_.GD.N0136.d006566]
    field_simp [hh] <;> ring
  · dsimp [_root_.GD.N0136.d006567]
    field_simp [hη] <;> ring

end Unbalanced

section Balanced

variable (h eta v1 v3 vst : ℚ)

def d006573 : ℚ :=
  -v1 / (2 * h) + v3 / h ^ 3 + vst / (2 * h * eta)

def d006574 : ℚ :=
  v1 / (2 * h) - v3 / h ^ 3 - vst / (2 * h * eta)

def d006575 : ℚ :=
  -v3 / (2 * h ^ 3)

def d006576 : ℚ :=
  v3 / (2 * h ^ 3)

def d006577 : ℚ :=
  -vst / (2 * h * eta)

def d006578 : ℚ :=
  vst / (2 * h * eta)

theorem d006579
    (hh : h ≠ 0) (hη : eta ≠ 0)
    (gh gmh g2h gm2h gh2t gmh2t : ℚ) :
    _root_.GD.N0136.d006573 h eta v1 v3 vst * gh
      + _root_.GD.N0136.d006574 h eta v1 v3 vst * gmh
      + _root_.GD.N0136.d006575 h v3 * g2h
      + _root_.GD.N0136.d006576 h v3 * gm2h
      + _root_.GD.N0136.d006577 h eta vst * gh2t
      + _root_.GD.N0136.d006578 h eta vst * gmh2t
      =
      -v1 * ((gh - gmh) / (2 * h))
        - v3 * ((g2h - 2 * gh + 2 * gmh - gm2h) / (2 * h ^ 3))
        - vst *
          ((gh2t - gmh2t - gh + gmh) / (2 * h * eta)) := by
  dsimp [_root_.GD.N0136.d006573, _root_.GD.N0136.d006574,
    _root_.GD.N0136.d006575, _root_.GD.N0136.d006576,
    _root_.GD.N0136.d006577, _root_.GD.N0136.d006578]
  field_simp [hh, hη] <;> ring

theorem d006580
    (hh : h ≠ 0) (hη : eta ≠ 0) :
    _root_.GD.N0136.d006574 h eta v1 v3 vst
        = -_root_.GD.N0136.d006573 h eta v1 v3 vst
      ∧ _root_.GD.N0136.d006576 h v3
        = -_root_.GD.N0136.d006575 h v3
      ∧ _root_.GD.N0136.d006578 h eta vst
        = -_root_.GD.N0136.d006577 h eta vst := by
  constructor
  · dsimp [_root_.GD.N0136.d006574, _root_.GD.N0136.d006573]
    field_simp [hh, hη] <;> ring
  constructor
  · dsimp [_root_.GD.N0136.d006576, _root_.GD.N0136.d006575]
    field_simp [hh] <;> ring
  · dsimp [_root_.GD.N0136.d006578, _root_.GD.N0136.d006577]
    field_simp [hh, hη] <;> ring

theorem d006581
    (hh : h ≠ 0) (hη : eta ≠ 0) :
    _root_.GD.N0136.d006573 h eta v1 v3 vst * h
      + _root_.GD.N0136.d006574 h eta v1 v3 vst * (-h)
      + _root_.GD.N0136.d006575 h v3 * (2 * h)
      + _root_.GD.N0136.d006576 h v3 * (-2 * h)
      + _root_.GD.N0136.d006577 h eta vst * h
      + _root_.GD.N0136.d006578 h eta vst * (-h)
      = -v1 := by
  dsimp [_root_.GD.N0136.d006573, _root_.GD.N0136.d006574,
    _root_.GD.N0136.d006575, _root_.GD.N0136.d006576,
    _root_.GD.N0136.d006577, _root_.GD.N0136.d006578]
  field_simp [hh, hη] <;> ring

theorem d006582
    (hh : h ≠ 0) (hη : eta ≠ 0) :
    _root_.GD.N0136.d006573 h eta v1 v3 vst * h ^ 3
      + _root_.GD.N0136.d006574 h eta v1 v3 vst * (-h) ^ 3
      + _root_.GD.N0136.d006575 h v3 * (2 * h) ^ 3
      + _root_.GD.N0136.d006576 h v3 * (-2 * h) ^ 3
      + _root_.GD.N0136.d006577 h eta vst * h ^ 3
      + _root_.GD.N0136.d006578 h eta vst * (-h) ^ 3
      = -h ^ 2 * v1 - 6 * v3 := by
  dsimp [_root_.GD.N0136.d006573, _root_.GD.N0136.d006574,
    _root_.GD.N0136.d006575, _root_.GD.N0136.d006576,
    _root_.GD.N0136.d006577, _root_.GD.N0136.d006578]
  field_simp [hh, hη] <;> ring

theorem d006583
    (hh : h ≠ 0) (hη : eta ≠ 0) :
    _root_.GD.N0136.d006573 h eta v1 v3 vst * (h * eta)
      + _root_.GD.N0136.d006574 h eta v1 v3 vst * ((-h) * eta)
      + _root_.GD.N0136.d006575 h v3 * ((2 * h) * eta)
      + _root_.GD.N0136.d006576 h v3 * ((-2 * h) * eta)
      + _root_.GD.N0136.d006577 h eta vst * (h * (2 * eta))
      + _root_.GD.N0136.d006578 h eta vst * ((-h) * (2 * eta))
      = -eta * v1 - vst := by
  dsimp [_root_.GD.N0136.d006573, _root_.GD.N0136.d006574,
    _root_.GD.N0136.d006575, _root_.GD.N0136.d006576,
    _root_.GD.N0136.d006577, _root_.GD.N0136.d006578]
  field_simp [hh, hη] <;> ring

end Balanced

section CoefficientSwap

variable (nu delta prod r : ℚ)

def d006584 : ℚ := -r * nu / delta
def d006585 : ℚ := -(r + 1) / (r - 1)
def d006586 : ℚ := prod / (delta * nu * (r - 1))
def d006587 : ℚ :=
  -2 * nu ^ 2 * (r + 1) / (delta * (r - 1))

theorem d006588
    (hν : nu ≠ 0) (hΔ : delta ≠ 0) (hr : r - 1 ≠ 0) :
    _root_.GD.N0136.d006584 nu (-delta) r = -_root_.GD.N0136.d006584 nu delta r
      ∧ _root_.GD.N0136.d006585 r = _root_.GD.N0136.d006585 r
      ∧ _root_.GD.N0136.d006586 nu (-delta) prod r = -_root_.GD.N0136.d006586 nu delta prod r
      ∧ _root_.GD.N0136.d006587 nu (-delta) r = -_root_.GD.N0136.d006587 nu delta r := by
  constructor
  · dsimp [_root_.GD.N0136.d006584]
    field_simp [hΔ] <;> ring
  constructor
  · rfl
  constructor
  · dsimp [_root_.GD.N0136.d006586]
    field_simp [hν, hΔ, hr] <;> ring
  · dsimp [_root_.GD.N0136.d006587]
    field_simp [hΔ, hr] <;> ring

end CoefficientSwap

section TentAndRisk

theorem d006589
    (lower upper rho : ℝ)
    (hlower : 0 < lower)
    (hlρ : lower ≤ rho)
    (hρu : rho ≤ upper) :
    |(2 / (lower + upper)) * rho - 1|
      ≤ (upper - lower) / (upper + lower) := by
  have hlu : lower ≤ upper := hlρ.trans hρu
  have hsum : 0 < lower + upper := by nlinarith
  have herr :
      (2 / (lower + upper)) * rho - 1
        = (2 * rho - (lower + upper)) / (lower + upper) := by
    field_simp [ne_of_gt hsum] <;> ring
  rw [herr]
  apply abs_le.2
  constructor
  · have hnumerator :
        -(upper - lower)
          ≤ 2 * rho - (lower + upper) := by
      nlinarith
    have hdiv := (div_le_div_iff_of_pos_right hsum).2 hnumerator
    simpa only [neg_div, add_comm] using hdiv
  · have hnumerator :
        2 * rho - (lower + upper)
          ≤ upper - lower := by
      nlinarith
    simpa only [add_comm] using
      (div_le_div_iff_of_pos_right hsum).2 hnumerator

theorem d006590
    (w : ℚ) (hw : w ≠ 0) :
    ((2 * w / 3) ^ 2) / w ^ 4 = 4 / (9 * w ^ 2) := by
  field_simp [hw] <;> ring

theorem d006591
    (delta energy : ℚ) (hM : energy ≠ 0) :
    -2 * (delta / energy) * delta
        + (delta / energy) ^ 2 * energy
      = -(delta ^ 2 / energy) := by
  field_simp [hM] <;> ring

theorem d006592
    (trace energy delta ceiling : ℝ)
    (hT : trace ≤ -delta)
    (hA : energy ≤ ceiling)
    (hδ : 0 < delta)
    (hM : 0 < ceiling) :
    2 * (delta / ceiling) * trace
        + (delta / ceiling) ^ 2 * energy < 0 := by
  have hε : 0 < delta / ceiling := div_pos hδ hM
  have hlinear :
      2 * (delta / ceiling) * trace
        ≤ 2 * (delta / ceiling) * (-delta) := by
    exact mul_le_mul_of_nonneg_left hT (by positivity)
  have hquadratic :
      (delta / ceiling) ^ 2 * energy
        ≤ (delta / ceiling) ^ 2 * ceiling := by
    exact mul_le_mul_of_nonneg_left hA (sq_nonneg _)
  calc
    2 * (delta / ceiling) * trace
          + (delta / ceiling) ^ 2 * energy
        ≤
          2 * (delta / ceiling) * (-delta)
            + (delta / ceiling) ^ 2 * ceiling :=
              add_le_add hlinear hquadratic
    _ = -(delta ^ 2 / ceiling) := by
      field_simp [ne_of_gt hM] <;> ring
    _ < 0 := neg_lt_zero.mpr (div_pos (sq_pos_of_pos hδ) hM)

end TentAndRisk

end GD.N0136
