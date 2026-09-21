import Mathlib

































namespace GD.N0124


abbrev d006387 := ℝ × (ℝ × ℝ)


def d006388 : Set _root_.GD.N0124.d006387 :=
  {p | 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2}


def d006389 : Set _root_.GD.N0124.d006387 :=
  {p | 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2.1 ∧ 0 < p.2.2}


def d006390 (e : ℝ) (p : _root_.GD.N0124.d006387) : ℝ :=
  (1 - e) * p.1 + e * p.2.1


noncomputable def d006391 (e : ℝ) (p : _root_.GD.N0124.d006387) : _root_.GD.N0124.d006387 :=
  let H := _root_.GD.N0124.d006390 e p
  (e * p.2.1 / H, (p.2.2 / H, H))


noncomputable def d006392 (e : ℝ) (p : _root_.GD.N0124.d006387) : _root_.GD.N0124.d006387 :=
  ((1 - p.1) * p.2.2 / (1 - e),
    (p.1 * p.2.2 / e, p.2.1 * p.2.2))

lemma d006393 {e : ℝ} {p : _root_.GD.N0124.d006387}
    (he0 : 0 < e) (he1 : e < 1) (hp : p ∈ _root_.GD.N0124.d006388) :
    0 < _root_.GD.N0124.d006390 e p := by
  exact add_pos (mul_pos (sub_pos.mpr he1) hp.1)
    (mul_pos he0 hp.2.1)

lemma d006394 {e : ℝ} {p : _root_.GD.N0124.d006387}
    (he0 : 0 < e) (he1 : e < 1) (hp : p ∈ _root_.GD.N0124.d006388) :
    _root_.GD.N0124.d006391 e p ∈ _root_.GD.N0124.d006389 := by
  have hH : 0 < _root_.GD.N0124.d006390 e p := _root_.GD.N0124.d006393 he0 he1 hp
  have hery : 0 < e * p.2.1 := mul_pos he0 hp.2.1
  have hleft : 0 < (1 - e) * p.1 := mul_pos (sub_pos.mpr he1) hp.1
  refine ⟨div_pos hery hH, ?_, div_pos hp.2.2 hH, hH⟩
  change e * p.2.1 / _root_.GD.N0124.d006390 e p < 1
  rw [div_lt_one hH]
  dsimp [_root_.GD.N0124.d006390]
  linarith

lemma d006395 {e : ℝ} {p : _root_.GD.N0124.d006387}
    (he0 : 0 < e) (he1 : e < 1) (hp : p ∈ _root_.GD.N0124.d006389) :
    _root_.GD.N0124.d006392 e p ∈ _root_.GD.N0124.d006388 := by
  refine ⟨div_pos (mul_pos (sub_pos.mpr hp.2.1) hp.2.2.2)
      (sub_pos.mpr he1),
    div_pos (mul_pos hp.1 hp.2.2.2) he0,
    mul_pos hp.2.2.1 hp.2.2.2⟩


theorem d006396 {e : ℝ} {p : _root_.GD.N0124.d006387}
    (he0 : 0 < e) (he1 : e < 1) (hp : p ∈ _root_.GD.N0124.d006388) :
    _root_.GD.N0124.d006392 e (_root_.GD.N0124.d006391 e p) = p := by
  have he : e ≠ 0 := ne_of_gt he0
  have h1e : 1 - e ≠ 0 := ne_of_gt (sub_pos.mpr he1)
  have hH : _root_.GD.N0124.d006390 e p ≠ 0 := ne_of_gt (_root_.GD.N0124.d006393 he0 he1 hp)
  apply Prod.ext
  · dsimp [_root_.GD.N0124.d006392, _root_.GD.N0124.d006391]
    field_simp [he, h1e, hH]
    simp [_root_.GD.N0124.d006390]
  · apply Prod.ext
    · dsimp [_root_.GD.N0124.d006392, _root_.GD.N0124.d006391]
      field_simp [he, h1e, hH]
    · dsimp [_root_.GD.N0124.d006392, _root_.GD.N0124.d006391]
      field_simp [he, h1e, hH]


theorem d006397 {e : ℝ} {p : _root_.GD.N0124.d006387}
    (he0 : 0 < e) (he1 : e < 1) (hp : p ∈ _root_.GD.N0124.d006389) :
    _root_.GD.N0124.d006391 e (_root_.GD.N0124.d006392 e p) = p := by
  have he : e ≠ 0 := ne_of_gt he0
  have h1e : 1 - e ≠ 0 := ne_of_gt (sub_pos.mpr he1)
  have hH : p.2.2 ≠ 0 := ne_of_gt hp.2.2.2
  apply Prod.ext
  · dsimp [_root_.GD.N0124.d006392, _root_.GD.N0124.d006391, _root_.GD.N0124.d006390]
    field_simp [he, h1e, hH]
    ring
  · apply Prod.ext
    · dsimp [_root_.GD.N0124.d006392, _root_.GD.N0124.d006391, _root_.GD.N0124.d006390]
      field_simp [he, h1e, hH]
      ring
    · dsimp [_root_.GD.N0124.d006392, _root_.GD.N0124.d006391, _root_.GD.N0124.d006390]
      field_simp [he, h1e, hH]
      ring



theorem d006398 {e : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    _root_.GD.N0124.d006391 e '' _root_.GD.N0124.d006388 = _root_.GD.N0124.d006389 := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact _root_.GD.N0124.d006394 he0 he1 hq
  · intro hp
    exact ⟨_root_.GD.N0124.d006392 e p, _root_.GD.N0124.d006395 he0 he1 hp,
      _root_.GD.N0124.d006397 he0 he1 hp⟩



theorem d006399 {e : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    Set.InjOn (_root_.GD.N0124.d006391 e) _root_.GD.N0124.d006388 := by
  intro p hp q hq hpq
  rw [← _root_.GD.N0124.d006396 he0 he1 hp, ← _root_.GD.N0124.d006396 he0 he1 hq, hpq]



theorem d006400 {e : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    Set.BijOn (_root_.GD.N0124.d006391 e) _root_.GD.N0124.d006388 _root_.GD.N0124.d006389 := by
  refine ⟨?_, _root_.GD.N0124.d006399 he0 he1, ?_⟩
  · exact fun _ hp => _root_.GD.N0124.d006394 he0 he1 hp
  · intro p hp
    rw [← _root_.GD.N0124.d006398 he0 he1] at hp
    rcases hp with ⟨q, hq, rfl⟩
    exact ⟨q, hq, rfl⟩





noncomputable def d006401 (e : ℝ) (p : _root_.GD.N0124.d006387) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![-p.2.2 / (1 - e), 0, (1 - p.1) / (1 - e);
     p.2.2 / e,       0, p.1 / e;
     0,                p.2.2, p.2.1]


theorem d006402 {e : ℝ} (p : _root_.GD.N0124.d006387)
    (he : e ≠ 0) (h1e : 1 - e ≠ 0) :
    (_root_.GD.N0124.d006401 e p).det = p.2.2 ^ 2 / (e * (1 - e)) := by
  simp [_root_.GD.N0124.d006401, Matrix.det_fin_three]
  field_simp [he, h1e]
  ring





theorem d006403 {e : ℝ} (p : _root_.GD.N0124.d006387)
    (he : e ≠ 0) (h1e : 1 - e ≠ 0) :
    (e * (1 - e)) * (_root_.GD.N0124.d006401 e p).det = p.2.2 ^ 2 := by
  rw [_root_.GD.N0124.d006402 p he h1e]
  field_simp [he, h1e]



theorem d006404 {e : ℝ} {p : _root_.GD.N0124.d006387}
    (he0 : 0 < e) (he1 : e < 1) (hp : p ∈ _root_.GD.N0124.d006389) :
    0 < (_root_.GD.N0124.d006401 e p).det := by
  rw [_root_.GD.N0124.d006402 p (ne_of_gt he0)
    (ne_of_gt (sub_pos.mpr he1))]
  exact div_pos (sq_pos_of_pos hp.2.2.2)
    (mul_pos he0 (sub_pos.mpr he1))

end GD.N0124
