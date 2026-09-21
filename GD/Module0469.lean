import GD.Module0459
import GD.Module0392










set_option autoImplicit false
set_option warningAsError true

namespace GD.N0165
noncomputable section

open _root_.GD.N0178 _root_.GD.N0179

def d007232 (t u x : ℝ) : ℝ :=
  x + 2 * u + 2 * t * (1 - u) / (1 - t)

def d007233 (d eta a : ℝ) : ℝ :=
  2 * d / ((1 - d) * (a + 2 * eta))

def d007234 (d eta a : ℝ) : ℝ :=
  (1 + _root_.GD.N0165.d007233 d eta a) ^ (-(7 : ℝ) / 2)

theorem d007235 {t u x : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hx : 0 < x) :
    0 < _root_.GD.N0165.d007232 t u x := by
  have h1 : 0 < 1 - t := sub_pos.mpr ht1
  have h2 : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  unfold _root_.GD.N0165.d007232
  positivity

theorem d007236 {t u x : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    _root_.GD.N0178.d007129 t u (x / t) = _root_.GD.N0165.d007232 t u x / t := by
  unfold _root_.GD.N0178.d007129 _root_.GD.N0165.d007232
  field_simp [ht.ne', (sub_pos.mpr ht1).ne'] <;> ring


theorem d007237 {t u x : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hx : 0 < x) :
    _root_.GD.N0178.d007131 t u (x / t) / t =
      15 * Real.sqrt x / ((1 - t) ^ 2 * _root_.GD.N0178.d007130 (_root_.GD.N0165.d007232 t u x)) := by
  have hS := _root_.GD.N0165.d007235 ht ht1 hu hu1 hx
  have hsqrtT : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hsqrtS : Real.sqrt (_root_.GD.N0165.d007232 t u x) ≠ 0 := (Real.sqrt_pos.mpr hS).ne'
  rw [_root_.GD.N0178.d007131, _root_.GD.N0165.d007236 ht ht1]
  unfold _root_.GD.N0178.d007130
  rw [Real.sqrt_div hx.le t, Real.sqrt_div hS.le t, div_pow]
  field_simp [ht.ne', (sub_pos.mpr ht1).ne', hS.ne', hsqrtT, hsqrtS] <;> ring


theorem d007238 {t u x : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hx : 0 < x) :
    _root_.GD.N0178.d007131 t u (x / t) / t =
      15 * Real.sqrt x / ((1 - t) ^ 2 *
        (x + 2 * u + 2 * t * (1 - u) / (1 - t)) ^ (7 / 2 : ℝ)) := by
  have h := _root_.GD.N0165.d007237 ht ht1 hu hu1 hx
  rw [_root_.GD.N0178.d007137 (_root_.GD.N0165.d007235 ht ht1 hu hu1 hx)] at h
  simpa only [_root_.GD.N0165.d007232] using h

theorem d007239 {d eta a : ℝ} (hd0 : 0 < d) (hd : d < 1)
    (heta : 0 < eta) (ha : 0 < a) : 0 < _root_.GD.N0165.d007233 d eta a := by
  have h1 : 0 < 1 - d := sub_pos.mpr hd
  unfold _root_.GD.N0165.d007233
  positivity

theorem d007240 {d eta a : ℝ} (hd0 : 0 < d) (hd : d < 1)
    (heta : 0 < eta) (ha : 0 < a) :
    _root_.GD.N0165.d007234 d eta a = (_root_.GD.N0178.d007130 (1 + _root_.GD.N0165.d007233 d eta a))⁻¹ := by
  have hb : 0 < 1 + _root_.GD.N0165.d007233 d eta a := by
    linarith [_root_.GD.N0165.d007239 hd0 hd heta ha]
  unfold _root_.GD.N0165.d007234
  rw [show -(7 : ℝ) / 2 = -(7 / 2 : ℝ) by ring, Real.rpow_neg hb.le,
    ← _root_.GD.N0178.d007137 hb]


theorem d007241 {t d eta a u x : ℝ}
    (ht : 0 < t) (htd : t ≤ d) (hd : d < 1)
    (heta : 0 < eta) (ha : 0 < a) (hu : eta ≤ u) (hu1 : u ≤ 1 - eta)
    (hax : a ≤ x) :
    2 * t * (1 - u) / ((1 - t) * (x + 2 * u)) ≤ _root_.GD.N0165.d007233 d eta a := by
  have ht1 : t < 1 := htd.trans_lt hd
  have hu0 : 0 ≤ u := (heta.trans_le hu).le
  have hB : 0 < a + 2 * eta := by positivity
  have hX : 0 < x + 2 * u := by linarith
  have hdt : 0 < (1 - t) * (x + 2 * u) := mul_pos (sub_pos.mpr ht1) hX
  have hdd : 0 < (1 - d) * (a + 2 * eta) := mul_pos (sub_pos.mpr hd) hB
  have hnum : 2 * t * (1 - u) ≤ 2 * d := by
    calc
      2 * t * (1 - u) ≤ 2 * t :=
        mul_le_of_le_one_right (by positivity) (by linarith)
      _ ≤ 2 * d := by linarith
  have hden : (1 - d) * (a + 2 * eta) ≤ (1 - t) * (x + 2 * u) :=
    mul_le_mul (by linarith) (by linarith) hB.le (sub_pos.mpr ht1).le
  calc
    2 * t * (1 - u) / ((1 - t) * (x + 2 * u)) ≤
        2 * d / ((1 - t) * (x + 2 * u)) :=
      div_le_div_of_nonneg_right hnum hdt.le
    _ ≤ 2 * d / ((1 - d) * (a + 2 * eta)) :=
      div_le_div_of_nonneg_left (by linarith) hdd hden
    _ = _root_.GD.N0165.d007233 d eta a := rfl

theorem d007242 {t d eta a u x : ℝ}
    (ht : 0 < t) (htd : t ≤ d) (hd : d < 1)
    (heta : 0 < eta) (ha : 0 < a) (hu : eta ≤ u) (hu1 : u ≤ 1 - eta)
    (hax : a ≤ x) :
    _root_.GD.N0165.d007232 t u x ≤ (1 + _root_.GD.N0165.d007233 d eta a) * (x + 2 * u) := by
  have ht1 : 0 < 1 - t := sub_pos.mpr (htd.trans_lt hd)
  have hX : 0 < x + 2 * u := by linarith
  have hrel := _root_.GD.N0165.d007241 ht htd hd heta ha hu hu1 hax
  have hmul := (div_le_iff₀ (mul_pos ht1 hX)).mp hrel
  have he : 2 * t * (1 - u) / (1 - t) ≤ _root_.GD.N0165.d007233 d eta a * (x + 2 * u) := by
    apply (div_le_iff₀ ht1).mpr
    nlinarith
  unfold _root_.GD.N0165.d007232
  nlinarith


theorem d007243 {t d eta a u x : ℝ}
    (ht : 0 < t) (htd : t ≤ d) (hd : d < 1)
    (heta : 0 < eta) (ha : 0 < a) (hu : eta ≤ u) (hu1 : u ≤ 1 - eta)
    (hax : a ≤ x) :
    _root_.GD.N0165.d007234 d eta a * _root_.GD.N0179.d006018 u x ≤ _root_.GD.N0178.d007131 t u (x / t) / t := by
  have hd0 : 0 < d := ht.trans_le htd
  have ht1 : t < 1 := htd.trans_lt hd
  have hu0 : 0 ≤ u := (heta.trans_le hu).le
  have hu2 : u ≤ 1 := by linarith
  have hx : 0 < x := ha.trans_le hax
  have hX : 0 < x + 2 * u := by linarith
  have hS := _root_.GD.N0165.d007235 ht ht1 hu0 hu2 hx
  have hR : 0 < 1 + _root_.GD.N0165.d007233 d eta a := by
    linarith [_root_.GD.N0165.d007239 hd0 hd heta ha]
  have hpow := _root_.GD.N0178.d007136 hS.le (_root_.GD.N0165.d007242 ht htd hd heta ha hu hu1 hax)
  rw [_root_.GD.N0178.d007135 hR.le] at hpow
  have hsq : (1 - t) ^ 2 ≤ 1 := by
    simpa only [one_pow] using
      pow_le_pow_left₀ (sub_pos.mpr ht1).le (show 1 - t ≤ 1 by linarith) 2
  have hden : (1 - t) ^ 2 * _root_.GD.N0178.d007130 (_root_.GD.N0165.d007232 t u x) ≤
      _root_.GD.N0178.d007130 (1 + _root_.GD.N0165.d007233 d eta a) * _root_.GD.N0178.d007130 (x + 2 * u) := by
    calc
      _ ≤ 1 * (_root_.GD.N0178.d007130 (1 + _root_.GD.N0165.d007233 d eta a) * _root_.GD.N0178.d007130 (x + 2 * u)) :=
        mul_le_mul hsq hpow (_root_.GD.N0178.d007133 hS.le) (by norm_num)
      _ = _ := one_mul _
  have hdenpos : 0 < (1 - t) ^ 2 * _root_.GD.N0178.d007130 (_root_.GD.N0165.d007232 t u x) :=
    mul_pos (sq_pos_of_pos (sub_pos.mpr ht1)) (_root_.GD.N0178.d007134 hS)
  rw [_root_.GD.N0165.d007237 ht ht1 hu0 hu2 hx]
  calc
    _root_.GD.N0165.d007234 d eta a * _root_.GD.N0179.d006018 u x =
        15 * Real.sqrt x /
          (_root_.GD.N0178.d007130 (1 + _root_.GD.N0165.d007233 d eta a) * _root_.GD.N0178.d007130 (x + 2 * u)) := by
      rw [_root_.GD.N0165.d007240 hd0 hd heta ha]
      change (_root_.GD.N0178.d007130 (1 + _root_.GD.N0165.d007233 d eta a))⁻¹ *
          (15 * Real.sqrt x / _root_.GD.N0178.d007130 (x + 2 * u)) = _
      field_simp [(_root_.GD.N0178.d007134 hR).ne', (_root_.GD.N0178.d007134 hX).ne'] <;> ring
    _ ≤ 15 * Real.sqrt x / ((1 - t) ^ 2 * _root_.GD.N0178.d007130 (_root_.GD.N0165.d007232 t u x)) :=
      div_le_div_of_nonneg_left (by positivity) hdenpos hden


theorem d007244 (t u s : ℝ) : _root_.GD.N0178.d007131 (1 - t) u s = _root_.GD.N0178.d007131 t (1 - u) s := by
  have hD : _root_.GD.N0178.d007129 (1 - t) u s = _root_.GD.N0178.d007129 t (1 - u) s := by
    unfold _root_.GD.N0178.d007129
    rw [show 1 - (1 - t) = t by ring, show 1 - (1 - u) = u by ring]
    ring
  unfold _root_.GD.N0178.d007131
  rw [hD]
  congr 1
  ring

theorem d007245 {t d eta a u x : ℝ}
    (ht : 0 < t) (htd : t ≤ d) (hd : d < 1)
    (heta : 0 < eta) (ha : 0 < a) (hu : eta ≤ u) (hu1 : u ≤ 1 - eta)
    (hax : a ≤ x) :
    _root_.GD.N0165.d007234 d eta a * _root_.GD.N0179.d006018 (1 - u) x ≤ _root_.GD.N0178.d007131 (1 - t) u (x / t) / t := by
  rw [_root_.GD.N0165.d007244]
  exact _root_.GD.N0165.d007243 ht htd hd heta ha (by linarith) (by linarith) hax

end
end GD.N0165

#print axioms _root_.GD.N0165.d007237
#print axioms _root_.GD.N0165.d007238
#print axioms _root_.GD.N0165.d007241
#print axioms _root_.GD.N0165.d007243
#print axioms _root_.GD.N0165.d007244
#print axioms _root_.GD.N0165.d007245
