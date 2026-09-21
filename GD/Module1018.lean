import GD.Module0178
import GD.Module1016
import GD.Module0897
import Mathlib.Tactic















open MeasureTheory ProbabilityTheory Set

namespace GD.N0232.N0720.N1236

noncomputable section

open _root_.GD.N0232.N0720.N1242
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1435
open _root_.GD.N0232.N0720.N1152
open _root_.GD.N0232.N0720.N1489



abbrev d016209 : ℝ := (1 : ℝ) / 2

def d016210 (t : ℝ) : ℝ := t * (1 - t)



def d016211 (t u v : ℝ) : ℝ :=
  (3 / (2 * Real.pi)) *
    (u ^ (-_root_.GD.N0232.N0720.N1236.d016209) * (1 - u) ^ (-_root_.GD.N0232.N0720.N1236.d016209) * v ^ _root_.GD.N0232.N0720.N1236.d016209) *
    _root_.GD.N0232.N0720.N1236.d016210 t ^ 2 *
    (_root_.GD.N0232.N0720.N1242.d002130 t u + _root_.GD.N0232.N0720.N1236.d016210 t * v) ^ (-(5 / 2 : ℝ))


def d016212 (t u : ℝ) : ℝ :=
  (1 / Real.pi) * u ^ (-_root_.GD.N0232.N0720.N1236.d016209) * (1 - u) ^ (-_root_.GD.N0232.N0720.N1236.d016209) *
    _root_.GD.N0232.N0720.N1236.d016210 t ^ _root_.GD.N0232.N0720.N1236.d016209 / _root_.GD.N0232.N0720.N1242.d002130 t u


def d016213 (a b v : ℝ) : ℝ :=
  v ^ _root_.GD.N0232.N0720.N1236.d016209 * (a + b * v) ^ (-(5 / 2 : ℝ))

private theorem d016214
    {a b v : ℝ} (ha : 0 < a) (hb : 0 < b) (hv : 0 < v) :
    _root_.GD.N0232.N0720.N1236.d016213 a b v =
      b ^ (-(5 / 2 : ℝ)) *
        _root_.GD.N0232.N0720.N1489.d013939 (a / b) v := by
  have hsum : a + b * v = b * (v + a / b) := by
    field_simp [hb.ne']
    ring
  have hright : 0 < v + a / b := add_pos hv (div_pos ha hb)
  unfold _root_.GD.N0232.N0720.N1236.d016213 _root_.GD.N0232.N0720.N1489.d013939
  rw [hsum, Real.mul_rpow hb.le hright.le]
  ring

private theorem d016215
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (_root_.GD.N0232.N0720.N1236.d016213 a b) (Ioi (0 : ℝ)) := by
  have hrho : 0 < a / b := div_pos ha hb
  have hrow := _root_.GD.N0232.N0720.N1489.d013946 hrho
  have hscaled := hrow.const_mul (b ^ (-(5 / 2 : ℝ)))
  apply IntegrableOn.congr_fun hscaled _ measurableSet_Ioi
  intro v hv
  exact (_root_.GD.N0232.N0720.N1236.d016214 ha hb hv).symm


theorem d016216
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (_root_.GD.N0232.N0720.N1236.d016213 a b) (Ioi (0 : ℝ)) :=
  _root_.GD.N0232.N0720.N1236.d016215 ha hb



theorem d016217
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ v : ℝ in Ioi 0, _root_.GD.N0232.N0720.N1236.d016213 a b v) =
      2 / (3 * a * b ^ (3 / 2 : ℝ)) := by
  have hrho : 0 < a / b := div_pos ha hb
  calc
    (∫ v : ℝ in Ioi 0, _root_.GD.N0232.N0720.N1236.d016213 a b v) =
        ∫ v : ℝ in Ioi 0,
          b ^ (-(5 / 2 : ℝ)) *
            _root_.GD.N0232.N0720.N1489.d013939 (a / b) v := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      exact _root_.GD.N0232.N0720.N1236.d016214 ha hb hv
    _ = b ^ (-(5 / 2 : ℝ)) *
          (∫ v : ℝ in Ioi 0,
            _root_.GD.N0232.N0720.N1489.d013939 (a / b) v) := by
      rw [integral_const_mul]
    _ = b ^ (-(5 / 2 : ℝ)) * (2 / (3 * (a / b))) := by
      rw [_root_.GD.N0232.N0720.N1489.d013947 hrho]
    _ = 2 / (3 * a * b ^ (3 / 2 : ℝ)) := by
      have hb32 : b ^ (3 / 2 : ℝ) ≠ 0 :=
        (Real.rpow_pos_of_pos hb _).ne'
      have hb52 : b ^ (5 / 2 : ℝ) ≠ 0 :=
        (Real.rpow_pos_of_pos hb _).ne'
      have hsplit : b ^ (5 / 2 : ℝ) =
          b * b ^ (3 / 2 : ℝ) := by
        rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by ring,
          Real.rpow_add hb, Real.rpow_one]
      rw [Real.rpow_neg hb.le]
      field_simp [ha.ne', hb.ne', hb32, hb52]
      nlinarith [hsplit]


theorem d016218
    {t u v : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) (hv : 0 < v) :
    _root_.GD.N0232.N0720.N1436.d013273 2 2 t (u, v) =
      _root_.GD.N0232.N0720.N1236.d016211 t u v := by
  have hp : (u, v) ∈ _root_.GD.N0232.N0720.N1436.d013218 := ⟨hu, hv⟩
  have hQ : 0 < _root_.GD.N0232.N0720.N1152.d016190 u v t := by
    unfold _root_.GD.N0232.N0720.N1152.d016190
    exact add_pos
      (add_pos (mul_pos hu.1 (sub_pos.mpr ht.2))
        (mul_pos (sub_pos.mpr hu.2) ht.1))
      (mul_pos (mul_pos hv ht.1) (sub_pos.mpr ht.2))
  have hden :
      _root_.GD.N0232.N0720.N1152.d016190 u v t =
        _root_.GD.N0232.N0720.N1242.d002130 t u + t * (1 - t) * v := by
    unfold _root_.GD.N0232.N0720.N1152.d016190 _root_.GD.N0232.N0720.N1242.d002130
    ring
  rw [_root_.GD.N0232.N0720.N1152.d016201 ht hp]
  unfold _root_.GD.N0232.N0720.N1152.d016191 _root_.GD.N0232.N0720.N1236.d016211 _root_.GD.N0232.N0720.N1236.d016210
  simp only
  rw [← hden]
  rw [_root_.GD.N0232.N0720.N1152.d016200 hu.1 hu.2 hv,
    _root_.GD.N0232.N0720.N1152.d016198 hQ]
  ring



theorem d016219
    {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (∫ v : ℝ in Ioi 0, _root_.GD.N0232.N0720.N1236.d016211 t u v) =
      _root_.GD.N0232.N0720.N1236.d016212 t u := by
  let a := _root_.GD.N0232.N0720.N1242.d002130 t u
  let b := _root_.GD.N0232.N0720.N1236.d016210 t
  have ha : 0 < a := _root_.GD.N0232.N0720.N1242.d002132 ht hu
  have hb : 0 < b := mul_pos ht.1 (sub_pos.mpr ht.2)
  have hpow : b ^ (3 / 2 : ℝ) * b ^ _root_.GD.N0232.N0720.N1236.d016209 = b ^ 2 := by
    rw [← Real.rpow_add hb]
    norm_num [_root_.GD.N0232.N0720.N1236.d016209]
  have hb32 : b ^ (3 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hb _).ne'
  calc
    (∫ v : ℝ in Ioi 0, _root_.GD.N0232.N0720.N1236.d016211 t u v) =
        (3 / (2 * Real.pi) * u ^ (-_root_.GD.N0232.N0720.N1236.d016209) * (1 - u) ^ (-_root_.GD.N0232.N0720.N1236.d016209) * b ^ 2) *
          (∫ v : ℝ in Ioi 0, _root_.GD.N0232.N0720.N1236.d016213 a b v) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v _
      unfold _root_.GD.N0232.N0720.N1236.d016211 _root_.GD.N0232.N0720.N1236.d016213 a b
      ring
    _ = (3 / (2 * Real.pi) * u ^ (-_root_.GD.N0232.N0720.N1236.d016209) * (1 - u) ^ (-_root_.GD.N0232.N0720.N1236.d016209) * b ^ 2) *
          (2 / (3 * a * b ^ (3 / 2 : ℝ))) := by
      rw [_root_.GD.N0232.N0720.N1236.d016217 ha hb]
    _ = _root_.GD.N0232.N0720.N1236.d016212 t u := by
      unfold _root_.GD.N0232.N0720.N1236.d016212 a b
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      have ha0 : _root_.GD.N0232.N0720.N1242.d002130 t u ≠ 0 := (_root_.GD.N0232.N0720.N1242.d002132 ht hu).ne'
      dsimp [b] at hpow
      field_simp [hpi, ha0, hb32]
      rw [← hpow]
      have hb32' : _root_.GD.N0232.N0720.N1236.d016210 t ^ (3 / 2 : ℝ) ≠ 0 :=
        (Real.rpow_pos_of_pos
          (mul_pos ht.1 (sub_pos.mpr ht.2)) _).ne'
      field_simp [hb32']


theorem d016220
    {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1236.d016212 t u =
      Real.sqrt (t * (1 - t)) /
        (Real.pi * Real.sqrt (u * (1 - u)) * _root_.GD.N0232.N0720.N1242.d002130 t u) := by
  have hub : 0 < u * (1 - u) := mul_pos hu.1 (sub_pos.mpr hu.2)
  have htb : 0 < t * (1 - t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  have hsqrtu : Real.sqrt (u * (1 - u)) ≠ 0 := by positivity
  have hden : _root_.GD.N0232.N0720.N1242.d002130 t u ≠ 0 := (_root_.GD.N0232.N0720.N1242.d002132 ht hu).ne'
  unfold _root_.GD.N0232.N0720.N1236.d016212 _root_.GD.N0232.N0720.N1236.d016210
  rw [← Real.sqrt_eq_rpow,
    Real.rpow_neg hu.1.le, Real.rpow_neg (sub_pos.mpr hu.2).le,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    Real.sqrt_mul hu.1.le]
  have hsu : Real.sqrt u ≠ 0 := (Real.sqrt_pos.2 hu.1).ne'
  have hs1u : Real.sqrt (1 - u) ≠ 0 :=
    (Real.sqrt_pos.2 (sub_pos.mpr hu.2)).ne'
  field_simp [Real.pi_ne_zero, hden, hsqrtu, hsu, hs1u]


theorem d016221
    {t u : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    (∫ v : ℝ in Ioi 0, _root_.GD.N0232.N0720.N1436.d013273 2 2 t (u, v)) =
      Real.sqrt (t * (1 - t)) /
        (Real.pi * Real.sqrt (u * (1 - u)) * _root_.GD.N0232.N0720.N1242.d002130 t u) := by
  calc
    _ = ∫ v : ℝ in Ioi 0, _root_.GD.N0232.N0720.N1236.d016211 t u v := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      exact _root_.GD.N0232.N0720.N1236.d016218 ht hu hv
    _ = _root_.GD.N0232.N0720.N1236.d016212 t u :=
      _root_.GD.N0232.N0720.N1236.d016219 ht hu
    _ = _ := _root_.GD.N0232.N0720.N1236.d016220 ht hu

end

end GD.N0232.N0720.N1236

#print axioms _root_.GD.N0232.N0720.N1236.d016217
#print axioms _root_.GD.N0232.N0720.N1236.d016218
#print axioms _root_.GD.N0232.N0720.N1236.d016221
