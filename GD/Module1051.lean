import GD.Module1050
import GD.Module0193
import GD.Module0955
import Mathlib.Tactic








open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace GD.N0232.N0720.N1289

noncomputable section

open _root_.GD.N0137 _root_.GD.N0107
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N1011
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1397
open _root_.GD.N0232.N0720.N1281

def d016779 (s : ℝ) (hs : 0 < s) (mu : ℝ) : _root_.GD.N0232.N0720.N1080.d014168 where
  location := mu
  scale₁ := s
  scale₂ := s
  scale₁_pos := hs
  scale₂_pos := hs

@[simp] theorem d016780
    (s : ℝ) (hs : 0 < s) (mu : ℝ) :
    (_root_.GD.N0232.N0720.N1289.d016779 s hs mu).location = mu := rfl

@[simp] theorem d016781
    (s : ℝ) (hs : 0 < s) (mu : ℝ) :
    (_root_.GD.N0232.N0720.N1289.d016779 s hs mu).scale₁ = s := rfl

@[simp] theorem d016782
    (s : ℝ) (hs : 0 < s) (mu : ℝ) :
    (_root_.GD.N0232.N0720.N1289.d016779 s hs mu).scale₂ = s := rfl

@[fun_prop] theorem d016783
    (s : ℝ) (hs : 0 < s) : Continuous (_root_.GD.N0232.N0720.N1289.d016779 s hs) := by
  apply (_root_.GD.N0232.N0720.N1499.d014996.comp_continuous_iff).mp
  change Continuous (fun mu : ℝ ↦ (mu, (s, s)))
  fun_prop

theorem d016784
    (omega : _root_.GD.N0137.d008894 2 × _root_.GD.N0137.d008894 2) :
    omega.1 0 ^ 2 + omega.1 1 ^ 2 +
        omega.2 0 ^ 2 + omega.2 1 ^ 2 =
      4 * (_root_.GD.N0232.N0720.N1397.d014815 omega).1 ^ 2 +
        (_root_.GD.N0232.N0720.N1397.d014815 omega).2.1 ^ 2 +
        (_root_.GD.N0232.N0720.N1397.d014815 omega).2.2.1 ^ 2 +
        (_root_.GD.N0232.N0720.N1397.d014815 omega).2.2.2 ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1397.d014817]
  have hsqrt : Real.sqrt (1 / 2 : ℝ) ^ 2 = 1 / 2 :=
    Real.sq_sqrt (by norm_num)
  dsimp only
  nlinarith

theorem d016785
    (mu : ℝ) (omega : _root_.GD.N0137.d008894 2 × _root_.GD.N0137.d008894 2) :
    (omega.1 0 - mu) ^ 2 + (omega.1 1 - mu) ^ 2 +
        (omega.2 0 - mu) ^ 2 + (omega.2 1 - mu) ^ 2 =
      4 * ((_root_.GD.N0232.N0720.N1397.d014815 omega).1 - mu) ^ 2 +
        (_root_.GD.N0232.N0720.N1397.d014815 omega).2.1 ^ 2 +
        (_root_.GD.N0232.N0720.N1397.d014815 omega).2.2.1 ^ 2 +
        (_root_.GD.N0232.N0720.N1397.d014815 omega).2.2.2 ^ 2 := by
  rw [_root_.GD.N0232.N0720.N1397.d014817]
  have hsqrt : Real.sqrt (1 / 2 : ℝ) ^ 2 = 1 / 2 :=
    Real.sq_sqrt (by norm_num)
  dsimp only
  nlinarith



theorem d016786
    (mu s : ℝ) (hs : 0 < s)
    (omega : _root_.GD.N0137.d008894 2 × _root_.GD.N0137.d008894 2) :
    _root_.GD.N0232.N0720.N1499.d015001 2 2 (_root_.GD.N0232.N0720.N1289.d016779 s hs mu) omega =
      _root_.GD.N0232.N0719.N0932.d009204 (2 * mu) s
          (2 * (_root_.GD.N0232.N0720.N1397.d014815 omega).1) *
        (_root_.GD.N0232.N0719.N0932.d009204 0 s
            (_root_.GD.N0232.N0720.N1397.d014815 omega).2.1 *
          (_root_.GD.N0232.N0719.N0932.d009204 0 s
              (_root_.GD.N0232.N0720.N1397.d014815 omega).2.2.1 *
            _root_.GD.N0232.N0719.N0932.d009204 0 s
              (_root_.GD.N0232.N0720.N1397.d014815 omega).2.2.2)) := by
  unfold _root_.GD.N0232.N0720.N1499.d015001 _root_.GD.N0232.N0719.N0932.d009213
    _root_.GD.N0232.N0719.N0932.d009190
  simp only [_root_.GD.N0232.N0720.N1289.d016780, _root_.GD.N0232.N0720.N1289.d016781,
    _root_.GD.N0232.N0720.N1289.d016782]
  simp_rw [_root_.GD.N0232.N0720.N1124.d016497
    _ _ _ hs]
  rw [show (∏ i : Fin 2,
      s⁻¹ * Real.exp
        ((omega.1 i) ^ 2 / 2 - ((omega.1 i) - mu) ^ 2 / (2 * s ^ 2))) =
      (s⁻¹ * Real.exp
        ((omega.1 0) ^ 2 / 2 - ((omega.1 0) - mu) ^ 2 / (2 * s ^ 2))) *
      (s⁻¹ * Real.exp
        ((omega.1 1) ^ 2 / 2 - ((omega.1 1) - mu) ^ 2 / (2 * s ^ 2))) by
        simp [Fin.prod_univ_two],
    show (∏ i : Fin 2,
      s⁻¹ * Real.exp
        ((omega.2 i) ^ 2 / 2 - ((omega.2 i) - mu) ^ 2 / (2 * s ^ 2))) =
      (s⁻¹ * Real.exp
        ((omega.2 0) ^ 2 / 2 - ((omega.2 0) - mu) ^ 2 / (2 * s ^ 2))) *
      (s⁻¹ * Real.exp
        ((omega.2 1) ^ 2 / 2 - ((omega.2 1) - mu) ^ 2 / (2 * s ^ 2))) by
        simp [Fin.prod_univ_two]]
  have hraw := _root_.GD.N0232.N0720.N1289.d016784 omega
  have hshift := _root_.GD.N0232.N0720.N1289.d016785 mu omega
  let z := _root_.GD.N0232.N0720.N1397.d014815 omega
  have hExponent :
      ((omega.1 0) ^ 2 / 2 - ((omega.1 0) - mu) ^ 2 / (2 * s ^ 2)) +
          ((omega.1 1) ^ 2 / 2 - ((omega.1 1) - mu) ^ 2 / (2 * s ^ 2)) +
          ((omega.2 0) ^ 2 / 2 - ((omega.2 0) - mu) ^ 2 / (2 * s ^ 2)) +
          ((omega.2 1) ^ 2 / 2 - ((omega.2 1) - mu) ^ 2 / (2 * s ^ 2)) =
        ((2 * z.1) ^ 2 / 2 - ((2 * z.1) - 2 * mu) ^ 2 / (2 * s ^ 2)) +
          (z.2.1 ^ 2 / 2 - z.2.1 ^ 2 / (2 * s ^ 2)) +
          (z.2.2.1 ^ 2 / 2 - z.2.2.1 ^ 2 / (2 * s ^ 2)) +
          (z.2.2.2 ^ 2 / 2 - z.2.2.2 ^ 2 / (2 * s ^ 2)) := by
    dsimp only [z]
    field_simp [hs.ne']
    nlinarith
  have hExp := congrArg Real.exp hExponent
  simp only [Real.exp_add] at hExp
  calc
    _ = s⁻¹ ^ 4 *
        (Real.exp
            ((omega.1 0) ^ 2 / 2 - ((omega.1 0) - mu) ^ 2 / (2 * s ^ 2)) *
          Real.exp
            ((omega.1 1) ^ 2 / 2 - ((omega.1 1) - mu) ^ 2 / (2 * s ^ 2)) *
          Real.exp
            ((omega.2 0) ^ 2 / 2 - ((omega.2 0) - mu) ^ 2 / (2 * s ^ 2)) *
          Real.exp
            ((omega.2 1) ^ 2 / 2 - ((omega.2 1) - mu) ^ 2 / (2 * s ^ 2))) := by
          ring
    _ = s⁻¹ ^ 4 *
        (Real.exp
            ((2 * z.1) ^ 2 / 2 - ((2 * z.1) - 2 * mu) ^ 2 / (2 * s ^ 2)) *
          Real.exp (z.2.1 ^ 2 / 2 - z.2.1 ^ 2 / (2 * s ^ 2)) *
          Real.exp (z.2.2.1 ^ 2 / 2 - z.2.2.1 ^ 2 / (2 * s ^ 2)) *
          Real.exp (z.2.2.2 ^ 2 / 2 - z.2.2.2 ^ 2 / (2 * s ^ 2))) := by
          rw [hExp]
    _ = _ := by
      dsimp only [z]
      ring_nf



theorem d016787
    (mu s x : ℝ) (hs : 0 < s) :
    _root_.GD.N0232.N0719.N0932.d009204 (2 * mu) s (2 * x) =
      _root_.GD.N0232.N0720.N1277.d002621 (s ^ 2 / 4) (x - mu) /
        _root_.GD.N0232.N0720.N1277.d002621 (1 / 4) x := by
  have hv : 0 < s ^ 2 / 4 := by positivity
  have hv0 : (0 : ℝ) < 1 / 4 := by norm_num
  rw [_root_.GD.N0232.N0720.N1124.d016497
    (2 * mu) s (2 * x) hs]
  rw [_root_.GD.N0232.N0720.N1277.d002623 hv,
    _root_.GD.N0232.N0720.N1277.d002623 hv0]
  unfold _root_.GD.N0232.N0720.N1277.d002622
  have hsqrtNum : Real.sqrt (2 * Real.pi * (s ^ 2 / 4)) =
      s / 2 * Real.sqrt (2 * Real.pi) := by
    calc
      Real.sqrt (2 * Real.pi * (s ^ 2 / 4)) =
          Real.sqrt ((s / 2) ^ 2 * (2 * Real.pi)) := by congr 1 <;> ring
      _ = Real.sqrt ((s / 2) ^ 2) * Real.sqrt (2 * Real.pi) := by
        rw [Real.sqrt_mul (sq_nonneg (s / 2))]
      _ = s / 2 * Real.sqrt (2 * Real.pi) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]
  have hsqrtDen : Real.sqrt (2 * Real.pi * (1 / 4 : ℝ)) =
      (1 / 2) * Real.sqrt (2 * Real.pi) := by
    calc
      Real.sqrt (2 * Real.pi * (1 / 4 : ℝ)) =
          Real.sqrt ((1 / 2 : ℝ) ^ 2 * (2 * Real.pi)) := by congr 1 <;> ring
      _ = Real.sqrt ((1 / 2 : ℝ) ^ 2) * Real.sqrt (2 * Real.pi) := by
        rw [Real.sqrt_mul (sq_nonneg (1 / 2 : ℝ))]
      _ = (1 / 2) * Real.sqrt (2 * Real.pi) := by norm_num
  rw [hsqrtNum, hsqrtDen]
  rw [show (1 / 2 : ℝ) * Real.sqrt (2 * Real.pi) =
      Real.sqrt (2 * Real.pi) / 2 by ring]
  have hden :
      ((Real.sqrt (2 * Real.pi) / 2)⁻¹ * Real.exp (-(x ^ 2) / (2 * (1 / 4)))) ≠ 0 := by
    positivity
  apply (eq_div_iff hden).2
  rw [show
      s⁻¹ * Real.exp
          ((2 * x) ^ 2 / 2 - ((2 * x) - 2 * mu) ^ 2 / (2 * s ^ 2)) *
          ((Real.sqrt (2 * Real.pi) / 2)⁻¹ *
            Real.exp (-(x ^ 2) / (2 * (1 / 4)))) =
        (s⁻¹ * (Real.sqrt (2 * Real.pi) / 2)⁻¹) *
          (Real.exp
              ((2 * x) ^ 2 / 2 - ((2 * x) - 2 * mu) ^ 2 / (2 * s ^ 2)) *
            Real.exp (-(x ^ 2) / (2 * (1 / 4)))) by ring,
    ← Real.exp_add]
  have hexponent :
      (2 * x) ^ 2 / 2 - ((2 * x) - 2 * mu) ^ 2 / (2 * s ^ 2) +
          (-(x ^ 2) / (2 * (1 / 4))) =
        -(x - mu) ^ 2 / (2 * (s ^ 2 / 4)) := by
    field_simp [hs.ne']
    ring
  rw [hexponent]
  have hroot : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp [hs.ne', hroot]

end

end GD.N0232.N0720.N1289

#print axioms _root_.GD.N0232.N0720.N1289.d016786
#print axioms _root_.GD.N0232.N0720.N1289.d016787

