import GD.Module0034
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory

namespace GD.N0213.N0505

noncomputable section

def d007548 (m₁ m₂ : ℝ) : ℝ := m₁ * m₂ / (m₁ + m₂)

def d007549 (m₁ m₂ A B w : ℝ) : ℝ :=
  m₁ * A * (m₂ / (m₁ + m₂)) ^ 2 +
    m₂ * B * (m₁ / (m₁ + m₂)) ^ 2 -
      (m₁ * A * w ^ 2 + m₂ * B * (1 - w) ^ 2)

theorem d007550 (m₁ m₂ A B w : ℝ)
    (hsum : m₁ + m₂ ≠ 0) :
    (m₁ * A + m₂ * B) * _root_.GD.N0213.N0505.d007549 m₁ m₂ A B w =
      (_root_.GD.N0213.N0505.d007548 m₁ m₂) ^ 2 * (A - B) ^ 2 -
        ((m₁ * A + m₂ * B) * w - m₂ * B) ^ 2 := by
  unfold _root_.GD.N0213.N0505.d007549 _root_.GD.N0213.N0505.d007548
  field_simp [hsum]
  ring

theorem d007551 (m₁ m₂ x y : ℝ)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    _root_.GD.N0213.N0505.d007548 m₁ m₂ * (x + y) ^ 2 ≤
      m₁ * x ^ 2 + m₂ * y ^ 2 := by
  unfold _root_.GD.N0213.N0505.d007548
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (add_pos hm₁ hm₂)).mpr
  nlinarith [sq_nonneg (m₁ * x - m₂ * y)]

theorem d007552 (m₁ m₂ A B D E w : ℝ)
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hcross : (A - B) ^ 2 ≤ D * E)
    (hsumEnergy : _root_.GD.N0213.N0505.d007548 m₁ m₂ * E ≤ m₁ * A + m₂ * B) :
    _root_.GD.N0213.N0505.d007549 m₁ m₂ A B w ≤ _root_.GD.N0213.N0505.d007548 m₁ m₂ * D := by
  let C := m₁ * A + m₂ * B
  let ℓ := _root_.GD.N0213.N0505.d007548 m₁ m₂
  have hℓ : 0 < ℓ := div_pos (mul_pos hm₁ hm₂) (add_pos hm₁ hm₂)
  have hC : 0 ≤ C := add_nonneg (mul_nonneg hm₁.le hA) (mul_nonneg hm₂.le hB)
  by_cases hCzero : C = 0
  · have hmA : m₁ * A = 0 := by
      apply le_antisymm
      · dsimp [C] at hCzero
        linarith [mul_nonneg hm₂.le hB]
      · exact mul_nonneg hm₁.le hA
    have hmB : m₂ * B = 0 := by
      apply le_antisymm
      · dsimp [C] at hCzero
        linarith [mul_nonneg hm₁.le hA]
      · exact mul_nonneg hm₂.le hB
    have hAzero : A = 0 := (mul_eq_zero.mp hmA).resolve_left hm₁.ne'
    have hBzero : B = 0 := (mul_eq_zero.mp hmB).resolve_left hm₂.ne'
    simpa only [_root_.GD.N0213.N0505.d007549, hAzero, hBzero, mul_zero, zero_mul, add_zero, sub_self]
      using mul_nonneg hℓ.le hD
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    apply (mul_le_mul_iff_right₀ hCpos).mp
    calc
      C * _root_.GD.N0213.N0505.d007549 m₁ m₂ A B w =
          ℓ ^ 2 * (A - B) ^ 2 - (C * w - m₂ * B) ^ 2 :=
        _root_.GD.N0213.N0505.d007550 m₁ m₂ A B w (add_pos hm₁ hm₂).ne'
      _ ≤ ℓ ^ 2 * (A - B) ^ 2 := sub_le_self _ (sq_nonneg _)
      _ ≤ ℓ ^ 2 * (D * E) := mul_le_mul_of_nonneg_left hcross (sq_nonneg ℓ)
      _ = (ℓ * D) * (ℓ * E) := by ring
      _ ≤ (ℓ * D) * C :=
        mul_le_mul_of_nonneg_left hsumEnergy (mul_nonneg hℓ.le hD)
      _ = C * (_root_.GD.N0213.N0505.d007548 m₁ m₂ * D) := mul_comm _ _

variable {Ω : Type*} [MeasurableSpace Ω]

theorem d007553 (μ : Measure Ω) (f g : Ω → ℝ)
    (m₁ m₂ w : ℝ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    _root_.GD.N0213.N0505.d007549 m₁ m₂ (∫ z, f z ^ 2 ∂μ) (∫ z, g z ^ 2 ∂μ) w ≤
      _root_.GD.N0213.N0505.d007548 m₁ m₂ * ∫ z, (f z - g z) ^ 2 ∂μ := by
  let A := ∫ z, f z ^ 2 ∂μ
  let B := ∫ z, g z ^ 2 ∂μ
  let D := ∫ z, (f z - g z) ^ 2 ∂μ
  let E := ∫ z, (f z + g z) ^ 2 ∂μ
  have hfSq := hf.integrable_sq
  have hgSq := hg.integrable_sq
  have hsubSq : Integrable (fun z ↦ (f z - g z) ^ 2) μ :=
    (hf.sub hg).integrable_sq
  have haddSq : Integrable (fun z ↦ (f z + g z) ^ 2) μ :=
    (hf.add hg).integrable_sq
  have hcrossInt : Integrable (fun z ↦ (f z - g z) * (f z + g z)) μ := by
    apply (hfSq.sub hgSq).congr
    filter_upwards with z
    dsimp
    ring
  have hcrossEq : (∫ z, (f z - g z) * (f z + g z) ∂μ) = A - B := by
    calc
      _ = ∫ z, f z ^ 2 - g z ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards with z
        ring
      _ = A - B := integral_sub hfSq hgSq
  have hcross : (A - B) ^ 2 ≤ D * E := by
    have h := _root_.GD.N0230.N0658.d000405
      μ (fun _ ↦ 1)
        (fun z ↦ f z - g z) (fun z ↦ f z + g z)
        (Filter.Eventually.of_forall (fun _ ↦ zero_le_one))
        (by simpa only [one_mul] using hsubSq)
        (by simpa only [one_mul] using hcrossInt)
        (by simpa only [one_mul] using haddSq)
    simp only [one_mul] at h
    rw [hcrossEq] at h
    exact h
  have hsumEnergy : _root_.GD.N0213.N0505.d007548 m₁ m₂ * E ≤ m₁ * A + m₂ * B := by
    calc
      _ = ∫ z, _root_.GD.N0213.N0505.d007548 m₁ m₂ * (f z + g z) ^ 2 ∂μ :=
        (integral_const_mul _ _).symm
      _ ≤ ∫ z, m₁ * f z ^ 2 + m₂ * g z ^ 2 ∂μ :=
        integral_mono (haddSq.const_mul _) ((hfSq.const_mul _).add (hgSq.const_mul _))
          (fun z ↦ _root_.GD.N0213.N0505.d007551 m₁ m₂ (f z) (g z) hm₁ hm₂)
      _ = m₁ * A + m₂ * B := by
        rw [integral_add (hfSq.const_mul _) (hgSq.const_mul _),
          integral_const_mul, integral_const_mul]
  exact _root_.GD.N0213.N0505.d007552 m₁ m₂ A B D E w hm₁ hm₂
    (integral_nonneg (fun z ↦ sq_nonneg (f z)))
    (integral_nonneg (fun z ↦ sq_nonneg (g z)))
    (integral_nonneg (fun z ↦ sq_nonneg (f z - g z))) hcross hsumEnergy

end

end GD.N0213.N0505

#print axioms _root_.GD.N0213.N0505.d007550
#print axioms _root_.GD.N0213.N0505.d007552
#print axioms _root_.GD.N0213.N0505.d007553
