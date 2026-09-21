import GD.Module0743

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators

namespace GD.N0099
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N0864

def d022643 : ℝ := 2 * Real.exp 1

theorem d022644 : 0 < _root_.GD.N0099.d022643 := by unfold _root_.GD.N0099.d022643; positivity


theorem d022645 (t x : ℝ) (ht : |t| ≤ 1) :
    gaussianPDFReal 0 1 x ≤ _root_.GD.N0099.d022643 * gaussianPDFReal t (_root_.GD.N0232.N0719.N0932.d009193 2) x := by
  rw [_root_.GD.N0232.N0719.N0864.d011071 t 2 x (by norm_num)]
  have ht2 : t ^ 2 ≤ 1 := by
    have h := sq_le_sq₀ (abs_nonneg t) (by norm_num : (0 : ℝ) ≤ 1) |>.mpr ht
    simpa only [sq_abs, one_pow] using h
  have hE : -(1 : ℝ) ≤ x ^ 2 / 2 - (x - t) ^ 2 / (2 * (2 : ℝ) ^ 2) := by
    nlinarith [sq_nonneg (x + t), sq_nonneg x]
  have hexp : 1 ≤ Real.exp 1 * Real.exp (x ^ 2 / 2 - (x - t) ^ 2 / (2 * (2 : ℝ) ^ 2)) := by
    rw [← Real.exp_add]
    exact Real.one_le_exp_iff.mpr (by linarith)
  have hh := mul_le_mul_of_nonneg_left hexp (gaussianPDFReal_nonneg 0 1 x)
  dsimp [_root_.GD.N0099.d022643]
  nlinarith

theorem d022646 (t : ℝ) (ht : |t| ≤ 1) :
    gaussianReal 0 1 ≤ ENNReal.ofReal _root_.GD.N0099.d022643 • gaussianReal t (_root_.GD.N0232.N0719.N0932.d009193 2) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    gaussianReal_of_var_ne_zero t (by
      intro hh
      have hh' := congrArg (fun x : ℝ≥0 => (x : ℝ)) hh
      change (2 : ℝ) ^ 2 = 0 at hh'
      norm_num at hh'),
    ← withDensity_smul _ (measurable_gaussianPDF _ _)]
  apply withDensity_mono
  apply ae_of_all
  intro x
  change ENNReal.ofReal (gaussianPDFReal 0 1 x) ≤
    ENNReal.ofReal _root_.GD.N0099.d022643 * ENNReal.ofReal (gaussianPDFReal t (_root_.GD.N0232.N0719.N0932.d009193 2) x)
  rw [← ENNReal.ofReal_mul _root_.GD.N0099.d022644.le]
  exact ENNReal.ofReal_le_ofReal (_root_.GD.N0099.d022645 t x ht)


theorem d022647 (L μ : ℝ) (hL : 0 < L) (hμ : |μ| ≤ L) :
    gaussianReal 0 (_root_.GD.N0232.N0719.N0932.d009193 L) ≤
      ENNReal.ofReal _root_.GD.N0099.d022643 • gaussianReal μ (_root_.GD.N0232.N0719.N0932.d009193 (2 * L)) := by
  have ht : |μ / L| ≤ 1 := by
    rw [abs_div, abs_of_pos hL]
    exact (div_le_one hL).mpr hμ
  have hm := Measure.map_mono (_root_.GD.N0099.d022646 (μ / L) ht)
    (show Measurable (fun x : ℝ => L * x) by fun_prop)
  rw [Measure.map_smul, gaussianReal_map_const_mul, gaussianReal_map_const_mul] at hm
  have hv0 : NNReal.mk (L ^ 2) (sq_nonneg L) * 1 = _root_.GD.N0232.N0719.N0932.d009193 L := by
    rw [mul_one]
    rfl
  have hv2 : NNReal.mk (L ^ 2) (sq_nonneg L) * _root_.GD.N0232.N0719.N0932.d009193 2 = _root_.GD.N0232.N0719.N0932.d009193 (2 * L) := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, _root_.GD.N0232.N0719.N0932.d009194, NNReal.coe_mk]
    ring
  simpa only [mul_zero, mul_div_cancel₀ _ hL.ne', hv0, hv2] using hm


theorem d022648 {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ μ' : Measure X) (ν ν' : Measure Y)
    [SigmaFinite μ] [SigmaFinite μ'] [SigmaFinite ν] [SigmaFinite ν']
    (a b : ℝ≥0∞) (hb : b ≠ ⊤)
    (hμ : μ ≤ a • μ') (hν : ν ≤ b • ν') :
    μ.prod ν ≤ (a * b) • μ'.prod ν' := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.prod_apply hs, Measure.smul_apply, smul_eq_mul,
    Measure.prod_apply hs]
  calc
    _ ≤ ∫⁻ x, (b • ν') (Prod.mk x ⁻¹' s) ∂(a • μ') :=
      lintegral_mono' hμ (fun x => hν _)
    _ = _ := by
      simp only [Measure.smul_apply, smul_eq_mul, lintegral_smul_measure]
      rw [lintegral_const_mul' _ _ hb]
      ring

theorem d022649 (n : ℕ) (X : Fin n → Type*) [∀ i, MeasurableSpace (X i)]
    (μ ν : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (a : Fin n → ℝ≥0∞) (ha : ∀ i, a i ≠ ⊤) (h : ∀ i, μ i ≤ a i • ν i) :
    Measure.pi μ ≤ (∏ i, a i) • Measure.pi ν := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν]
    simp
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove X 0
    have ht := ih (fun i => X ((0 : Fin (n + 1)).succAbove i))
      (fun i => μ ((0 : Fin (n + 1)).succAbove i))
      (fun i => ν ((0 : Fin (n + 1)).succAbove i))
      (fun i => a ((0 : Fin (n + 1)).succAbove i))
      (fun i => ha ((0 : Fin (n + 1)).succAbove i))
      (fun i => h ((0 : Fin (n + 1)).succAbove i))
    have hp := _root_.GD.N0099.d022648 (μ 0) (ν 0)
      (Measure.pi fun i => μ ((0 : Fin (n + 1)).succAbove i))
      (Measure.pi fun i => ν ((0 : Fin (n + 1)).succAbove i))
      (a 0) (∏ i, a ((0 : Fin (n + 1)).succAbove i))
      (ENNReal.prod_ne_top fun i _ => ha ((0 : Fin (n + 1)).succAbove i)) (h 0) ht
    have hm := Measure.map_mono hp e.symm.measurable
    rw [Measure.map_smul] at hm
    have hμ := (measurePreserving_piFinSuccAbove μ 0).symm.map_eq
    have hν := (measurePreserving_piFinSuccAbove ν 0).symm.map_eq
    rw [hμ, hν] at hm
    rw [Fin.prod_univ_succAbove a 0]
    exact hm

theorem d022650 (n : ℕ) (L μ : ℝ)
    (hL : 0 < L) (hμ : |μ| ≤ L) :
    _root_.GD.N0232.N0719.d009174 n 0 L ≤
      ENNReal.ofReal (_root_.GD.N0099.d022643 ^ n) • _root_.GD.N0232.N0719.d009174 n μ (2 * L) := by
  simp only [_root_.GD.N0232.N0719.N0932.d009211]
  have hh := _root_.GD.N0099.d022649 n (fun _ => ℝ)
    (fun _ => gaussianReal 0 (_root_.GD.N0232.N0719.N0932.d009193 L))
    (fun _ => gaussianReal μ (_root_.GD.N0232.N0719.N0932.d009193 (2 * L)))
    (fun _ => ENNReal.ofReal _root_.GD.N0099.d022643) (fun _ => ENNReal.ofReal_ne_top)
    (fun _ => _root_.GD.N0099.d022647 L μ hL hμ)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow _root_.GD.N0099.d022644.le] using hh


theorem d022651 (k : ℕ) (sizes : Fin k → ℕ) (L μ : ℝ)
    (hL : 0 < L) (hμ : |μ| ≤ L) :
    _root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ => L) ≤
      ENNReal.ofReal (∏ i, _root_.GD.N0099.d022643 ^ sizes i) •
        _root_.GD.N0232.N0719.d009176 k sizes μ (fun _ => 2 * L) := by
  have hh := _root_.GD.N0099.d022649 k (fun i => _root_.GD.N0137.d008894 (sizes i))
    (fun i => _root_.GD.N0232.N0719.d009174 (sizes i) 0 L)
    (fun i => _root_.GD.N0232.N0719.d009174 (sizes i) μ (2 * L))
    (fun i => ENNReal.ofReal (_root_.GD.N0099.d022643 ^ sizes i)) (fun _ => ENNReal.ofReal_ne_top)
    (fun i => _root_.GD.N0099.d022650 (sizes i) L μ hL hμ)
  simpa only [_root_.GD.N0232.N0719.d009176, ← ENNReal.ofReal_prod_of_nonneg
    (fun i _ => pow_nonneg _root_.GD.N0099.d022644.le (sizes i))] using hh

end
end GD.N0099

#print axioms _root_.GD.N0099.d022646
#print axioms _root_.GD.N0099.d022647
#print axioms _root_.GD.N0099.d022648
#print axioms _root_.GD.N0099.d022651
