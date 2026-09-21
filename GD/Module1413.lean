import GD.Module1412

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators

namespace GD.N0036
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N0864 _root_.GD.N0099

def d022652 (ε : ℝ) : ℝ := (1 + ε) * Real.exp ε

theorem d022653 (ε : ℝ) (hε : 0 < ε) : 0 < _root_.GD.N0036.d022652 ε := by
  unfold _root_.GD.N0036.d022652
  positivity

theorem d022654 (ε t x : ℝ) (hε : 0 < ε) (ht : |t| ≤ ε) :
    -ε ≤ x ^ 2 / 2 - (x - t) ^ 2 / (2 * (1 + ε) ^ 2) := by
  have ht2 : t ^ 2 ≤ ε ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg t) hε.le).mpr ht
  have hy : -2 * x * t ≤ ε * x ^ 2 + t ^ 2 / ε := by
    have hh : (-2 * x * t - ε * x ^ 2) * ε ≤ t ^ 2 := by
      nlinarith [sq_nonneg (ε * x + t)]
    have hh' := (le_div_iff₀ hε).mpr hh
    linarith
  have htdiv : t ^ 2 / ε ≤ ε := (div_le_iff₀ hε).mpr (by nlinarith)
  have hr : 0 < (1 + ε) ^ 2 := sq_pos_of_pos (by linarith)
  have hextra : 0 ≤ (ε + ε ^ 2) * x ^ 2 := mul_nonneg (by positivity) (sq_nonneg x)
  have hq : (x - t) ^ 2 ≤ (1 + ε) ^ 2 * (x ^ 2 + 2 * ε) := by
    nlinarith [mul_nonneg hε.le (sq_nonneg ε)]
  have hdiv : (x - t) ^ 2 / (2 * (1 + ε) ^ 2) ≤ x ^ 2 / 2 + ε :=
    (div_le_iff₀ (by positivity : 0 < 2 * (1 + ε) ^ 2)).mpr (by nlinarith)
  linarith


theorem d022655 (ε t : ℝ) (hε : 0 < ε) (ht : |t| ≤ ε) :
    gaussianReal 0 1 ≤ ENNReal.ofReal (_root_.GD.N0036.d022652 ε) •
      gaussianReal t (_root_.GD.N0232.N0719.N0932.d009193 (1 + ε)) := by
  have hr : 0 < 1 + ε := by linarith
  have hpdf (x : ℝ) : gaussianPDFReal 0 1 x ≤
      _root_.GD.N0036.d022652 ε * gaussianPDFReal t (_root_.GD.N0232.N0719.N0932.d009193 (1 + ε)) x := by
    rw [_root_.GD.N0232.N0719.N0864.d011071 t (1 + ε) x hr]
    have hexp : 1 ≤ Real.exp ε *
        Real.exp (x ^ 2 / 2 - (x - t) ^ 2 / (2 * (1 + ε) ^ 2)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by have := _root_.GD.N0036.d022654 ε t x hε ht; linarith)
    have hh := mul_le_mul_of_nonneg_left hexp (gaussianPDFReal_nonneg 0 1 x)
    dsimp [_root_.GD.N0036.d022652]
    convert hh using 1 <;> (first | rfl | field_simp [hr.ne'])
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    gaussianReal_of_var_ne_zero t (by
      intro hh
      have hh' := congrArg (fun x : ℝ≥0 => (x : ℝ)) hh
      change (1 + ε) ^ 2 = 0 at hh'
      exact (sq_pos_of_pos hr).ne' hh'),
    ← withDensity_smul _ (measurable_gaussianPDF _ _)]
  apply withDensity_mono
  apply ae_of_all
  intro x
  change ENNReal.ofReal (gaussianPDFReal 0 1 x) ≤
    ENNReal.ofReal (_root_.GD.N0036.d022652 ε) * ENNReal.ofReal (gaussianPDFReal t (_root_.GD.N0232.N0719.N0932.d009193 (1 + ε)) x)
  rw [← ENNReal.ofReal_mul (_root_.GD.N0036.d022653 ε hε).le]
  exact ENNReal.ofReal_le_ofReal (hpdf x)

theorem d022656 (ε L μ : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (hμ : |μ| ≤ ε * L) :
    gaussianReal 0 (_root_.GD.N0232.N0719.N0932.d009193 L) ≤ ENNReal.ofReal (_root_.GD.N0036.d022652 ε) •
      gaussianReal μ (_root_.GD.N0232.N0719.N0932.d009193 ((1 + ε) * L)) := by
  have ht : |μ / L| ≤ ε := by
    rw [abs_div, abs_of_pos hL]
    exact (div_le_iff₀ hL).mpr hμ
  have hm := Measure.map_mono (_root_.GD.N0036.d022655 ε (μ / L) hε ht)
    (show Measurable (fun x : ℝ => L * x) by fun_prop)
  rw [Measure.map_smul, gaussianReal_map_const_mul, gaussianReal_map_const_mul] at hm
  have hv0 : NNReal.mk (L ^ 2) (sq_nonneg L) * 1 = _root_.GD.N0232.N0719.N0932.d009193 L := by rw [mul_one]; rfl
  have hv1 : NNReal.mk (L ^ 2) (sq_nonneg L) * _root_.GD.N0232.N0719.N0932.d009193 (1 + ε) =
      _root_.GD.N0232.N0719.N0932.d009193 ((1 + ε) * L) := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, _root_.GD.N0232.N0719.N0932.d009194, NNReal.coe_mk]
    ring
  simpa only [mul_zero, mul_div_cancel₀ _ hL.ne', hv0, hv1] using hm

theorem d022657 (n : ℕ) (ε L μ : ℝ) (hε : 0 < ε) (hL : 0 < L)
    (hμ : |μ| ≤ ε * L) :
    _root_.GD.N0232.N0719.d009174 n 0 L ≤ ENNReal.ofReal (_root_.GD.N0036.d022652 ε ^ n) •
      _root_.GD.N0232.N0719.d009174 n μ ((1 + ε) * L) := by
  rw [_root_.GD.N0232.N0719.N0932.d009211, _root_.GD.N0232.N0719.N0932.d009211]
  have hh := _root_.GD.N0099.d022649 n (fun _ => ℝ)
    (fun _ => gaussianReal 0 (_root_.GD.N0232.N0719.N0932.d009193 L))
    (fun _ => gaussianReal μ (_root_.GD.N0232.N0719.N0932.d009193 ((1 + ε) * L)))
    (fun _ => ENNReal.ofReal (_root_.GD.N0036.d022652 ε)) (fun _ => ENNReal.ofReal_ne_top)
    (fun _ => _root_.GD.N0036.d022656 ε L μ hε hL hμ)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow (_root_.GD.N0036.d022653 ε hε).le] using hh

theorem d022658 (k : ℕ) (sizes : Fin k → ℕ)
    (ε L μ : ℝ) (hε : 0 < ε) (hL : 0 < L) (hμ : |μ| ≤ ε * L) :
    _root_.GD.N0232.N0719.d009176 k sizes 0 (fun _ => L) ≤
      ENNReal.ofReal (∏ l, _root_.GD.N0036.d022652 ε ^ sizes l) •
        _root_.GD.N0232.N0719.d009176 k sizes μ (fun _ => (1 + ε) * L) := by
  have hh := _root_.GD.N0099.d022649 k (fun l => _root_.GD.N0137.d008894 (sizes l))
    (fun l => _root_.GD.N0232.N0719.d009174 (sizes l) 0 L)
    (fun l => _root_.GD.N0232.N0719.d009174 (sizes l) μ ((1 + ε) * L))
    (fun l => ENNReal.ofReal (_root_.GD.N0036.d022652 ε ^ sizes l)) (fun _ => ENNReal.ofReal_ne_top)
    (fun l => _root_.GD.N0036.d022657 (sizes l) ε L μ hε hL hμ)
  simpa only [_root_.GD.N0232.N0719.d009176,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => (pow_pos (_root_.GD.N0036.d022653 ε hε) _).le)] using hh

theorem d022659 : Continuous _root_.GD.N0036.d022652 := by
  unfold _root_.GD.N0036.d022652
  fun_prop

@[simp] theorem d022660 : _root_.GD.N0036.d022652 0 = 1 := by simp [_root_.GD.N0036.d022652]

end
end GD.N0036

#print axioms _root_.GD.N0036.d022654
#print axioms _root_.GD.N0036.d022655
#print axioms _root_.GD.N0036.d022658
