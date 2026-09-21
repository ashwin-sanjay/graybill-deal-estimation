import GD.Module0380
import GD.Module0826
import GD.Module0752




















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace GD.N0106.N0428.N0765.N1617
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0932 _root_.GD.N0232.N0719.N1011
open _root_.GD.N0106.N0428.N0765.N1611 _root_.GD.N0106.N0428.N0765.N1618 _root_.GD.N0106.N0428.N0765.N1628

abbrev d012686 := _root_.GD.N0106.N0428.N0765.N1611.d012588


def d012687 (t : ℝ) : ℝ := (Real.sqrt t)⁻¹

theorem d012688 {t : ℝ} (ht : 0 < t) : 0 < _root_.GD.N0106.N0428.N0765.N1617.d012687 t :=
  inv_pos.mpr (Real.sqrt_pos.mpr ht)

theorem d012689 {t : ℝ} (ht : 0 < t) : _root_.GD.N0106.N0428.N0765.N1617.d012687 t ^ 2 = t⁻¹ := by
  simp only [_root_.GD.N0106.N0428.N0765.N1617.d012687, inv_pow, Real.sq_sqrt ht.le]


def d012690 (f : ℝ → ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), t⁻¹ * f t


theorem d012691 (f : ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    _root_.GD.N0106.N0428.N0765.N1617.d012690 (fun t => f (c * t)) = _root_.GD.N0106.N0428.N0765.N1617.d012690 f := by
  have hpoint : ∀ t : ℝ, t⁻¹ * f (c * t) =
      c * ((c * t)⁻¹ * f (c * t)) := by
    intro t
    simp only [mul_inv]
    field_simp [hc.ne']
  unfold _root_.GD.N0106.N0428.N0765.N1617.d012690
  simp_rw [hpoint]
  rw [integral_const_mul,
    integral_comp_mul_left_Ioi (fun t : ℝ => t⁻¹ * f t) 0 hc]
  simp [hc.ne', smul_eq_mul, mul_assoc]



theorem d012692 (f : ℝ → ℝ) :
    _root_.GD.N0106.N0428.N0765.N1617.d012690 (fun s => f (s ^ (-(2 : ℝ)))) = (1 / 2 : ℝ) * _root_.GD.N0106.N0428.N0765.N1617.d012690 f := by
  have h := integral_comp_rpow_Ioi (fun t : ℝ => t⁻¹ * f t)
    (by norm_num : (-(2 : ℝ)) ≠ 0)
  have hp : (∫ s in Ioi (0 : ℝ),
      (|(-(2 : ℝ))| * s ^ (-(2 : ℝ) - 1)) •
        ((s ^ (-(2 : ℝ)))⁻¹ * f (s ^ (-(2 : ℝ))))) =
      2 * _root_.GD.N0106.N0428.N0765.N1617.d012690 (fun s => f (s ^ (-(2 : ℝ)))) := by
    rw [_root_.GD.N0106.N0428.N0765.N1617.d012690, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    have hs' : 0 < s := hs
    have he : s ^ (-(2 : ℝ) - 1) * (s ^ (-(2 : ℝ)))⁻¹ = s⁻¹ := by
      rw [← Real.rpow_neg hs'.le, ← Real.rpow_add hs']
      norm_num [Real.rpow_neg_one]
    simp only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2), smul_eq_mul]
    calc (2 * s ^ (-(2 : ℝ) - 1)) *
          ((s ^ (-(2 : ℝ)))⁻¹ * f (s ^ (-(2 : ℝ)))) =
        2 * (s ^ (-(2 : ℝ) - 1) * (s ^ (-(2 : ℝ)))⁻¹) *
          f (s ^ (-(2 : ℝ))) := by ring
      _ = _ := by rw [he]; ring
  rw [hp] at h
  change 2 * _root_.GD.N0106.N0428.N0765.N1617.d012690 (fun s => f (s ^ (-(2 : ℝ)))) = _root_.GD.N0106.N0428.N0765.N1617.d012690 f at h
  linarith

def d012693 (x : _root_.GD.N0106.N0428.N0765.N1617.d012686) : ℝ :=
  Real.exp ((_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x + 11 * _root_.GD.N0106.N0428.N0765.N1611.d012589 0 x ^ 2) / 2) *
    Real.exp ((_root_.GD.N0106.N0428.N0765.N1611.d012590 1 x + 11 * _root_.GD.N0106.N0428.N0765.N1611.d012589 1 x ^ 2) / 2)

theorem d012694 (x : _root_.GD.N0106.N0428.N0765.N1617.d012686) : 0 < _root_.GD.N0106.N0428.N0765.N1617.d012693 x := by
  unfold _root_.GD.N0106.N0428.N0765.N1617.d012693
  positivity

def d012695 (x : _root_.GD.N0106.N0428.N0765.N1617.d012686) (mu t₁ t₂ : ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0932.d009219 2 (fun _ => 11) mu
    ![_root_.GD.N0106.N0428.N0765.N1617.d012687 t₁, _root_.GD.N0106.N0428.N0765.N1617.d012687 t₂] x


theorem d012696 (mu t₁ t₂ : ℝ)
    (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) :
    _root_.GD.N0106.N0428.N0765.N1611.d012595 mu ![_root_.GD.N0106.N0428.N0765.N1617.d012687 t₁, _root_.GD.N0106.N0428.N0765.N1617.d012687 t₂] =
      (_root_.GD.N0232.N0719.d009182 2 (fun _ => 11)).withDensity
        (fun x => ENNReal.ofReal (_root_.GD.N0106.N0428.N0765.N1617.d012695 x mu t₁ t₂)) := by
  apply _root_.GD.N0232.N0719.N0932.d009223
  intro i
  fin_cases i
  · exact _root_.GD.N0106.N0428.N0765.N1617.d012688 ht₁
  · exact _root_.GD.N0106.N0428.N0765.N1617.d012688 ht₂

theorem d012697 {t : ℝ} (ht : 0 < t) :
    ((Real.sqrt (2 * Real.pi * _root_.GD.N0106.N0428.N0765.N1617.d012687 t ^ 2))⁻¹ /
      (Real.sqrt (2 * Real.pi))⁻¹) ^ 11 = t ^ ((11 : ℝ) / 2) := by
  have hs := _root_.GD.N0106.N0428.N0765.N1617.d012688 ht
  have hpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hroot : Real.sqrt (2 * Real.pi * _root_.GD.N0106.N0428.N0765.N1617.d012687 t ^ 2) =
      Real.sqrt (2 * Real.pi) * _root_.GD.N0106.N0428.N0765.N1617.d012687 t := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi),
      Real.sqrt_sq_eq_abs, abs_of_pos hs]
  have hfront : (Real.sqrt (2 * Real.pi * _root_.GD.N0106.N0428.N0765.N1617.d012687 t ^ 2))⁻¹ /
      (Real.sqrt (2 * Real.pi))⁻¹ = Real.sqrt t := by
    rw [hroot, mul_inv]
    simp only [_root_.GD.N0106.N0428.N0765.N1617.d012687, inv_inv]
    exact mul_div_cancel_left₀ _ (inv_ne_zero hpi.ne')
  rw [hfront, Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ht.le]
  norm_num

theorem d012698 (x : _root_.GD.N0106.N0428.N0765.N1617.d012686) (i : Fin 2) (mu t : ℝ)
    (ht : 0 < t) :
    _root_.GD.N0232.N0719.N0932.d009213 11 mu (_root_.GD.N0106.N0428.N0765.N1617.d012687 t) (x i) =
      Real.exp ((_root_.GD.N0106.N0428.N0765.N1611.d012590 i x + 11 * _root_.GD.N0106.N0428.N0765.N1611.d012589 i x ^ 2) / 2) *
        (t ^ ((11 : ℝ) / 2) * Real.exp (-(_root_.GD.N0106.N0428.N0765.N1618.d005722 (_root_.GD.N0106.N0428.N0765.N1611.d012590 i x) (_root_.GD.N0106.N0428.N0765.N1611.d012589 i x) mu / 2 * t))) := by
  rw [_root_.GD.N0232.N0719.N1011.d011287 (by norm_num : 2 ≤ 11)
    mu (_root_.GD.N0106.N0428.N0765.N1617.d012687 t) (_root_.GD.N0106.N0428.N0765.N1617.d012688 ht).ne']
  unfold _root_.GD.N0232.N0719.N1011.d011284
  rw [_root_.GD.N0106.N0428.N0765.N1617.d012697 ht,
    ← _root_.GD.N0232.N0719.N1011.d011286 (by norm_num : 2 ≤ 11) (x i)]
  change t ^ ((11 : ℝ) / 2) *
    Real.exp ((_root_.GD.N0106.N0428.N0765.N1611.d012590 i x + 11 * _root_.GD.N0106.N0428.N0765.N1611.d012589 i x ^ 2) / 2 -
      (_root_.GD.N0106.N0428.N0765.N1611.d012590 i x + 11 * (_root_.GD.N0106.N0428.N0765.N1611.d012589 i x - mu) ^ 2) / (2 * _root_.GD.N0106.N0428.N0765.N1617.d012687 t ^ 2)) = _
  rw [_root_.GD.N0106.N0428.N0765.N1617.d012689 ht]
  have hexp : (_root_.GD.N0106.N0428.N0765.N1611.d012590 i x + 11 * _root_.GD.N0106.N0428.N0765.N1611.d012589 i x ^ 2) / 2 -
      (_root_.GD.N0106.N0428.N0765.N1611.d012590 i x + 11 * (_root_.GD.N0106.N0428.N0765.N1611.d012589 i x - mu) ^ 2) / (2 * t⁻¹) =
      (_root_.GD.N0106.N0428.N0765.N1611.d012590 i x + 11 * _root_.GD.N0106.N0428.N0765.N1611.d012589 i x ^ 2) / 2 +
        -(_root_.GD.N0106.N0428.N0765.N1618.d005722 (_root_.GD.N0106.N0428.N0765.N1611.d012590 i x) (_root_.GD.N0106.N0428.N0765.N1611.d012589 i x) mu / 2 * t) := by
    unfold _root_.GD.N0106.N0428.N0765.N1618.d005722
    field_simp [ht.ne']
    ring
  rw [hexp, Real.exp_add]
  ring


def d012699 (x : _root_.GD.N0106.N0428.N0765.N1617.d012686) (mu : ℝ) (t : ℝ × ℝ) : ℝ :=
  (t.1⁻¹ * t.2⁻¹) * _root_.GD.N0106.N0428.N0765.N1617.d012695 x mu t.1 t.2

theorem d012700 {t : ℝ} (ht : 0 < t) :
    t ^ ((11 : ℝ) / 2) * t⁻¹ = t ^ ((11 : ℝ) / 2 - 1) := by
  rw [← Real.rpow_neg_one, ← Real.rpow_add ht]
  congr 1 <;> ring

theorem d012701 (x : _root_.GD.N0106.N0428.N0765.N1617.d012686) (mu : ℝ) (t : ℝ × ℝ)
    (ht₁ : 0 < t.1) (ht₂ : 0 < t.2) :
    _root_.GD.N0106.N0428.N0765.N1617.d012699 x mu t = _root_.GD.N0106.N0428.N0765.N1617.d012693 x *
      _root_.GD.N0106.N0428.N0765.N1628.d005802 (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012590 1 x) (_root_.GD.N0106.N0428.N0765.N1611.d012589 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012589 1 x) mu t.1 t.2 := by
  have h₀ := _root_.GD.N0106.N0428.N0765.N1617.d012698 x 0 mu t.1 ht₁
  have h₁ := _root_.GD.N0106.N0428.N0765.N1617.d012698 x 1 mu t.2 ht₂
  unfold _root_.GD.N0106.N0428.N0765.N1617.d012699 _root_.GD.N0106.N0428.N0765.N1617.d012695 _root_.GD.N0232.N0719.N0932.d009219 _root_.GD.N0232.N0719.N0932.d009190
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at *
  rw [h₀, h₁]
  unfold _root_.GD.N0106.N0428.N0765.N1617.d012693 _root_.GD.N0106.N0428.N0765.N1628.d005802 _root_.GD.N0106.N0428.N0765.N1628.d005801
  rw [← _root_.GD.N0106.N0428.N0765.N1617.d012700 ht₁, ← _root_.GD.N0106.N0428.N0765.N1617.d012700 ht₂]
  ring

abbrev d012702 : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))

theorem d012703 :
    ∀ᵐ t : ℝ × ℝ ∂_root_.GD.N0106.N0428.N0765.N1617.d012702, 0 < t.1 ∧ 0 < t.2 := by
  have hf := (Measure.quasiMeasurePreserving_fst
    (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume.restrict (Ioi (0 : ℝ)))).ae
      (ae_restrict_mem measurableSet_Ioi)
  have hs := (Measure.quasiMeasurePreserving_snd
    (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume.restrict (Ioi (0 : ℝ)))).ae
      (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hf, hs] with t ht₁ ht₂
  exact ⟨ht₁, ht₂⟩

theorem d012704 {Qv t : ℝ} (ht : 0 < t) : 0 < _root_.GD.N0106.N0428.N0765.N1628.d005801 Qv t := by
  unfold _root_.GD.N0106.N0428.N0765.N1628.d005801
  exact mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)

theorem d012705 {Qv : ℝ} (hQ : 0 < Qv) :
    IntegrableOn (_root_.GD.N0106.N0428.N0765.N1628.d005801 Qv) (Ioi (0 : ℝ)) := by
  apply Integrable.of_integral_ne_zero
  rw [_root_.GD.N0106.N0428.N0765.N1628.d005805 hQ]
  exact (mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.Gamma_pos_of_pos (by norm_num))) (Real.rpow_pos_of_pos hQ _)).ne'

theorem d012706 {S₁ S₂ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (a b mu : ℝ) :
    Integrable (fun t : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1628.d005802 S₁ S₂ a b mu t.1 t.2)
      _root_.GD.N0106.N0428.N0765.N1617.d012702 :=
  (_root_.GD.N0106.N0428.N0765.N1617.d012705 (_root_.GD.N0106.N0428.N0765.N1618.d005725 hS₁ a mu)).mul_prod
    (_root_.GD.N0106.N0428.N0765.N1617.d012705 (_root_.GD.N0106.N0428.N0765.N1618.d005725 hS₂ b mu))

theorem d012707 {S₁ S₂ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (a b mu : ℝ) :
    (∫ t : ℝ × ℝ, _root_.GD.N0106.N0428.N0765.N1628.d005802 S₁ S₂ a b mu t.1 t.2 ∂_root_.GD.N0106.N0428.N0765.N1617.d012702) =
      _root_.GD.N0106.N0428.N0765.N1628.d005803 * _root_.GD.N0106.N0428.N0765.N1618.d005723 S₁ S₂ a b mu := by
  rw [← integral_integral (_root_.GD.N0106.N0428.N0765.N1617.d012706 hS₁ hS₂ a b mu)]
  exact _root_.GD.N0106.N0428.N0765.N1628.d005807 hS₁ hS₂ a b mu

theorem d012708 {S₁ S₂ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (a b mu : ℝ) : 0 < _root_.GD.N0106.N0428.N0765.N1618.d005723 S₁ S₂ a b mu := by
  exact mul_pos (Real.rpow_pos_of_pos (_root_.GD.N0106.N0428.N0765.N1618.d005725 hS₁ a mu) _)
    (Real.rpow_pos_of_pos (_root_.GD.N0106.N0428.N0765.N1618.d005725 hS₂ b mu) _)

theorem d012709 {S₁ S₂ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (a b : ℝ) : Integrable (_root_.GD.N0106.N0428.N0765.N1618.d005723 S₁ S₂ a b) := by
  have hi := ((_root_.GD.N0106.N0428.N0765.N1618.d005764 hS₁ hS₂ a b).integral_prod_right).const_mul _root_.GD.N0106.N0428.N0765.N1618.d005727⁻¹
  refine hi.congr (Filter.Eventually.of_forall fun mu => ?_)
  dsimp only [Function.uncurry]
  rw [_root_.GD.N0106.N0428.N0765.N1618.d005758 hS₁ hS₂ a b mu]
  simp only [uIoc_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]

theorem d012710 {S₁ S₂ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (a b : ℝ) : Integrable (fun mu => mu * _root_.GD.N0106.N0428.N0765.N1618.d005723 S₁ S₂ a b mu) := by
  have hi := ((_root_.GD.N0106.N0428.N0765.N1618.d005765 hS₁ hS₂ a b).integral_prod_right).const_mul _root_.GD.N0106.N0428.N0765.N1618.d005727⁻¹
  refine hi.congr (Filter.Eventually.of_forall fun mu => ?_)
  dsimp only [Function.uncurry]
  rw [_root_.GD.N0106.N0428.N0765.N1618.d005758 hS₁ hS₂ a b mu]
  simp only [uIoc_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    integral_const_mul]
  ring



theorem d012711 {S₁ S₂ : ℝ} (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (a b : ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hint : Integrable (fun mu => f mu * _root_.GD.N0106.N0428.N0765.N1618.d005723 S₁ S₂ a b mu)) :
    Integrable (fun z : ℝ × (ℝ × ℝ) => f z.1 *
      _root_.GD.N0106.N0428.N0765.N1628.d005802 S₁ S₂ a b z.1 z.2.1 z.2.2) (volume.prod _root_.GD.N0106.N0428.N0765.N1617.d012702) := by
  have hm : Measurable (fun z : ℝ × (ℝ × ℝ) => f z.1 *
      _root_.GD.N0106.N0428.N0765.N1628.d005802 S₁ S₂ a b z.1 z.2.1 z.2.2) := by
    unfold _root_.GD.N0106.N0428.N0765.N1628.d005802 _root_.GD.N0106.N0428.N0765.N1628.d005801 _root_.GD.N0106.N0428.N0765.N1618.d005722
    fun_prop
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  constructor
  · exact Filter.Eventually.of_forall fun mu =>
      (_root_.GD.N0106.N0428.N0765.N1617.d012706 hS₁ hS₂ a b mu).const_mul (f mu)
  · refine (hint.norm.const_mul _root_.GD.N0106.N0428.N0765.N1628.d005803).congr
      (Filter.Eventually.of_forall fun mu => ?_)
    have he : (∫ t : ℝ × ℝ, ‖f mu * _root_.GD.N0106.N0428.N0765.N1628.d005802 S₁ S₂ a b mu t.1 t.2‖
        ∂_root_.GD.N0106.N0428.N0765.N1617.d012702) = |f mu| *
          (_root_.GD.N0106.N0428.N0765.N1628.d005803 * _root_.GD.N0106.N0428.N0765.N1618.d005723 S₁ S₂ a b mu) := by
      calc _ = ∫ t : ℝ × ℝ, |f mu| * _root_.GD.N0106.N0428.N0765.N1628.d005802 S₁ S₂ a b mu t.1 t.2
          ∂_root_.GD.N0106.N0428.N0765.N1617.d012702 := by
            apply integral_congr_ae
            filter_upwards [_root_.GD.N0106.N0428.N0765.N1617.d012703] with t ht
            unfold _root_.GD.N0106.N0428.N0765.N1628.d005802
            rw [Real.norm_eq_abs, abs_mul,
              abs_of_pos (mul_pos (_root_.GD.N0106.N0428.N0765.N1617.d012704 ht.1) (_root_.GD.N0106.N0428.N0765.N1617.d012704 ht.2))]
        _ = _ := by rw [integral_const_mul, _root_.GD.N0106.N0428.N0765.N1617.d012707 hS₁ hS₂ a b mu]
    dsimp only
    rw [he, Real.norm_eq_abs, abs_mul,
      abs_of_pos (_root_.GD.N0106.N0428.N0765.N1617.d012708 hS₁ hS₂ a b mu)]
    ring

theorem d012712 (x : _root_.GD.N0106.N0428.N0765.N1617.d012686) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594)
    (f : ℝ → ℝ) (hf : Measurable f)
    (hint : Integrable (fun mu => f mu *
      _root_.GD.N0106.N0428.N0765.N1618.d005723 (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012590 1 x) (_root_.GD.N0106.N0428.N0765.N1611.d012589 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012589 1 x) mu)) :
    Integrable (fun z : ℝ × (ℝ × ℝ) => f z.1 * _root_.GD.N0106.N0428.N0765.N1617.d012699 x z.1 z.2)
      (volume.prod _root_.GD.N0106.N0428.N0765.N1617.d012702) := by
  have hi := (_root_.GD.N0106.N0428.N0765.N1617.d012711 (hx 0) (hx 1) (_root_.GD.N0106.N0428.N0765.N1611.d012589 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012589 1 x)
    f hf hint).const_mul (_root_.GD.N0106.N0428.N0765.N1617.d012693 x)
  refine hi.congr ?_
  have hp := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure ℝ)) (ν := _root_.GD.N0106.N0428.N0765.N1617.d012702)).ae _root_.GD.N0106.N0428.N0765.N1617.d012703
  filter_upwards [hp] with z hz
  rw [_root_.GD.N0106.N0428.N0765.N1617.d012701 x z.1 z.2 hz.1 hz.2]
  ring

theorem d012713 (x : _root_.GD.N0106.N0428.N0765.N1617.d012686) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    Integrable (fun z : ℝ × (ℝ × ℝ) => _root_.GD.N0106.N0428.N0765.N1617.d012699 x z.1 z.2)
      (volume.prod _root_.GD.N0106.N0428.N0765.N1617.d012702) := by
  simpa using _root_.GD.N0106.N0428.N0765.N1617.d012712 x hx (fun _ => 1) measurable_const
    (by simpa using _root_.GD.N0106.N0428.N0765.N1617.d012709 (hx 0) (hx 1) (_root_.GD.N0106.N0428.N0765.N1611.d012589 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012589 1 x))

theorem d012714 (x : _root_.GD.N0106.N0428.N0765.N1617.d012686) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    Integrable (fun z : ℝ × (ℝ × ℝ) => z.1 * _root_.GD.N0106.N0428.N0765.N1617.d012699 x z.1 z.2)
      (volume.prod _root_.GD.N0106.N0428.N0765.N1617.d012702) :=
  _root_.GD.N0106.N0428.N0765.N1617.d012712 x hx id measurable_id
    (_root_.GD.N0106.N0428.N0765.N1617.d012710 (hx 0) (hx 1) (_root_.GD.N0106.N0428.N0765.N1611.d012589 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012589 1 x))

theorem d012715 (x : _root_.GD.N0106.N0428.N0765.N1617.d012686) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594)
    (mu : ℝ) :
    (∫ t, _root_.GD.N0106.N0428.N0765.N1617.d012699 x mu t ∂_root_.GD.N0106.N0428.N0765.N1617.d012702) =
      _root_.GD.N0106.N0428.N0765.N1617.d012693 x * _root_.GD.N0106.N0428.N0765.N1628.d005803 *
        _root_.GD.N0106.N0428.N0765.N1618.d005723 (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012590 1 x) (_root_.GD.N0106.N0428.N0765.N1611.d012589 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012589 1 x) mu := by
  have he : (fun t => _root_.GD.N0106.N0428.N0765.N1617.d012699 x mu t) =ᵐ[_root_.GD.N0106.N0428.N0765.N1617.d012702]
      (fun t => _root_.GD.N0106.N0428.N0765.N1617.d012693 x * _root_.GD.N0106.N0428.N0765.N1628.d005802 (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012590 1 x)
        (_root_.GD.N0106.N0428.N0765.N1611.d012589 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012589 1 x) mu t.1 t.2) := by
    filter_upwards [_root_.GD.N0106.N0428.N0765.N1617.d012703] with t ht
    exact _root_.GD.N0106.N0428.N0765.N1617.d012701 x mu t ht.1 ht.2
  rw [integral_congr_ae he, integral_const_mul,
    _root_.GD.N0106.N0428.N0765.N1617.d012707 (hx 0) (hx 1) (_root_.GD.N0106.N0428.N0765.N1611.d012589 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012589 1 x) mu]
  ring

def d012716 (x : _root_.GD.N0106.N0428.N0765.N1617.d012686) : ℝ :=
  ∫ mu, ∫ t, _root_.GD.N0106.N0428.N0765.N1617.d012699 x mu t ∂_root_.GD.N0106.N0428.N0765.N1617.d012702

def d012717 (x : _root_.GD.N0106.N0428.N0765.N1617.d012686) : ℝ :=
  (∫ mu, ∫ t, mu * _root_.GD.N0106.N0428.N0765.N1617.d012699 x mu t ∂_root_.GD.N0106.N0428.N0765.N1617.d012702) /
    _root_.GD.N0106.N0428.N0765.N1617.d012716 x

theorem d012718 (x : _root_.GD.N0106.N0428.N0765.N1617.d012686) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    0 < _root_.GD.N0106.N0428.N0765.N1617.d012716 x := by
  unfold _root_.GD.N0106.N0428.N0765.N1617.d012716
  simp_rw [_root_.GD.N0106.N0428.N0765.N1617.d012715 x hx]
  rw [integral_const_mul, _root_.GD.N0106.N0428.N0765.N1618.d005766 (hx 0) (hx 1) (_root_.GD.N0106.N0428.N0765.N1611.d012589 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012589 1 x)]
  exact mul_pos (mul_pos (_root_.GD.N0106.N0428.N0765.N1617.d012694 x) _root_.GD.N0106.N0428.N0765.N1628.d005806)
    (mul_pos (mul_pos (inv_pos.mpr _root_.GD.N0106.N0428.N0765.N1618.d005732) _root_.GD.N0106.N0428.N0765.N1618.d005753)
      (_root_.GD.N0106.N0428.N0765.N1534.d005310 (hx 0) (hx 1)))



theorem d012719 (x : _root_.GD.N0106.N0428.N0765.N1617.d012686) (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1611.d012594) :
    _root_.GD.N0106.N0428.N0765.N1617.d012717 x = _root_.GD.N0106.N0428.N0765.N1611.d012593 x := by
  unfold _root_.GD.N0106.N0428.N0765.N1617.d012717 _root_.GD.N0106.N0428.N0765.N1617.d012716
  simp_rw [integral_const_mul, _root_.GD.N0106.N0428.N0765.N1617.d012715 x hx]
  have hnum : (∫ mu, mu * (_root_.GD.N0106.N0428.N0765.N1617.d012693 x * _root_.GD.N0106.N0428.N0765.N1628.d005803 *
      _root_.GD.N0106.N0428.N0765.N1618.d005723 (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012590 1 x) (_root_.GD.N0106.N0428.N0765.N1611.d012589 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012589 1 x) mu)) =
      (_root_.GD.N0106.N0428.N0765.N1617.d012693 x * _root_.GD.N0106.N0428.N0765.N1628.d005803) *
        ∫ mu, mu * _root_.GD.N0106.N0428.N0765.N1618.d005723 (_root_.GD.N0106.N0428.N0765.N1611.d012590 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012590 1 x)
          (_root_.GD.N0106.N0428.N0765.N1611.d012589 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012589 1 x) mu := by
    rw [← integral_const_mul]
    congr 1
    funext mu
    ring
  rw [hnum, integral_const_mul,
    mul_div_mul_left _ _ (mul_pos (_root_.GD.N0106.N0428.N0765.N1617.d012694 x) _root_.GD.N0106.N0428.N0765.N1628.d005806).ne']
  exact _root_.GD.N0106.N0428.N0765.N1618.d005769 (hx 0) (hx 1) (_root_.GD.N0106.N0428.N0765.N1611.d012589 0 x) (_root_.GD.N0106.N0428.N0765.N1611.d012589 1 x)

theorem d012720 (location : ℝ) (scales : Fin 2 → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0106.N0428.N0765.N1617.d012717 =ᵐ[_root_.GD.N0106.N0428.N0765.N1611.d012595 location scales] _root_.GD.N0106.N0428.N0765.N1611.d012593 := by
  filter_upwards [_root_.GD.N0106.N0428.N0765.N1611.d012605 location scales hscales] with x hx
  exact _root_.GD.N0106.N0428.N0765.N1617.d012719 x hx

end
end GD.N0106.N0428.N0765.N1617

#print axioms _root_.GD.N0106.N0428.N0765.N1617.d012691
#print axioms _root_.GD.N0106.N0428.N0765.N1617.d012692
#print axioms _root_.GD.N0106.N0428.N0765.N1617.d012696
#print axioms _root_.GD.N0106.N0428.N0765.N1617.d012698
#print axioms _root_.GD.N0106.N0428.N0765.N1617.d012701
#print axioms _root_.GD.N0106.N0428.N0765.N1617.d012705
#print axioms _root_.GD.N0106.N0428.N0765.N1617.d012711
#print axioms _root_.GD.N0106.N0428.N0765.N1617.d012713
#print axioms _root_.GD.N0106.N0428.N0765.N1617.d012714
#print axioms _root_.GD.N0106.N0428.N0765.N1617.d012715
#print axioms _root_.GD.N0106.N0428.N0765.N1617.d012718
#print axioms _root_.GD.N0106.N0428.N0765.N1617.d012719
#print axioms _root_.GD.N0106.N0428.N0765.N1617.d012720
