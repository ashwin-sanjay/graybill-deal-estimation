import GD.Module1690
import GD.Module1683




set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace GD.N0101.N0395
noncomputable section
open _root_.GD.N0213
open _root_.GD.N0213.N0510 _root_.GD.N0213.N0526 _root_.GD.N0213.N0505
open _root_.GD.N0101.N0397 _root_.GD.N0101.N0396 _root_.GD.N0101.N0394
open _root_.GD.N0101.N0351
open _root_.GD.N0230.N0665

abbrev d028514 := Fin 2 → ℝ

def d028515 (a r₀ r₁ : ℝ) (h : _root_.GD.N0101.N0395.d028514 → ℝ) (i : Fin 2) : ℝ :=
  ∫ z, h (_root_.GD.N0101.N0397.d028118.symm z) ^ 2 ∂_root_.GD.N0101.N0396.d028146 a r₀ r₁ i

def d028516 (a r₀ r₁ : ℝ) (h : _root_.GD.N0101.N0395.d028514 → ℝ) (v : _root_.GD.N0101.N0395.d028514) : ℝ :=
  _root_.GD.N0101.N0396.d028143 a r₀ r₁ 0 * _root_.GD.N0101.N0395.d028515 a r₀ r₁ h 0 * v 0 ^ 2 +
    _root_.GD.N0101.N0396.d028143 a r₀ r₁ 1 * _root_.GD.N0101.N0395.d028515 a r₀ r₁ h 1 * v 1 ^ 2

def d028517 (a : ℝ) (t : _root_.GD.N0101.N0395.d028514) (h : _root_.GD.N0101.N0395.d028514 → ℝ) (v : _root_.GD.N0101.N0395.d028514) : ℝ≥0∞ :=
  ∫⁻ β, ENNReal.ofReal (_root_.GD.N0101.N0351.d023186 β v * h β ^ 2)
    ∂_root_.GD.N0213.N0510.d023126 (fun _ : Fin 2 => a) (fun i => a * t i)

theorem d028518 {a r₀ r₁ : ℝ}
    (ha : 0 < a) (h₀ : 0 < r₀) (h₁ : 0 < r₁) (h : _root_.GD.N0101.N0395.d028514 → ℝ) (i : Fin 2) :
    _root_.GD.N0101.N0396.d028143 a r₀ r₁ i * _root_.GD.N0101.N0395.d028515 a r₀ r₁ h i =
      ∫ z, _root_.GD.N0101.N0396.d028144 i z * h (_root_.GD.N0101.N0397.d028118.symm z) ^ 2 ∂_root_.GD.N0101.N0397.d028125 a r₀ r₁ := by
  have hm := _root_.GD.N0101.N0396.d028147 ha h₀ h₁ i
  unfold _root_.GD.N0101.N0395.d028515 _root_.GD.N0101.N0396.d028146
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0101.N0396.d028151 ha h₀ h₁ i] with z hz
  rw [ENNReal.toReal_ofReal (div_nonneg hz hm.le), smul_eq_mul]
  field_simp [hm.ne']

theorem d028519 {a r₀ r₁ : ℝ}
    (ha : 0 < a) (h₀ : 0 < r₀) (h₁ : 0 < r₁)
    (h : _root_.GD.N0101.N0395.d028514 → ℝ) (hh : Measurable h) (hb : ∀ β, h β ∈ Icc (0 : ℝ) 1) (i : Fin 2) :
    Integrable (fun z => _root_.GD.N0101.N0396.d028144 i z * h (_root_.GD.N0101.N0397.d028118.symm z) ^ 2)
      (_root_.GD.N0101.N0397.d028125 a r₀ r₁) := by
  apply (_root_.GD.N0101.N0396.d028149 ha h₀ h₁ i).mono' (by fun_prop)
  filter_upwards [_root_.GD.N0101.N0396.d028151 ha h₀ h₁ i] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hz (sq_nonneg _))]
  have hs : h (_root_.GD.N0101.N0397.d028118.symm z) ^ 2 ≤ 1 := by
    nlinarith [(hb (_root_.GD.N0101.N0397.d028118.symm z)).1, (hb (_root_.GD.N0101.N0397.d028118.symm z)).2]
  exact mul_le_of_le_one_right hz hs

theorem d028520 {a r₀ r₁ : ℝ}
    (ha : 0 < a) (h₀ : 0 < r₀) (h₁ : 0 < r₁)
    (h : _root_.GD.N0101.N0395.d028514 → ℝ) (hh : Measurable h) (hb : ∀ β, h β ∈ Icc (0 : ℝ) 1) (v : _root_.GD.N0101.N0395.d028514) :
    Integrable (fun z => _root_.GD.N0101.N0351.d023186 (_root_.GD.N0101.N0397.d028118.symm z) v * h (_root_.GD.N0101.N0397.d028118.symm z) ^ 2)
      (_root_.GD.N0101.N0397.d028125 a r₀ r₁) := by
  apply (((_root_.GD.N0101.N0395.d028519 ha h₀ h₁ h hh hb 0).mul_const (v 0 ^ 2)).add
    ((_root_.GD.N0101.N0395.d028519 ha h₀ h₁ h hh hb 1).mul_const (v 1 ^ 2))).congr
  filter_upwards with z
  simp only [_root_.GD.N0101.N0351.d023186, Fin.sum_univ_two, _root_.GD.N0101.N0396.d028144, Pi.add_apply]
  ring

theorem d028521 {a r₀ r₁ : ℝ}
    (ha : 0 < a) (h₀ : 0 < r₀) (h₁ : 0 < r₁)
    (h : _root_.GD.N0101.N0395.d028514 → ℝ) (hh : Measurable h) (hb : ∀ β, h β ∈ Icc (0 : ℝ) 1) (v : _root_.GD.N0101.N0395.d028514) :
    (∫ z, _root_.GD.N0101.N0351.d023186 (_root_.GD.N0101.N0397.d028118.symm z) v * h (_root_.GD.N0101.N0397.d028118.symm z) ^ 2
      ∂_root_.GD.N0101.N0397.d028125 a r₀ r₁) = _root_.GD.N0101.N0395.d028516 a r₀ r₁ h v := by
  calc
    _ = ∫ z, (_root_.GD.N0101.N0396.d028144 0 z * h (_root_.GD.N0101.N0397.d028118.symm z) ^ 2) * v 0 ^ 2 +
        (_root_.GD.N0101.N0396.d028144 1 z * h (_root_.GD.N0101.N0397.d028118.symm z) ^ 2) * v 1 ^ 2
        ∂_root_.GD.N0101.N0397.d028125 a r₀ r₁ := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [_root_.GD.N0101.N0351.d023186, Fin.sum_univ_two, _root_.GD.N0101.N0396.d028144]
      ring
    _ = _ := by
      rw [integral_add ((_root_.GD.N0101.N0395.d028519 ha h₀ h₁ h hh hb 0).mul_const _)
        ((_root_.GD.N0101.N0395.d028519 ha h₀ h₁ h hh hb 1).mul_const _),
        integral_mul_const, integral_mul_const,
        ← _root_.GD.N0101.N0395.d028518 ha h₀ h₁ h 0,
        ← _root_.GD.N0101.N0395.d028518 ha h₀ h₁ h 1]
      rfl

theorem d028522 (a : ℝ) (ha : 0 < a) (t : _root_.GD.N0101.N0395.d028514)
    (ht : ∀ i, 0 < t i) (h : _root_.GD.N0101.N0395.d028514 → ℝ) (hh : Measurable h)
    (hb : ∀ β, h β ∈ Icc (0 : ℝ) 1) (v : _root_.GD.N0101.N0395.d028514) :
    _root_.GD.N0101.N0395.d028517 a t h v =
      ENNReal.ofReal (_root_.GD.N0101.N0395.d028516 a (a * t 0) (a * t 1) h v) := by
  have h₀ := mul_pos ha (ht 0)
  have h₁ := mul_pos ha (ht 1)
  have hr : (![a * t 0, a * t 1] : _root_.GD.N0101.N0395.d028514) = (fun i => a * t i) := by
    funext i
    fin_cases i <;> rfl
  have hn : ∀ᵐ z ∂_root_.GD.N0101.N0397.d028125 a (a * t 0) (a * t 1),
      0 ≤ _root_.GD.N0101.N0351.d023186 (_root_.GD.N0101.N0397.d028118.symm z) v * h (_root_.GD.N0101.N0397.d028118.symm z) ^ 2 := by
    filter_upwards [_root_.GD.N0101.N0396.d028151 ha h₀ h₁ 0,
      _root_.GD.N0101.N0396.d028151 ha h₀ h₁ 1] with z hz₀ hz₁
    simp only [_root_.GD.N0101.N0351.d023186, Fin.sum_univ_two]
    exact mul_nonneg (add_nonneg (mul_nonneg hz₀ (sq_nonneg _))
      (mul_nonneg hz₁ (sq_nonneg _))) (sq_nonneg _)
  have heq := ofReal_integral_eq_lintegral_ofReal
    (_root_.GD.N0101.N0395.d028520 ha h₀ h₁ h hh hb v) hn
  rw [_root_.GD.N0101.N0395.d028521 ha h₀ h₁ h hh hb v] at heq
  rw [heq]
  unfold _root_.GD.N0101.N0397.d028125
  rw [lintegral_map (by unfold _root_.GD.N0101.N0351.d023186; fun_prop) _root_.GD.N0101.N0397.d028118.measurable, hr]
  simp only [MeasurableEquiv.symm_apply_apply]
  rfl

theorem d028523 {a r₀ r₁ : ℝ}
    (ha : 0 < a) (h₀ : 0 < r₀) (h₁ : 0 < r₁) (h : _root_.GD.N0101.N0395.d028514 → ℝ) (v : _root_.GD.N0101.N0395.d028514) :
    0 ≤ _root_.GD.N0101.N0395.d028516 a r₀ r₁ h v := by
  have hm₀ := (_root_.GD.N0101.N0396.d028147 ha h₀ h₁ 0).le
  have hm₁ := (_root_.GD.N0101.N0396.d028147 ha h₀ h₁ 1).le
  have hA (i : Fin 2) : 0 ≤ _root_.GD.N0101.N0395.d028515 a r₀ r₁ h i := integral_nonneg (fun _ => sq_nonneg _)
  unfold _root_.GD.N0101.N0395.d028516
  exact add_nonneg (mul_nonneg (mul_nonneg hm₀ (hA 0)) (sq_nonneg _))
    (mul_nonneg (mul_nonneg hm₁ (hA 1)) (sq_nonneg _))

theorem d028524 (a : ℝ) (ha : 0 < a) (t : _root_.GD.N0101.N0395.d028514)
    (ht : ∀ i, 0 < t i) :
    _root_.GD.N0230.N0665.d000407 t 0 = _root_.GD.N0101.N0396.d028143 a (a*t 0) (a*t 1) 1 /
      (_root_.GD.N0101.N0396.d028143 a (a*t 0) (a*t 1) 0 + _root_.GD.N0101.N0396.d028143 a (a*t 0) (a*t 1) 1) ∧
    _root_.GD.N0230.N0665.d000407 t 1 = _root_.GD.N0101.N0396.d028143 a (a*t 0) (a*t 1) 0 /
      (_root_.GD.N0101.N0396.d028143 a (a*t 0) (a*t 1) 0 + _root_.GD.N0101.N0396.d028143 a (a*t 0) (a*t 1) 1) := by
  have hr : (![a * t 0, a * t 1] : _root_.GD.N0101.N0395.d028514) = (fun i => a * t i) := by
    funext i
    fin_cases i <;> rfl
  have hs := _root_.GD.N0213.N0510.d023139 (fun _ : Fin 2 => a) t (fun _ => ha) ht
  have hc := (_root_.GD.N0213.N0510.d023138 (fun _ : Fin 2 => a) t (fun _ => ha) ht).ne'
  have htotal : _root_.GD.N0230.N0665.d000406 t = (t 0 + t 1) / (t 0 * t 1) := by
    unfold _root_.GD.N0230.N0665.d000406
    rw [Fin.sum_univ_two]
    field_simp [(ht 0).ne', (ht 1).ne']
    exact add_comm _ _
  simp only [_root_.GD.N0101.N0396.d028143, hr, hs, _root_.GD.N0230.N0665.d000407, htotal]
  constructor <;> rw [← mul_add, mul_div_mul_left _ _ hc] <;>
    field_simp [(ht 0).ne', (ht 1).ne', (add_pos (ht 0) (ht 1)).ne']



theorem d028525 (a : ℝ) (ha : 0 < a) (t : _root_.GD.N0101.N0395.d028514)
    (ht : ∀ i, 0 < t i) (h : _root_.GD.N0101.N0395.d028514 → ℝ) (hh : Measurable h)
    (hb : ∀ β, h β ∈ Icc (0 : ℝ) 1) (w : _root_.GD.N0101.N0395.d028514) (hw : ∑ i, w i = 1) :
    _root_.GD.N0101.N0395.d028517 a t h (_root_.GD.N0230.N0665.d000407 t) ≤
      _root_.GD.N0101.N0395.d028517 a t h w + _root_.GD.N0101.N0394.d028506 a h t := by
  have h₀ := mul_pos ha (ht 0)
  have h₁ := mul_pos ha (ht 1)
  let H : (ℝ × ℝ) → ℝ := fun z => h (_root_.GD.N0101.N0397.d028118.symm z)
  let ν := _root_.GD.N0101.N0396.d028146 a (a*t 0) (a*t 1) 0
  letI := _root_.GD.N0101.N0396.d028152 ha h₀ h₁ 0
  have hH : MemLp H 2 ν := by
    apply MemLp.of_bound (hh.comp _root_.GD.N0101.N0397.d028118.symm.measurable).aestronglyMeasurable 1
    filter_upwards with z
    change |h (_root_.GD.N0101.N0397.d028118.symm z)| ≤ 1
    rw [abs_of_nonneg (hb _).1]
    exact (hb _).2
  have hHs : MemLp (fun z => H (_root_.GD.N0213.N0526.d028101 (a*t 0) (a*t 1) z)) 2 ν := by
    apply MemLp.of_bound ((hh.comp _root_.GD.N0101.N0397.d028118.symm.measurable).comp
      (_root_.GD.N0213.N0526.d028102 _ _)).aestronglyMeasurable 1
    filter_upwards with z
    change |h (_root_.GD.N0101.N0397.d028118.symm (_root_.GD.N0213.N0526.d028101 (a*t 0) (a*t 1) z))| ≤ 1
    rw [abs_of_nonneg (hb _).1]
    exact (hb _).2
  have hpair := _root_.GD.N0101.N0396.d028154 ha h₀ h₁ H (w 0) hH hHs
  have hw₁ : w 1 = 1 - w 0 := by rw [Fin.sum_univ_two] at hw; linarith
  have hg := _root_.GD.N0101.N0395.d028524 a ha t ht
  have hreg : _root_.GD.N0101.N0395.d028516 a (a*t 0) (a*t 1) h (_root_.GD.N0230.N0665.d000407 t) ≤
      _root_.GD.N0101.N0395.d028516 a (a*t 0) (a*t 1) h w +
        _root_.GD.N0213.N0505.d007548 (_root_.GD.N0101.N0396.d028143 a (a*t 0) (a*t 1) 0)
          (_root_.GD.N0101.N0396.d028143 a (a*t 0) (a*t 1) 1) *
          ∫ z, (H z - H (_root_.GD.N0213.N0526.d028101 (a*t 0) (a*t 1) z)) ^ 2 ∂ν := by
    unfold _root_.GD.N0213.N0505.d007549 at hpair
    unfold _root_.GD.N0101.N0395.d028516 _root_.GD.N0101.N0395.d028515
    rw [hg.1, hg.2, hw₁]
    exact sub_le_iff_le_add.mp hpair |>.trans_eq (add_comm _ _)
  have hE : 0 ≤ _root_.GD.N0213.N0505.d007548 (_root_.GD.N0101.N0396.d028143 a (a*t 0) (a*t 1) 0)
      (_root_.GD.N0101.N0396.d028143 a (a*t 0) (a*t 1) 1) := by
    unfold _root_.GD.N0213.N0505.d007548
    exact (div_pos (mul_pos (_root_.GD.N0101.N0396.d028147 ha h₀ h₁ 0) (_root_.GD.N0101.N0396.d028147 ha h₀ h₁ 1))
      (add_pos (_root_.GD.N0101.N0396.d028147 ha h₀ h₁ 0) (_root_.GD.N0101.N0396.d028147 ha h₀ h₁ 1))).le
  have henergy : _root_.GD.N0101.N0394.d028506 a h t =
      ENNReal.ofReal (_root_.GD.N0213.N0505.d007548 (_root_.GD.N0101.N0396.d028143 a (a*t 0) (a*t 1) 0)
        (_root_.GD.N0101.N0396.d028143 a (a*t 0) (a*t 1) 1) *
        ∫ z, (H z - H (_root_.GD.N0213.N0526.d028101 (a*t 0) (a*t 1) z)) ^ 2 ∂ν) := by
    have hiD : Integrable (fun z => (H z - H (_root_.GD.N0213.N0526.d028101 (a*t 0) (a*t 1) z)) ^ 2) ν := by
      simpa only [Pi.sub_apply] using (hH.sub hHs).integrable_sq
    rw [ENNReal.ofReal_mul hE,
      ofReal_integral_eq_lintegral_ofReal hiD
        (ae_of_all _ fun _ => sq_nonneg _)]
    rfl
  rw [_root_.GD.N0101.N0395.d028522 a ha t ht h hh hb,
    _root_.GD.N0101.N0395.d028522 a ha t ht h hh hb, henergy,
    ← ENNReal.ofReal_add (_root_.GD.N0101.N0395.d028523 ha h₀ h₁ h w)
      (mul_nonneg hE (integral_nonneg fun _ => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal hreg

end
end GD.N0101.N0395

#print axioms _root_.GD.N0101.N0395.d028518
#print axioms _root_.GD.N0101.N0395.d028522
#print axioms _root_.GD.N0101.N0395.d028524
#print axioms _root_.GD.N0101.N0395.d028525
