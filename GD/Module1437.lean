import GD.Module1309
import GD.Module1299
import Mathlib.Tactic








set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Set Filter Topology

namespace GD.N0106.N0428.N0765.N1608
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1612


def d022843 (eta : ℝ) : ℝ := eta ^ 2 / (1 + eta) ^ 3


def d022844 (x : ℝ) : ℝ := (_root_.GD.N0106.N0428.N0765.N1535.d021137 (x : ℂ)).re

def d022845 : ℝ := 2375083944510933 / 590295810358705651712

def d022846 : ℝ := 2502505592391819 / 288230376151711744

def d022847 : ℝ := 2375083944510933 / 405828369621610135552

theorem d022848 {eta : ℝ} (heta : 1 ≤ eta) (heta50 : eta ≤ 50) :
    Real.log eta ∈ Icc (0 : ℝ) 4 := by
  have h50 : (50 : ℝ) < Real.exp 4 := by
    refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 8)
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  exact ⟨Real.log_nonneg heta,
    ((Real.log_lt_iff_lt_exp (by linarith : 0 < eta)).2 (heta50.trans_lt h50)).le⟩

theorem d022849 {eta : ℝ} (heta : 0 < eta) : 0 < _root_.GD.N0106.N0428.N0765.N1608.d022843 eta := by
  unfold _root_.GD.N0106.N0428.N0765.N1608.d022843
  positivity

theorem d022850 {eta : ℝ} (heta : 0 < eta) :
    eta * _root_.GD.N0106.N0428.N0765.N1608.d022843 eta⁻¹ = _root_.GD.N0106.N0428.N0765.N1608.d022843 eta := by
  unfold _root_.GD.N0106.N0428.N0765.N1608.d022843
  field_simp [heta.ne', show 1 + eta ≠ 0 by positivity]
  <;> ring

theorem d022851 {eta : ℝ} (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1608.d022843 eta ≤ (1 + eta) / 16 := by
  rw [_root_.GD.N0106.N0428.N0765.N1608.d022843, div_le_iff₀ (by positivity : 0 < (1 + eta) ^ 3)]
  have h : 4 * eta ≤ (1 + eta) ^ 2 := by nlinarith [sq_nonneg (eta - 1)]
  have hs := mul_le_mul h h (by positivity : 0 ≤ 4 * eta) (sq_nonneg (1 + eta))
  nlinarith [hs]

theorem d022852 {eta : ℝ} (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1608.d022843 eta ≤ 1 / eta := by
  rw [_root_.GD.N0106.N0428.N0765.N1608.d022843, div_le_div_iff₀ (by positivity : 0 < (1 + eta) ^ 3) heta]
  nlinarith [sq_nonneg eta]

theorem d022853 (location eta : ℝ) (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1612.d021391 location eta = _root_.GD.N0106.N0428.N0765.N1612.d021391 0 eta := by
  rw [_root_.GD.N0106.N0428.N0765.N1612.d021393 location eta heta, _root_.GD.N0106.N0428.N0765.N1612.d021393 0 eta heta]

theorem d022854 (location : ℝ) {eta : ℝ} (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1612.d021391 location eta = eta * _root_.GD.N0106.N0428.N0765.N1612.d021391 location eta⁻¹ := by
  rw [_root_.GD.N0106.N0428.N0765.N1612.d021393 location eta heta,
    _root_.GD.N0106.N0428.N0765.N1612.d021393 location eta⁻¹ (inv_pos.mpr heta)]
  exact _root_.GD.N0106.N0428.N0765.N1543.d005401 heta

theorem d022855 (location x : ℝ) :
    _root_.GD.N0106.N0428.N0765.N1608.d022844 x = 11 * _root_.GD.N0106.N0428.N0765.N1612.d021391 location (Real.exp x) / (1 + Real.exp x) := by
  rw [_root_.GD.N0106.N0428.N0765.N1608.d022844, _root_.GD.N0106.N0428.N0765.N1535.d021163 location x, Complex.ofReal_re]
  rfl

theorem d022856 (location : ℝ) {eta : ℝ} (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1612.d021392 location eta⁻¹ = eta * _root_.GD.N0106.N0428.N0765.N1612.d021391 location eta := by
  simp only [_root_.GD.N0106.N0428.N0765.N1612.d021392, inv_inv]


theorem d022857 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hca : c ≤ 16 * a / 11) (hcb : c ≤ b)
    (hJ : ∀ x ∈ Icc (0 : ℝ) 4, a ≤ _root_.GD.N0106.N0428.N0765.N1608.d022844 x)
    (hK : ∀ e ∈ Ioc (0 : ℝ) (1 / 50), b ≤ _root_.GD.N0106.N0428.N0765.N1612.d021392 0 e)
    (location : ℝ) {eta : ℝ} (heta : 0 < eta) :
    c * _root_.GD.N0106.N0428.N0765.N1608.d022843 eta ≤ _root_.GD.N0106.N0428.N0765.N1612.d021391 location eta := by
  have upper : ∀ t : ℝ, 1 ≤ t → c * _root_.GD.N0106.N0428.N0765.N1608.d022843 t ≤ _root_.GD.N0106.N0428.N0765.N1612.d021391 0 t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
    by_cases ht50 : t ≤ 50
    · have h := hJ (Real.log t)
        (_root_.GD.N0106.N0428.N0765.N1608.d022848 ht ht50)
      rw [_root_.GD.N0106.N0428.N0765.N1608.d022855 0, Real.exp_log htpos] at h
      have hD : a * (1 + t) / 11 ≤ _root_.GD.N0106.N0428.N0765.N1612.d021391 0 t := by
        have hmul := (le_div_iff₀ (by positivity : 0 < 1 + t)).1 h
        linarith
      calc
        c * _root_.GD.N0106.N0428.N0765.N1608.d022843 t ≤ (16 * a / 11) * _root_.GD.N0106.N0428.N0765.N1608.d022843 t :=
          mul_le_mul_of_nonneg_right hca (_root_.GD.N0106.N0428.N0765.N1608.d022849 htpos).le
        _ ≤ (16 * a / 11) * ((1 + t) / 16) :=
          mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1608.d022851 htpos) (by positivity)
        _ = a * (1 + t) / 11 := by ring
        _ ≤ _root_.GD.N0106.N0428.N0765.N1612.d021391 0 t := hD
    · have hrec : t⁻¹ ∈ Ioc (0 : ℝ) (1 / 50) := by
        refine ⟨inv_pos.mpr htpos, ?_⟩
        rw [inv_eq_one_div, div_le_div_iff₀ htpos (by norm_num : (0 : ℝ) < 50)]
        linarith
      have h := hK t⁻¹ hrec
      rw [_root_.GD.N0106.N0428.N0765.N1608.d022856 0 htpos] at h
      have hD : b / t ≤ _root_.GD.N0106.N0428.N0765.N1612.d021391 0 t := by
        apply (div_le_iff₀ htpos).2
        simpa only [mul_comm] using h
      calc
        c * _root_.GD.N0106.N0428.N0765.N1608.d022843 t ≤ b * _root_.GD.N0106.N0428.N0765.N1608.d022843 t :=
          mul_le_mul_of_nonneg_right hcb (_root_.GD.N0106.N0428.N0765.N1608.d022849 htpos).le
        _ ≤ b * (1 / t) := mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0765.N1608.d022852 htpos) hb
        _ = b / t := by ring
        _ ≤ _root_.GD.N0106.N0428.N0765.N1612.d021391 0 t := hD
  rw [_root_.GD.N0106.N0428.N0765.N1608.d022853 location eta heta]
  by_cases heta1 : 1 ≤ eta
  · exact upper eta heta1
  · have hrec : 1 ≤ eta⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ heta]
      linarith
    have h := mul_le_mul_of_nonneg_left (upper eta⁻¹ hrec) heta.le
    rw [_root_.GD.N0106.N0428.N0765.N1608.d022854 0 heta]
    calc
      c * _root_.GD.N0106.N0428.N0765.N1608.d022843 eta = eta * (c * _root_.GD.N0106.N0428.N0765.N1608.d022843 eta⁻¹) := by rw [← _root_.GD.N0106.N0428.N0765.N1608.d022850 heta]; ring
      _ ≤ eta * _root_.GD.N0106.N0428.N0765.N1612.d021391 0 eta⁻¹ := h

theorem d022858 :
    0 < _root_.GD.N0106.N0428.N0765.N1608.d022845 ∧ 0 < _root_.GD.N0106.N0428.N0765.N1608.d022846 ∧ 0 < _root_.GD.N0106.N0428.N0765.N1608.d022847 ∧
      _root_.GD.N0106.N0428.N0765.N1608.d022847 = 16 * _root_.GD.N0106.N0428.N0765.N1608.d022845 / 11 ∧ _root_.GD.N0106.N0428.N0765.N1608.d022847 < _root_.GD.N0106.N0428.N0765.N1608.d022846 := by
  norm_num [_root_.GD.N0106.N0428.N0765.N1608.d022845, _root_.GD.N0106.N0428.N0765.N1608.d022846, _root_.GD.N0106.N0428.N0765.N1608.d022847]


theorem d022859
    (hJ : ∀ x ∈ Icc (0 : ℝ) 4, _root_.GD.N0106.N0428.N0765.N1608.d022845 ≤ _root_.GD.N0106.N0428.N0765.N1608.d022844 x)
    (hK : ∀ e ∈ Ioc (0 : ℝ) (1 / 50), _root_.GD.N0106.N0428.N0765.N1608.d022846 ≤ _root_.GD.N0106.N0428.N0765.N1612.d021392 0 e)
    (location : ℝ) {eta : ℝ} (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1608.d022847 * _root_.GD.N0106.N0428.N0765.N1608.d022843 eta ≤ _root_.GD.N0106.N0428.N0765.N1612.d021391 location eta := by
  obtain ⟨ha, hb, _, hca, hcb⟩ := _root_.GD.N0106.N0428.N0765.N1608.d022858
  exact _root_.GD.N0106.N0428.N0765.N1608.d022857 _root_.GD.N0106.N0428.N0765.N1608.d022845 _root_.GD.N0106.N0428.N0765.N1608.d022846 _root_.GD.N0106.N0428.N0765.N1608.d022847 ha.le hb.le
    hca.le hcb.le hJ hK location heta

theorem d022860
    (hJ : ∀ x ∈ Icc (0 : ℝ) 4, _root_.GD.N0106.N0428.N0765.N1608.d022845 ≤ _root_.GD.N0106.N0428.N0765.N1608.d022844 x)
    (hK : ∀ e ∈ Ioc (0 : ℝ) (1 / 50), _root_.GD.N0106.N0428.N0765.N1608.d022846 ≤ _root_.GD.N0106.N0428.N0765.N1612.d021392 0 e)
    (location : ℝ) {eta : ℝ} (heta : 0 < eta) :
    _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta _root_.GD.N0106.N0428.N0765.N1611.d012593 <
      _root_.GD.N0106.N0428.N0765.N1610.d020776 location eta
        (_root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 11)) := by
  have h := _root_.GD.N0106.N0428.N0765.N1608.d022859 hJ hK location heta
  have hp := mul_pos _root_.GD.N0106.N0428.N0765.N1608.d022858.2.2.1 (_root_.GD.N0106.N0428.N0765.N1608.d022849 heta)
  exact sub_pos.mp (hp.trans_le h)



theorem d022861 (c : ℝ) (hc : c < 5 / 264) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ location eta : ℝ, 0 < eta →
      (eta < δ → c * eta ^ 2 ≤ _root_.GD.N0106.N0428.N0765.N1612.d021391 location eta) ∧
      (eta⁻¹ < δ → c / eta ≤ _root_.GD.N0106.N0428.N0765.N1612.d021391 location eta) := by
  have hnear : ∀ᶠ e in 𝓝[>] (0 : ℝ), c < _root_.GD.N0106.N0428.N0765.N1612.d021392 0 e :=
    (_root_.GD.N0106.N0428.N0765.N1612.d021395 0).eventually (Ioi_mem_nhds hc)
  obtain ⟨d, hd, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hnear
  refine ⟨min d 1, lt_min hd zero_lt_one, min_le_right _ _, ?_⟩
  intro location eta heta
  have near : ∀ e : ℝ, 0 < e → e < min d 1 → c ≤ _root_.GD.N0106.N0428.N0765.N1612.d021392 0 e := by
    intro e he heδ
    exact (hbound ⟨he, heδ.trans_le (min_le_left _ _)⟩).le
  constructor
  · intro heδ
    have h := near eta heta heδ
    have hid : _root_.GD.N0106.N0428.N0765.N1612.d021391 location eta = eta ^ 2 * _root_.GD.N0106.N0428.N0765.N1612.d021392 0 eta := by
      rw [_root_.GD.N0106.N0428.N0765.N1608.d022853 location eta heta, _root_.GD.N0106.N0428.N0765.N1608.d022854 0 heta, _root_.GD.N0106.N0428.N0765.N1612.d021392]
      field_simp [heta.ne']
      <;> ring
    rw [hid]
    nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg eta)]
  · intro heδ
    have h := near eta⁻¹ (inv_pos.mpr heta) heδ
    rw [_root_.GD.N0106.N0428.N0765.N1608.d022856 0 heta] at h
    rw [_root_.GD.N0106.N0428.N0765.N1608.d022853 location eta heta]
    exact (div_le_iff₀ heta).2 (by simpa only [mul_comm] using h)



theorem d022862 :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ location eta : ℝ, 0 < eta →
      (eta < δ ∨ eta⁻¹ < δ) → 0 < _root_.GD.N0106.N0428.N0765.N1612.d021391 location eta := by
  obtain ⟨δ, hδ, hδ1, h⟩ := _root_.GD.N0106.N0428.N0765.N1608.d022861 (5 / 528) (by norm_num)
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro location eta heta hsmall
  rcases hsmall with hsmall | hsmall
  · exact (by positivity : 0 < (5 / 528 : ℝ) * eta ^ 2).trans_le
      ((h location eta heta).1 hsmall)
  · exact (by positivity : 0 < (5 / 528 : ℝ) / eta).trans_le
      ((h location eta heta).2 hsmall)

end
end GD.N0106.N0428.N0765.N1608
