import GD.Module1571
import GD.Module1573



















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set MeasureTheory

namespace GD.N0106.N0428.N0770.N1729
noncomputable section

open _root_.GD.N0137 _root_.GD.N0107 _root_.GD.N0141
open _root_.GD.N0232.N0720.N1207
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0106.N0428.N0770.N1725
open _root_.GD.N0106.N0428.N0770.N1724
open _root_.GD.N0106.N0428.N0770.N1722
open _root_.GD.N0106.N0428.N0770.N1726


def d027406 : Set (ℝ × ℝ) :=
  Icc (1 / 500 - _root_.GD.N0106.N0428.N0770.N1725.d024118 / 2) (1 / 500 + _root_.GD.N0106.N0428.N0770.N1725.d024118 / 2) ×ˢ Icc (1 / 1000 - _root_.GD.N0106.N0428.N0770.N1725.d024118 / 2) (1 / 1000 + _root_.GD.N0106.N0428.N0770.N1725.d024118 / 2)

theorem d027407 : MeasurableSet _root_.GD.N0106.N0428.N0770.N1729.d027406 :=
  measurableSet_Icc.prod measurableSet_Icc

theorem d027408 : _root_.GD.N0106.N0428.N0770.N1729.d027406 ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ) := by
  intro p hp
  simp only [_root_.GD.N0106.N0428.N0770.N1729.d027406, Set.mem_prod, Set.mem_Icc] at hp
  have hr : _root_.GD.N0106.N0428.N0770.N1725.d024118 ≤ 1 / 1000000 := by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]
  exact Set.mem_prod.mpr
    ⟨Set.mem_Ioo.mpr ⟨by linarith [hp.1.1, hr, _root_.GD.N0106.N0428.N0770.N1725.d024121], by linarith [hp.1.2, hr]⟩,
      Set.mem_Ioi.mpr (by linarith [hp.2.1, hr])⟩

theorem d027409 : volume _root_.GD.N0106.N0428.N0770.N1729.d027406 ≠ ⊤ := by
  unfold _root_.GD.N0106.N0428.N0770.N1729.d027406
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top


theorem d027410 : volume.real _root_.GD.N0106.N0428.N0770.N1729.d027406 = _root_.GD.N0106.N0428.N0770.N1725.d024118 ^ 2 := by
  unfold _root_.GD.N0106.N0428.N0770.N1729.d027406
  have h1 : (0 : ℝ) ≤ 1 / 500 + _root_.GD.N0106.N0428.N0770.N1725.d024118 / 2 - (1 / 500 - _root_.GD.N0106.N0428.N0770.N1725.d024118 / 2) := by linarith [_root_.GD.N0106.N0428.N0770.N1725.d024121]
  have h2 : (0 : ℝ) ≤ 1 / 1000 + _root_.GD.N0106.N0428.N0770.N1725.d024118 / 2 - (1 / 1000 - _root_.GD.N0106.N0428.N0770.N1725.d024118 / 2) := by linarith [_root_.GD.N0106.N0428.N0770.N1725.d024121]
  rw [measureReal_def, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
    Real.volume_Icc, ENNReal.toReal_mul, ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2]
  ring



theorem d027411 {c w x : ℝ} (hw : 0 < w) (hx : |x - c| ≤ w / 2) : 1 / 2 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x := by
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024124
  apply le_max_of_le_left
  have h : |x - c| / w ≤ 1 / 2 := by
    rw [div_le_iff₀ hw]
    linarith
  linarith

theorem d027412 {c w x : ℝ} (hw : 0 < w) (h : c + w ≤ x ∨ x ≤ c - w) :
    _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x = 0 := by
  by_contra hne
  have hx := (_root_.GD.N0106.N0428.N0770.N1726.d024372 hw).mp hne
  rcases h with h | h
  · linarith [hx.2]
  · linarith [hx.1]


theorem d027413 {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0770.N1729.d027406) : 3 / 4 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024131 p := by
  simp only [_root_.GD.N0106.N0428.N0770.N1729.d027406, Set.mem_prod, Set.mem_Icc] at hp
  have h1 : 1 / 2 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024124 (1 / 500) _root_.GD.N0106.N0428.N0770.N1725.d024118 p.1 :=
    _root_.GD.N0106.N0428.N0770.N1729.d027411 _root_.GD.N0106.N0428.N0770.N1725.d024121 (abs_le.mpr ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩)
  have h2 : 1 / 2 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024124 (1 / 1000) _root_.GD.N0106.N0428.N0770.N1725.d024118 p.2 :=
    _root_.GD.N0106.N0428.N0770.N1729.d027411 _root_.GD.N0106.N0428.N0770.N1725.d024121 (abs_le.mpr ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩)
  have hr : _root_.GD.N0106.N0428.N0770.N1725.d024118 ≤ 1 / 1000000 := by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]
  have h3 : _root_.GD.N0106.N0428.N0770.N1725.d024124 (1 - 1 / 500) _root_.GD.N0106.N0428.N0770.N1725.d024118 p.1 = 0 :=
    _root_.GD.N0106.N0428.N0770.N1729.d027412 _root_.GD.N0106.N0428.N0770.N1725.d024121 (Or.inr (by linarith [hp.1.2, hr]))
  have h4 : _root_.GD.N0106.N0428.N0770.N1725.d024124 20 _root_.GD.N0106.N0428.N0770.N1725.d024118 p.2 = 0 :=
    _root_.GD.N0106.N0428.N0770.N1729.d027412 _root_.GD.N0106.N0428.N0770.N1725.d024121 (Or.inr (by linarith [hp.2.2, hr]))
  have hprod : (1 / 2 : ℝ) * (1 / 2) ≤ _root_.GD.N0106.N0428.N0770.N1725.d024124 (1 / 500) _root_.GD.N0106.N0428.N0770.N1725.d024118 p.1 * _root_.GD.N0106.N0428.N0770.N1725.d024124 (1 / 1000) _root_.GD.N0106.N0428.N0770.N1725.d024118 p.2 :=
    mul_le_mul h1 h2 (by norm_num) (_root_.GD.N0106.N0428.N0770.N1725.d024139 _ _ _)
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024131 _root_.GD.N0106.N0428.N0770.N1725.d024126
  rw [h3, h4]
  simp only [sub_zero, mul_zero]
  linarith [hprod]

theorem d027414 {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0770.N1729.d027406) : 9 / 16 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024131 p ^ 2 := by
  have h := _root_.GD.N0106.N0428.N0770.N1729.d027413 hp
  calc (9 / 16 : ℝ) = (3 / 4) ^ 2 := by norm_num
    _ ≤ _root_.GD.N0106.N0428.N0770.N1725.d024131 p ^ 2 := pow_le_pow_left₀ (by norm_num) h 2

theorem d027415 (e F : ℝ) : _root_.GD.N0106.N0428.N0770.N1725.d024169 (1 / 2) e F = 1 / 2 + F / 4 := by
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024169
  ring


theorem d027416 {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0770.N1729.d027406) : 1 / 2 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024170 (1 / 2) p := by
  simp only [_root_.GD.N0106.N0428.N0770.N1729.d027406, Set.mem_prod, Set.mem_Icc] at hp
  have hr : _root_.GD.N0106.N0428.N0770.N1725.d024118 ≤ 1 / 1000000 := by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]
  have he0 : 0 < p.1 := by linarith [hp.1.1, hr, _root_.GD.N0106.N0428.N0770.N1725.d024121]
  have he1 : p.1 < 1 := by linarith [hp.1.2, hr]
  have hF : 0 < p.2 := by linarith [hp.2.1, hr]
  have hden : 0 < p.1 * (1 - p.1) := mul_pos he0 (sub_pos.mpr he1)
  have hsqrt : 1 / 2 ≤ Real.sqrt (p.2 / (p.1 * (1 - p.1))) := by
    rw [Real.le_sqrt (by norm_num) (div_nonneg hF.le hden.le), le_div_iff₀ hden]
    have : p.1 * (1 - p.1) ≤ p.1 := mul_le_of_le_one_right he0.le (by linarith)
    linarith [this, hp.1.2, hp.2.1, hr, _root_.GD.N0106.N0428.N0770.N1725.d024121]
  have hN : 1 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024169 (1 / 2) p.1 p.2 ^ (-(5 / 2 : ℝ)) := by
    rw [_root_.GD.N0106.N0428.N0770.N1729.d027415]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) (by linarith [hp.2.2, hr])
      (by norm_num)
  show 1 / 2 ≤ Real.sqrt (p.2 / (p.1 * (1 - p.1))) * _root_.GD.N0106.N0428.N0770.N1725.d024169 (1 / 2) p.1 p.2 ^ (-(5 / 2 : ℝ))
  calc (1 / 2 : ℝ) = 1 / 2 * 1 := by ring
    _ ≤ _ := mul_le_mul hsqrt hN zero_le_one (Real.sqrt_nonneg _)

theorem d027417 {p : ℝ × ℝ} (hp : p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) :
    0 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024170 (1 / 2) p := by
  show 0 ≤ Real.sqrt (p.2 / (p.1 * (1 - p.1))) * _root_.GD.N0106.N0428.N0770.N1725.d024169 (1 / 2) p.1 p.2 ^ (-(5 / 2 : ℝ))
  exact mul_nonneg (Real.sqrt_nonneg _)
    (Real.rpow_pos_of_pos (_root_.GD.N0106.N0428.N0770.N1725.d024172 ⟨by norm_num, by norm_num⟩ hp.1 hp.2) _).le

theorem d027418 {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0770.N1729.d027406) : 9 / 32 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024170 (1 / 2) p * _root_.GD.N0106.N0428.N0770.N1725.d024131 p ^ 2 := by
  have h := mul_le_mul (_root_.GD.N0106.N0428.N0770.N1729.d027416 hp) (_root_.GD.N0106.N0428.N0770.N1729.d027414 hp) (by norm_num)
    (_root_.GD.N0106.N0428.N0770.N1729.d027417 (_root_.GD.N0106.N0428.N0770.N1729.d027408 hp))
  linarith [h]



theorem d027419 : _root_.GD.N0106.N0428.N0770.N1724.d024296 1 1 = 1 / 2 := by
  rw [_root_.GD.N0106.N0428.N0770.N1724.d024305]
  norm_num

theorem d027420 : _root_.GD.N0106.N0428.N0770.N1722.d024329 1 1 = 3 / (32 * Real.pi) := by
  unfold _root_.GD.N0106.N0428.N0770.N1722.d024329
  rw [_root_.GD.N0106.N0428.N0770.N1729.d027419]
  ring

theorem d027421 : Measurable (fun x : ℝ × ℝ => _root_.GD.N0106.N0428.N0770.N1725.d024131 x ^ 2) :=
  _root_.GD.N0106.N0428.N0770.N1725.d024138.pow_const 2



theorem d027422 :
    IntegrableOn (fun x => _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 1 1) x * _root_.GD.N0106.N0428.N0770.N1725.d024131 x ^ 2) _root_.GD.N0232.N0720.N1436.d013218 volume := by
  have hbound : ∀ p ∈ _root_.GD.N0106.N0428.N0770.N1724.d024301, |_root_.GD.N0106.N0428.N0770.N1725.d024131 p + _root_.GD.N0106.N0428.N0770.N1724.d024296 1 1| ≤ 8 := by
    intro p _
    rw [_root_.GD.N0106.N0428.N0770.N1729.d027419]
    have := _root_.GD.N0106.N0428.N0770.N1725.d024143 p
    have h2 := abs_add_le (_root_.GD.N0106.N0428.N0770.N1725.d024131 p) (1 / 2)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h2
    linarith
  have hmem := _root_.GD.N0106.N0428.N0770.N1724.d024320 0 1 1 one_pos one_pos (fun p => _root_.GD.N0106.N0428.N0770.N1725.d024131 p + _root_.GD.N0106.N0428.N0770.N1724.d024296 1 1)
    (_root_.GD.N0106.N0428.N0770.N1725.d024138.add measurable_const) (B := 8) (by norm_num) hbound
  have hmem' : MemLp (fun w => _root_.GD.N0107.d009090 2 2 w * _root_.GD.N0106.N0428.N0770.N1725.d024131 (_root_.GD.N0106.N0428.N0770.N1724.d024300 w)) 2
      (_root_.GD.N0107.d009030 2 2 0 1 1) :=
    hmem.ae_eq (Filter.Eventually.of_forall fun w => by
      first
        | simp only [add_sub_cancel_right]
        | (simp only []; ring)
        | ring)
  have hsq := hmem'.integrable_sq
  have hint : Integrable (fun w => _root_.GD.N0107.d009090 2 2 w ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024131 (_root_.GD.N0106.N0428.N0770.N1724.d024300 w) ^ 2)
      (_root_.GD.N0107.d009030 2 2 0 1 1) := by
    simpa only [mul_pow] using hsq
  exact (_root_.GD.N0106.N0428.N0770.N1722.d024344 0 1 1 one_pos one_pos (fun x => _root_.GD.N0106.N0428.N0770.N1725.d024131 x ^ 2)
    _root_.GD.N0106.N0428.N0770.N1729.d027421).mp hint


theorem d027423 :
    (∫ w, _root_.GD.N0107.d009090 2 2 w ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024131 (_root_.GD.N0106.N0428.N0770.N1724.d024300 w) ^ 2
      ∂_root_.GD.N0107.d009030 2 2 0 1 1) =
      _root_.GD.N0106.N0428.N0770.N1722.d024329 1 1 * ∫ x in _root_.GD.N0232.N0720.N1436.d013218, _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 1 1) x * _root_.GD.N0106.N0428.N0770.N1725.d024131 x ^ 2 :=
  _root_.GD.N0106.N0428.N0770.N1722.d024342 0 1 1 one_pos one_pos (fun x => _root_.GD.N0106.N0428.N0770.N1725.d024131 x ^ 2) _root_.GD.N0106.N0428.N0770.N1729.d027421


theorem d027424 :
    9 / 32 * _root_.GD.N0106.N0428.N0770.N1725.d024118 ^ 2 ≤ ∫ x in _root_.GD.N0232.N0720.N1436.d013218, _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 1 1) x * _root_.GD.N0106.N0428.N0770.N1725.d024131 x ^ 2 := by
  rw [_root_.GD.N0106.N0428.N0770.N1729.d027419]
  have hint : IntegrableOn (fun x => _root_.GD.N0106.N0428.N0770.N1725.d024170 (1 / 2) x * _root_.GD.N0106.N0428.N0770.N1725.d024131 x ^ 2) _root_.GD.N0232.N0720.N1436.d013218 volume := by
    have h := _root_.GD.N0106.N0428.N0770.N1729.d027422
    rwa [_root_.GD.N0106.N0428.N0770.N1729.d027419] at h
  have hcore : IntegrableOn (fun x => _root_.GD.N0106.N0428.N0770.N1725.d024170 (1 / 2) x * _root_.GD.N0106.N0428.N0770.N1725.d024131 x ^ 2) _root_.GD.N0106.N0428.N0770.N1729.d027406 volume :=
    hint.mono_set _root_.GD.N0106.N0428.N0770.N1729.d027408
  have h1 : 9 / 32 * volume.real _root_.GD.N0106.N0428.N0770.N1729.d027406 ≤ ∫ x in _root_.GD.N0106.N0428.N0770.N1729.d027406, _root_.GD.N0106.N0428.N0770.N1725.d024170 (1 / 2) x * _root_.GD.N0106.N0428.N0770.N1725.d024131 x ^ 2 :=
    setIntegral_ge_of_const_le_real _root_.GD.N0106.N0428.N0770.N1729.d027407 _root_.GD.N0106.N0428.N0770.N1729.d027409
      (fun x hx => _root_.GD.N0106.N0428.N0770.N1729.d027418 hx) hcore
  have h2 : ∫ x in _root_.GD.N0106.N0428.N0770.N1729.d027406, _root_.GD.N0106.N0428.N0770.N1725.d024170 (1 / 2) x * _root_.GD.N0106.N0428.N0770.N1725.d024131 x ^ 2 ≤
      ∫ x in _root_.GD.N0232.N0720.N1436.d013218, _root_.GD.N0106.N0428.N0770.N1725.d024170 (1 / 2) x * _root_.GD.N0106.N0428.N0770.N1725.d024131 x ^ 2 := by
    apply setIntegral_mono_set hint
    · filter_upwards [ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219] with x hx
      exact mul_nonneg (_root_.GD.N0106.N0428.N0770.N1729.d027417 hx) (sq_nonneg _)
    · exact HasSubset.Subset.eventuallyLE _root_.GD.N0106.N0428.N0770.N1729.d027408
  rw [_root_.GD.N0106.N0428.N0770.N1729.d027410] at h1
  linarith [h1, h2]


theorem d027425 :
    27 * _root_.GD.N0106.N0428.N0770.N1725.d024118 ^ 2 / 32768 <
      ∫ w, _root_.GD.N0107.d009090 2 2 w ^ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024131 (_root_.GD.N0106.N0428.N0770.N1724.d024300 w) ^ 2
        ∂_root_.GD.N0107.d009030 2 2 0 1 1 := by
  rw [_root_.GD.N0106.N0428.N0770.N1729.d027423, _root_.GD.N0106.N0428.N0770.N1729.d027420]
  have hI := _root_.GD.N0106.N0428.N0770.N1729.d027424
  have hpi := Real.pi_le_four
  have hpipos := Real.pi_pos
  have hK : 0 ≤ 3 / (32 * Real.pi) := by positivity
  have hrho := pow_pos _root_.GD.N0106.N0428.N0770.N1725.d024121 2
  calc 27 * _root_.GD.N0106.N0428.N0770.N1725.d024118 ^ 2 / 32768 < 27 * _root_.GD.N0106.N0428.N0770.N1725.d024118 ^ 2 / 4096 := by
        linarith [hrho]
    _ ≤ 27 * _root_.GD.N0106.N0428.N0770.N1725.d024118 ^ 2 / (1024 * Real.pi) :=
        div_le_div_of_nonneg_left (by linarith [hrho]) (by positivity) (by linarith [hpi])
    _ = 3 / (32 * Real.pi) * (9 / 32 * _root_.GD.N0106.N0428.N0770.N1725.d024118 ^ 2) := by
        first
          | ring
          | (field_simp; ring)
    _ ≤ 3 / (32 * Real.pi) * ∫ x in _root_.GD.N0232.N0720.N1436.d013218, _root_.GD.N0106.N0428.N0770.N1725.d024170 (_root_.GD.N0106.N0428.N0770.N1724.d024296 1 1) x * _root_.GD.N0106.N0428.N0770.N1725.d024131 x ^ 2 :=
        mul_le_mul_of_nonneg_left hI hK

end
end GD.N0106.N0428.N0770.N1729

#print axioms _root_.GD.N0106.N0428.N0770.N1729.d027413
#print axioms _root_.GD.N0106.N0428.N0770.N1729.d027416
#print axioms _root_.GD.N0106.N0428.N0770.N1729.d027422
#print axioms _root_.GD.N0106.N0428.N0770.N1729.d027425
