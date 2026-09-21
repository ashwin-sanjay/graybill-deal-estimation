import GD.Module1623
import GD.Module1573




































set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set MeasureTheory

namespace GD.N0106.N0428.N0770.N1741
noncomputable section

open _root_.GD.N0106.N0428.N0770.N1725
open _root_.GD.N0106.N0428.N0770.N1727
open _root_.GD.N0106.N0428.N0770.N1737
open _root_.GD.N0106.N0428.N0770.N1726




instance d027696 :
    IsFiniteMeasureOnCompacts (volume : Measure (ℝ × ℝ)) :=
  Measure.prod.instIsFiniteMeasureOnCompacts _ _

theorem d027697 : _root_.GD.N0106.N0428.N0770.N1725.d024118 ≤ 1 / 1000000 := by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]



theorem d027698 {q e F : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (he : e ∈ Ioo (0 : ℝ) 1) (hF : 0 < F) :
    0 < _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) := by
  show 0 < Real.sqrt (F / (e * (1 - e))) * _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ (-(5 / 2 : ℝ))
  exact mul_pos (Real.sqrt_pos.mpr (div_pos hF (mul_pos he.1 (sub_pos.mpr he.2))))
    (Real.rpow_pos_of_pos (_root_.GD.N0106.N0428.N0770.N1725.d024172 hq he hF) _)

theorem d027699 {q e F : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (he : e ∈ Ioo (0 : ℝ) 1)
    (hF : 0 < F) :
    0 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) :=
  (_root_.GD.N0106.N0428.N0770.N1741.d027698 hq he hF).le



theorem d027700 (q e F : ℝ) : _root_.GD.N0106.N0428.N0770.N1725.d024170 (1 - q) (1 - e, F) = _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) := by
  show Real.sqrt (F / ((1 - e) * (1 - (1 - e)))) * _root_.GD.N0106.N0428.N0770.N1725.d024169 (1 - q) (1 - e) F ^ (-(5 / 2 : ℝ)) =
    Real.sqrt (F / (e * (1 - e))) * _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ (-(5 / 2 : ℝ))
  rw [show (1 - e) * (1 - (1 - e)) = e * (1 - e) by ring,
    show _root_.GD.N0106.N0428.N0770.N1725.d024169 (1 - q) (1 - e) F = _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F by unfold _root_.GD.N0106.N0428.N0770.N1725.d024169; ring]

theorem d027701 (q e F : ℝ) : _root_.GD.N0106.N0428.N0770.N1725.d024170 (1 - q) (e, F) = _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 - e, F) := by
  simpa only [sub_sub_cancel] using _root_.GD.N0106.N0428.N0770.N1741.d027700 q (1 - e) F

theorem d027702 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (_root_.GD.N0106.N0428.N0770.N1725.d024170 q) (Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) := by
  have hN : Continuous (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0770.N1725.d024169 q p.1 p.2) := by
    unfold _root_.GD.N0106.N0428.N0770.N1725.d024169
    fun_prop
  have hsqrt : ContinuousOn (fun p : ℝ × ℝ => Real.sqrt (p.2 / (p.1 * (1 - p.1))))
      (Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) := by
    apply ContinuousOn.sqrt
    apply ContinuousOn.div continuous_snd.continuousOn
      (continuous_fst.mul (continuous_const.sub continuous_fst)).continuousOn
    intro p hp
    exact ne_of_gt (mul_pos hp.1.1 (sub_pos.mpr hp.1.2))
  have hpow : ContinuousOn (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0770.N1725.d024169 q p.1 p.2 ^ (-(5 / 2 : ℝ)))
      (Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) := by
    apply ContinuousOn.rpow_const hN.continuousOn
    intro p hp
    exact Or.inl (ne_of_gt (_root_.GD.N0106.N0428.N0770.N1725.d024172 hq hp.1 hp.2))
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024170
  exact hsqrt.mul hpow



theorem d027703 (q ea Fa eb Fb : ℝ) :
    _root_.GD.N0106.N0428.N0770.N1727.d024439 (1 - q) ea Fa eb Fb = _root_.GD.N0106.N0428.N0770.N1727.d024439 q ea Fa eb Fb := by
  unfold _root_.GD.N0106.N0428.N0770.N1727.d024439 _root_.GD.N0106.N0428.N0770.N1727.d024437 _root_.GD.N0106.N0428.N0770.N1727.d024438
  simp only [_root_.GD.N0106.N0428.N0770.N1741.d027701, sub_sub_cancel]
  ring



theorem d027704 {q ea Fa eb Fb : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hea : ea ∈ Icc (1 / 500 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (1 / 500 + _root_.GD.N0106.N0428.N0770.N1725.d024118))
    (hFa : Fa ∈ Icc (1 / 1000 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (1 / 1000 + _root_.GD.N0106.N0428.N0770.N1725.d024118))
    (heb : eb ∈ Icc (1 / 120 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (1 / 120 + _root_.GD.N0106.N0428.N0770.N1725.d024118))
    (hFb : Fb ∈ Icc (20 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (20 + _root_.GD.N0106.N0428.N0770.N1725.d024118)) :
    0 < _root_.GD.N0106.N0428.N0770.N1727.d024439 q ea Fa eb Fb := by
  rcases le_total q (1 / 2) with h | h
  · exact _root_.GD.N0106.N0428.N0770.N1737.d027693 ⟨hq.1, h⟩ hea hFa heb hFb
  · have h' : 1 - q ∈ Icc (0 : ℝ) (1 / 2) := ⟨by linarith [hq.2], by linarith⟩
    have hpos := _root_.GD.N0106.N0428.N0770.N1737.d027693 h' hea hFa heb hFb
    rwa [_root_.GD.N0106.N0428.N0770.N1741.d027703] at hpos




def d027705 (c f : ℝ) : Set (ℝ × ℝ) :=
  Icc (c - _root_.GD.N0106.N0428.N0770.N1725.d024118) (c + _root_.GD.N0106.N0428.N0770.N1725.d024118) ×ˢ Icc (f - _root_.GD.N0106.N0428.N0770.N1725.d024118) (f + _root_.GD.N0106.N0428.N0770.N1725.d024118)

theorem d027706 (c f w : ℝ) : Continuous (_root_.GD.N0106.N0428.N0770.N1725.d024125 c f w) := by
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024125
  exact (_root_.GD.N0106.N0428.N0770.N1725.d024133 c w).fst'.mul (_root_.GD.N0106.N0428.N0770.N1725.d024133 f w).snd'

theorem d027707 (c f w : ℝ) (p : ℝ × ℝ) : 0 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p :=
  mul_nonneg (_root_.GD.N0106.N0428.N0770.N1725.d024139 _ _ _) (_root_.GD.N0106.N0428.N0770.N1725.d024139 _ _ _)

theorem d027708 (c f w : ℝ) (hw : 0 < w) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w p ≤ 1 := by
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024125
  calc _root_.GD.N0106.N0428.N0770.N1725.d024124 c w p.1 * _root_.GD.N0106.N0428.N0770.N1725.d024124 f w p.2 ≤ 1 * 1 :=
      mul_le_mul (_root_.GD.N0106.N0428.N0770.N1725.d024140 c w p.1 hw) (_root_.GD.N0106.N0428.N0770.N1725.d024140 f w p.2 hw) (_root_.GD.N0106.N0428.N0770.N1725.d024139 _ _ _) zero_le_one
    _ = 1 := one_mul 1

theorem d027709 (c f : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024118 p ≠ 0 ↔
      p.1 ∈ Ioo (c - _root_.GD.N0106.N0428.N0770.N1725.d024118) (c + _root_.GD.N0106.N0428.N0770.N1725.d024118) ∧ p.2 ∈ Ioo (f - _root_.GD.N0106.N0428.N0770.N1725.d024118) (f + _root_.GD.N0106.N0428.N0770.N1725.d024118) := by
  simp only [_root_.GD.N0106.N0428.N0770.N1725.d024125, mul_ne_zero_iff, _root_.GD.N0106.N0428.N0770.N1726.d024372 _root_.GD.N0106.N0428.N0770.N1725.d024121]

theorem d027710 {c f : ℝ} {p : ℝ × ℝ} (hp : p ∉ _root_.GD.N0106.N0428.N0770.N1741.d027705 c f) :
    _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024118 p = 0 := by
  by_contra h
  obtain ⟨h1, h2⟩ := (_root_.GD.N0106.N0428.N0770.N1741.d027709 c f p).mp h
  apply hp
  simp only [_root_.GD.N0106.N0428.N0770.N1741.d027705, Set.mem_prod, Set.mem_Icc]
  exact ⟨⟨h1.1.le, h1.2.le⟩, ⟨h2.1.le, h2.2.le⟩⟩

theorem d027711 (c f : ℝ) (hc : _root_.GD.N0106.N0428.N0770.N1725.d024118 < c) (hc1 : c + _root_.GD.N0106.N0428.N0770.N1725.d024118 < 1)
    (hf : _root_.GD.N0106.N0428.N0770.N1725.d024118 < f) {p : ℝ × ℝ} (hp : p ∉ Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) :
    _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024118 p = 0 := by
  by_contra h
  obtain ⟨h1, h2⟩ := (_root_.GD.N0106.N0428.N0770.N1741.d027709 c f p).mp h
  apply hp
  exact Set.mem_prod.mpr ⟨Set.mem_Ioo.mpr ⟨by linarith [h1.1, hc], by linarith [h1.2, hc1]⟩,
    Set.mem_Ioi.mpr (by linarith [h2.1, hf])⟩

theorem d027712 {c f : ℝ} (hc : _root_.GD.N0106.N0428.N0770.N1725.d024118 < c) (hc1 : c + _root_.GD.N0106.N0428.N0770.N1725.d024118 < 1) (hf : _root_.GD.N0106.N0428.N0770.N1725.d024118 < f) :
    _root_.GD.N0106.N0428.N0770.N1741.d027705 c f ⊆ Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ) := by
  intro p hp
  simp only [_root_.GD.N0106.N0428.N0770.N1741.d027705, Set.mem_prod, Set.mem_Icc] at hp
  exact Set.mem_prod.mpr
    ⟨Set.mem_Ioo.mpr ⟨by linarith [hp.1.1, hc], by linarith [hp.1.2, hc1]⟩,
      Set.mem_Ioi.mpr (by linarith [hp.2.1, hf])⟩


theorem d027713 {c c' w x : ℝ} (hw : 0 < w)
    (hcc : c + 2 * w ≤ c' ∨ c' + 2 * w ≤ c) : _root_.GD.N0106.N0428.N0770.N1725.d024124 c w x * _root_.GD.N0106.N0428.N0770.N1725.d024124 c' w x = 0 := by
  by_contra h
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h
  rw [_root_.GD.N0106.N0428.N0770.N1726.d024372 hw] at h1 h2
  rcases hcc with hcc | hcc
  · linarith [h1.2, h2.1]
  · linarith [h1.1, h2.2]

theorem d027714 (c f c' f' : ℝ) (hcc : c + 2 * _root_.GD.N0106.N0428.N0770.N1725.d024118 ≤ c' ∨ c' + 2 * _root_.GD.N0106.N0428.N0770.N1725.d024118 ≤ c)
    (p : ℝ × ℝ) : _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024118 p * _root_.GD.N0106.N0428.N0770.N1725.d024125 c' f' _root_.GD.N0106.N0428.N0770.N1725.d024118 p = 0 := by
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024125
  calc _root_.GD.N0106.N0428.N0770.N1725.d024124 c _root_.GD.N0106.N0428.N0770.N1725.d024118 p.1 * _root_.GD.N0106.N0428.N0770.N1725.d024124 f _root_.GD.N0106.N0428.N0770.N1725.d024118 p.2 * (_root_.GD.N0106.N0428.N0770.N1725.d024124 c' _root_.GD.N0106.N0428.N0770.N1725.d024118 p.1 * _root_.GD.N0106.N0428.N0770.N1725.d024124 f' _root_.GD.N0106.N0428.N0770.N1725.d024118 p.2)
      = (_root_.GD.N0106.N0428.N0770.N1725.d024124 c _root_.GD.N0106.N0428.N0770.N1725.d024118 p.1 * _root_.GD.N0106.N0428.N0770.N1725.d024124 c' _root_.GD.N0106.N0428.N0770.N1725.d024118 p.1) * (_root_.GD.N0106.N0428.N0770.N1725.d024124 f _root_.GD.N0106.N0428.N0770.N1725.d024118 p.2 * _root_.GD.N0106.N0428.N0770.N1725.d024124 f' _root_.GD.N0106.N0428.N0770.N1725.d024118 p.2) := by ring
    _ = 0 := by rw [_root_.GD.N0106.N0428.N0770.N1741.d027713 _root_.GD.N0106.N0428.N0770.N1725.d024121 hcc, zero_mul]



theorem d027715 (c f : ℝ) {φ : ℝ × ℝ → ℝ}
    (hφ : ContinuousOn φ (_root_.GD.N0106.N0428.N0770.N1741.d027705 c f)) :
    Integrable (fun p => φ p * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024118 p) := by
  have hK : IsCompact (_root_.GD.N0106.N0428.N0770.N1741.d027705 c f) := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun p => φ p * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024118 p) (_root_.GD.N0106.N0428.N0770.N1741.d027705 c f) :=
    hφ.mul (_root_.GD.N0106.N0428.N0770.N1741.d027706 c f _root_.GD.N0106.N0428.N0770.N1725.d024118).continuousOn
  refine (hcont.integrableOn_compact hK).integrable_of_forall_notMem_eq_zero ?_
  intro p hp
  rw [_root_.GD.N0106.N0428.N0770.N1741.d027710 hp, mul_zero]




def d027716 (c f : ℝ) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.addLeft c).prodCongr (MeasurableEquiv.addLeft f)


def d027717 (c f : ℝ) : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  ((MeasurableEquiv.addLeft c).trans (MeasurableEquiv.subLeft 1)).prodCongr
    (MeasurableEquiv.addLeft f)

theorem d027718 (c f : ℝ) (p : ℝ × ℝ) : _root_.GD.N0106.N0428.N0770.N1741.d027716 c f p = (c + p.1, f + p.2) := rfl

theorem d027719 (c f : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1741.d027717 c f p = (1 - (c + p.1), f + p.2) := rfl

theorem d027720 (c f : ℝ) :
    MeasurePreserving (_root_.GD.N0106.N0428.N0770.N1741.d027716 c f) volume volume := by
  have h := (measurePreserving_add_left (volume : Measure ℝ) c).prod
    (measurePreserving_add_left (volume : Measure ℝ) f)
  first
    | exact h
    | exact ⟨(_root_.GD.N0106.N0428.N0770.N1741.d027716 c f).measurable, h.map_eq⟩

theorem d027721 (c f : ℝ) :
    MeasurePreserving (_root_.GD.N0106.N0428.N0770.N1741.d027717 c f) volume volume := by
  have h := (((volume : Measure ℝ).measurePreserving_sub_left (1 : ℝ)).comp
    (measurePreserving_add_left (volume : Measure ℝ) c)).prod
    (measurePreserving_add_left (volume : Measure ℝ) f)
  first
    | exact h
    | exact ⟨(_root_.GD.N0106.N0428.N0770.N1741.d027717 c f).measurable, h.map_eq⟩

theorem d027722 (c f : ℝ) (g : ℝ × ℝ → ℝ) :
    ∫ p : ℝ × ℝ, g (c + p.1, f + p.2) = ∫ p, g p := by
  have h := (_root_.GD.N0106.N0428.N0770.N1741.d027720 c f).integral_comp' g
  simpa only [_root_.GD.N0106.N0428.N0770.N1741.d027718] using h

theorem d027723 (c f : ℝ) (g : ℝ × ℝ → ℝ) :
    ∫ p : ℝ × ℝ, g (1 - (c + p.1), f + p.2) = ∫ p, g p := by
  have h := (_root_.GD.N0106.N0428.N0770.N1741.d027721 c f).integral_comp' g
  simpa only [_root_.GD.N0106.N0428.N0770.N1741.d027719] using h

theorem d027724 (c f : ℝ) {g : ℝ × ℝ → ℝ} (hg : Integrable g) :
    Integrable (fun p : ℝ × ℝ => g (c + p.1, f + p.2)) := by
  have h := ((_root_.GD.N0106.N0428.N0770.N1741.d027720 c f).integrable_comp_emb
    (_root_.GD.N0106.N0428.N0770.N1741.d027716 c f).measurableEmbedding).mpr hg
  first
    | exact h
    | simpa only [Function.comp_def, _root_.GD.N0106.N0428.N0770.N1741.d027718] using h

theorem d027725 (c f : ℝ) {g : ℝ × ℝ → ℝ} (hg : Integrable g) :
    Integrable (fun p : ℝ × ℝ => g (1 - (c + p.1), f + p.2)) := by
  have h := ((_root_.GD.N0106.N0428.N0770.N1741.d027721 c f).integrable_comp_emb
    (_root_.GD.N0106.N0428.N0770.N1741.d027717 c f).measurableEmbedding).mpr hg
  first
    | exact h
    | simpa only [Function.comp_def, _root_.GD.N0106.N0428.N0770.N1741.d027719] using h

theorem d027726 (c w x : ℝ) : _root_.GD.N0106.N0428.N0770.N1725.d024124 c w (c + x) = _root_.GD.N0106.N0428.N0770.N1725.d024124 0 w x := by
  have h1 : c + x - c = x := by ring
  simp only [_root_.GD.N0106.N0428.N0770.N1725.d024124, h1, sub_zero]

theorem d027727 (c w x : ℝ) : _root_.GD.N0106.N0428.N0770.N1725.d024124 (1 - c) w (1 - (c + x)) = _root_.GD.N0106.N0428.N0770.N1725.d024124 0 w x := by
  have h1 : 1 - (c + x) - (1 - c) = -x := by ring
  simp only [_root_.GD.N0106.N0428.N0770.N1725.d024124, h1, abs_neg, sub_zero]

theorem d027728 (c f w : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024125 c f w (c + p.1, f + p.2) = _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 w p := by
  simp only [_root_.GD.N0106.N0428.N0770.N1725.d024125, _root_.GD.N0106.N0428.N0770.N1741.d027726]

theorem d027729 (c f w : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 - c) f w (1 - (c + p.1), f + p.2) = _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 w p := by
  simp only [_root_.GD.N0106.N0428.N0770.N1725.d024125, _root_.GD.N0106.N0428.N0770.N1741.d027727, _root_.GD.N0106.N0428.N0770.N1741.d027726]



theorem d027730 (c f : ℝ) (φ : ℝ × ℝ → ℝ) :
    ∫ p, φ p * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024118 p =
      ∫ p, φ (c + p.1, f + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p := by
  have h := _root_.GD.N0106.N0428.N0770.N1741.d027722 c f (fun p => φ p * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024118 p)
  simp only [_root_.GD.N0106.N0428.N0770.N1741.d027728] at h
  exact h.symm



theorem d027731 (c f : ℝ) (φ : ℝ × ℝ → ℝ) :
    ∫ p, φ p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 - c) f _root_.GD.N0106.N0428.N0770.N1725.d024118 p =
      ∫ p, φ (1 - (c + p.1), f + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p := by
  have h := _root_.GD.N0106.N0428.N0770.N1741.d027723 c f (fun p => φ p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 - c) f _root_.GD.N0106.N0428.N0770.N1725.d024118 p)
  simp only [_root_.GD.N0106.N0428.N0770.N1741.d027729] at h
  exact h.symm

theorem d027732 (c f : ℝ) (φ : ℝ × ℝ → ℝ) :
    ∫ p, φ p * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2 =
      ∫ p, φ (c + p.1, f + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2 := by
  have h := _root_.GD.N0106.N0428.N0770.N1741.d027722 c f (fun p => φ p * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2)
  simp only [_root_.GD.N0106.N0428.N0770.N1741.d027728] at h
  exact h.symm

theorem d027733 (c f : ℝ) (φ : ℝ × ℝ → ℝ) :
    ∫ p, φ p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 - c) f _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2 =
      ∫ p, φ (1 - (c + p.1), f + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2 := by
  have h := _root_.GD.N0106.N0428.N0770.N1741.d027723 c f (fun p => φ p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 - c) f _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2)
  simp only [_root_.GD.N0106.N0428.N0770.N1741.d027729] at h
  exact h.symm




def d027734 (q : ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024131 p + _root_.GD.N0106.N0428.N0770.N1725.d024119 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024131 p ^ 2)

theorem d027735 (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024131 p = 3 * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 / 500) (1 / 1000) _root_.GD.N0106.N0428.N0770.N1725.d024118 p
      - 3 * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 - 1 / 500) (1 / 1000) _root_.GD.N0106.N0428.N0770.N1725.d024118 p
      - 4 * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 / 120) 20 _root_.GD.N0106.N0428.N0770.N1725.d024118 p
      + 4 * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 - 1 / 120) 20 _root_.GD.N0106.N0428.N0770.N1725.d024118 p := by
  simp only [_root_.GD.N0106.N0428.N0770.N1725.d024131, _root_.GD.N0106.N0428.N0770.N1725.d024126, _root_.GD.N0106.N0428.N0770.N1725.d024125]
  ring


theorem d027736 (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024131 p ^ 2 = 9 * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 / 500) (1 / 1000) _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2
      + 9 * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 - 1 / 500) (1 / 1000) _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2
      + 16 * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 / 120) 20 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2
      + 16 * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 - 1 / 120) 20 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2 := by
  have h1 := _root_.GD.N0106.N0428.N0770.N1741.d027714 (1 / 500) (1 / 1000) (1 - 1 / 500) (1 / 1000)
    (Or.inl (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])) p
  have h2 := _root_.GD.N0106.N0428.N0770.N1741.d027714 (1 / 500) (1 / 1000) (1 / 120) 20
    (Or.inl (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])) p
  have h3 := _root_.GD.N0106.N0428.N0770.N1741.d027714 (1 / 500) (1 / 1000) (1 - 1 / 120) 20
    (Or.inl (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])) p
  have h4 := _root_.GD.N0106.N0428.N0770.N1741.d027714 (1 - 1 / 500) (1 / 1000) (1 / 120) 20
    (Or.inr (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])) p
  have h5 := _root_.GD.N0106.N0428.N0770.N1741.d027714 (1 - 1 / 500) (1 / 1000) (1 - 1 / 120) 20
    (Or.inr (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])) p
  have h6 := _root_.GD.N0106.N0428.N0770.N1741.d027714 (1 / 120) 20 (1 - 1 / 120) 20
    (Or.inl (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])) p
  rw [_root_.GD.N0106.N0428.N0770.N1741.d027735]
  linear_combination (-18) * h1 + (-24) * h2 + 24 * h3 + 24 * h4 + (-24) * h5 + (-32) * h6

theorem d027737 {p : ℝ × ℝ} (hp : p ∉ Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) :
    _root_.GD.N0106.N0428.N0770.N1725.d024131 p = 0 := by
  rw [_root_.GD.N0106.N0428.N0770.N1741.d027735,
    _root_.GD.N0106.N0428.N0770.N1741.d027711 (1 / 500) (1 / 1000)
      (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) hp,
    _root_.GD.N0106.N0428.N0770.N1741.d027711 (1 - 1 / 500) (1 / 1000)
      (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) hp,
    _root_.GD.N0106.N0428.N0770.N1741.d027711 (1 / 120) 20
      (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) hp,
    _root_.GD.N0106.N0428.N0770.N1741.d027711 (1 - 1 / 120) 20
      (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) hp]
  ring

theorem d027738 {q : ℝ} {p : ℝ × ℝ}
    (hp : p ∉ Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) : _root_.GD.N0106.N0428.N0770.N1741.d027734 q p = 0 := by
  unfold _root_.GD.N0106.N0428.N0770.N1741.d027734
  rw [_root_.GD.N0106.N0428.N0770.N1741.d027737 hp]
  ring



theorem d027739 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (p : ℝ × ℝ) :
    0 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024131 p ^ 2 := by
  by_cases hp : p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)
  · exact mul_nonneg (_root_.GD.N0106.N0428.N0770.N1741.d027699 hq hp.1 hp.2) (sq_nonneg (_root_.GD.N0106.N0428.N0770.N1725.d024131 p))
  · rw [_root_.GD.N0106.N0428.N0770.N1741.d027737 hp]
    simp



def d027740 (k₁ k₂ c f q : ℝ) (p : ℝ × ℝ) : ℝ :=
  k₁ * ((p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p) + k₂ * _root_.GD.N0106.N0428.N0770.N1725.d024119 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024118 p)

theorem d027741 (q : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1741.d027734 q p =
      _root_.GD.N0106.N0428.N0770.N1741.d027740 6 9 (1 / 500) (1 / 1000) q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 / 500) (1 / 1000) _root_.GD.N0106.N0428.N0770.N1725.d024118 p
      + _root_.GD.N0106.N0428.N0770.N1741.d027740 (-6) 9 (1 - 1 / 500) (1 / 1000) q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 - 1 / 500) (1 / 1000) _root_.GD.N0106.N0428.N0770.N1725.d024118 p
      + _root_.GD.N0106.N0428.N0770.N1741.d027740 (-8) 16 (1 / 120) 20 q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 / 120) 20 _root_.GD.N0106.N0428.N0770.N1725.d024118 p
      + _root_.GD.N0106.N0428.N0770.N1741.d027740 8 16 (1 - 1 / 120) 20 q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 - 1 / 120) 20 _root_.GD.N0106.N0428.N0770.N1725.d024118 p := by
  unfold _root_.GD.N0106.N0428.N0770.N1741.d027734 _root_.GD.N0106.N0428.N0770.N1741.d027740
  rw [_root_.GD.N0106.N0428.N0770.N1741.d027736, _root_.GD.N0106.N0428.N0770.N1741.d027735]
  ring

theorem d027742 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (k₁ k₂ c f : ℝ)
    (hc : _root_.GD.N0106.N0428.N0770.N1725.d024118 < c) (hc1 : c + _root_.GD.N0106.N0428.N0770.N1725.d024118 < 1) (hf : _root_.GD.N0106.N0428.N0770.N1725.d024118 < f) :
    ContinuousOn (_root_.GD.N0106.N0428.N0770.N1741.d027740 k₁ k₂ c f q) (_root_.GD.N0106.N0428.N0770.N1741.d027705 c f) := by
  have hW : ContinuousOn (_root_.GD.N0106.N0428.N0770.N1725.d024170 q) (_root_.GD.N0106.N0428.N0770.N1741.d027705 c f) :=
    (_root_.GD.N0106.N0428.N0770.N1741.d027702 hq).mono (_root_.GD.N0106.N0428.N0770.N1741.d027712 hc hc1 hf)
  unfold _root_.GD.N0106.N0428.N0770.N1741.d027740
  exact (continuousOn_const.mul ((continuous_fst.sub continuous_const).continuousOn.mul hW)).add
    (continuousOn_const.mul (hW.mul (_root_.GD.N0106.N0428.N0770.N1741.d027706 c f _root_.GD.N0106.N0428.N0770.N1725.d024118).continuousOn))

theorem d027743 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (k₁ k₂ c f : ℝ)
    (hc : _root_.GD.N0106.N0428.N0770.N1725.d024118 < c) (hc1 : c + _root_.GD.N0106.N0428.N0770.N1725.d024118 < 1) (hf : _root_.GD.N0106.N0428.N0770.N1725.d024118 < f) :
    Integrable (fun p => _root_.GD.N0106.N0428.N0770.N1741.d027740 k₁ k₂ c f q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024118 p) :=
  _root_.GD.N0106.N0428.N0770.N1741.d027715 c f (_root_.GD.N0106.N0428.N0770.N1741.d027742 hq k₁ k₂ c f hc hc1 hf)



theorem d027744 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    Integrable (_root_.GD.N0106.N0428.N0770.N1741.d027734 q) := by
  have hA := _root_.GD.N0106.N0428.N0770.N1741.d027743 hq 6 9 (1 / 500) (1 / 1000)
    (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])
  have hA' := _root_.GD.N0106.N0428.N0770.N1741.d027743 hq (-6) 9 (1 - 1 / 500) (1 / 1000)
    (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])
  have hB := _root_.GD.N0106.N0428.N0770.N1741.d027743 hq (-8) 16 (1 / 120) 20
    (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])
  have hB' := _root_.GD.N0106.N0428.N0770.N1741.d027743 hq 8 16 (1 - 1 / 120) 20
    (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])
  exact (((hA.add hA').add hB).add hB').congr
    (Filter.Eventually.of_forall fun p => (_root_.GD.N0106.N0428.N0770.N1741.d027741 q p).symm)

theorem d027745 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (c f : ℝ)
    (hc : _root_.GD.N0106.N0428.N0770.N1725.d024118 < c) (hc1 : c + _root_.GD.N0106.N0428.N0770.N1725.d024118 < 1) (hf : _root_.GD.N0106.N0428.N0770.N1725.d024118 < f) :
    Integrable (fun p => _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 c f _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2) := by
  have hW := (_root_.GD.N0106.N0428.N0770.N1741.d027702 hq).mono (_root_.GD.N0106.N0428.N0770.N1741.d027712 hc hc1 hf)
  have h := _root_.GD.N0106.N0428.N0770.N1741.d027715 c f
    (hW.mul (_root_.GD.N0106.N0428.N0770.N1741.d027706 c f _root_.GD.N0106.N0428.N0770.N1725.d024118).continuousOn)
  convert h using 1
  funext p
  simp only [Pi.mul_apply]
  ring

theorem d027746 (q : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024131 p ^ 2 =
      9 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 / 500) (1 / 1000) _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2)
      + 9 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 - 1 / 500) (1 / 1000) _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2)
      + 16 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 / 120) 20 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2)
      + 16 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 - 1 / 120) 20 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2) := by
  rw [_root_.GD.N0106.N0428.N0770.N1741.d027736]
  ring

theorem d027747 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    Integrable (fun p => _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024131 p ^ 2) := by
  have hA := _root_.GD.N0106.N0428.N0770.N1741.d027745 hq (1 / 500) (1 / 1000)
    (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])
  have hA' := _root_.GD.N0106.N0428.N0770.N1741.d027745 hq (1 - 1 / 500) (1 / 1000)
    (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])
  have hB := _root_.GD.N0106.N0428.N0770.N1741.d027745 hq (1 / 120) 20
    (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])
  have hB' := _root_.GD.N0106.N0428.N0770.N1741.d027745 hq (1 - 1 / 120) 20
    (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])
  exact ((((hA.const_mul 9).add (hA'.const_mul 9)).add
    (hB.const_mul 16)).add (hB'.const_mul 16)).congr
      (Filter.Eventually.of_forall fun p => (_root_.GD.N0106.N0428.N0770.N1741.d027746 q p).symm)



theorem d027748 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (c f : ℝ)
    (hc : _root_.GD.N0106.N0428.N0770.N1725.d024118 < c) (hc1 : c + _root_.GD.N0106.N0428.N0770.N1725.d024118 < 1) (hf : _root_.GD.N0106.N0428.N0770.N1725.d024118 < f) :
    ContinuousOn (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0770.N1725.d024170 q (c + p.1, f + p.2)) (_root_.GD.N0106.N0428.N0770.N1741.d027705 0 0) := by
  have hmaps : MapsTo (fun p : ℝ × ℝ => (c + p.1, f + p.2)) (_root_.GD.N0106.N0428.N0770.N1741.d027705 0 0)
      (Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) := by
    intro p hp
    simp only [_root_.GD.N0106.N0428.N0770.N1741.d027705, Set.mem_prod, Set.mem_Icc] at hp
    have h1 : c + p.1 ∈ Ioo (0 : ℝ) 1 :=
      Set.mem_Ioo.mpr ⟨by linarith [hp.1.1, hc], by linarith [hp.1.2, hc1]⟩
    have h2 : f + p.2 ∈ Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith [hp.2.1, hf])
    exact Set.mem_prod.mpr ⟨h1, h2⟩
  exact (_root_.GD.N0106.N0428.N0770.N1741.d027702 hq).comp'
    (by fun_prop : Continuous (fun p : ℝ × ℝ => (c + p.1, f + p.2))).continuousOn hmaps

theorem d027749 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (c f : ℝ)
    (hc : _root_.GD.N0106.N0428.N0770.N1725.d024118 < c) (hc1 : c + _root_.GD.N0106.N0428.N0770.N1725.d024118 < 1) (hf : _root_.GD.N0106.N0428.N0770.N1725.d024118 < f) :
    ContinuousOn (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 - (c + p.1), f + p.2)) (_root_.GD.N0106.N0428.N0770.N1741.d027705 0 0) := by
  have hmaps : MapsTo (fun p : ℝ × ℝ => (1 - (c + p.1), f + p.2)) (_root_.GD.N0106.N0428.N0770.N1741.d027705 0 0)
      (Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) := by
    intro p hp
    simp only [_root_.GD.N0106.N0428.N0770.N1741.d027705, Set.mem_prod, Set.mem_Icc] at hp
    have h1 : 1 - (c + p.1) ∈ Ioo (0 : ℝ) 1 :=
      Set.mem_Ioo.mpr ⟨by linarith [hp.1.2, hc1], by linarith [hp.1.1, hc]⟩
    have h2 : f + p.2 ∈ Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith [hp.2.1, hf])
    exact Set.mem_prod.mpr ⟨h1, h2⟩
  exact (_root_.GD.N0106.N0428.N0770.N1741.d027702 hq).comp'
    (by fun_prop : Continuous (fun p : ℝ × ℝ => (1 - (c + p.1), f + p.2))).continuousOn hmaps


theorem d027750 {p : ℝ × ℝ} (h : _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ≠ 0) :
    -_root_.GD.N0106.N0428.N0770.N1725.d024118 < p.1 ∧ p.1 < _root_.GD.N0106.N0428.N0770.N1725.d024118 ∧ -_root_.GD.N0106.N0428.N0770.N1725.d024118 < p.2 ∧ p.2 < _root_.GD.N0106.N0428.N0770.N1725.d024118 := by
  obtain ⟨hu, hv⟩ := (_root_.GD.N0106.N0428.N0770.N1741.d027709 0 0 p).mp h
  exact ⟨by linarith [hu.1], by linarith [hu.2], by linarith [hv.1], by linarith [hv.2]⟩



theorem d027751 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) {p : ℝ × ℝ}
    (hp : -_root_.GD.N0106.N0428.N0770.N1725.d024118 < p.1 ∧ p.1 < _root_.GD.N0106.N0428.N0770.N1725.d024118 ∧ -_root_.GD.N0106.N0428.N0770.N1725.d024118 < p.2 ∧ p.2 < _root_.GD.N0106.N0428.N0770.N1725.d024118) :
    0 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 / 500 + p.1, 1 / 1000 + p.2) ∧
      0 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 - (1 / 500 + p.1), 1 / 1000 + p.2) ∧
      0 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 / 120 + p.1, 20 + p.2) ∧
      0 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 - (1 / 120 + p.1), 20 + p.2) := by
  obtain ⟨hu1, hu2, hv1, hv2⟩ := hp
  have hrs := _root_.GD.N0106.N0428.N0770.N1741.d027697
  exact ⟨_root_.GD.N0106.N0428.N0770.N1741.d027699 hq (e := 1 / 500 + p.1) (F := 1 / 1000 + p.2)
      ⟨by linarith [hu1, hrs], by linarith [hu2, hrs]⟩ (by linarith [hv1, hrs]),
    _root_.GD.N0106.N0428.N0770.N1741.d027699 hq (e := 1 - (1 / 500 + p.1)) (F := 1 / 1000 + p.2)
      ⟨by linarith [hu2, hrs], by linarith [hu1, hrs]⟩ (by linarith [hv1, hrs]),
    _root_.GD.N0106.N0428.N0770.N1741.d027699 hq (e := 1 / 120 + p.1) (F := 20 + p.2)
      ⟨by linarith [hu1, hrs], by linarith [hu2, hrs]⟩ (by linarith [hv1, hrs]),
    _root_.GD.N0106.N0428.N0770.N1741.d027699 hq (e := 1 - (1 / 120 + p.1)) (F := 20 + p.2)
      ⟨by linarith [hu2, hrs], by linarith [hu1, hrs]⟩ (by linarith [hv1, hrs])⟩



def d027752 (q : ℝ) (p : ℝ × ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0770.N1741.d027740 6 9 (1 / 500) (1 / 1000) q (1 / 500 + p.1, 1 / 1000 + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p
  + _root_.GD.N0106.N0428.N0770.N1741.d027740 (-6) 9 (1 - 1 / 500) (1 / 1000) q (1 - (1 / 500 + p.1), 1 / 1000 + p.2)
      * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p
  + _root_.GD.N0106.N0428.N0770.N1741.d027740 (-8) 16 (1 / 120) 20 q (1 / 120 + p.1, 20 + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p
  + _root_.GD.N0106.N0428.N0770.N1741.d027740 8 16 (1 - 1 / 120) 20 q (1 - (1 / 120 + p.1), 20 + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p


def d027753 (q : ℝ) (p : ℝ × ℝ) : ℝ :=
  (_root_.GD.N0106.N0428.N0770.N1727.d024438 q (1 / 500 + p.1) (1 / 1000 + p.2) + _root_.GD.N0106.N0428.N0770.N1727.d024438 q (1 / 120 + p.1) (20 + p.2))
    * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p


def d027754 (q : ℝ) (p : ℝ × ℝ) : ℝ :=
  (9 * _root_.GD.N0106.N0428.N0770.N1727.d024438 q (1 / 500 + p.1) (1 / 1000 + p.2)
    + 16 * _root_.GD.N0106.N0428.N0770.N1727.d024438 q (1 / 120 + p.1) (20 + p.2)) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2

theorem d027755 (q : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1741.d027754 q p =
      9 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 / 500 + p.1, 1 / 1000 + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2)
      + 9 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 - (1 / 500 + p.1), 1 / 1000 + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2)
      + 16 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 / 120 + p.1, 20 + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2)
      + 16 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 - (1 / 120 + p.1), 20 + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2) := by
  unfold _root_.GD.N0106.N0428.N0770.N1741.d027754 _root_.GD.N0106.N0428.N0770.N1727.d024438
  ring


theorem d027756 {f₁ f₂ f₃ f₄ : ℝ × ℝ → ℝ}
    (h₁ : Integrable f₁) (h₂ : Integrable f₂) (h₃ : Integrable f₃) (h₄ : Integrable f₄) :
    (∫ p, f₁ p + f₂ p + f₃ p + f₄ p) =
      (∫ p, f₁ p) + (∫ p, f₂ p) + (∫ p, f₃ p) + ∫ p, f₄ p := by
  have h12 := integral_add h₁ h₂
  have h123 := integral_add (h₁.add h₂) h₃
  have h1234 := integral_add ((h₁.add h₂).add h₃) h₄
  simp only [Pi.add_apply] at h123 h1234
  rw [h1234, h123, h12]

theorem d027757 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    Integrable (_root_.GD.N0106.N0428.N0770.N1741.d027754 q) ∧
      (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024131 p ^ 2) = ∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027754 q p := by
  have hA := _root_.GD.N0106.N0428.N0770.N1741.d027745 hq (1 / 500) (1 / 1000)
    (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])
  have hA' := _root_.GD.N0106.N0428.N0770.N1741.d027745 hq (1 - 1 / 500) (1 / 1000)
    (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])
  have hB := _root_.GD.N0106.N0428.N0770.N1741.d027745 hq (1 / 120) 20
    (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])
  have hB' := _root_.GD.N0106.N0428.N0770.N1741.d027745 hq (1 - 1 / 120) 20
    (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])
  have h1 : Integrable (fun p =>
      _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 / 500 + p.1, 1 / 1000 + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2) := by
    simpa only [_root_.GD.N0106.N0428.N0770.N1741.d027728] using _root_.GD.N0106.N0428.N0770.N1741.d027724 (1 / 500) (1 / 1000) hA
  have h2 : Integrable (fun p =>
      _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 - (1 / 500 + p.1), 1 / 1000 + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2) := by
    simpa only [_root_.GD.N0106.N0428.N0770.N1741.d027729] using
      _root_.GD.N0106.N0428.N0770.N1741.d027725 (1 / 500) (1 / 1000) hA'
  have h3 : Integrable (fun p =>
      _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 / 120 + p.1, 20 + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2) := by
    simpa only [_root_.GD.N0106.N0428.N0770.N1741.d027728] using _root_.GD.N0106.N0428.N0770.N1741.d027724 (1 / 120) 20 hB
  have h4 : Integrable (fun p =>
      _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 - (1 / 120 + p.1), 20 + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2) := by
    simpa only [_root_.GD.N0106.N0428.N0770.N1741.d027729] using _root_.GD.N0106.N0428.N0770.N1741.d027725 (1 / 120) 20 hB'
  constructor
  · exact ((((h1.const_mul 9).add (h2.const_mul 9)).add
      (h3.const_mul 16)).add (h4.const_mul 16)).congr
        (Filter.Eventually.of_forall fun p => (_root_.GD.N0106.N0428.N0770.N1741.d027755 q p).symm)
  · calc
      (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024131 p ^ 2) =
          9 * (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 / 500) (1 / 1000) _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2)
          + 9 * (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 - 1 / 500) (1 / 1000) _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2)
          + 16 * (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 / 120) 20 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2)
          + 16 * (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 - 1 / 120) 20 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2) := by
        simp_rw [_root_.GD.N0106.N0428.N0770.N1741.d027746]
        rw [_root_.GD.N0106.N0428.N0770.N1741.d027756 (hA.const_mul 9) (hA'.const_mul 9)
          (hB.const_mul 16) (hB'.const_mul 16)]
        simp only [integral_const_mul]
      _ = 9 * (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 / 500 + p.1, 1 / 1000 + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2)
          + 9 * (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 - (1 / 500 + p.1), 1 / 1000 + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2)
          + 16 * (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 / 120 + p.1, 20 + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2)
          + 16 * (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 - (1 / 120 + p.1), 20 + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2) := by
        rw [_root_.GD.N0106.N0428.N0770.N1741.d027732 (1 / 500) (1 / 1000),
          _root_.GD.N0106.N0428.N0770.N1741.d027733 (1 / 500) (1 / 1000),
          _root_.GD.N0106.N0428.N0770.N1741.d027732 (1 / 120) 20, _root_.GD.N0106.N0428.N0770.N1741.d027733 (1 / 120) 20]
      _ = ∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027754 q p := by
        simp_rw [_root_.GD.N0106.N0428.N0770.N1741.d027755]
        rw [_root_.GD.N0106.N0428.N0770.N1741.d027756 (h1.const_mul 9) (h2.const_mul 9)
          (h3.const_mul 16) (h4.const_mul 16)]
        simp only [integral_const_mul]

theorem d027758 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1741.d027754 q p ≤ 16 * _root_.GD.N0106.N0428.N0770.N1741.d027753 q p := by
  by_cases h : _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p = 0
  · simp only [_root_.GD.N0106.N0428.N0770.N1741.d027754, _root_.GD.N0106.N0428.N0770.N1741.d027753, h, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
  · obtain ⟨hWA, hWA', hWB, hWB'⟩ := _root_.GD.N0106.N0428.N0770.N1741.d027751 hq (_root_.GD.N0106.N0428.N0770.N1741.d027750 h)
    have hA : 0 ≤ _root_.GD.N0106.N0428.N0770.N1727.d024438 q (1 / 500 + p.1) (1 / 1000 + p.2) := add_nonneg hWA hWA'
    have hB : 0 ≤ _root_.GD.N0106.N0428.N0770.N1727.d024438 q (1 / 120 + p.1) (20 + p.2) := add_nonneg hWB hWB'
    have hH0 := _root_.GD.N0106.N0428.N0770.N1741.d027707 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p
    have hH1 := _root_.GD.N0106.N0428.N0770.N1741.d027708 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 _root_.GD.N0106.N0428.N0770.N1725.d024121 p
    have hsq : _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ^ 2 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p := by nlinarith
    have hcoeff : 9 * _root_.GD.N0106.N0428.N0770.N1727.d024438 q (1 / 500 + p.1) (1 / 1000 + p.2)
        + 16 * _root_.GD.N0106.N0428.N0770.N1727.d024438 q (1 / 120 + p.1) (20 + p.2) ≤
      16 * (_root_.GD.N0106.N0428.N0770.N1727.d024438 q (1 / 500 + p.1) (1 / 1000 + p.2)
        + _root_.GD.N0106.N0428.N0770.N1727.d024438 q (1 / 120 + p.1) (20 + p.2)) := by linarith
    have hm := mul_le_mul hcoeff hsq (sq_nonneg (_root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) (add_nonneg hA hB))
    unfold _root_.GD.N0106.N0428.N0770.N1741.d027754 _root_.GD.N0106.N0428.N0770.N1741.d027753
    nlinarith only [hm]

theorem d027759 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    Integrable (fun p => _root_.GD.N0106.N0428.N0770.N1741.d027740 6 9 (1 / 500) (1 / 1000) q (1 / 500 + p.1, 1 / 1000 + p.2)
      * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p) := by
  have h := _root_.GD.N0106.N0428.N0770.N1741.d027724 (1 / 500) (1 / 1000) (_root_.GD.N0106.N0428.N0770.N1741.d027743 hq 6 9 (1 / 500)
    (1 / 1000) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]))
  simpa only [_root_.GD.N0106.N0428.N0770.N1741.d027728] using h

theorem d027760 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    Integrable (fun p => _root_.GD.N0106.N0428.N0770.N1741.d027740 (-6) 9 (1 - 1 / 500) (1 / 1000) q
      (1 - (1 / 500 + p.1), 1 / 1000 + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p) := by
  have h := _root_.GD.N0106.N0428.N0770.N1741.d027725 (1 / 500) (1 / 1000) (_root_.GD.N0106.N0428.N0770.N1741.d027743 hq (-6) 9
    (1 - 1 / 500) (1 / 1000) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]))
  simpa only [_root_.GD.N0106.N0428.N0770.N1741.d027729] using h

theorem d027761 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    Integrable (fun p => _root_.GD.N0106.N0428.N0770.N1741.d027740 (-8) 16 (1 / 120) 20 q (1 / 120 + p.1, 20 + p.2)
      * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p) := by
  have h := _root_.GD.N0106.N0428.N0770.N1741.d027724 (1 / 120) 20 (_root_.GD.N0106.N0428.N0770.N1741.d027743 hq (-8) 16 (1 / 120) 20
    (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]))
  simpa only [_root_.GD.N0106.N0428.N0770.N1741.d027728] using h

theorem d027762 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    Integrable (fun p => _root_.GD.N0106.N0428.N0770.N1741.d027740 8 16 (1 - 1 / 120) 20 q (1 - (1 / 120 + p.1), 20 + p.2)
      * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p) := by
  have h := _root_.GD.N0106.N0428.N0770.N1741.d027725 (1 / 120) 20 (_root_.GD.N0106.N0428.N0770.N1741.d027743 hq 8 16 (1 - 1 / 120) 20
    (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]))
  simpa only [_root_.GD.N0106.N0428.N0770.N1741.d027729] using h

theorem d027763 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    Integrable (fun p => _root_.GD.N0106.N0428.N0770.N1741.d027752 q p) := by
  unfold _root_.GD.N0106.N0428.N0770.N1741.d027752
  exact (((_root_.GD.N0106.N0428.N0770.N1741.d027759 hq).add (_root_.GD.N0106.N0428.N0770.N1741.d027760 hq)).add
    (_root_.GD.N0106.N0428.N0770.N1741.d027761 hq)).add (_root_.GD.N0106.N0428.N0770.N1741.d027762 hq)

theorem d027764 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    Integrable (fun p => _root_.GD.N0106.N0428.N0770.N1741.d027753 q p) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ =>
      _root_.GD.N0106.N0428.N0770.N1727.d024438 q (1 / 500 + p.1) (1 / 1000 + p.2) + _root_.GD.N0106.N0428.N0770.N1727.d024438 q (1 / 120 + p.1) (20 + p.2))
      (_root_.GD.N0106.N0428.N0770.N1741.d027705 0 0) := by
    unfold _root_.GD.N0106.N0428.N0770.N1727.d024438
    exact ((_root_.GD.N0106.N0428.N0770.N1741.d027748 hq (1 / 500) (1 / 1000)
        (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])).add
      (_root_.GD.N0106.N0428.N0770.N1741.d027749 hq (1 / 500) (1 / 1000)
        (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]))).add
      ((_root_.GD.N0106.N0428.N0770.N1741.d027748 hq (1 / 120) 20
        (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])).add
      (_root_.GD.N0106.N0428.N0770.N1741.d027749 hq (1 / 120) 20
        (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])))
  unfold _root_.GD.N0106.N0428.N0770.N1741.d027753
  exact _root_.GD.N0106.N0428.N0770.N1741.d027715 0 0 hc



theorem d027765 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    ∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027734 q p = ∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027752 q p := by
  have hA := _root_.GD.N0106.N0428.N0770.N1741.d027743 hq 6 9 (1 / 500) (1 / 1000)
    (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])
  have hA' := _root_.GD.N0106.N0428.N0770.N1741.d027743 hq (-6) 9 (1 - 1 / 500) (1 / 1000)
    (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])
  have hB := _root_.GD.N0106.N0428.N0770.N1741.d027743 hq (-8) 16 (1 / 120) 20
    (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])
  have hB' := _root_.GD.N0106.N0428.N0770.N1741.d027743 hq 8 16 (1 - 1 / 120) 20
    (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]) (by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118])
  have h1 := _root_.GD.N0106.N0428.N0770.N1741.d027759 hq
  have h2 := _root_.GD.N0106.N0428.N0770.N1741.d027760 hq
  have h3 := _root_.GD.N0106.N0428.N0770.N1741.d027761 hq
  have h4 := _root_.GD.N0106.N0428.N0770.N1741.d027762 hq
  calc ∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027734 q p
      = ∫ p, (_root_.GD.N0106.N0428.N0770.N1741.d027740 6 9 (1 / 500) (1 / 1000) q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 / 500) (1 / 1000) _root_.GD.N0106.N0428.N0770.N1725.d024118 p
          + _root_.GD.N0106.N0428.N0770.N1741.d027740 (-6) 9 (1 - 1 / 500) (1 / 1000) q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 - 1 / 500) (1 / 1000) _root_.GD.N0106.N0428.N0770.N1725.d024118 p
          + _root_.GD.N0106.N0428.N0770.N1741.d027740 (-8) 16 (1 / 120) 20 q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 / 120) 20 _root_.GD.N0106.N0428.N0770.N1725.d024118 p
          + _root_.GD.N0106.N0428.N0770.N1741.d027740 8 16 (1 - 1 / 120) 20 q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 - 1 / 120) 20 _root_.GD.N0106.N0428.N0770.N1725.d024118 p) := by
        simp only [_root_.GD.N0106.N0428.N0770.N1741.d027741]
    _ = (∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027740 6 9 (1 / 500) (1 / 1000) q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 / 500) (1 / 1000) _root_.GD.N0106.N0428.N0770.N1725.d024118 p)
          + (∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027740 (-6) 9 (1 - 1 / 500) (1 / 1000) q p
              * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 - 1 / 500) (1 / 1000) _root_.GD.N0106.N0428.N0770.N1725.d024118 p)
          + (∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027740 (-8) 16 (1 / 120) 20 q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 / 120) 20 _root_.GD.N0106.N0428.N0770.N1725.d024118 p)
          + (∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027740 8 16 (1 - 1 / 120) 20 q p * _root_.GD.N0106.N0428.N0770.N1725.d024125 (1 - 1 / 120) 20 _root_.GD.N0106.N0428.N0770.N1725.d024118 p) := by
        rw [_root_.GD.N0106.N0428.N0770.N1741.d027756 hA hA' hB hB']
    _ = (∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027740 6 9 (1 / 500) (1 / 1000) q (1 / 500 + p.1, 1 / 1000 + p.2)
            * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p)
          + (∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027740 (-6) 9 (1 - 1 / 500) (1 / 1000) q (1 - (1 / 500 + p.1), 1 / 1000 + p.2)
            * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p)
          + (∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027740 (-8) 16 (1 / 120) 20 q (1 / 120 + p.1, 20 + p.2) * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p)
          + (∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027740 8 16 (1 - 1 / 120) 20 q (1 - (1 / 120 + p.1), 20 + p.2)
            * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p) := by
        rw [_root_.GD.N0106.N0428.N0770.N1741.d027730 (1 / 500) (1 / 1000), _root_.GD.N0106.N0428.N0770.N1741.d027731 (1 / 500) (1 / 1000),
          _root_.GD.N0106.N0428.N0770.N1741.d027730 (1 / 120) 20, _root_.GD.N0106.N0428.N0770.N1741.d027731 (1 / 120) 20]
    _ = ∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027752 q p := by
        unfold _root_.GD.N0106.N0428.N0770.N1741.d027752
        rw [_root_.GD.N0106.N0428.N0770.N1741.d027756 h1 h2 h3 h4]



theorem d027766 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1741.d027752 q p ≤ -(1 / 500) * _root_.GD.N0106.N0428.N0770.N1741.d027753 q p := by
  by_cases h : _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p = 0
  · unfold _root_.GD.N0106.N0428.N0770.N1741.d027752 _root_.GD.N0106.N0428.N0770.N1741.d027753
    rw [h]
    simp
  · obtain ⟨hu1, hu2, hv1, hv2⟩ := _root_.GD.N0106.N0428.N0770.N1741.d027750 h
    have hH0 : 0 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p := _root_.GD.N0106.N0428.N0770.N1741.d027707 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p
    have hH1 : _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ≤ 1 := _root_.GD.N0106.N0428.N0770.N1741.d027708 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 _root_.GD.N0106.N0428.N0770.N1725.d024121 p
    have hea : 1 / 500 + p.1 ∈ Icc (1 / 500 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (1 / 500 + _root_.GD.N0106.N0428.N0770.N1725.d024118) :=
      ⟨by linarith [hu1], by linarith [hu2]⟩
    have hFa : 1 / 1000 + p.2 ∈ Icc (1 / 1000 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (1 / 1000 + _root_.GD.N0106.N0428.N0770.N1725.d024118) :=
      ⟨by linarith [hv1], by linarith [hv2]⟩
    have heb : 1 / 120 + p.1 ∈ Icc (1 / 120 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (1 / 120 + _root_.GD.N0106.N0428.N0770.N1725.d024118) :=
      ⟨by linarith [hu1], by linarith [hu2]⟩
    have hFb : 20 + p.2 ∈ Icc (20 - _root_.GD.N0106.N0428.N0770.N1725.d024118) (20 + _root_.GD.N0106.N0428.N0770.N1725.d024118) := ⟨by linarith [hv1], by linarith [hv2]⟩
    have hgap := _root_.GD.N0106.N0428.N0770.N1741.d027704 hq hea hFa heb hFb
    obtain ⟨hWA, hWA', hWB, hWB'⟩ := _root_.GD.N0106.N0428.N0770.N1741.d027751 hq ⟨hu1, hu2, hv1, hv2⟩
    have hS : 0 ≤ 9 * _root_.GD.N0106.N0428.N0770.N1727.d024438 q (1 / 500 + p.1) (1 / 1000 + p.2)
        + 16 * _root_.GD.N0106.N0428.N0770.N1727.d024438 q (1 / 120 + p.1) (20 + p.2) := by
      unfold _root_.GD.N0106.N0428.N0770.N1727.d024438
      linarith [hWA, hWA', hWB, hWB']
    have key : -(1 / 500) * _root_.GD.N0106.N0428.N0770.N1741.d027753 q p - _root_.GD.N0106.N0428.N0770.N1741.d027752 q p =
        2 * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p
            * _root_.GD.N0106.N0428.N0770.N1727.d024439 q (1 / 500 + p.1) (1 / 1000 + p.2) (1 / 120 + p.1) (20 + p.2)
          + _root_.GD.N0106.N0428.N0770.N1725.d024119 * (_root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p * (1 - _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p))
            * (9 * _root_.GD.N0106.N0428.N0770.N1727.d024438 q (1 / 500 + p.1) (1 / 1000 + p.2)
              + 16 * _root_.GD.N0106.N0428.N0770.N1727.d024438 q (1 / 120 + p.1) (20 + p.2)) := by
      unfold _root_.GD.N0106.N0428.N0770.N1741.d027752 _root_.GD.N0106.N0428.N0770.N1741.d027753 _root_.GD.N0106.N0428.N0770.N1741.d027740 _root_.GD.N0106.N0428.N0770.N1727.d024439 _root_.GD.N0106.N0428.N0770.N1727.d024437 _root_.GD.N0106.N0428.N0770.N1727.d024438
      try dsimp only
      rw [_root_.GD.N0106.N0428.N0770.N1741.d027728, _root_.GD.N0106.N0428.N0770.N1741.d027729, _root_.GD.N0106.N0428.N0770.N1741.d027728, _root_.GD.N0106.N0428.N0770.N1741.d027729]
      ring
    have hnn : 0 ≤ 2 * _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p
            * _root_.GD.N0106.N0428.N0770.N1727.d024439 q (1 / 500 + p.1) (1 / 1000 + p.2) (1 / 120 + p.1) (20 + p.2)
          + _root_.GD.N0106.N0428.N0770.N1725.d024119 * (_root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p * (1 - _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p))
            * (9 * _root_.GD.N0106.N0428.N0770.N1727.d024438 q (1 / 500 + p.1) (1 / 1000 + p.2)
              + 16 * _root_.GD.N0106.N0428.N0770.N1727.d024438 q (1 / 120 + p.1) (20 + p.2)) :=
      add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hH0) hgap.le)
        (mul_nonneg (mul_nonneg _root_.GD.N0106.N0428.N0770.N1725.d024123.le (mul_nonneg hH0 (sub_nonneg.mpr hH1))) hS)
    linarith [key, hnn]

theorem d027767 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (p : ℝ × ℝ) : 0 ≤ _root_.GD.N0106.N0428.N0770.N1741.d027753 q p := by
  by_cases h : _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p = 0
  · simp only [_root_.GD.N0106.N0428.N0770.N1741.d027753, h, mul_zero, le_refl]
  · obtain ⟨hWA, hWA', hWB, hWB'⟩ := _root_.GD.N0106.N0428.N0770.N1741.d027751 hq (_root_.GD.N0106.N0428.N0770.N1741.d027750 h)
    unfold _root_.GD.N0106.N0428.N0770.N1741.d027753 _root_.GD.N0106.N0428.N0770.N1727.d024438
    exact mul_nonneg (add_nonneg (add_nonneg hWA hWA') (add_nonneg hWB hWB'))
      (_root_.GD.N0106.N0428.N0770.N1741.d027707 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p)


theorem d027768 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) {p : ℝ × ℝ}
    (hp : p ∈ Ioo (-_root_.GD.N0106.N0428.N0770.N1725.d024118) _root_.GD.N0106.N0428.N0770.N1725.d024118 ×ˢ Ioo (-_root_.GD.N0106.N0428.N0770.N1725.d024118) _root_.GD.N0106.N0428.N0770.N1725.d024118) : _root_.GD.N0106.N0428.N0770.N1741.d027753 q p ≠ 0 := by
  have hH : _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p ≠ 0 := by
    rw [_root_.GD.N0106.N0428.N0770.N1741.d027709]
    exact ⟨Set.mem_Ioo.mpr ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
      Set.mem_Ioo.mpr ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
  have hHpos : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024125 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p :=
    lt_of_le_of_ne (_root_.GD.N0106.N0428.N0770.N1741.d027707 0 0 _root_.GD.N0106.N0428.N0770.N1725.d024118 p) (Ne.symm hH)
  obtain ⟨hu1, hu2, hv1, hv2⟩ := _root_.GD.N0106.N0428.N0770.N1741.d027750 hH
  have hrs := _root_.GD.N0106.N0428.N0770.N1741.d027697
  have hWA : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024170 q (1 / 500 + p.1, 1 / 1000 + p.2) :=
    _root_.GD.N0106.N0428.N0770.N1741.d027698 hq (e := 1 / 500 + p.1) (F := 1 / 1000 + p.2)
      ⟨by linarith [hu1, hrs], by linarith [hu2, hrs]⟩ (by linarith [hv1, hrs])
  obtain ⟨_, hWA', hWB, hWB'⟩ := _root_.GD.N0106.N0428.N0770.N1741.d027751 hq ⟨hu1, hu2, hv1, hv2⟩
  unfold _root_.GD.N0106.N0428.N0770.N1741.d027753 _root_.GD.N0106.N0428.N0770.N1727.d024438
  exact (mul_pos (by linarith [hWA, hWA', hWB, hWB']) hHpos).ne'

theorem d027769 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : 0 < ∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027753 q p := by
  have hnn : (0 : ℝ × ℝ → ℝ) ≤ fun p => _root_.GD.N0106.N0428.N0770.N1741.d027753 q p := fun p => _root_.GD.N0106.N0428.N0770.N1741.d027767 hq p
  rw [integral_pos_iff_support_of_nonneg hnn (_root_.GD.N0106.N0428.N0770.N1741.d027764 hq)]
  have hsub : Ioo (-_root_.GD.N0106.N0428.N0770.N1725.d024118) _root_.GD.N0106.N0428.N0770.N1725.d024118 ×ˢ Ioo (-_root_.GD.N0106.N0428.N0770.N1725.d024118) _root_.GD.N0106.N0428.N0770.N1725.d024118 ⊆ Function.support (fun p => _root_.GD.N0106.N0428.N0770.N1741.d027753 q p) :=
    fun p hp => Function.mem_support.mpr (_root_.GD.N0106.N0428.N0770.N1741.d027768 hq hp)
  have hvol : (0 : ENNReal) < volume (Ioo (-_root_.GD.N0106.N0428.N0770.N1725.d024118) _root_.GD.N0106.N0428.N0770.N1725.d024118 ×ˢ Ioo (-_root_.GD.N0106.N0428.N0770.N1725.d024118) _root_.GD.N0106.N0428.N0770.N1725.d024118) := by
    simp only [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo]
    have h2 : (0 : ℝ) < _root_.GD.N0106.N0428.N0770.N1725.d024118 - -_root_.GD.N0106.N0428.N0770.N1725.d024118 := by norm_num [_root_.GD.N0106.N0428.N0770.N1725.d024118]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr h2).ne' (ENNReal.ofReal_pos.mpr h2).ne'
  exact lt_of_lt_of_le hvol (measure_mono hsub)

theorem d027770 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    (∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027734 q p) ≤ -(1 / 500) * ∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027753 q p := by
  rw [_root_.GD.N0106.N0428.N0770.N1741.d027765 hq]
  have hle : ∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027752 q p ≤ ∫ p, -(1 / 500) * _root_.GD.N0106.N0428.N0770.N1741.d027753 q p :=
    integral_mono (_root_.GD.N0106.N0428.N0770.N1741.d027763 hq) ((_root_.GD.N0106.N0428.N0770.N1741.d027764 hq).const_mul _)
      (fun p => _root_.GD.N0106.N0428.N0770.N1741.d027766 hq p)
  rw [integral_const_mul] at hle
  exact hle



theorem d027771 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : ∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027734 q p < 0 := by
  have hle := _root_.GD.N0106.N0428.N0770.N1741.d027770 hq
  have hpos := _root_.GD.N0106.N0428.N0770.N1741.d027769 hq
  linarith [hle, hpos]



theorem d027772 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    (∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024131 p ^ 2) ≤ 16 * ∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027753 q p := by
  rw [(_root_.GD.N0106.N0428.N0770.N1741.d027757 hq).2]
  have hle := integral_mono (_root_.GD.N0106.N0428.N0770.N1741.d027757 hq).1 ((_root_.GD.N0106.N0428.N0770.N1741.d027764 hq).const_mul 16)
    (_root_.GD.N0106.N0428.N0770.N1741.d027758 hq)
  simpa only [integral_const_mul] using hle


def d027773 (q t : ℝ) (p : ℝ × ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0770.N1741.d027734 q p + (t - _root_.GD.N0106.N0428.N0770.N1725.d024119) * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024131 p ^ 2)

theorem d027774 (q t : ℝ) (p : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0770.N1741.d027773 q t p = 2 * (p.1 - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024131 p + t * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024131 p ^ 2) := by
  unfold _root_.GD.N0106.N0428.N0770.N1741.d027773 _root_.GD.N0106.N0428.N0770.N1741.d027734
  ring

theorem d027775 {q t : ℝ} {p : ℝ × ℝ}
    (hp : p ∉ Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)) : _root_.GD.N0106.N0428.N0770.N1741.d027773 q t p = 0 := by
  rw [_root_.GD.N0106.N0428.N0770.N1741.d027774, _root_.GD.N0106.N0428.N0770.N1741.d027737 hp]
  ring

theorem d027776 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    Integrable (_root_.GD.N0106.N0428.N0770.N1741.d027773 q t) :=
  (_root_.GD.N0106.N0428.N0770.N1741.d027744 hq).add ((_root_.GD.N0106.N0428.N0770.N1741.d027747 hq).const_mul (t - _root_.GD.N0106.N0428.N0770.N1725.d024119))

theorem d027777 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    (∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027773 q t p) = (∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027734 q p) +
      (t - _root_.GD.N0106.N0428.N0770.N1725.d024119) * ∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024131 p ^ 2 := by
  unfold _root_.GD.N0106.N0428.N0770.N1741.d027773
  rw [integral_add (_root_.GD.N0106.N0428.N0770.N1741.d027744 hq) ((_root_.GD.N0106.N0428.N0770.N1741.d027747 hq).const_mul _),
    integral_const_mul]



theorem d027778 {q t : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (ht : t < 9 / 40000) : (∫ p, _root_.GD.N0106.N0428.N0770.N1741.d027773 q t p) < 0 := by
  rw [_root_.GD.N0106.N0428.N0770.N1741.d027777 hq]
  by_cases hsmall : t ≤ _root_.GD.N0106.N0428.N0770.N1725.d024119
  · have hnonneg : 0 ≤ ∫ p, _root_.GD.N0106.N0428.N0770.N1725.d024170 q p * _root_.GD.N0106.N0428.N0770.N1725.d024131 p ^ 2 := integral_nonneg (_root_.GD.N0106.N0428.N0770.N1741.d027739 hq)
    have hprod := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsmall) hnonneg
    have hneg := _root_.GD.N0106.N0428.N0770.N1741.d027771 hq
    linarith only [hprod, hneg]
  · have hdiff : 0 ≤ t - _root_.GD.N0106.N0428.N0770.N1725.d024119 := by linarith
    have henergy := mul_le_mul_of_nonneg_left (_root_.GD.N0106.N0428.N0770.N1741.d027772 hq) hdiff
    have hbase := _root_.GD.N0106.N0428.N0770.N1741.d027770 hq
    have hslack := _root_.GD.N0106.N0428.N0770.N1741.d027769 hq
    have hcoeff : 16 * (t - _root_.GD.N0106.N0428.N0770.N1725.d024119) - 1 / 500 < 0 := by
      change 16 * (t - 1 / 10000) - 1 / 500 < 0
      linarith only [ht]
    have hnegative := mul_neg_of_neg_of_pos hcoeff hslack
    nlinarith only [henergy, hbase, hnegative]

end
end GD.N0106.N0428.N0770.N1741

#print axioms _root_.GD.N0106.N0428.N0770.N1741.d027704
#print axioms _root_.GD.N0106.N0428.N0770.N1741.d027765
#print axioms _root_.GD.N0106.N0428.N0770.N1741.d027769
#print axioms _root_.GD.N0106.N0428.N0770.N1741.d027771
#print axioms _root_.GD.N0106.N0428.N0770.N1741.d027757
#print axioms _root_.GD.N0106.N0428.N0770.N1741.d027772
#print axioms _root_.GD.N0106.N0428.N0770.N1741.d027778
