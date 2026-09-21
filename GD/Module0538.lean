import GD.Module0511
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace GD.N0213.N0522
noncomputable section

theorem d008018 {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (e : X ≃ᵐ Y) (w : X → ℝ≥0∞) :
    (μ.withDensity w).map e = (μ.map e).withDensity (fun y => w (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs), withDensity_apply _ hs,
    ← lintegral_indicator hs, lintegral_map_equiv,
    ← lintegral_indicator (e.measurable hs)]
  apply lintegral_congr
  intro x
  by_cases hx : e x ∈ s <;> simp [hx]

variable {k : ℕ}

def d008019 (α β : Fin k → ℝ) : ℝ :=
  if ∀ i, 0 < β i then ∏ i, β i ^ (α i - 1) else 0

def d008020 (α : Fin k → ℝ) : Measure (Fin k → ℝ) :=
  volume.withDensity (fun β => ENNReal.ofReal (_root_.GD.N0213.N0522.d008019 α β))

theorem d008021 (α β : Fin k → ℝ) : 0 ≤ _root_.GD.N0213.N0522.d008019 α β := by
  unfold _root_.GD.N0213.N0522.d008019
  split_ifs with h
  · exact Finset.prod_nonneg fun i _ => Real.rpow_nonneg (h i).le _
  · exact le_rfl

theorem d008022 (α : Fin k → ℝ) : Measurable (_root_.GD.N0213.N0522.d008019 α) := by
  unfold _root_.GD.N0213.N0522.d008019
  apply Measurable.ite
  · simp only [setOf_forall]
    exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)
  · fun_prop
  · fun_prop

theorem d008023 (α β : Fin k → ℝ) {c : ℝ} (hc : 0 < c) :
    _root_.GD.N0213.N0522.d008019 α (c • β) = c ^ ((∑ i, α i) - k) * _root_.GD.N0213.N0522.d008019 α β := by
  have heq : (∀ i, 0 < (c • β) i) ↔ ∀ i, 0 < β i := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pos_iff_of_pos_left hc]
  unfold _root_.GD.N0213.N0522.d008019
  rw [if_congr heq rfl rfl]
  split_ifs with h
  · simp only [Pi.smul_apply, smul_eq_mul]
    simp_rw [Real.mul_rpow hc.le (h _).le]
    rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos hc]
    congr 2
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  · simp

theorem d008024 (α β : Fin k → ℝ) {c : ℝ}
    (hc : 0 < c) (hα : ∑ i, α i = 1) :
    _root_.GD.N0213.N0522.d008019 α (c • β) = c ^ (1 - (k : ℝ)) * _root_.GD.N0213.N0522.d008019 α β := by
  rw [_root_.GD.N0213.N0522.d008023 α β hc, hα]

theorem d008025 (α : Fin k → ℝ) {c : ℝ}
    (hc : 0 < c) (hα : ∑ i, α i = 1) :
    (_root_.GD.N0213.N0522.d008020 α).map (fun β => c • β) = (ENNReal.ofReal c)⁻¹ • _root_.GD.N0213.N0522.d008020 α := by
  let e : (Fin k → ℝ) ≃ᵐ (Fin k → ℝ) :=
    (Homeomorph.smulOfNeZero c hc.ne').toMeasurableEquiv
  have he : ∀ β, e β = c • β := fun _ => rfl
  have hei : ∀ β, e.symm β = c⁻¹ • β := fun _ => rfl
  have hw : (fun β => ENNReal.ofReal (_root_.GD.N0213.N0522.d008019 α (e.symm β))) =
      (ENNReal.ofReal ((c⁻¹) ^ (1 - (k : ℝ)))) •
        (fun β => ENNReal.ofReal (_root_.GD.N0213.N0522.d008019 α β)) := by
    funext β
    rw [hei, _root_.GD.N0213.N0522.d008024 α β (inv_pos.mpr hc) hα,
      ENNReal.ofReal_mul (Real.rpow_nonneg (inv_pos.mpr hc).le _)]
    rfl
  have hm := _root_.GD.N0213.N0522.d008018 volume e (fun β => ENNReal.ofReal (_root_.GD.N0213.N0522.d008019 α β))
  change (_root_.GD.N0213.N0522.d008020 α).map (fun β => c • β) = _ at hm
  rw [show (volume : Measure (Fin k → ℝ)).map e =
      ENNReal.ofReal |(c ^ k)⁻¹| • volume by
        simpa only [show (e : (Fin k → ℝ) → (Fin k → ℝ)) = (fun β => c • β) from funext he,
          Module.finrank_pi, Module.finrank_self, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul, mul_one] using
          (Measure.map_addHaar_smul (volume : Measure (Fin k → ℝ)) hc.ne'),
    hw, withDensity_smul_measure, withDensity_smul _ ((_root_.GD.N0213.N0522.d008022 α).ennreal_ofReal),
    smul_smul] at hm
  have hfactor : ENNReal.ofReal |(c ^ k)⁻¹| *
      ENNReal.ofReal ((c⁻¹) ^ (1 - (k : ℝ))) = (ENNReal.ofReal c)⁻¹ := by
    rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (inv_pos.mpr (pow_pos hc _)),
      Real.inv_rpow hc.le, ← mul_inv]
    have hp : c ^ k * c ^ (1 - (k : ℝ)) = c := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hc,
        show (k : ℝ) + (1 - k) = 1 by ring, Real.rpow_one]
    rw [hp, ENNReal.ofReal_inv_of_pos hc]
  rw [hfactor] at hm
  exact hm

theorem d008026 (α : Fin k → ℝ) :
    ∀ᵐ β ∂_root_.GD.N0213.N0522.d008020 α, ∀ i, 0 < β i := by
  rw [_root_.GD.N0213.N0522.d008020, ae_withDensity_iff ((_root_.GD.N0213.N0522.d008022 α).ennreal_ofReal)]
  filter_upwards with β hβ
  by_contra h
  simp [_root_.GD.N0213.N0522.d008019, h] at hβ

theorem d008027 (α β : Fin k → ℝ) :
    0 < _root_.GD.N0213.N0522.d008019 α β ↔ ∀ i, 0 < β i := by
  unfold _root_.GD.N0213.N0522.d008019
  split_ifs with h
  · exact iff_of_true (Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (h i) _)) h
  · simp only [lt_self_iff_false, false_iff]
    exact h

theorem d008028 (α : Fin k → ℝ) (s : Set (Fin k → ℝ)) :
    _root_.GD.N0213.N0522.d008020 α s = 0 ↔ volume ({β : Fin k → ℝ | ∀ i, 0 < β i} ∩ s) = 0 := by
  rw [_root_.GD.N0213.N0522.d008020, withDensity_apply_eq_zero ((_root_.GD.N0213.N0522.d008022 α).ennreal_ofReal)]
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le, _root_.GD.N0213.N0522.d008027]

theorem d008029 (α : Fin k → ℝ) (hk : 0 < k) :
    0 < _root_.GD.N0213.N0522.d008020 α {β | ∑ i, β i ≤ 1} := by
  let U : Set (Fin k → ℝ) := {β | (∀ i, 0 < β i) ∧ ∑ i, β i < 1}
  have hopen : IsOpen U := by
    change IsOpen ({β : Fin k → ℝ | ∀ i, 0 < β i} ∩ {β | ∑ i, β i < 1})
    apply IsOpen.inter
    · simp only [setOf_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
    · exact isOpen_lt (by fun_prop) continuous_const
  have hne : U.Nonempty := by
    refine ⟨fun _ => 1 / (2 * (k : ℝ)), ?_, ?_⟩
    · intro i
      positivity
    · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
      field_simp
      nlinarith
  have hU : 0 < _root_.GD.N0213.N0522.d008020 α U := by
    apply pos_iff_ne_zero.mpr
    rw [ne_eq, _root_.GD.N0213.N0522.d008028]
    have hi : {β : Fin k → ℝ | ∀ i, 0 < β i} ∩ U = U :=
      inter_eq_right.mpr (fun _ hx => hx.1)
    rw [hi]
    exact (hopen.measure_pos volume hne).ne'
  exact lt_of_lt_of_le hU (measure_mono (fun β hβ => hβ.2.le))

def d008030 (α β : Fin k → ℝ) : ℝ :=
  ∏ i, (Ioc (0 : ℝ) 1).indicator (fun x => x ^ (α i - 1)) (β i)

theorem d008031 (α β : Fin k → ℝ) : 0 ≤ _root_.GD.N0213.N0522.d008030 α β := by
  apply Finset.prod_nonneg
  intro i _
  by_cases h : β i ∈ Ioc (0 : ℝ) 1
  · rw [indicator_of_mem h]
    exact Real.rpow_nonneg h.1.le _
  · rw [indicator_of_notMem h]

theorem d008032 (α : Fin k → ℝ) (hα : ∀ i, 0 < α i) :
    Integrable (_root_.GD.N0213.N0522.d008030 α) := by
  change Integrable (fun β : Fin k → ℝ =>
    ∏ i, (Ioc (0 : ℝ) 1).indicator (fun x => x ^ (α i - 1)) (β i))
  rw [volume_pi]
  apply Integrable.fintype_prod
  intro i
  apply (integrable_indicator_iff measurableSet_Ioc).mpr
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    (intervalIntegral.intervalIntegrable_rpow' (by linarith [hα i]))

theorem d008033 (α β : Fin k → ℝ) :
    {β : Fin k → ℝ | ∑ i, β i ≤ 1}.indicator
      (fun β => ENNReal.ofReal (_root_.GD.N0213.N0522.d008019 α β)) β ≤ ENNReal.ofReal (_root_.GD.N0213.N0522.d008030 α β) := by
  by_cases hsum : ∑ i, β i ≤ 1
  · rw [indicator_of_mem (show β ∈ {β : Fin k → ℝ | ∑ i, β i ≤ 1} from hsum)]
    by_cases hpos : ∀ i, 0 < β i
    · have hb (i : Fin k) : β i ∈ Ioc (0 : ℝ) 1 := ⟨hpos i,
        (Finset.single_le_sum (fun j _ => (hpos j).le) (Finset.mem_univ i)).trans hsum⟩
      simp only [_root_.GD.N0213.N0522.d008019, if_pos hpos, _root_.GD.N0213.N0522.d008030, indicator_of_mem (hb _)]
      exact le_rfl
    · simp [_root_.GD.N0213.N0522.d008019, hpos]
  · rw [indicator_of_notMem (show β ∉ {β : Fin k → ℝ | ∑ i, β i ≤ 1} from hsum)]
    exact zero_le

theorem d008034 (α : Fin k → ℝ) (hα : ∀ i, 0 < α i) :
    _root_.GD.N0213.N0522.d008020 α {β | ∑ i, β i ≤ 1} ≠ ⊤ := by
  have hm : MeasurableSet {β : Fin k → ℝ | ∑ i, β i ≤ 1} := by
    apply measurableSet_le _ measurable_const
    fun_prop
  rw [_root_.GD.N0213.N0522.d008020, withDensity_apply _ hm, ← lintegral_indicator hm]
  apply ne_top_of_le_ne_top _ (lintegral_mono (_root_.GD.N0213.N0522.d008033 α))
  rw [← ofReal_integral_eq_lintegral_ofReal (_root_.GD.N0213.N0522.d008032 α hα)
    (ae_of_all _ (_root_.GD.N0213.N0522.d008031 α))]
  exact ENNReal.ofReal_ne_top

theorem d008035 (α : Fin k → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) :
    (_root_.GD.N0213.N0522.d008020 α).map (fun β => ∑ i, β i) =
      _root_.GD.N0213.N0522.d008020 α {β | ∑ i, β i ≤ 1} • volume.restrict (Ioi (0 : ℝ)) := by
  have hk : 0 < k := by
    by_contra h
    have hz : k = 0 := Nat.eq_zero_of_not_pos h
    subst k
    simp at hsum
  apply _root_.GD.N0213.N0514.d007719 (_root_.GD.N0213.N0522.d008020 α) (fun β => ∑ i, β i)
    (fun c β => c • β) (by fun_prop) _ (fun c _ => by fun_prop)
    (fun c hc => _root_.GD.N0213.N0522.d008025 α hc hsum) _ (_root_.GD.N0213.N0522.d008034 α hα)
  · filter_upwards [_root_.GD.N0213.N0522.d008026 α] with β hβ
    exact Finset.sum_pos (fun i _ => hβ i) ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  · intro c _ β
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

open _root_.GD.N0213.N0495
open Filter
open scoped Topology

theorem d008036 (α : Fin k → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) {L : ℝ} (hL : 0 < L) (q : ℝ) :
    Integrable (fun β => (∑ i, β i) ^ q * _root_.GD.N0213.N0495.d007174 L (∑ i, β i) ^ 2) (_root_.GD.N0213.N0522.d008020 α) := by
  have hm : Measurable (fun β : Fin k → ℝ => ∑ i, β i) := by fun_prop
  have hf : Measurable (fun r => r ^ q * _root_.GD.N0213.N0495.d007174 L r ^ 2) := by
    dsimp only [_root_.GD.N0213.N0495.d007174]
    fun_prop
  apply (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mp
  rw [_root_.GD.N0213.N0522.d008035 α hα hsum]
  exact (_root_.GD.N0213.N0495.d007183 hL q).smul_measure (_root_.GD.N0213.N0522.d008034 α hα)

def d008037 (α : Fin k → ℝ) (L : ℝ) : Measure (Fin k → ℝ) :=
  (_root_.GD.N0213.N0522.d008020 α).withDensity (fun β => ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 L (∑ i, β i) ^ 2))

theorem d008038 (α : Fin k → ℝ) (L : ℝ)
    (s : Set (Fin k → ℝ)) : _root_.GD.N0213.N0522.d008037 α L s = 0 ↔ _root_.GD.N0213.N0522.d008020 α s = 0 := by
  have hm : Measurable (fun β : Fin k → ℝ => ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 L (∑ i, β i) ^ 2)) := by
    dsimp only [_root_.GD.N0213.N0495.d007174]
    fun_prop
  rw [_root_.GD.N0213.N0522.d008037, withDensity_apply_eq_zero hm]
  have hn (β : Fin k → ℝ) : ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 L (∑ i, β i) ^ 2) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (_root_.GD.N0213.N0495.d007176 L _)))
  have hz : {x : Fin k → ℝ | ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 L (∑ i, x i) ^ 2) ≠ 0} = univ :=
    eq_univ_of_forall hn
  rw [hz, univ_inter]

theorem d008039 (α : Fin k → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) {L : ℝ} (hL : 0 < L) :
    _root_.GD.N0213.N0522.d008037 α L univ ≠ ⊤ := by
  have hi : Integrable (fun β => _root_.GD.N0213.N0495.d007174 L (∑ i, β i) ^ 2) (_root_.GD.N0213.N0522.d008020 α) := by
    simpa only [Real.rpow_zero, one_mul] using _root_.GD.N0213.N0522.d008036 α hα hsum hL 0
  rw [_root_.GD.N0213.N0522.d008037, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun β => sq_nonneg _))]
  exact ENNReal.ofReal_ne_top

theorem d008040 (α : Fin k → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) {L : ℝ} (hL : 0 < L) :
    (∫ β, (∑ i, β i) * _root_.GD.N0213.N0495.d007175 L (∑ i, β i) ^ 2 ∂_root_.GD.N0213.N0522.d008020 α) =
      (_root_.GD.N0213.N0522.d008020 α {β | ∑ i, β i ≤ 1}).toReal * (4 * _root_.GD.N0213.N0495.d007186 / L) := by
  have hm : Measurable (fun β : Fin k → ℝ => ∑ i, β i) := by fun_prop
  have hf : Measurable (fun r => r * _root_.GD.N0213.N0495.d007175 L r ^ 2) := by
    dsimp only [_root_.GD.N0213.N0495.d007175, _root_.GD.N0213.N0495.d007174]
    fun_prop
  rw [← integral_map hm.aemeasurable hf.aestronglyMeasurable,
    _root_.GD.N0213.N0522.d008035 α hα hsum, integral_smul_measure, smul_eq_mul, _root_.GD.N0213.N0495.d007190 hL]

theorem d008041 (α : Fin k → ℝ)
    (hα : ∀ i, 0 < α i) (hsum : ∑ i, α i = 1) :
    Tendsto (fun n : ℕ => ∫ β, (∑ i, β i) *
      _root_.GD.N0213.N0495.d007175 ((n : ℝ) + 1) (∑ i, β i) ^ 2 ∂_root_.GD.N0213.N0522.d008020 α) atTop (𝓝 0) := by
  have heq (n : ℕ) := _root_.GD.N0213.N0522.d008040 α hα hsum
    (L := (n : ℝ) + 1) (by positivity)
  simp_rw [heq]
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul
    ((_root_.GD.N0213.N0522.d008020 α {β | ∑ i, β i ≤ 1}).toReal * (4 * _root_.GD.N0213.N0495.d007186))
  simpa only [mul_zero, mul_one_div, mul_div_assoc] using h

end
end GD.N0213.N0522

#print axioms _root_.GD.N0213.N0522.d008018
#print axioms _root_.GD.N0213.N0522.d008023
#print axioms _root_.GD.N0213.N0522.d008024
#print axioms _root_.GD.N0213.N0522.d008025
#print axioms _root_.GD.N0213.N0522.d008026
#print axioms _root_.GD.N0213.N0522.d008028
#print axioms _root_.GD.N0213.N0522.d008029
#print axioms _root_.GD.N0213.N0522.d008034
#print axioms _root_.GD.N0213.N0522.d008035
#print axioms _root_.GD.N0213.N0522.d008036
#print axioms _root_.GD.N0213.N0522.d008039
#print axioms _root_.GD.N0213.N0522.d008038
#print axioms _root_.GD.N0213.N0522.d008041
