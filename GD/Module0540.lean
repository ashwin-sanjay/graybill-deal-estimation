import GD.Module0539

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace GD.N0101.N0360
noncomputable section
open _root_.GD.N0225.N0539
open _root_.GD.N0213
open _root_.GD.N0213.N0495

variable {k : ℕ}

def d008062 (β : Fin k → ℝ) : ℝ := ∑ i, β i

theorem d008063 : Measurable (_root_.GD.N0101.N0360.d008062 (k := k)) := by
  unfold _root_.GD.N0101.N0360.d008062
  fun_prop

theorem d008064 (c : ℝ) (β : Fin k → ℝ) :
    _root_.GD.N0101.N0360.d008062 (c • β) = c * _root_.GD.N0101.N0360.d008062 β := by
  simp only [_root_.GD.N0101.N0360.d008062, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

theorem d008065 (α : Fin k → ℝ) (hsum : ∑ i, α i = 1) :
    ∀ᵐ β ∂_root_.GD.N0225.N0539.d008044 α, 0 < _root_.GD.N0101.N0360.d008062 β := by
  have hk : 0 < k := by
    by_contra h
    have hz : k = 0 := Nat.eq_zero_of_not_pos h
    subst k
    simp at hsum
  filter_upwards [_root_.GD.N0225.N0539.d008050 α] with β hβ
  exact Finset.sum_pos (fun i _ => hβ i) ⟨⟨0, hk⟩, Finset.mem_univ _⟩


def d008066 (α : Fin k → ℝ) (g : (Fin k → ℝ) → ℝ) :
    Measure (Fin k → ℝ) :=
  (_root_.GD.N0225.N0539.d008044 α).withDensity (fun β => ENNReal.ofReal (_root_.GD.N0101.N0360.d008062 β * g β))

theorem d008067 (α : Fin k → ℝ)
    (hsum : ∑ i, α i = 1) (g : (Fin k → ℝ) → ℝ)
    (hscale : ∀ c : ℝ, 0 < c → ∀ β, (∀ i, 0 < β i) →
      g (c • β) = c⁻¹ * g β) {c : ℝ} (hc : 0 < c) :
    (_root_.GD.N0101.N0360.d008066 α g).map (fun β => c • β) =
      (ENNReal.ofReal c)⁻¹ • _root_.GD.N0101.N0360.d008066 α g := by
  let e : (Fin k → ℝ) ≃ᵐ (Fin k → ℝ) :=
    (Homeomorph.smulOfNeZero c hc.ne').toMeasurableEquiv
  have hei : ∀ β, e.symm β = c⁻¹ • β := fun _ => rfl
  have hd : (_root_.GD.N0225.N0539.d008044 α).withDensity
      (fun β => ENNReal.ofReal (_root_.GD.N0101.N0360.d008062 (e.symm β) * g (e.symm β))) =
      _root_.GD.N0101.N0360.d008066 α g := by
    apply withDensity_congr_ae
    filter_upwards [_root_.GD.N0225.N0539.d008050 α] with β hβ
    rw [hei, _root_.GD.N0101.N0360.d008064, hscale _ (inv_pos.mpr hc) β hβ, inv_inv]
    congr 1
    field_simp
  have hm := _root_.GD.N0225.N0539.d008042 (_root_.GD.N0225.N0539.d008044 α) e
    (fun β => ENNReal.ofReal (_root_.GD.N0101.N0360.d008062 β * g β))
  change (_root_.GD.N0101.N0360.d008066 α g).map (fun β => c • β) = _ at hm
  rw [show (_root_.GD.N0225.N0539.d008044 α).map e = (ENNReal.ofReal c)⁻¹ • _root_.GD.N0225.N0539.d008044 α from
    _root_.GD.N0225.N0539.d008049 α hc hsum, withDensity_smul_measure, hd] at hm
  exact hm

theorem d008068 (α : Fin k → ℝ)
    (hsum : ∑ i, α i = 1) (g : (Fin k → ℝ) → ℝ)
    (hgn : ∀ β, (∀ i, 0 < β i) → 0 ≤ g β)
    (hJ : (∫⁻ β, ENNReal.ofReal
      (Real.exp (-_root_.GD.N0101.N0360.d008062 β) * _root_.GD.N0101.N0360.d008062 β * g β) ∂_root_.GD.N0225.N0539.d008044 α) ≠ ⊤) :
    _root_.GD.N0101.N0360.d008066 α g {β | _root_.GD.N0101.N0360.d008062 β ≤ 1} ≠ ⊤ := by
  have hs : MeasurableSet {β : Fin k → ℝ | _root_.GD.N0101.N0360.d008062 β ≤ 1} :=
    measurableSet_le _root_.GD.N0101.N0360.d008063 measurable_const
  rw [_root_.GD.N0101.N0360.d008066, withDensity_apply _ hs, ← lintegral_indicator hs]
  apply ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [_root_.GD.N0225.N0539.d008050 α, _root_.GD.N0101.N0360.d008065 α hsum] with β hβ hr
  by_cases hb : _root_.GD.N0101.N0360.d008062 β ≤ 1
  · rw [indicator_of_mem (show β ∈ {β | _root_.GD.N0101.N0360.d008062 β ≤ 1} from hb),
      ← ENNReal.ofReal_mul (Real.exp_pos 1).le]
    apply ENNReal.ofReal_le_ofReal
    have he : (1 : ℝ) ≤ Real.exp 1 * Real.exp (-_root_.GD.N0101.N0360.d008062 β) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith)
    calc
      _root_.GD.N0101.N0360.d008062 β * g β = 1 * (_root_.GD.N0101.N0360.d008062 β * g β) := by ring
      _ ≤ (Real.exp 1 * Real.exp (-_root_.GD.N0101.N0360.d008062 β)) * (_root_.GD.N0101.N0360.d008062 β * g β) :=
        mul_le_mul_of_nonneg_right he (mul_nonneg hr.le (hgn β hβ))
      _ = _ := by ring
  · rw [indicator_of_notMem (show β ∉ {β | _root_.GD.N0101.N0360.d008062 β ≤ 1} from hb)]
    exact zero_le

theorem d008069 (α : Fin k → ℝ)
    (hsum : ∑ i, α i = 1) (g : (Fin k → ℝ) → ℝ)
    (hgn : ∀ β, (∀ i, 0 < β i) → 0 ≤ g β)
    (hscale : ∀ c : ℝ, 0 < c → ∀ β, (∀ i, 0 < β i) →
      g (c • β) = c⁻¹ * g β)
    (hJ : (∫⁻ β, ENNReal.ofReal
      (Real.exp (-_root_.GD.N0101.N0360.d008062 β) * _root_.GD.N0101.N0360.d008062 β * g β) ∂_root_.GD.N0225.N0539.d008044 α) ≠ ⊤) :
    (_root_.GD.N0101.N0360.d008066 α g).map _root_.GD.N0101.N0360.d008062 =
      _root_.GD.N0101.N0360.d008066 α g {β | _root_.GD.N0101.N0360.d008062 β ≤ 1} • volume.restrict (Ioi (0 : ℝ)) := by
  apply _root_.GD.N0213.N0514.d007719 (_root_.GD.N0101.N0360.d008066 α g)
    _root_.GD.N0101.N0360.d008062 (fun c β => c • β) _root_.GD.N0101.N0360.d008063 _ (fun _ _ => by fun_prop)
    (fun _ hc => _root_.GD.N0101.N0360.d008067 α hsum g hscale hc)
    (fun c _ β => _root_.GD.N0101.N0360.d008064 c β)
    (_root_.GD.N0101.N0360.d008068 α hsum g hgn hJ)
  exact (withDensity_absolutelyContinuous (_root_.GD.N0225.N0539.d008044 α) _).ae_le
    (_root_.GD.N0101.N0360.d008065 α hsum)



theorem d008070
    (α : Fin k → ℝ) (hsum : ∑ i, α i = 1)
    (g : (Fin k → ℝ) → ℝ) (hgm : Measurable g)
    (hgn : ∀ β, (∀ i, 0 < β i) → 0 ≤ g β)
    (hscale : ∀ c : ℝ, 0 < c → ∀ β, (∀ i, 0 < β i) →
      g (c • β) = c⁻¹ * g β)
    (hJ : (∫⁻ β, ENNReal.ofReal
      (Real.exp (-_root_.GD.N0101.N0360.d008062 β) * _root_.GD.N0101.N0360.d008062 β * g β) ∂_root_.GD.N0225.N0539.d008044 α) ≠ ⊤)
    {L : ℝ} (hL : 0 < L) :
    (∫⁻ β, ENNReal.ofReal (g β) ∂_root_.GD.N0225.N0539.d008058 α L) ≠ ⊤ := by
  have hf : Measurable (fun r : ℝ => _root_.GD.N0213.N0495.d007174 L r ^ 2 / r) := by
    dsimp only [_root_.GD.N0213.N0495.d007174]
    fun_prop
  have hi : Integrable (fun β => _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0360.d008062 β) ^ 2 / _root_.GD.N0101.N0360.d008062 β)
      (_root_.GD.N0101.N0360.d008066 α g) := by
    apply (integrable_map_measure hf.aestronglyMeasurable
      _root_.GD.N0101.N0360.d008063.aemeasurable).mp
    rw [_root_.GD.N0101.N0360.d008069 α hsum g hgn hscale hJ]
    exact (_root_.GD.N0213.N0495.d007185 hL).smul_measure
      (_root_.GD.N0101.N0360.d008068 α hsum g hgn hJ)
  have hn : ∀ᵐ β ∂_root_.GD.N0101.N0360.d008066 α g,
      0 ≤ _root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0360.d008062 β) ^ 2 / _root_.GD.N0101.N0360.d008062 β := by
    have hp : ∀ᵐ β ∂_root_.GD.N0101.N0360.d008066 α g, 0 < _root_.GD.N0101.N0360.d008062 β :=
      (withDensity_absolutelyContinuous (_root_.GD.N0225.N0539.d008044 α) _).ae_le (_root_.GD.N0101.N0360.d008065 α hsum)
    filter_upwards [hp] with β hβ using div_nonneg (sq_nonneg _) hβ.le
  have hfinite : (∫⁻ β, ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0360.d008062 β) ^ 2 / _root_.GD.N0101.N0360.d008062 β)
      ∂_root_.GD.N0101.N0360.d008066 α g) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
    exact ENNReal.ofReal_ne_top
  have heq : (∫⁻ β, ENNReal.ofReal (g β) ∂_root_.GD.N0225.N0539.d008058 α L) =
      ∫⁻ β, ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0360.d008062 β) ^ 2 / _root_.GD.N0101.N0360.d008062 β)
        ∂_root_.GD.N0101.N0360.d008066 α g := by
    have hq : Measurable (fun β : Fin k → ℝ =>
        ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0360.d008062 β) ^ 2 / _root_.GD.N0101.N0360.d008062 β)) :=
      (hf.comp _root_.GD.N0101.N0360.d008063).ennreal_ofReal
    rw [_root_.GD.N0225.N0539.d008058, _root_.GD.N0101.N0360.d008066,
      lintegral_withDensity_eq_lintegral_mul _ (by dsimp only [_root_.GD.N0213.N0495.d007174]; fun_prop)
        hgm.ennreal_ofReal,
      lintegral_withDensity_eq_lintegral_mul _
        (_root_.GD.N0101.N0360.d008063.mul hgm).ennreal_ofReal
        hq]
    apply lintegral_congr_ae
    filter_upwards [_root_.GD.N0225.N0539.d008050 α, _root_.GD.N0101.N0360.d008065 α hsum] with β hβ hr
    simp only [Pi.mul_apply]
    change ENNReal.ofReal (_root_.GD.N0213.N0495.d007174 L (_root_.GD.N0101.N0360.d008062 β) ^ 2) * ENNReal.ofReal (g β) = _
    rw [← ENNReal.ofReal_mul (sq_nonneg _),
      ← ENNReal.ofReal_mul (mul_nonneg hr.le (hgn β hβ))]
    congr 1
    field_simp
  rw [heq]
  exact hfinite

theorem d008071
    (α : Fin k → ℝ) (hsum : ∑ i, α i = 1)
    (g : (Fin k → ℝ) → ℝ) (hgm : Measurable g)
    (hgn : ∀ β, (∀ i, 0 < β i) → 0 ≤ g β)
    (hscale : ∀ c : ℝ, 0 < c → ∀ β, (∀ i, 0 < β i) →
      g (c • β) = c⁻¹ * g β)
    (hJ : (∫⁻ β, ENNReal.ofReal
      (Real.exp (-_root_.GD.N0101.N0360.d008062 β) * _root_.GD.N0101.N0360.d008062 β * g β) ∂_root_.GD.N0225.N0539.d008044 α) ≠ ⊤)
    {L : ℝ} (hL : 0 < L) : Integrable g (_root_.GD.N0225.N0539.d008058 α L) := by
  refine ⟨hgm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal ?_).mpr ?_⟩
  · filter_upwards [(withDensity_absolutelyContinuous (_root_.GD.N0225.N0539.d008044 α) _).ae_le
      (_root_.GD.N0225.N0539.d008050 α)] with β hβ using hgn β hβ
  · exact lt_top_iff_ne_top.mpr
      (_root_.GD.N0101.N0360.d008070
        α hsum g hgm hgn hscale hJ hL)

end
end GD.N0101.N0360

#print axioms _root_.GD.N0101.N0360.d008067
#print axioms _root_.GD.N0101.N0360.d008068
#print axioms _root_.GD.N0101.N0360.d008069
#print axioms _root_.GD.N0101.N0360.d008070
#print axioms _root_.GD.N0101.N0360.d008071
