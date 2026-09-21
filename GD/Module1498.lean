import GD.Module1484
import GD.Module0802

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace GD.N0072
noncomputable section
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0933 _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0107

variable {k : ℕ}



theorem d023440 :
    _root_.GD.N0072.d007621 (fun _ : Fin 2 => 1) (![1 / 2, -(1 / 2)] : Fin 2 → ℝ) <
      _root_.GD.N0072.d007621 (fun _ : Fin 2 => 1) (_root_.GD.N0072.d007614 (![1 / 2, -(1 / 2)] : Fin 2 → ℝ)) := by
  norm_num [_root_.GD.N0072.d007621, _root_.GD.N0072.d007614, _root_.GD.N0072.d007613, Fin.sum_univ_two]

theorem d023441 (p : Fin k → ℝ) (hp : ∑ i, p i = 1) (i : Fin k) :
    _root_.GD.N0072.d007614 p i ≤ 1 := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => _root_.GD.N0072.d007616 p hp j)
    (Finset.mem_univ i)
  rwa [_root_.GD.N0072.d007617 p hp] at h

theorem d023442 (v p : Fin k → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hp : ∑ i, p i = 1) : _root_.GD.N0072.d007621 v (_root_.GD.N0072.d007614 p) ≤ ∑ i, v i := by
  apply Finset.sum_le_sum
  intro i _
  have h0 := _root_.GD.N0072.d007616 p hp i
  have h1 := _root_.GD.N0072.d023441 p hp i
  have hsq : _root_.GD.N0072.d007614 p i ^ 2 ≤ 1 := by
    simpa only [one_pow] using (sq_le_sq₀ h0 zero_le_one).mpr h1
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq (hv i)



theorem d023443 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1) :
    _root_.GD.N0072.d023291 sizes (_root_.GD.N0072.d007614 ∘ w) ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes := by
  refine ⟨_root_.GD.N0072.d023295 sizes _ (_root_.GD.N0072.d007625.comp hw), ?_⟩
  intro θ
  let v : Fin k → ℝ := fun i => θ.scale i ^ 2 / (sizes i : ℝ)
  have hv : ∀ i, 0 ≤ v i := fun i => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009301 k sizes θ.scale) :=
    _root_.GD.N0232.N0719.N0910.d010289 sizes hn θ.scale
  rw [_root_.GD.N0072.d023297 sizes hn _ (_root_.GD.N0072.d007625.comp hw)
    (fun t => _root_.GD.N0072.d007617 (w t) (hunit t))]
  apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top : ENNReal.ofReal (∑ i, v i) ≠ ⊤)
  calc
    _ ≤ ∫⁻ _t, ENNReal.ofReal (∑ i, v i) ∂_root_.GD.N0232.N0719.N0933.d009301 k sizes θ.scale :=
      lintegral_mono (fun t => ENNReal.ofReal_le_ofReal (_root_.GD.N0072.d023442 v (w t) hv (hunit t)))
    _ = ENNReal.ofReal (∑ i, v i) := by simp



theorem d023444 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes (_root_.GD.N0072.d007614 ∘ w)) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) := by
  rw [_root_.GD.N0072.d023297 sizes hn _ (_root_.GD.N0072.d007625.comp hw)
      (fun t => _root_.GD.N0072.d007617 (w t) (hunit t)),
    _root_.GD.N0072.d023297 sizes hn w hw hunit]
  exact lintegral_mono (fun t => ENNReal.ofReal_le_ofReal
    (_root_.GD.N0072.d007623 _ (w t)
      (fun i => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) (hunit t)))

theorem d023445 (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes (_root_.GD.N0072.d007614 ∘ w)) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes w) := by
  have hn0 : ∀ i, 0 < sizes i := fun i => lt_of_lt_of_le (by decide : 0 < 2) (hn i)
  have hm : Measurable (fun t : Fin k → ℝ => w (fun i => (sizes i : ℝ) * t i)) := by
    fun_prop
  rw [_root_.GD.N0072.d023294 sizes hn0 (_root_.GD.N0072.d007614 ∘ w),
    _root_.GD.N0072.d023294 sizes hn0 w]
  exact _root_.GD.N0072.d023444 sizes hn _ hm (fun t => hunit _) θ




theorem d023446 (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (B : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ≥0∞) :
    (∃ w : (Fin k → ℝ) → Fin k → ℝ, Measurable w ∧
      (∀ t, ∑ i, w t i = 1) ∧
      ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes w) ≤ B θ) ↔
    (∃ w : (Fin k → ℝ) → Fin k → ℝ, Measurable w ∧
      (∀ t, ∑ i, w t i = 1) ∧ (∀ t i, 0 ≤ w t i) ∧
      ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes w) ≤ B θ) := by
  constructor
  · rintro ⟨w, hw, hunit, hcap⟩
    exact ⟨_root_.GD.N0072.d007614 ∘ w, _root_.GD.N0072.d007625.comp hw,
      fun t => _root_.GD.N0072.d007617 (w t) (hunit t),
      fun t i => _root_.GD.N0072.d007616 (w t) (hunit t) i,
      fun θ => (_root_.GD.N0072.d023445 sizes hn w hw hunit θ).trans (hcap θ)⟩
  · rintro ⟨w, hw, hunit, _, hcap⟩
    exact ⟨w, hw, hunit, hcap⟩




theorem d023447 (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (B : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ≥0∞) :
    (∃ w : (Fin k → ℝ) → Fin k → ℝ, Measurable w ∧
      (∀ t, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes w) ≤ B θ) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes w) < B θ) ↔
    (∃ w : (Fin k → ℝ) → Fin k → ℝ, Measurable w ∧
      (∀ t, ∑ i, w t i = 1) ∧ (∀ t i, 0 ≤ w t i) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes w) ≤ B θ) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes w) < B θ) := by
  constructor
  · rintro ⟨w, hw, hunit, hcap, θ₀, hs⟩
    exact ⟨_root_.GD.N0072.d007614 ∘ w, _root_.GD.N0072.d007625.comp hw,
      fun t => _root_.GD.N0072.d007617 (w t) (hunit t),
      fun t i => _root_.GD.N0072.d007616 (w t) (hunit t) i,
      fun θ => (_root_.GD.N0072.d023445 sizes hn w hw hunit θ).trans (hcap θ),
      θ₀, (_root_.GD.N0072.d023445 sizes hn w hw hunit θ₀).trans_lt hs⟩
  · rintro ⟨w, hw, hunit, _, hcap, hs⟩
    exact ⟨w, hw, hunit, hcap, hs⟩

theorem d023448 (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (B : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ≥0∞) :
    (∃ w : (Fin k → ℝ) → Fin k → ℝ, Measurable w ∧
      (∀ t, ∑ i, w t i = 1) ∧
      ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes w) < B θ) ↔
    (∃ w : (Fin k → ℝ) → Fin k → ℝ, Measurable w ∧
      (∀ t, ∑ i, w t i = 1) ∧ (∀ t i, 0 ≤ w t i) ∧
      ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes w) < B θ) := by
  constructor
  · rintro ⟨w, hw, hunit, hcap⟩
    exact ⟨_root_.GD.N0072.d007614 ∘ w, _root_.GD.N0072.d007625.comp hw,
      fun t => _root_.GD.N0072.d007617 (w t) (hunit t),
      fun t i => _root_.GD.N0072.d007616 (w t) (hunit t) i,
      fun θ => (_root_.GD.N0072.d023445 sizes hn w hw hunit θ).trans_lt (hcap θ)⟩
  · rintro ⟨w, hw, hunit, _, hcap⟩
    exact ⟨w, hw, hunit, hcap⟩



theorem d023449
    (ν : Measure (Fin k → ℝ)) (v : Fin k → ℝ) (hv : ∀ i, 0 < v i)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1)
    (hfinite : (∫⁻ t, ENNReal.ofReal (_root_.GD.N0072.d007621 v (w t)) ∂ν) ≠ ⊤)
    (hneg : 0 < ν {t | ∃ i, w t i < 0}) :
    (∫⁻ t, ENNReal.ofReal (_root_.GD.N0072.d007621 v (_root_.GD.N0072.d007614 (w t))) ∂ν) <
      ∫⁻ t, ENNReal.ofReal (_root_.GD.N0072.d007621 v (w t)) ∂ν := by
  let F : (Fin k → ℝ) → ℝ := fun t => _root_.GD.N0072.d007621 v (_root_.GD.N0072.d007614 (w t))
  let G : (Fin k → ℝ) → ℝ := fun t => _root_.GD.N0072.d007621 v (w t)
  have hFm : Measurable F := (_root_.GD.N0072.d007626 v).comp (_root_.GD.N0072.d007625.comp hw)
  have hGm : Measurable G := (_root_.GD.N0072.d007626 v).comp hw
  have hFnn : ∀ t, 0 ≤ F t := fun t => _root_.GD.N0072.d007622 v _ (fun i => (hv i).le)
  have hGnn : ∀ t, 0 ≤ G t := fun t => _root_.GD.N0072.d007622 v _ (fun i => (hv i).le)
  have hle : ∀ t, F t ≤ G t := fun t => _root_.GD.N0072.d007623 v _ (fun i => (hv i).le) (hunit t)
  have hGi : Integrable G ν := by
    have h := integrable_toReal_of_lintegral_ne_top hGm.ennreal_ofReal.aemeasurable hfinite
    simpa only [ENNReal.toReal_ofReal (hGnn _)] using h
  have hFi : Integrable F ν := hGi.mono' hFm.aestronglyMeasurable
    (ae_of_all _ fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hFnn t)]; exact hle t)
  have hnot : ¬ F =ᵐ[ν] G := by
    intro hae
    have hz : ν {t | F t ≠ G t} = 0 := by simpa only [Filter.EventuallyEq, ae_iff] using hae
    apply hneg.ne'
    apply measure_mono_null _ hz
    intro t ht
    exact ne_of_lt (_root_.GD.N0072.d007624 v (w t) hv (hunit t) ht)
  have hstrict : (∫ t, F t ∂ν) < ∫ t, G t ∂ν :=
    lt_of_le_of_ne (integral_mono hFi hGi hle)
      (fun heq => hnot ((integral_eq_iff_of_ae_le hFi hGi (ae_of_all _ hle)).mp heq))
  change (∫⁻ t, ENNReal.ofReal (F t) ∂ν) < ∫⁻ t, ENNReal.ofReal (G t) ∂ν
  rw [← ofReal_integral_eq_lintegral_ofReal hFi (ae_of_all _ hFnn),
    ← ofReal_integral_eq_lintegral_ofReal hGi (ae_of_all _ hGnn)]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (integral_nonneg hFnn)).mpr hstrict




theorem d023450 (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (θ₀ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (hneg : 0 < _root_.GD.N0232.N0719.N0859.d010812 k sizes θ₀ {z | ∃ i, w (_root_.GD.N0232.N0719.N0900.d009103 k sizes z) i < 0})
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    0 < _root_.GD.N0232.N0719.N0933.d009301 k sizes θ.scale {t | ∃ i, w t i < 0} := by
  have hm : Measurable (_root_.GD.N0232.N0719.N0900.d009103 k sizes) := by fun_prop
  have hs : MeasurableSet {t | ∃ i, w t i < 0} := by
    simp only [setOf_exists]
    exact MeasurableSet.iUnion (fun i => measurableSet_lt ((measurable_pi_apply i).comp hw)
      measurable_const)
  rw [← _root_.GD.N0072.d023301 sizes hn θ, Measure.map_apply hm hs]
  change 0 < _root_.GD.N0232.N0719.N0859.d010812 k sizes θ {z | ∃ i, w (_root_.GD.N0232.N0719.N0900.d009103 k sizes z) i < 0}
  apply pos_iff_ne_zero.mpr
  intro hz
  exact hneg.ne' (_root_.GD.N0072.d023300 sizes θ₀ θ hz)



theorem d023451 (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1)
    (hfinite : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≠ ⊤)
    (θ₀ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (hneg : 0 < _root_.GD.N0232.N0719.N0859.d010812 k sizes θ₀ {z | ∃ i, w (_root_.GD.N0232.N0719.N0900.d009103 k sizes z) i < 0}) :
    ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes (_root_.GD.N0072.d007614 ∘ w)) <
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) := by
  intro θ
  rw [_root_.GD.N0072.d023297 sizes hn _ (_root_.GD.N0072.d007625.comp hw)
      (fun t => _root_.GD.N0072.d007617 (w t) (hunit t)),
    _root_.GD.N0072.d023297 sizes hn w hw hunit]
  have hv : ∀ i, 0 < θ.scale i ^ 2 / (sizes i : ℝ) := fun i =>
    div_pos (sq_pos_of_pos (θ.scale_pos i))
      (by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (hn i)))
  apply _root_.GD.N0072.d023449 _ _ hv w hw hunit
  · rw [← _root_.GD.N0072.d023297 sizes hn w hw hunit θ]
    exact hfinite θ
  · exact _root_.GD.N0072.d023450 sizes hn w hw θ₀ hneg θ





theorem d023452 (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1)
    (hfinite : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≠ ⊤)
    (θ₀ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (hneg : 0 < _root_.GD.N0232.N0719.N0859.d010812 k sizes θ₀ {z | ∃ i, w (_root_.GD.N0232.N0719.N0900.d009103 k sizes z) i < 0}) :
    ∃ w' : (Fin k → ℝ) → Fin k → ℝ,
      Measurable w' ∧ (∀ t, ∑ i, w' t i = 1) ∧ (∀ t i, 0 ≤ w' t i) ∧
      _root_.GD.N0072.d023291 sizes w' ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes ∧
      ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w') <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) := by
  have hstrict := _root_.GD.N0072.d023451 sizes hn w hw hunit hfinite θ₀ hneg
  exact ⟨_root_.GD.N0072.d007614 ∘ w, _root_.GD.N0072.d007625.comp hw,
    fun t => _root_.GD.N0072.d007617 (w t) (hunit t),
    fun t i => _root_.GD.N0072.d007616 (w t) (hunit t) i,
    _root_.GD.N0072.d023443 sizes hn w hw hunit, hstrict⟩




theorem d023453 (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1)
    (hfinite : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes w) ≠ ⊤)
    (θ₀ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (hneg : 0 < _root_.GD.N0232.N0719.N0859.d010812 k sizes θ₀ {z | ∃ i, w (fun j => _root_.GD.N0107.d009085 (z j)) i < 0}) :
    ∃ w' : (Fin k → ℝ) → Fin k → ℝ,
      Measurable w' ∧ (∀ t, ∑ i, w' t i = 1) ∧ (∀ t i, 0 ≤ w' t i) ∧
      _root_.GD.N0072.d023292 sizes w' ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes ∧
      ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes w') <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes w) := by
  have hn0 : ∀ i, 0 < sizes i := fun i => lt_of_lt_of_le (by decide : 0 < 2) (hn i)
  let wr : (Fin k → ℝ) → Fin k → ℝ := fun t => w (fun i => (sizes i : ℝ) * t i)
  have hwr : Measurable wr := by unfold wr; fun_prop
  have hwrunit : ∀ t, ∑ i, wr t i = 1 := fun t => hunit _
  have hraw : _root_.GD.N0072.d023291 sizes wr = _root_.GD.N0072.d023292 sizes w :=
    (_root_.GD.N0072.d023294 sizes hn0 w).symm
  have hrawq : _root_.GD.N0072.d023291 sizes (_root_.GD.N0072.d007614 ∘ wr) =
      _root_.GD.N0072.d023292 sizes (_root_.GD.N0072.d007614 ∘ w) := by
    simpa only [wr, Function.comp_def] using
      (_root_.GD.N0072.d023294 sizes hn0 (_root_.GD.N0072.d007614 ∘ w)).symm
  have hf : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes wr) ≠ ⊤ := by
    simpa only [hraw] using hfinite
  have hnr : 0 < _root_.GD.N0232.N0719.N0859.d010812 k sizes θ₀ {z | ∃ i, wr (_root_.GD.N0232.N0719.N0900.d009103 k sizes z) i < 0} := by
    simpa only [wr, _root_.GD.N0072.d023293 sizes hn0] using hneg
  have hs := _root_.GD.N0072.d023451 sizes hn wr hwr hwrunit hf θ₀ hnr
  have hqfinite := _root_.GD.N0072.d023443 sizes hn wr hwr hwrunit
  rw [hrawq] at hqfinite
  simp only [hrawq, hraw] at hs
  exact ⟨_root_.GD.N0072.d007614 ∘ w, _root_.GD.N0072.d007625.comp hw,
    fun t => _root_.GD.N0072.d007617 (w t) (hunit t),
    fun t i => _root_.GD.N0072.d007616 (w t) (hunit t) i, hqfinite, hs⟩

end
end GD.N0072

#print axioms _root_.GD.N0072.d023449
#print axioms _root_.GD.N0072.d023440
#print axioms _root_.GD.N0072.d023443
#print axioms _root_.GD.N0072.d023444
#print axioms _root_.GD.N0072.d023446
#print axioms _root_.GD.N0072.d023447
#print axioms _root_.GD.N0072.d023448
#print axioms _root_.GD.N0072.d023450
#print axioms _root_.GD.N0072.d023451
#print axioms _root_.GD.N0072.d023452
#print axioms _root_.GD.N0072.d023453
