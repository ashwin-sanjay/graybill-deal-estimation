import GD.Module1467
import GD.Module1473

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace GD.N0101.N0412
noncomputable section
open _root_.GD.N0101.N0357 _root_.GD.N0101.N0350
open _root_.GD.N0213.N0523
open _root_.GD.N0213.N0495
open _root_.GD.N0232.N0719.N0954
open _root_.GD.N0230.N0665

variable {k : ℕ}

def d023276 (a : Fin k → ℝ) (ρ L : ℝ)
    (v t : Fin k → ℝ) : ℝ :=
  ∫ β, (∑ i, (β i)⁻¹ * v i ^ 2) * _root_.GD.N0213.N0495.d007174 L (∑ i, β i) ^ 2
    ∂_root_.GD.N0101.N0357.d023161 a ρ t

def d023277 (a : Fin k → ℝ) (ρ L : ℝ)
    (w : (Fin k → ℝ) → Fin k → ℝ) (t : Fin k → ℝ) : ℝ :=
  max 0 (_root_.GD.N0101.N0357.d023162 a ρ t *
    (_root_.GD.N0101.N0412.d023276 a ρ L (_root_.GD.N0230.N0665.d000407 t) t - _root_.GD.N0101.N0412.d023276 a ρ L (w t) t))

def d023278 (a : Fin k → ℝ) (ρ : ℝ) (i j : Fin k) : ℝ :=
  4 * (1 - ρ) * (((a i * (1 - ρ)) ^ 2)⁻¹ + ((a j * (1 - ρ)) ^ 2)⁻¹)

def d023279 (a : Fin k → ℝ) (ρ L : ℝ) (t : Fin k → ℝ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else
    _root_.GD.N0101.N0412.d023278 a ρ i j * _root_.GD.N0101.N0350.d023173 a ρ L i j t

theorem d023280 (a : Fin k → ℝ) (ρ L : ℝ)
    (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w) :
    AEStronglyMeasurable (fun t => _root_.GD.N0101.N0412.d023276 a ρ L (w t) t)
      (volume.restrict _root_.GD.N0101.N0357.d023158) := by
  let G : (Fin k → ℝ) × (Fin k → ℝ) → ℝ := fun z =>
    _root_.GD.N0232.N0719.N0954.d009343 (fun i => _root_.GD.N0213.N0523.d023144 (a i) ρ)
      (fun i => a i * z.1 i) z.2 *
        ((∑ i, (z.2 i)⁻¹ * w z.1 i ^ 2) * _root_.GD.N0213.N0495.d007174 L (∑ i, z.2 i) ^ 2)
  have hp : Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) =>
      _root_.GD.N0232.N0719.N0954.d009343 (fun i => _root_.GD.N0213.N0523.d023144 (a i) ρ)
        (fun i => a i * z.1 i) z.2) := by
    unfold _root_.GD.N0232.N0719.N0954.d009343
    apply Finset.measurable_prod
    intro i _
    unfold gammaPDFReal
    apply Measurable.ite
    · exact measurableSet_le measurable_const ((measurable_pi_apply i).comp measurable_snd)
    · fun_prop
    · exact measurable_const
  have hG : Measurable G := hp.mul (by dsimp only [_root_.GD.N0213.N0495.d007174]; fun_prop)
  have hm : Measurable (fun t => ∫ β, G (t, β)) :=
    hG.stronglyMeasurable.integral_prod_right'.measurable
  apply hm.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem _root_.GD.N0101.N0357.d023159] with t ht
  exact (_root_.GD.N0232.N0719.N0954.d009364
    (fun i => zero_lt_one.trans (_root_.GD.N0213.N0523.d023146 (ha i) hρ))
    (fun i => mul_pos (ha i) (ht i)) _).symm

theorem d023281 (a : Fin k → ℝ) (ρ L : ℝ)
    (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w) :
    AEStronglyMeasurable (_root_.GD.N0101.N0412.d023277 a ρ L w) (volume.restrict _root_.GD.N0101.N0357.d023158) := by
  have hp : Measurable (_root_.GD.N0230.N0665.d000407 : (Fin k → ℝ) → Fin k → ℝ) := by
    unfold _root_.GD.N0230.N0665.d000407 _root_.GD.N0230.N0665.d000406
    fun_prop
  have hg := (_root_.GD.N0101.N0350.d023177 a ρ).aestronglyMeasurable.mul
    ((_root_.GD.N0101.N0412.d023280 a ρ L ha hρ _ hp).sub
      (_root_.GD.N0101.N0412.d023280 a ρ L ha hρ w hw))
  exact (aemeasurable_const.max hg.aemeasurable).aestronglyMeasurable

theorem d023282 (a : Fin k → ℝ) {ρ : ℝ} (hρ : ρ < 1)
    (i j : Fin k) : 0 ≤ _root_.GD.N0101.N0412.d023278 a ρ i j := by
  unfold _root_.GD.N0101.N0412.d023278
  positivity

theorem d023283 (a : Fin k → ℝ) (ρ L : ℝ)
    (ha : ∀ i, 0 < a i) (hρ : ρ < 1) {t : Fin k → ℝ} (ht : t ∈ _root_.GD.N0101.N0357.d023158) :
    0 ≤ _root_.GD.N0101.N0412.d023279 a ρ L t := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (_root_.GD.N0101.N0412.d023282 a hρ i j)
      (_root_.GD.N0101.N0350.d023179 a ρ L ha hρ i j ht)



theorem d023284 {n : ℕ}
    (a t w : Fin (n + 1) → ℝ) (ha : ∀ i, 0 < a i) (ht : t ∈ _root_.GD.N0101.N0357.d023158)
    {ρ L : ℝ} (hρ : ρ < 1) (hL : 0 < L)
    (hw : ∀ i, w i ∈ Icc (0 : ℝ) 1) (hunit : ∑ i, w i = 1) :
    max 0 (_root_.GD.N0101.N0357.d023162 a ρ t *
      (_root_.GD.N0101.N0412.d023276 a ρ L (_root_.GD.N0230.N0665.d000407 t) t - _root_.GD.N0101.N0412.d023276 a ρ L w t)) ≤
      _root_.GD.N0101.N0412.d023279 a ρ L t := by
  apply max_le
  · exact _root_.GD.N0101.N0412.d023283 a ρ L ha hρ ht
  · have h := _root_.GD.N0101.N0348.d023096
      a t w ha ht hρ hL hw hunit
    have he := mul_le_mul_of_nonneg_left h (_root_.GD.N0101.N0357.d023163 a ρ ha hρ ht).le
    apply he.trans_eq
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j
    · simp only [if_pos hij, mul_zero]
    · simp only [if_neg hij]
      let D := _root_.GD.N0101.N0350.d023172 a ρ L t
      change _root_.GD.N0101.N0357.d023162 a ρ t *
        (4 * (D / (a i * (1 - ρ)) ^ 2 + D / (a j * (1 - ρ)) ^ 2) /
          ((1 - ρ)⁻¹ * (t i + t j))) =
        (4 * (1 - ρ) * (((a i * (1 - ρ)) ^ 2)⁻¹ + ((a j * (1 - ρ)) ^ 2)⁻¹)) *
          (_root_.GD.N0101.N0357.d023162 a ρ t * D / (t i + t j))
      field_simp [(sub_pos.mpr hρ).ne', (ha i).ne', (ha j).ne',
        (add_pos (ht i) (ht j)).ne']

theorem d023285 (a : Fin k → ℝ) (ρ : ℝ)
    (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * a i) (hsum : ∑ i, (1 - ρ * a i) = 1)
    (hab : ∀ i j, i ≠ j → 1 < a i + a j) {L : ℝ} (hL : 0 < L) :
    Integrable (_root_.GD.N0101.N0412.d023279 a ρ L) (volume.restrict _root_.GD.N0101.N0357.d023158) := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  by_cases hij : i = j
  · simp only [if_pos hij]
    exact integrable_zero _ _ _
  · simpa only [if_neg hij] using
      (_root_.GD.N0101.N0350.d023183 a ρ ha hρ hα hsum i j hij (hab i j hij) hL).const_mul
        (_root_.GD.N0101.N0412.d023278 a ρ i j)

theorem d023286 (a : Fin k → ℝ) (ρ : ℝ)
    (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * a i) (hsum : ∑ i, (1 - ρ * a i) = 1)
    (hab : ∀ i j, i ≠ j → 1 < a i + a j) {L : ℝ} (hL : 0 < L) :
    (∫ t in _root_.GD.N0101.N0357.d023158, _root_.GD.N0101.N0412.d023279 a ρ L t) =
      ∑ i, ∑ j, if i = j then 0 else _root_.GD.N0101.N0412.d023278 a ρ i j *
        (∫ t in _root_.GD.N0101.N0357.d023158, _root_.GD.N0101.N0350.d023173 a ρ L i j t) := by
  have hi (i j : Fin k) : Integrable (fun t => if i = j then 0 else
      _root_.GD.N0101.N0412.d023278 a ρ i j * _root_.GD.N0101.N0350.d023173 a ρ L i j t) (volume.restrict _root_.GD.N0101.N0357.d023158) := by
    by_cases hij : i = j
    · simp only [if_pos hij]
      exact integrable_zero _ _ _
    · simpa only [if_neg hij] using
        (_root_.GD.N0101.N0350.d023183 a ρ ha hρ hα hsum i j hij (hab i j hij) hL).const_mul
          (_root_.GD.N0101.N0412.d023278 a ρ i j)
  unfold _root_.GD.N0101.N0412.d023279
  rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j <;> simp only [hij, ite_true, ite_false, integral_zero, integral_const_mul]

theorem d023287 (a : Fin k → ℝ) (ρ : ℝ)
    (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * a i) (hsum : ∑ i, (1 - ρ * a i) = 1)
    (hab : ∀ i j, i ≠ j → 1 < a i + a j) :
    Tendsto (fun m : ℕ => ∫ t in _root_.GD.N0101.N0357.d023158,
      _root_.GD.N0101.N0412.d023279 a ρ ((m : ℝ) + 1) t) atTop (𝓝 0) := by
  have heq (m : ℕ) := _root_.GD.N0101.N0412.d023286 a ρ ha hρ hα hsum hab
    (L := (m : ℝ) + 1) (by positivity)
  simp_rw [heq]
  have hpair (i j : Fin k) : Tendsto (fun m : ℕ => if i = j then (0 : ℝ) else
      _root_.GD.N0101.N0412.d023278 a ρ i j * ∫ t in _root_.GD.N0101.N0357.d023158, _root_.GD.N0101.N0350.d023173 a ρ ((m : ℝ) + 1) i j t)
      atTop (𝓝 0) := by
    by_cases hij : i = j
    · simp only [if_pos hij]
      exact tendsto_const_nhds
    · simpa only [if_neg hij, mul_zero] using
        (_root_.GD.N0101.N0350.d023185 a ρ ha hρ hα hsum i j hij (hab i j hij)).const_mul
          (_root_.GD.N0101.N0412.d023278 a ρ i j)
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ => hpair i j))

theorem d023288 {n : ℕ}
    (a : Fin (n + 1) → ℝ) (ρ : ℝ) (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * a i) (hsum : ∑ i, (1 - ρ * a i) = 1)
    (hab : ∀ i j, i ≠ j → 1 < a i + a j)
    (w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) (hwm : Measurable w)
    (hw : ∀ t i, w t i ∈ Icc (0 : ℝ) 1) (hunit : ∀ t, ∑ i, w t i = 1)
    {L : ℝ} (hL : 0 < L) :
    Integrable (_root_.GD.N0101.N0412.d023277 a ρ L w) (volume.restrict _root_.GD.N0101.N0357.d023158) := by
  apply (_root_.GD.N0101.N0412.d023285 a ρ ha hρ hα hsum hab hL).mono'
    (_root_.GD.N0101.N0412.d023281 a ρ L ha hρ w hwm)
  filter_upwards [ae_restrict_mem _root_.GD.N0101.N0357.d023159] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
  exact _root_.GD.N0101.N0412.d023284 a t (w t) ha ht hρ hL (hw t) (hunit t)

theorem d023289 {n : ℕ}
    (a : Fin (n + 1) → ℝ) (ρ : ℝ) (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * a i) (hsum : ∑ i, (1 - ρ * a i) = 1)
    (hab : ∀ i j, i ≠ j → 1 < a i + a j)
    (w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) (hwm : Measurable w)
    (hw : ∀ t i, w t i ∈ Icc (0 : ℝ) 1) (hunit : ∀ t, ∑ i, w t i = 1)
    {L : ℝ} (hL : 0 < L) :
    (∫ t in _root_.GD.N0101.N0357.d023158, _root_.GD.N0101.N0412.d023277 a ρ L w t) ≤
      ∑ i, ∑ j, if i = j then 0 else _root_.GD.N0101.N0412.d023278 a ρ i j *
        (∫ t in _root_.GD.N0101.N0357.d023158, _root_.GD.N0101.N0350.d023173 a ρ L i j t) := by
  rw [← _root_.GD.N0101.N0412.d023286 a ρ ha hρ hα hsum hab hL]
  apply integral_mono_ae
    (_root_.GD.N0101.N0412.d023288 a ρ ha hρ hα hsum hab w hwm hw hunit hL)
    (_root_.GD.N0101.N0412.d023285 a ρ ha hρ hα hsum hab hL)
  filter_upwards [ae_restrict_mem _root_.GD.N0101.N0357.d023159] with t ht
  exact _root_.GD.N0101.N0412.d023284 a t (w t) ha ht hρ hL (hw t) (hunit t)



theorem d023290 {n : ℕ}
    (a : Fin (n + 1) → ℝ) (ρ : ℝ) (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (hα : ∀ i, 0 < 1 - ρ * a i) (hsum : ∑ i, (1 - ρ * a i) = 1)
    (hab : ∀ i j, i ≠ j → 1 < a i + a j)
    (w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) (hwm : Measurable w)
    (hw : ∀ t i, w t i ∈ Icc (0 : ℝ) 1) (hunit : ∀ t, ∑ i, w t i = 1) :
    Tendsto (fun m : ℕ => ∫ t in _root_.GD.N0101.N0357.d023158,
      _root_.GD.N0101.N0412.d023277 a ρ ((m : ℝ) + 1) w t) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg (fun _ => le_max_left _ _))
    (Eventually.of_forall fun m : ℕ => ?_)
    (_root_.GD.N0101.N0412.d023287 a ρ ha hρ hα hsum hab)
  apply integral_mono_ae
    (_root_.GD.N0101.N0412.d023288 a ρ ha hρ hα hsum hab w hwm hw hunit (by positivity))
    (_root_.GD.N0101.N0412.d023285 a ρ ha hρ hα hsum hab (by positivity))
  filter_upwards [ae_restrict_mem _root_.GD.N0101.N0357.d023159] with t ht
  exact _root_.GD.N0101.N0412.d023284 a t (w t) ha ht hρ (by positivity) (hw t) (hunit t)

end
end GD.N0101.N0412

#print axioms _root_.GD.N0101.N0412.d023280
#print axioms _root_.GD.N0101.N0412.d023284
#print axioms _root_.GD.N0101.N0412.d023285
#print axioms _root_.GD.N0101.N0412.d023286
#print axioms _root_.GD.N0101.N0412.d023287
#print axioms _root_.GD.N0101.N0412.d023288
#print axioms _root_.GD.N0101.N0412.d023289
#print axioms _root_.GD.N0101.N0412.d023290
