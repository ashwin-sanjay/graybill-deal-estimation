import GD.Module1484

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

namespace GD.N0002
noncomputable section
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0933 _root_.GD.N0232.N0719.N0900
open _root_.GD.N0072

variable {k : ℕ}



theorem d023302 (p q : Fin k → ℝ)
    (hp : ∀ i, 0 < p i) (hpunit : ∑ i, p i = 1) (hqunit : ∑ i, q i = 1) :
    _root_.GD.N0072.d007621 (fun i => (p i)⁻¹) q =
      1 + ∑ i, (q i - p i) ^ 2 / p i := by
  have hpoint (i : Fin k) :
      q i ^ 2 * (p i)⁻¹ = (q i - p i) ^ 2 / p i + 2 * q i - p i := by
    field_simp [(hp i).ne']
    ring
  unfold _root_.GD.N0072.d007621
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    hpunit, hqunit]
  ring

theorem d023303 (p q : Fin k → ℝ)
    (hp : ∀ i, 0 < p i) (hpunit : ∑ i, p i = 1) (hqunit : ∑ i, q i = 1) :
    1 ≤ _root_.GD.N0072.d007621 (fun i => (p i)⁻¹) q := by
  rw [_root_.GD.N0002.d023302 p q hp hpunit hqunit]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ =>
    div_nonneg (sq_nonneg _) (hp i).le))

theorem d023304 (p q : Fin k → ℝ)
    (hp : ∀ i, 0 < p i) (hpunit : ∑ i, p i = 1) (hqunit : ∑ i, q i = 1) :
    _root_.GD.N0072.d007621 (fun i => (p i)⁻¹) q = 1 ↔ q = p := by
  constructor
  · intro heq
    have hz : ∑ i, (q i - p i) ^ 2 / p i = 0 := by
      rw [_root_.GD.N0002.d023302 p q hp hpunit hqunit] at heq
      linarith
    have hpoint := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) => div_nonneg (sq_nonneg (q i - p i)) (hp i).le)).mp hz
    funext i
    have hsq : (q i - p i) ^ 2 = 0 :=
      (div_eq_zero_iff.mp (hpoint i (Finset.mem_univ i))).resolve_right (hp i).ne'
    nlinarith [sq_nonneg (q i - p i)]
  · intro hqp
    subst q
    rw [_root_.GD.N0002.d023302 p p hp hpunit hpunit]
    simp


theorem d023305 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (p : Fin k → ℝ) (hpunit : ∑ i, p i = 1) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes (fun _ => p)) =
      ENNReal.ofReal (_root_.GD.N0072.d007621 (fun i => θ.scale i ^ 2 / (sizes i : ℝ)) p) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009301 k sizes θ.scale) :=
    _root_.GD.N0232.N0719.N0910.d010289 sizes hn _
  rw [_root_.GD.N0072.d023297 sizes hn (fun _ => p) measurable_const (fun _ => hpunit)]
  simp


def d023306 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (p : Fin k → ℝ) (hp : ∀ i, 0 < p i) : _root_.GD.N0232.N0719.N0859.d010809 k where
  location := 0
  scale := fun i => Real.sqrt ((sizes i : ℝ) / p i)
  scale_pos := fun i => Real.sqrt_pos.mpr (div_pos
    (by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (hn i))) (hp i))

theorem d023307 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (p : Fin k → ℝ) (hp : ∀ i, 0 < p i) (i : Fin k) :
    (_root_.GD.N0002.d023306 sizes hn p hp).scale i ^ 2 / (sizes i : ℝ) = (p i)⁻¹ := by
  have hnpos : (0 : ℝ) < sizes i := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (hn i))
  simp only [_root_.GD.N0002.d023306, Real.sq_sqrt (div_nonneg hnpos.le (hp i).le)]
  field_simp [hnpos.ne']



theorem d023308 (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (p : Fin k → ℝ) (hp : ∀ i, 0 < p i)
    (hpunit : ∑ i, p i = 1) (w : (Fin k → ℝ) → Fin k → ℝ)
    (hw : Measurable w) (hunit : ∀ t, ∑ i, w t i = 1)
    (hdom : _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0002.d023306 sizes hn p hp)
        (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0002.d023306 sizes hn p hp)
        (_root_.GD.N0072.d023291 sizes (fun _ => p))) :
    w =ᵐ[_root_.GD.N0232.N0719.N0933.d009301 k sizes (_root_.GD.N0002.d023306 sizes hn p hp).scale]
      fun _ => p := by
  let ν := _root_.GD.N0232.N0719.N0933.d009301 k sizes (_root_.GD.N0002.d023306 sizes hn p hp).scale
  letI : IsProbabilityMeasure ν :=
    _root_.GD.N0232.N0719.N0910.d010289 sizes hn _
  rw [_root_.GD.N0072.d023297 sizes hn w hw hunit,
    _root_.GD.N0072.d023297 sizes hn (fun _ => p) measurable_const (fun _ => hpunit)] at hdom
  simp_rw [_root_.GD.N0002.d023307 sizes hn p hp] at hdom
  have hbase : _root_.GD.N0072.d007621 (fun i => (p i)⁻¹) p = 1 :=
    (_root_.GD.N0002.d023304 p p hp hpunit hpunit).mpr rfl
  rw [hbase] at hdom
  have hle : (fun _ => ENNReal.ofReal 1) ≤ᵐ[ν]
      (fun t => ENNReal.ofReal (_root_.GD.N0072.d007621 (fun i => (p i)⁻¹) (w t))) :=
    ae_of_all _ (fun t => ENNReal.ofReal_le_ofReal (_root_.GD.N0002.d023303 p (w t) hp hpunit (hunit t)))
  have heq := ae_eq_of_ae_le_of_lintegral_le hle (by simp)
    (((_root_.GD.N0072.d007626 _).comp hw).ennreal_ofReal.aemeasurable) hdom
  filter_upwards [heq] with t ht
  apply (_root_.GD.N0002.d023304 p (w t) hp hpunit (hunit t)).mp
  exact (ENNReal.ofReal_eq_ofReal_iff
    (zero_le_one.trans (_root_.GD.N0002.d023303 p (w t) hp hpunit (hunit t))) zero_le_one).mp ht.symm



theorem d023309 (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (θ η : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0933.d009301 k sizes θ.scale ≪ _root_.GD.N0232.N0719.N0933.d009301 k sizes η.scale := by
  rw [← _root_.GD.N0072.d023301 sizes hn θ, ← _root_.GD.N0072.d023301 sizes hn η]
  exact (_root_.GD.N0072.d023300 sizes θ η).map (by fun_prop)




theorem d023310 (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (p : Fin k → ℝ) (hp : ∀ i, 0 < p i)
    (hpunit : ∑ i, p i = 1) (w : (Fin k → ℝ) → Fin k → ℝ)
    (hw : Measurable w) (hunit : ∀ t, ∑ i, w t i = 1)
    (hdom : _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0002.d023306 sizes hn p hp)
        (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0002.d023306 sizes hn p hp)
        (_root_.GD.N0072.d023291 sizes (fun _ => p))) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) =
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes (fun _ => p)) := by
  have hae := _root_.GD.N0002.d023308 sizes hn p hp hpunit w hw hunit hdom
  have heq := (_root_.GD.N0002.d023309 sizes hn θ _).ae_le hae
  rw [_root_.GD.N0072.d023297 sizes hn w hw hunit,
    _root_.GD.N0072.d023297 sizes hn (fun _ => p) measurable_const (fun _ => hpunit)]
  apply lintegral_congr_ae
  filter_upwards [heq] with t ht
  rw [ht]

theorem d023311 (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (p : Fin k → ℝ) (hp : ∀ i, 0 < p i)
    (hpunit : ∑ i, p i = 1) :
    ¬ ∃ w : (Fin k → ℝ) → Fin k → ℝ, Measurable w ∧
      (∀ t, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes (fun _ => p))) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes (fun _ => p)) := by
  rintro ⟨w, hw, hunit, hdom, θ, hstrict⟩
  exact (ne_of_lt hstrict) (_root_.GD.N0002.d023310
    sizes hn p hp hpunit w hw hunit (hdom _) θ)

theorem d023312 (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (p : Fin k → ℝ) (hp : ∀ i, 0 < p i)
    (hpunit : ∑ i, p i = 1) :
    ¬ ∃ w : (Fin k → ℝ) → Fin k → ℝ, Measurable w ∧
      (∀ t, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes (fun _ => p))) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes w) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023292 sizes (fun _ => p)) := by
  rintro ⟨w, hw, hunit, hdom, θ, hstrict⟩
  have hn0 : ∀ i, 0 < sizes i := fun i =>
    lt_of_lt_of_le (by decide : 0 < 2) (hn i)
  simp_rw [_root_.GD.N0072.d023294 sizes hn0] at hdom hstrict
  apply _root_.GD.N0002.d023311 sizes hn p hp hpunit
  refine ⟨(fun t => w (fun i => (sizes i : ℝ) * t i)), ?_, fun t => hunit _, hdom, θ, hstrict⟩
  fun_prop

#print axioms _root_.GD.N0002.d023302
#print axioms _root_.GD.N0002.d023304
#print axioms _root_.GD.N0002.d023305
#print axioms _root_.GD.N0002.d023307
#print axioms _root_.GD.N0002.d023308
#print axioms _root_.GD.N0002.d023309
#print axioms _root_.GD.N0002.d023310
#print axioms _root_.GD.N0002.d023311
#print axioms _root_.GD.N0002.d023312

end
end GD.N0002
