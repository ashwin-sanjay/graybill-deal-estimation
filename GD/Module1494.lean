import GD.Module1485
import GD.Module0035

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace GD.N0223
noncomputable section
open _root_.GD.N0072 _root_.GD.N0230.N0665
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0933

variable {k : ℕ} [NeZero k]
def d023375 (v₀ v₁ : Fin k → ℝ) (L : ℝ) : Fin k → ℝ :=
  fun i => v₀ i + L * v₁ i

def d023376 (v₀ v₁ : Fin k → ℝ) (L : ℝ) : Fin k → ℝ :=
  _root_.GD.N0230.N0665.d000407 (_root_.GD.N0223.d023375 v₀ v₁ L)

theorem d023377 (v₀ v₁ : Fin k → ℝ) (hv₀ : ∀ i, 0 < v₀ i)
    (hv₁ : ∀ i, 0 ≤ v₁ i) {L : ℝ} (hL : 0 ≤ L) (i : Fin k) :
    0 < _root_.GD.N0223.d023375 v₀ v₁ L i :=
  add_pos_of_pos_of_nonneg (hv₀ i) (mul_nonneg hL (hv₁ i))

theorem d023378 (v₀ v₁ : Fin k → ℝ) (hv₀ : ∀ i, 0 < v₀ i)
    (hv₁ : ∀ i, 0 ≤ v₁ i) {L : ℝ} (hL : 0 ≤ L) :
    ∑ i, _root_.GD.N0223.d023376 v₀ v₁ L i = 1 :=
  _root_.GD.N0230.N0665.d000409 (_root_.GD.N0223.d023377 v₀ v₁ hv₀ hv₁ hL)

theorem d023379 (v₀ v₁ : Fin k → ℝ) (hv₀ : ∀ i, 0 < v₀ i)
    (hv₁ : ∀ i, 0 ≤ v₁ i) {L : ℝ} (hL : 0 ≤ L) (i : Fin k) :
    0 < _root_.GD.N0223.d023376 v₀ v₁ L i :=
  div_pos (inv_pos.mpr (_root_.GD.N0223.d023377 v₀ v₁ hv₀ hv₁ hL i))
    (_root_.GD.N0230.N0665.d000408 (_root_.GD.N0223.d023377 v₀ v₁ hv₀ hv₁ hL))

theorem d023380 (v₀ v₁ : Fin k → ℝ) (hv₀ : ∀ i, 0 < v₀ i)
    (hv₁ : ∀ i, 0 ≤ v₁ i) {L : ℝ} (hL : 0 ≤ L) (i : Fin k) :
    _root_.GD.N0223.d023376 v₀ v₁ L i ≤ 1 := by
  have h := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.univ) => (_root_.GD.N0223.d023379 v₀ v₁ hv₀ hv₁ hL j).le)
    (Finset.mem_univ i)
  rwa [_root_.GD.N0223.d023378 v₀ v₁ hv₀ hv₁ hL] at h

theorem d023381 (v₀ v₁ q : Fin k → ℝ) (L : ℝ) :
    _root_.GD.N0072.d007621 (_root_.GD.N0223.d023375 v₀ v₁ L) q = _root_.GD.N0072.d007621 v₀ q + L * _root_.GD.N0072.d007621 v₁ q := by
  simp only [_root_.GD.N0072.d007621, _root_.GD.N0223.d023375, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem d023382 (v₀ v₁ q : Fin k → ℝ) (hv₀ : ∀ i, 0 < v₀ i)
    (hv₁ : ∀ i, 0 ≤ v₁ i) {L : ℝ} (hL : 0 ≤ L) (hqunit : ∑ i, q i = 1) :
    _root_.GD.N0072.d007621 (_root_.GD.N0223.d023375 v₀ v₁ L) (_root_.GD.N0223.d023376 v₀ v₁ L) ≤
      _root_.GD.N0072.d007621 (_root_.GD.N0223.d023375 v₀ v₁ L) q := by
  simpa only [_root_.GD.N0072.d007621, _root_.GD.N0223.d023376, mul_comm] using
    (_root_.GD.N0230.N0665.d000411
      (_root_.GD.N0223.d023377 v₀ v₁ hv₀ hv₁ hL)).trans_le
      (_root_.GD.N0230.N0665.d000415 (_root_.GD.N0223.d023377 v₀ v₁ hv₀ hv₁ hL) hqunit)

theorem d023383 (v₀ v₁ q : Fin k → ℝ) (hv₀ : ∀ i, 0 < v₀ i)
    (hv₁ : ∀ i, 0 ≤ v₁ i) {L : ℝ} (hL : 0 ≤ L) (hqunit : ∑ i, q i = 1) :
    _root_.GD.N0072.d007621 (_root_.GD.N0223.d023375 v₀ v₁ L) q =
      _root_.GD.N0072.d007621 (_root_.GD.N0223.d023375 v₀ v₁ L) (_root_.GD.N0223.d023376 v₀ v₁ L) ↔
      q = _root_.GD.N0223.d023376 v₀ v₁ L := by
  have h := _root_.GD.N0230.N0665.d000416
    (_root_.GD.N0223.d023377 v₀ v₁ hv₀ hv₁ hL) hqunit
  rw [← _root_.GD.N0230.N0665.d000411
    (_root_.GD.N0223.d023377 v₀ v₁ hv₀ hv₁ hL)] at h
  simpa only [_root_.GD.N0072.d007621, _root_.GD.N0223.d023376, mul_comm] using h

def d023384 (μ ν : Measure (Fin k → ℝ)) (t : Fin k → ℝ) : ℝ :=
  (μ.rnDeriv ν t).toReal

theorem d023385 (v₀ v₁ : Fin k → ℝ) (hv₀ : ∀ i, 0 < v₀ i)
    (hv₁ : ∀ i, 0 ≤ v₁ i) (i j : Fin k)
    (hdet : v₀ i * v₁ j - v₀ j * v₁ i ≠ 0)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    _root_.GD.N0223.d023376 v₀ v₁ r = _root_.GD.N0223.d023376 v₀ v₁ s ↔ r = s := by
  constructor
  · intro heq
    obtain ⟨c, _, hscale⟩ := (_root_.GD.N0230.N0665.d000418
      (_root_.GD.N0223.d023377 v₀ v₁ hv₀ hv₁ hr)
      (_root_.GD.N0223.d023377 v₀ v₁ hv₀ hv₁ hs)).mp heq
    have hcross : _root_.GD.N0223.d023375 v₀ v₁ r i * _root_.GD.N0223.d023375 v₀ v₁ s j =
        _root_.GD.N0223.d023375 v₀ v₁ r j * _root_.GD.N0223.d023375 v₀ v₁ s i := by
      rw [hscale i, hscale j]
      ring
    have hfactor : (r - s) * (v₀ i * v₁ j - v₀ j * v₁ i) = 0 := by
      dsimp only [_root_.GD.N0223.d023375] at hcross
      nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hdet)
  · rintro rfl
    rfl

def d023386 (μ ν : Measure (Fin k → ℝ)) (v₀ v₁ : Fin k → ℝ)
    (t : Fin k → ℝ) : Fin k → ℝ := _root_.GD.N0223.d023376 v₀ v₁ (_root_.GD.N0223.d023384 μ ν t)

theorem d023387 (μ ν : Measure (Fin k → ℝ))
    (v₀ v₁ : Fin k → ℝ) (hv₀ : ∀ i, 0 < v₀ i) (hv₁ : ∀ i, 0 ≤ v₁ i)
    (i j : Fin k) (hdet : v₀ i * v₁ j - v₀ j * v₁ i ≠ 0)
    (t u : Fin k → ℝ) :
    _root_.GD.N0223.d023386 μ ν v₀ v₁ t = _root_.GD.N0223.d023386 μ ν v₀ v₁ u ↔
      _root_.GD.N0223.d023384 μ ν t = _root_.GD.N0223.d023384 μ ν u :=
  _root_.GD.N0223.d023385 v₀ v₁ hv₀ hv₁ i j hdet
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg

@[fun_prop] theorem d023388 (μ ν : Measure (Fin k → ℝ))
    (v₀ v₁ : Fin k → ℝ) : Measurable (_root_.GD.N0223.d023386 μ ν v₀ v₁) := by
  have hm := (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  unfold _root_.GD.N0223.d023386 _root_.GD.N0223.d023376 _root_.GD.N0230.N0665.d000407 _root_.GD.N0230.N0665.d000406 _root_.GD.N0223.d023375 _root_.GD.N0223.d023384
  fun_prop

theorem d023389 (μ ν : Measure (Fin k → ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (v₀ v₁ : Fin k → ℝ)
    (hv₀ : ∀ i, 0 ≤ v₀ i) (hv₁ : ∀ i, 0 ≤ v₁ i)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w) :
    (∫⁻ t, ENNReal.ofReal (_root_.GD.N0072.d007621 (_root_.GD.N0223.d023375 v₀ v₁ (_root_.GD.N0223.d023384 μ ν t)) (w t)) ∂ν) =
      (∫⁻ t, ENNReal.ofReal (_root_.GD.N0072.d007621 v₀ (w t)) ∂ν) +
      (∫⁻ t, ENNReal.ofReal (_root_.GD.N0072.d007621 v₁ (w t)) ∂μ) := by
  letI : μ.HaveLebesgueDecomposition ν :=
    Measure.haveLebesgueDecomposition_of_finiteMeasure (μ := μ) (ν := ν)
  have hm₀ : Measurable (fun t => ENNReal.ofReal (_root_.GD.N0072.d007621 v₀ (w t))) :=
    ((_root_.GD.N0072.d007626 v₀).comp hw).ennreal_ofReal
  have hm₁ : Measurable (fun t => ENNReal.ofReal (_root_.GD.N0072.d007621 v₁ (w t))) :=
    ((_root_.GD.N0072.d007626 v₁).comp hw).ennreal_ofReal
  calc
    _ = ∫⁻ t, ENNReal.ofReal (_root_.GD.N0072.d007621 v₀ (w t)) +
        μ.rnDeriv ν t * ENNReal.ofReal (_root_.GD.N0072.d007621 v₁ (w t)) ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [Measure.rnDeriv_ne_top μ ν] with t ht
      rw [_root_.GD.N0223.d023381]
      unfold _root_.GD.N0223.d023384
      rw [ENNReal.ofReal_add (_root_.GD.N0072.d007622 _ _ hv₀)
        (mul_nonneg ENNReal.toReal_nonneg (_root_.GD.N0072.d007622 _ _ hv₁)),
        ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      simp only [ENNReal.ofReal_toReal ht]
    _ = _ := by
      rw [lintegral_add_left hm₀, lintegral_rnDeriv_mul hμν hm₁.aemeasurable]

theorem d023390 (v p : Fin k → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hp : ∀ i, 0 ≤ p i) (hunit : ∑ i, p i = 1) : _root_.GD.N0072.d007621 v p ≤ ∑ i, v i := by
  apply Finset.sum_le_sum
  intro i _
  have hi : p i ≤ 1 := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hp j) (Finset.mem_univ i)
    rwa [hunit] at h
  have hs : p i ^ 2 ≤ 1 := by nlinarith [hp i]
  exact (mul_le_mul_of_nonneg_right hs (hv i)).trans_eq (one_mul _)

theorem d023391 (μ ν τ : Measure (Fin k → ℝ)) [IsFiniteMeasure τ]
    (v₀ v₁ v : Fin k → ℝ) (hv₀ : ∀ i, 0 < v₀ i)
    (hv₁ : ∀ i, 0 ≤ v₁ i) (hv : ∀ i, 0 ≤ v i) :
    (∫⁻ t, ENNReal.ofReal (_root_.GD.N0072.d007621 v (_root_.GD.N0223.d023386 μ ν v₀ v₁ t)) ∂τ) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (b := ∫⁻ _t, ENNReal.ofReal (∑ i, v i) ∂τ)
  · rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top τ Set.univ)
  · exact lintegral_mono (fun t => ENNReal.ofReal_le_ofReal (_root_.GD.N0223.d023390 _ _ hv
      (fun i => (_root_.GD.N0223.d023379 v₀ v₁ hv₀ hv₁ ENNReal.toReal_nonneg i).le)
      (_root_.GD.N0223.d023378 v₀ v₁ hv₀ hv₁ ENNReal.toReal_nonneg)))

theorem d023392
    (μ ν : Measure (Fin k → ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (v₀ v₁ : Fin k → ℝ)
    (hv₀ : ∀ i, 0 < v₀ i) (hv₁ : ∀ i, 0 ≤ v₁ i)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1)
    (h₀ : (∫⁻ t, ENNReal.ofReal (_root_.GD.N0072.d007621 v₀ (w t)) ∂ν) ≤
      ∫⁻ t, ENNReal.ofReal (_root_.GD.N0072.d007621 v₀ (_root_.GD.N0223.d023386 μ ν v₀ v₁ t)) ∂ν)
    (h₁ : (∫⁻ t, ENNReal.ofReal (_root_.GD.N0072.d007621 v₁ (w t)) ∂μ) ≤
      ∫⁻ t, ENNReal.ofReal (_root_.GD.N0072.d007621 v₁ (_root_.GD.N0223.d023386 μ ν v₀ v₁ t)) ∂μ) :
    w =ᵐ[ν] _root_.GD.N0223.d023386 μ ν v₀ v₁ := by
  let p := _root_.GD.N0223.d023386 μ ν v₀ v₁
  let A := fun t => _root_.GD.N0223.d023375 v₀ v₁ (_root_.GD.N0223.d023384 μ ν t)
  have hpm := _root_.GD.N0223.d023388 μ ν v₀ v₁
  have hdom : (∫⁻ t, ENNReal.ofReal (_root_.GD.N0072.d007621 (A t) (w t)) ∂ν) ≤
      ∫⁻ t, ENNReal.ofReal (_root_.GD.N0072.d007621 (A t) (p t)) ∂ν := by
    dsimp only [A, p]
    rw [_root_.GD.N0223.d023389 μ ν hμν v₀ v₁ (fun i => (hv₀ i).le) hv₁ w hw,
      _root_.GD.N0223.d023389 μ ν hμν v₀ v₁ (fun i => (hv₀ i).le) hv₁ _ hpm]
    exact add_le_add h₀ h₁
  have hfin : (∫⁻ t, ENNReal.ofReal (_root_.GD.N0072.d007621 (A t) (p t)) ∂ν) ≠ ⊤ := by
    dsimp only [A, p]
    rw [_root_.GD.N0223.d023389 μ ν hμν v₀ v₁ (fun i => (hv₀ i).le) hv₁ _ hpm]
    exact ENNReal.add_ne_top.mpr ⟨_root_.GD.N0223.d023391 μ ν ν v₀ v₁ v₀ hv₀ hv₁
      (fun i => (hv₀ i).le), _root_.GD.N0223.d023391 μ ν μ v₀ v₁ v₁ hv₀ hv₁ hv₁⟩
  have hle : (fun t => ENNReal.ofReal (_root_.GD.N0072.d007621 (A t) (p t))) ≤ᵐ[ν]
      (fun t => ENNReal.ofReal (_root_.GD.N0072.d007621 (A t) (w t))) :=
    ae_of_all _ (fun t => ENNReal.ofReal_le_ofReal
      (_root_.GD.N0223.d023382 v₀ v₁ (w t) hv₀ hv₁ ENNReal.toReal_nonneg (hunit t)))
  have hm : Measurable (fun t => ENNReal.ofReal (_root_.GD.N0072.d007621 (A t) (w t))) := by
    have hL := (Measure.measurable_rnDeriv μ ν).ennreal_toReal
    dsimp only [A]
    unfold _root_.GD.N0072.d007621 _root_.GD.N0223.d023375 _root_.GD.N0223.d023384
    fun_prop
  have heq := ae_eq_of_ae_le_of_lintegral_le hle hfin hm.aemeasurable hdom
  filter_upwards [heq] with t ht
  apply (_root_.GD.N0223.d023383 v₀ v₁ (w t) hv₀ hv₁
    ENNReal.toReal_nonneg (hunit t)).mp
  exact (ENNReal.ofReal_eq_ofReal_iff
    (_root_.GD.N0072.d007622 _ _ (fun i => (_root_.GD.N0223.d023377 v₀ v₁ hv₀ hv₁ ENNReal.toReal_nonneg i).le))
    (_root_.GD.N0072.d007622 _ _ (fun i => (_root_.GD.N0223.d023377 v₀ v₁ hv₀ hv₁ ENNReal.toReal_nonneg i).le))).mp ht.symm

def d023393 (sizes : Fin k → ℕ) (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) : ℝ :=
  θ.scale i ^ 2 / (sizes i : ℝ)

theorem d023394 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) : 0 < _root_.GD.N0223.d023393 sizes θ i :=
  div_pos (sq_pos_of_pos (θ.scale_pos i))
    (by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (hn i)))

def d023395 (sizes : Fin k → ℕ) (θ₀ θ₁ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    (Fin k → ℝ) → Fin k → ℝ :=
  _root_.GD.N0223.d023386 (_root_.GD.N0232.N0719.N0933.d009301 k sizes θ₁.scale)
    (_root_.GD.N0232.N0719.N0933.d009301 k sizes θ₀.scale)
    (_root_.GD.N0223.d023393 sizes θ₀) (_root_.GD.N0223.d023393 sizes θ₁)

@[fun_prop] theorem d023396 (sizes : Fin k → ℕ)
    (θ₀ θ₁ : _root_.GD.N0232.N0719.N0859.d010809 k) : Measurable (_root_.GD.N0223.d023395 sizes θ₀ θ₁) :=
  _root_.GD.N0223.d023388 _ _ _ _

theorem d023397 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (θ₀ θ₁ : _root_.GD.N0232.N0719.N0859.d010809 k) (t : Fin k → ℝ) :
    ∑ i, _root_.GD.N0223.d023395 sizes θ₀ θ₁ t i = 1 :=
  _root_.GD.N0223.d023378 _ _ (_root_.GD.N0223.d023394 sizes hn θ₀)
    (fun i => (_root_.GD.N0223.d023394 sizes hn θ₁ i).le) ENNReal.toReal_nonneg

theorem d023398 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (θ₀ θ₁ : _root_.GD.N0232.N0719.N0859.d010809 k) (t : Fin k → ℝ) (i : Fin k) :
    0 < _root_.GD.N0223.d023395 sizes θ₀ θ₁ t i :=
  _root_.GD.N0223.d023379 _ _ (_root_.GD.N0223.d023394 sizes hn θ₀)
    (fun j => (_root_.GD.N0223.d023394 sizes hn θ₁ j).le) ENNReal.toReal_nonneg i

theorem d023399 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (θ₀ θ₁ θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
      (_root_.GD.N0072.d023291 sizes (_root_.GD.N0223.d023395 sizes θ₀ θ₁)) ≠ ⊤ := by
  letI := _root_.GD.N0232.N0719.N0910.d010289 sizes hn θ.scale
  rw [_root_.GD.N0072.d023297 sizes hn _ (_root_.GD.N0223.d023396 sizes θ₀ θ₁)
    (_root_.GD.N0223.d023397 sizes hn θ₀ θ₁)]
  exact _root_.GD.N0223.d023391 _ _ _ _ _ _ (_root_.GD.N0223.d023394 sizes hn θ₀)
    (fun i => (_root_.GD.N0223.d023394 sizes hn θ₁ i).le)
    (fun i => (_root_.GD.N0223.d023394 sizes hn θ i).le)

theorem d023400 (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (θ₀ θ₁ : _root_.GD.N0232.N0719.N0859.d010809 k) (w : (Fin k → ℝ) → Fin k → ℝ)
    (hw : Measurable w) (hunit : ∀ t, ∑ i, w t i = 1)
    (h₀ : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ₀ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ₀
        (_root_.GD.N0072.d023291 sizes (_root_.GD.N0223.d023395 sizes θ₀ θ₁)))
    (h₁ : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ₁ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ₁
        (_root_.GD.N0072.d023291 sizes (_root_.GD.N0223.d023395 sizes θ₀ θ₁))) :
    w =ᵐ[_root_.GD.N0232.N0719.N0933.d009301 k sizes θ₀.scale] _root_.GD.N0223.d023395 sizes θ₀ θ₁ := by
  letI := _root_.GD.N0232.N0719.N0910.d010289 sizes hn θ₀.scale
  letI := _root_.GD.N0232.N0719.N0910.d010289 sizes hn θ₁.scale
  rw [_root_.GD.N0072.d023297 sizes hn w hw hunit,
    _root_.GD.N0072.d023297 sizes hn _ (_root_.GD.N0223.d023396 sizes θ₀ θ₁)
      (_root_.GD.N0223.d023397 sizes hn θ₀ θ₁)] at h₀ h₁
  exact _root_.GD.N0223.d023392 _ _
    (_root_.GD.N0002.d023309 sizes hn θ₁ θ₀)
    _ _ (_root_.GD.N0223.d023394 sizes hn θ₀)
    (fun i => (_root_.GD.N0223.d023394 sizes hn θ₁ i).le) w hw hunit h₀ h₁

theorem d023401 (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (θ₀ θ₁ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hunit : ∀ t, ∑ i, w t i = 1)
    (h₀ : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ₀ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ₀
        (_root_.GD.N0072.d023291 sizes (_root_.GD.N0223.d023395 sizes θ₀ θ₁)))
    (h₁ : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ₁ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ₁
        (_root_.GD.N0072.d023291 sizes (_root_.GD.N0223.d023395 sizes θ₀ θ₁)))
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) =
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
        (_root_.GD.N0072.d023291 sizes (_root_.GD.N0223.d023395 sizes θ₀ θ₁)) := by
  have hae := _root_.GD.N0223.d023400 sizes hn θ₀ θ₁ w hw hunit h₀ h₁
  have heq := (_root_.GD.N0002.d023309 sizes hn θ θ₀).ae_le hae
  rw [_root_.GD.N0072.d023297 sizes hn w hw hunit,
    _root_.GD.N0072.d023297 sizes hn _ (_root_.GD.N0223.d023396 sizes θ₀ θ₁)
      (_root_.GD.N0223.d023397 sizes hn θ₀ θ₁)]
  apply lintegral_congr_ae
  filter_upwards [heq] with t ht
  rw [ht]

theorem d023402 (sizes : Fin k → ℕ)
    (hn : ∀ i, 2 ≤ sizes i) (θ₀ θ₁ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    ¬ ∃ w : (Fin k → ℝ) → Fin k → ℝ, Measurable w ∧
      (∀ t, ∑ i, w t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
          (_root_.GD.N0072.d023291 sizes (_root_.GD.N0223.d023395 sizes θ₀ θ₁))) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
          (_root_.GD.N0072.d023291 sizes (_root_.GD.N0223.d023395 sizes θ₀ θ₁)) := by
  rintro ⟨w, hw, hunit, hdom, θ, hstrict⟩
  exact (ne_of_lt hstrict) (_root_.GD.N0223.d023401
    sizes hn θ₀ θ₁ w hw hunit (hdom θ₀) (hdom θ₁) θ)

#print axioms _root_.GD.N0223.d023383
#print axioms _root_.GD.N0223.d023385
#print axioms _root_.GD.N0223.d023387
#print axioms _root_.GD.N0223.d023389
#print axioms _root_.GD.N0223.d023391
#print axioms _root_.GD.N0223.d023392
#print axioms _root_.GD.N0223.d023399
#print axioms _root_.GD.N0223.d023400
#print axioms _root_.GD.N0223.d023401
#print axioms _root_.GD.N0223.d023402

end
end GD.N0223
