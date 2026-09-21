import GD.Module1471
import GD.Module0538
import GD.Module1679

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace GD.N0213.N0516
noncomputable section
open _root_.GD.N0213.N0523 _root_.GD.N0213.N0522

variable {k : ℕ}

def d028396 (shape rate x : Fin k → ℝ) : ℝ≥0∞ :=
  ∏ i, gammaPDF (shape i) (rate i) (x i)

def d028397 (a : Fin k → ℝ) (ρ : ℝ) (β : Fin k → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (_root_.GD.N0213.N0522.d008019 (fun i => 1 - ρ * a i) β)

def d028398 (a β t : Fin k → ℝ) : ℝ≥0∞ :=
  _root_.GD.N0213.N0516.d028396 a (fun i => a i * β i) t

def d028399 (a : Fin k → ℝ) (ρ : ℝ) (t β : Fin k → ℝ) : ℝ≥0∞ :=
  _root_.GD.N0213.N0516.d028396 (fun i => _root_.GD.N0213.N0523.d023144 (a i) ρ) (fun i => a i * t i) β

def d028400 (a : Fin k → ℝ) (ρ : ℝ) (t : Fin k → ℝ) : ℝ≥0∞ :=
  if ∀ i, 0 < t i then ∏ i, ENNReal.ofReal (_root_.GD.N0213.N0523.d023145 (a i) ρ (t i)) else 0

@[fun_prop] theorem d028401 (a : Fin k → ℝ) (ρ : ℝ) :
    Measurable (_root_.GD.N0213.N0516.d028397 a ρ) := (_root_.GD.N0213.N0522.d008022 _).ennreal_ofReal

@[fun_prop] theorem d028402 (a : Fin k → ℝ) :
    Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) => _root_.GD.N0213.N0516.d028398 a z.1 z.2) := by
  unfold _root_.GD.N0213.N0516.d028398 _root_.GD.N0213.N0516.d028396
  fun_prop

@[fun_prop] theorem d028403 (a : Fin k → ℝ) (ρ : ℝ) :
    Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) => _root_.GD.N0213.N0516.d028399 a ρ z.1 z.2) := by
  unfold _root_.GD.N0213.N0516.d028399 _root_.GD.N0213.N0516.d028396
  fun_prop

@[fun_prop] theorem d028404 (a : Fin k → ℝ) (ρ : ℝ) :
    Measurable (_root_.GD.N0213.N0516.d028400 a ρ) := by
  unfold _root_.GD.N0213.N0516.d028400
  apply Measurable.ite
  · simp only [setOf_forall]
    exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)
  · unfold _root_.GD.N0213.N0523.d023145
    fun_prop
  · fun_prop

theorem d028405 (shape rate : Fin k → ℝ) :
    (Measure.pi fun i => gammaMeasure (shape i) (rate i)) =
      (volume : Measure (Fin k → ℝ)).withDensity (_root_.GD.N0213.N0516.d028396 shape rate) := by
  unfold _root_.GD.N0213.N0516.d028396 gammaMeasure
  letI (i : Fin k) : SigmaFinite (volume.withDensity (gammaPDF (shape i) (rate i))) := by
    unfold gammaPDF
    infer_instance
  simpa only [← volume_pi] using _root_.GD.N0089.d006088
    (fun _ : Fin k => (volume : Measure ℝ)) (fun i => gammaPDF (shape i) (rate i))
    (fun i => (measurable_gammaPDFReal (shape i) (rate i)).ennreal_ofReal)

theorem d028406 (a β : Fin k → ℝ) (ρ : ℝ) (hβ : ∀ i, 0 < β i) :
    _root_.GD.N0213.N0516.d028397 a ρ β = ∏ i, ENNReal.ofReal (β i ^ (-ρ * a i)) := by
  unfold _root_.GD.N0213.N0516.d028397 _root_.GD.N0213.N0522.d008019
  rw [if_pos hβ, ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg (hβ i).le _)]
  apply Finset.prod_congr rfl
  intro i _
  congr 2
  ring

theorem d028407 {a r x : ℝ} (ha : 1 < a) (hx : x ≤ 0) :
    gammaPDF a r x = 0 := by
  by_cases hx0 : x = 0
  · subst x
    simp [gammaPDF, gammaPDFReal, Real.zero_rpow (show a - 1 ≠ 0 by linarith)]
  · simp [gammaPDF, gammaPDFReal, not_le.mpr (lt_of_le_of_ne hx hx0)]

theorem d028408 {a ρ t β : ℝ}
    (ha : 0 < a) (hρ : ρ < 1) (ht : 0 < t) (hβ : 0 < β) :
    ENNReal.ofReal (β ^ (-ρ * a)) * gammaPDF a (a * β) t =
      ENNReal.ofReal (_root_.GD.N0213.N0523.d023145 a ρ t) * gammaPDF (_root_.GD.N0213.N0523.d023144 a ρ) (a * t) β := by
  unfold gammaPDF
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hβ.le _),
    ← ENNReal.ofReal_mul' (gammaPDFReal_nonneg
      (lt_trans zero_lt_one (_root_.GD.N0213.N0523.d023146 ha hρ)) (mul_pos ha ht) β)]
  congr 1
  simpa only [mul_comm] using _root_.GD.N0213.N0523.d023147 ha hρ ht hβ

theorem d028409 (a : Fin k → ℝ) (ρ : ℝ)
    (ha : ∀ i, 0 < a i) (hρ : ρ < 1) (t β : Fin k → ℝ)
    (ht0 : ∀ i, t i ≠ 0) :
    _root_.GD.N0213.N0516.d028397 a ρ β * _root_.GD.N0213.N0516.d028398 a β t =
      _root_.GD.N0213.N0516.d028400 a ρ t * _root_.GD.N0213.N0516.d028399 a ρ t β := by
  classical
  by_cases ht : ∀ i, 0 < t i
  · by_cases hβ : ∀ i, 0 < β i
    · rw [_root_.GD.N0213.N0516.d028406 a β ρ hβ]
      unfold _root_.GD.N0213.N0516.d028398 _root_.GD.N0213.N0516.d028399 _root_.GD.N0213.N0516.d028396 _root_.GD.N0213.N0516.d028400
      rw [if_pos ht, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => _root_.GD.N0213.N0516.d028408 (ha i) hρ (ht i) (hβ i))
    · have hp : _root_.GD.N0213.N0516.d028397 a ρ β = 0 := by simp [_root_.GD.N0213.N0516.d028397, _root_.GD.N0213.N0522.d008019, hβ]
      have hpost : _root_.GD.N0213.N0516.d028399 a ρ t β = 0 := by
        unfold _root_.GD.N0213.N0516.d028399 _root_.GD.N0213.N0516.d028396
        push Not at hβ
        obtain ⟨i, hi⟩ := hβ
        exact Finset.prod_eq_zero (Finset.mem_univ i)
          (_root_.GD.N0213.N0516.d028407 (_root_.GD.N0213.N0523.d023146 (ha i) hρ) hi)
      rw [hp, hpost, zero_mul, mul_zero]
  · have he : _root_.GD.N0213.N0516.d028400 a ρ t = 0 := by simp [_root_.GD.N0213.N0516.d028400, ht]
    have hsample : _root_.GD.N0213.N0516.d028398 a β t = 0 := by
      unfold _root_.GD.N0213.N0516.d028398 _root_.GD.N0213.N0516.d028396
      push Not at ht
      obtain ⟨i, hi⟩ := ht
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [gammaPDF, gammaPDFReal, not_le.mpr (lt_of_le_of_ne hi (ht0 i))]
    rw [he, hsample, zero_mul, mul_zero]

theorem d028410 (a : Fin k → ℝ) (ρ : ℝ)
    (ha : ∀ i, 0 < a i) (hρ : ρ < 1) :
    ∀ᵐ t : Fin k → ℝ ∂volume, ∀ β,
      _root_.GD.N0213.N0516.d028397 a ρ β * _root_.GD.N0213.N0516.d028398 a β t =
        _root_.GD.N0213.N0516.d028400 a ρ t * _root_.GD.N0213.N0516.d028399 a ρ t β := by
  have ht : ∀ᵐ t : Fin k → ℝ ∂volume, ∀ i, t i ≠ 0 := by
    rw [ae_all_iff]
    intro i
    simpa only [← volume_pi] using Measure.ae_eval_ne
      (fun _ : Fin k => (volume : Measure ℝ)) i 0
  filter_upwards [ht] with t ht
  exact fun β => _root_.GD.N0213.N0516.d028409 a ρ ha hρ t β ht

def d028411 (a β : Fin k → ℝ) : Measure (Fin k → ℝ) :=
  Measure.pi fun i => gammaMeasure (a i) (a i * β i)

def d028412 (a : Fin k → ℝ) (ρ : ℝ) (t : Fin k → ℝ) : Measure (Fin k → ℝ) :=
  Measure.pi fun i => gammaMeasure (_root_.GD.N0213.N0523.d023144 (a i) ρ) (a i * t i)

def d028413 (a : Fin k → ℝ) (ρ : ℝ) : Measure (Fin k → ℝ) :=
  volume.withDensity (_root_.GD.N0213.N0516.d028400 a ρ)

theorem d028414 (a β : Fin k → ℝ) :
    _root_.GD.N0213.N0516.d028411 a β = (volume : Measure (Fin k → ℝ)).withDensity (_root_.GD.N0213.N0516.d028398 a β) :=
  _root_.GD.N0213.N0516.d028405 a (fun i => a i * β i)

theorem d028415 (a : Fin k → ℝ) (ρ : ℝ) (t : Fin k → ℝ) :
    _root_.GD.N0213.N0516.d028412 a ρ t =
      (volume : Measure (Fin k → ℝ)).withDensity (_root_.GD.N0213.N0516.d028399 a ρ t) :=
  _root_.GD.N0213.N0516.d028405 (fun i => _root_.GD.N0213.N0523.d023144 (a i) ρ) (fun i => a i * t i)

theorem d028416 (a : Fin k → ℝ) (ρ : ℝ)
    (ha : ∀ i, 0 < a i) (hρ : ρ < 1)
    (F : (Fin k → ℝ) → (Fin k → ℝ) → ℝ≥0∞)
    (hF : Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) => F z.1 z.2)) :
    (∫⁻ β, ∫⁻ t, F β t ∂_root_.GD.N0213.N0516.d028411 a β ∂_root_.GD.N0213.N0522.d008020 (fun i => 1 - ρ * a i)) =
      ∫⁻ t, ∫⁻ β, F β t ∂_root_.GD.N0213.N0516.d028412 a ρ t ∂_root_.GD.N0213.N0516.d028413 a ρ := by
  have hleft :
      (∫⁻ β, ∫⁻ t, F β t ∂_root_.GD.N0213.N0516.d028411 a β ∂_root_.GD.N0213.N0522.d008020 (fun i => 1 - ρ * a i)) =
        ∫⁻ β, ∫⁻ t, _root_.GD.N0213.N0516.d028397 a ρ β * _root_.GD.N0213.N0516.d028398 a β t * F β t := by
    calc
      _ = ∫⁻ β, (∫⁻ t, _root_.GD.N0213.N0516.d028398 a β t * F β t)
          ∂_root_.GD.N0213.N0522.d008020 (fun i => 1 - ρ * a i) := by
        apply lintegral_congr
        intro β
        rw [_root_.GD.N0213.N0516.d028414, lintegral_withDensity_eq_lintegral_mul _
          (show Measurable (_root_.GD.N0213.N0516.d028398 a β) by fun_prop)
          (show Measurable (fun t => F β t) by fun_prop)]
        rfl
      _ = _ := by
        change (∫⁻ β, (∫⁻ t, _root_.GD.N0213.N0516.d028398 a β t * F β t)
          ∂(volume : Measure (Fin k → ℝ)).withDensity (_root_.GD.N0213.N0516.d028397 a ρ)) = _
        rw [lintegral_withDensity_eq_lintegral_mul _ (_root_.GD.N0213.N0516.d028401 a ρ)
          (show Measurable (fun β : Fin k → ℝ => ∫⁻ t, _root_.GD.N0213.N0516.d028398 a β t * F β t)
            by fun_prop)]
        apply lintegral_congr
        intro β
        change _root_.GD.N0213.N0516.d028397 a ρ β * (∫⁻ t, _root_.GD.N0213.N0516.d028398 a β t * F β t) = _
        rw [← lintegral_const_mul'' _ (by fun_prop)]
        apply lintegral_congr
        intro t
        rw [mul_assoc]
  have hright :
      (∫⁻ t, ∫⁻ β, F β t ∂_root_.GD.N0213.N0516.d028412 a ρ t ∂_root_.GD.N0213.N0516.d028413 a ρ) =
        ∫⁻ t, ∫⁻ β, _root_.GD.N0213.N0516.d028400 a ρ t * _root_.GD.N0213.N0516.d028399 a ρ t β * F β t := by
    calc
      _ = ∫⁻ t, (∫⁻ β, _root_.GD.N0213.N0516.d028399 a ρ t β * F β t) ∂_root_.GD.N0213.N0516.d028413 a ρ := by
        apply lintegral_congr
        intro t
        rw [_root_.GD.N0213.N0516.d028415, lintegral_withDensity_eq_lintegral_mul _
          (show Measurable (_root_.GD.N0213.N0516.d028399 a ρ t) by fun_prop)
          (show Measurable (fun β => F β t) by fun_prop)]
        rfl
      _ = _ := by
        rw [_root_.GD.N0213.N0516.d028413, lintegral_withDensity_eq_lintegral_mul _ (_root_.GD.N0213.N0516.d028404 a ρ)
          (show Measurable (fun t : Fin k → ℝ => ∫⁻ β, _root_.GD.N0213.N0516.d028399 a ρ t β * F β t)
            by fun_prop)]
        apply lintegral_congr
        intro t
        change _root_.GD.N0213.N0516.d028400 a ρ t * (∫⁻ β, _root_.GD.N0213.N0516.d028399 a ρ t β * F β t) = _
        rw [← lintegral_const_mul'' _ (by fun_prop)]
        apply lintegral_congr
        intro β
        rw [mul_assoc]
  have hcore : Measurable (fun z : (Fin k → ℝ) × (Fin k → ℝ) =>
      _root_.GD.N0213.N0516.d028397 a ρ z.1 * _root_.GD.N0213.N0516.d028398 a z.1 z.2 * F z.1 z.2) := by fun_prop
  rw [hleft, hright, lintegral_lintegral_swap hcore.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [_root_.GD.N0213.N0516.d028410 a ρ ha hρ] with t ht
  apply lintegral_congr
  intro β
  rw [ht β]

end
end GD.N0213.N0516

#print axioms _root_.GD.N0213.N0516.d028405
#print axioms _root_.GD.N0213.N0516.d028409
#print axioms _root_.GD.N0213.N0516.d028410
#print axioms _root_.GD.N0213.N0516.d028416
