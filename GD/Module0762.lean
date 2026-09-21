import GD.Module0761
import GD.Module0699




















open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0930

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0860
open _root_.GD.N0232.N0719.N0942
open _root_.GD.N0232.N0719.N0933
open _root_.GD.N0232.N0719.N0910



@[fun_prop]
theorem d011489 {k : ℕ} :
    Measurable (_root_.GD.N0232.N0719.N0860.d011425 : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) := by
  unfold _root_.GD.N0232.N0719.N0860.d011425
  fun_prop

@[fun_prop]
theorem d011490 {k : ℕ} :
    Measurable (_root_.GD.N0232.N0719.N0860.d011429 : _root_.GD.N0232.N0719.N0900.d009096 k →
      _root_.GD.N0238.N0754.d004717 k) := by
  unfold _root_.GD.N0232.N0719.N0860.d011429
  fun_prop

@[fun_prop]
theorem d011491 {k : ℕ} :
    Measurable (_root_.GD.N0232.N0719.N0860.d011434 : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ) := by
  unfold _root_.GD.N0232.N0719.N0860.d011434
  fun_prop

theorem d011492 (k : ℕ) :
    MeasurableSet {s : _root_.GD.N0232.N0719.N0900.d009096 k | _root_.GD.N0232.N0719.N0860.d011426 s} := by
  rw [show {s : _root_.GD.N0232.N0719.N0900.d009096 k | _root_.GD.N0232.N0719.N0860.d011426 s} =
      ⋂ i : Fin k, {s : _root_.GD.N0232.N0719.N0900.d009096 k | 0 ≤ s.meanVariance i} by
    ext s
    simp [_root_.GD.N0232.N0719.N0860.d011426]]
  exact MeasurableSet.iInter fun i ↦
    measurableSet_le measurable_const (_root_.GD.N0232.N0719.N0900.d009100 i)

theorem d011493 (k : ℕ) :
    MeasurableSet {s : _root_.GD.N0232.N0719.N0900.d009096 k | _root_.GD.N0232.N0719.N0860.d011429 s ≠ 0} := by
  exact (measurableSet_eq_fun
    _root_.GD.N0232.N0719.N0930.d011490 measurable_const).compl


@[fun_prop]
theorem d011494
    {k : ℕ} (amplitude : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0942.d011471 (k := k) amplitude) := by
  unfold _root_.GD.N0232.N0719.N0942.d011471
  exact Measurable.ite
    ((measurableSet_eq_fun _root_.GD.N0232.N0719.N0930.d011489 measurable_const).inter
      (measurableSet_eq_fun _root_.GD.N0232.N0719.N0930.d011491 measurable_const))
    measurable_const measurable_const


@[fun_prop]
theorem d011495
    {k : ℕ} (hk : 0 < k) (amplitude : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0860.d011455 hk (fun _ ↦ amplitude)) := by
  classical
  have hrepr : _root_.GD.N0232.N0719.N0860.d011455 hk (fun _ ↦ amplitude) =
      fun s : _root_.GD.N0232.N0719.N0900.d009096 k ↦
        if _root_.GD.N0232.N0719.N0860.d011426 s then
          if _root_.GD.N0232.N0719.N0860.d011429 s ≠ 0 then
            _root_.GD.N0232.N0719.N0860.d011425 s + _root_.GD.N0232.N0719.N0860.d011434 s * amplitude
          else _root_.GD.N0232.N0719.N0860.d011425 s
        else 0 := by
    funext s
    simp [_root_.GD.N0232.N0719.N0860.d011455]
  rw [hrepr]
  exact Measurable.ite (_root_.GD.N0232.N0719.N0930.d011492 k)
    (Measurable.ite (_root_.GD.N0232.N0719.N0930.d011493 k)
      (_root_.GD.N0232.N0719.N0930.d011489.add
        (_root_.GD.N0232.N0719.N0930.d011491.mul measurable_const))
      _root_.GD.N0232.N0719.N0930.d011489)
    measurable_const


@[fun_prop]
theorem d011496
    {k : ℕ} (hk : 0 < k) (amplitude : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0860.d011458 hk
      (_root_.GD.N0232.N0719.N0942.d011471 (k := k) amplitude)) := by
  rw [_root_.GD.N0232.N0719.N0942.d011474 hk]
  exact _root_.GD.N0232.N0719.N0930.d011495 hk amplitude

@[fun_prop]
theorem d011497
    {k : ℕ} (hk : 0 < k) :
    Measurable (_root_.GD.N0232.N0719.N0860.d011458 hk (fun _ : _root_.GD.N0232.N0719.N0900.d009096 k ↦ 0)) := by
  have hrestriction :
      _root_.GD.N0232.N0719.N0860.d011457 (fun _ : _root_.GD.N0232.N0719.N0900.d009096 k ↦ 0) = fun _ ↦ 0 := by
    funext u
    rfl
  unfold _root_.GD.N0232.N0719.N0860.d011458
  rw [hrestriction]
  exact _root_.GD.N0232.N0719.N0930.d011495 hk 0

@[fun_prop]
theorem d011498
    {k : ℕ} (sizes : Fin k → ℕ) (amplitude : ℝ) :
    Measurable (fun omega : _root_.GD.N0232.N0719.d009173 k sizes ↦
      _root_.GD.N0232.N0719.N0942.d011471 amplitude (_root_.GD.N0232.N0719.N0900.d009104 k sizes omega)) := by
  exact (_root_.GD.N0232.N0719.N0930.d011494 amplitude).comp
    (_root_.GD.N0232.N0719.N0900.d009115 k sizes)

@[fun_prop]
theorem d011499
    {k : ℕ} (sizes : Fin k → ℕ) (hk : 0 < k) (amplitude : ℝ) :
    Measurable (fun omega : _root_.GD.N0232.N0719.d009173 k sizes ↦
      _root_.GD.N0232.N0719.N0860.d011458 hk (_root_.GD.N0232.N0719.N0942.d011471 amplitude)
        (_root_.GD.N0232.N0719.N0900.d009104 k sizes omega)) := by
  exact (_root_.GD.N0232.N0719.N0930.d011496 hk amplitude).comp
    (_root_.GD.N0232.N0719.N0900.d009115 k sizes)




def d011500 (n : ℕ) (y : Fin (n + 1) → ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i, y i


def d011501 (n : ℕ) (z : ℝ × (Fin n → ℝ)) : ℝ :=
  ((n + 1 : ℕ) : ℝ)⁻¹ * z.1 +
    ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ j, z.2 j

@[fun_prop]
theorem d011502 (n : ℕ) :
    Measurable (_root_.GD.N0232.N0719.N0930.d011500 n) := by
  unfold _root_.GD.N0232.N0719.N0930.d011500
  fun_prop

@[fun_prop]
theorem d011503 (n : ℕ) :
    Measurable (_root_.GD.N0232.N0719.N0930.d011501 n) := by
  unfold _root_.GD.N0232.N0719.N0930.d011501
  fun_prop


theorem d011504
    (n : ℕ) (y : Fin (n + 1) → ℝ) :
    _root_.GD.N0232.N0719.N0930.d011501 n (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) ↦ ℝ) 0 y) = _root_.GD.N0232.N0719.N0930.d011500 n y := by
  change
    ((n + 1 : ℕ) : ℝ)⁻¹ * y 0 +
        ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ j : Fin n, y j.succ =
      ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i, y i
  rw [Fin.sum_univ_succ]
  ring



theorem d011505
    {β : Type*} [MeasurableSpace β]
    (n : ℕ) (mu : Measure ℝ) (nu : Measure β)
    [SFinite mu] [SFinite nu] [NoAtoms mu]
    (tail : β → ℝ) (htail : Measurable tail) :
    (mu.prod nu) {z : ℝ × β |
      ((n + 1 : ℕ) : ℝ)⁻¹ * z.1 + tail z.2 = 0} = 0 := by
  have hmeas : MeasurableSet {z : ℝ × β |
      ((n + 1 : ℕ) : ℝ)⁻¹ * z.1 + tail z.2 = 0} :=
    by
      change MeasurableSet
        ((fun z : ℝ × β ↦
          ((n + 1 : ℕ) : ℝ)⁻¹ * z.1 + tail z.2) ⁻¹' ({0} : Set ℝ))
      exact ((measurable_const.mul measurable_fst).add
        (htail.comp measurable_snd)) (measurableSet_singleton (0 : ℝ))
  rw [Measure.prod_apply_symm hmeas]
  have hzero : ∀ y : β,
      mu ((fun x : ℝ ↦ (x, y)) ⁻¹'
        {z : ℝ × β |
          ((n + 1 : ℕ) : ℝ)⁻¹ * z.1 + tail z.2 = 0}) = 0 := by
    intro y
    have ha : (((n + 1 : ℕ) : ℝ)⁻¹) ≠ 0 := by
      exact inv_ne_zero (by positivity)
    have hsection :
        (fun x : ℝ ↦ (x, y)) ⁻¹'
            {z : ℝ × β |
              ((n + 1 : ℕ) : ℝ)⁻¹ * z.1 + tail z.2 = 0} =
          {-tail y / (((n + 1 : ℕ) : ℝ)⁻¹)} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro hx
        apply (eq_div_iff ha).2
        linarith
      · intro hx
        rw [hx]
        field_simp [ha]
        ring
    rw [hsection, measure_singleton]
  simp_rw [hzero]
  exact lintegral_zero



theorem d011506
    (n : ℕ) (mu : Fin (n + 1) → Measure ℝ)
    [∀ i, SigmaFinite (mu i)] [NoAtoms (mu 0)] :
    Measure.pi mu {y | _root_.GD.N0232.N0719.N0930.d011500 n y = 0} = 0 := by
  let e := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) ↦ ℝ) 0
  let tailMeasure : Measure (Fin n → ℝ) :=
    Measure.pi (fun j ↦ mu ((0 : Fin (n + 1)).succAbove j))
  let tail : (Fin n → ℝ) → ℝ := fun y ↦
    ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ j, y j
  have htail : Measurable tail := by
    dsimp [tail]
    fun_prop
  let splitSet : Set (ℝ × (Fin n → ℝ)) :=
    {z | ((n + 1 : ℕ) : ℝ)⁻¹ * z.1 + tail z.2 = 0}
  have hsplitMeas : MeasurableSet splitSet := by
    dsimp [splitSet]
    change MeasurableSet
      ((fun z : ℝ × (Fin n → ℝ) ↦
        ((n + 1 : ℕ) : ℝ)⁻¹ * z.1 + tail z.2) ⁻¹' ({0} : Set ℝ))
    exact ((measurable_const.mul measurable_fst).add
      (htail.comp measurable_snd)) (measurableSet_singleton (0 : ℝ))
  have hpreimage :
      e ⁻¹' splitSet = {y | _root_.GD.N0232.N0719.N0930.d011500 n y = 0} := by
    ext y
    change
      ((n + 1 : ℕ) : ℝ)⁻¹ *
          (e y).1 + tail (e y).2 = 0 ↔
        _root_.GD.N0232.N0719.N0930.d011500 n y = 0
    simpa [e, tail, _root_.GD.N0232.N0719.N0930.d011501] using
      congrArg (fun x : ℝ ↦ x = 0) (_root_.GD.N0232.N0719.N0930.d011504 n y)
  have hpreserving := measurePreserving_piFinSuccAbove mu
    (0 : Fin (n + 1))
  calc
    Measure.pi mu {y | _root_.GD.N0232.N0719.N0930.d011500 n y = 0} =
        Measure.pi mu (e ⁻¹' splitSet) := by rw [hpreimage]
    _ = (Measure.pi mu).map e splitSet := by
      exact (Measure.map_apply e.measurable hsplitMeas).symm
    _ = (mu 0).prod tailMeasure splitSet := by
      rw [hpreserving.map_eq]
    _ = 0 := by
      exact _root_.GD.N0232.N0719.N0930.d011505 n (mu 0) tailMeasure tail htail





theorem d011507
    (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin (n + 1) → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0232.N0719.N0933.d009300 (n + 1) sizes location scales
        {y | _root_.GD.N0232.N0719.N0930.d011500 n y = 0} = 0 := by
  unfold _root_.GD.N0232.N0719.N0933.d009300
  letI : NoAtoms
      (_root_.GD.N0232.N0719.N0933.d009288 (sizes 0) location (scales 0)) := by
    rw [_root_.GD.N0232.N0719.N0933.d009297
      (lt_of_lt_of_le (by decide : 0 < 2) (hsizes 0))]
    apply noAtoms_gaussianReal
    intro hv
    have hvcoe := congrArg (fun q : ℝ≥0 ↦ (q : ℝ)) hv
    simp only [NNReal.coe_mk, NNReal.coe_zero] at hvcoe
    have hsize : (0 : ℝ) < sizes 0 := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (hsizes 0))
    have hscale : scales 0 ≠ 0 := (hscales 0).ne'
    exact (div_ne_zero (pow_ne_zero 2 hscale) hsize.ne') hvcoe
  exact _root_.GD.N0232.N0719.N0930.d011506 n
    (fun i ↦ _root_.GD.N0232.N0719.N0933.d009288 (sizes i) location (scales i))



theorem d011508
    (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (omega : _root_.GD.N0232.N0719.d009173 (n + 1) sizes) :
    _root_.GD.N0232.N0719.N0860.d011425 (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) =
      _root_.GD.N0232.N0719.N0930.d011500 n (_root_.GD.N0232.N0719.N0933.d009304 (n + 1) sizes omega).1 := by
  rfl



theorem d011509
    (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin (n + 1) → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales
        {omega | _root_.GD.N0232.N0719.N0860.d011425 (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) = 0} = 0 := by
  let meanLaw := _root_.GD.N0232.N0719.N0933.d009300 (n + 1) sizes location scales
  let varianceLaw := _root_.GD.N0232.N0719.N0933.d009301 (n + 1) sizes scales
  let centerSet : Set (Fin (n + 1) → ℝ) :=
    {y | _root_.GD.N0232.N0719.N0930.d011500 n y = 0}
  let pairSet : Set ((Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :=
    Prod.fst ⁻¹' centerSet
  have hcenterMeas : MeasurableSet centerSet := by
    dsimp [centerSet]
    change MeasurableSet
      ((_root_.GD.N0232.N0719.N0930.d011500 n) ⁻¹' ({0} : Set ℝ))
    exact (_root_.GD.N0232.N0719.N0930.d011502 n) (measurableSet_singleton (0 : ℝ))
  have hpairMeas : MeasurableSet pairSet :=
    measurable_fst hcenterMeas
  have hpreimage :
      _root_.GD.N0232.N0719.N0933.d009304 (n + 1) sizes ⁻¹' pairSet =
        {omega | _root_.GD.N0232.N0719.N0860.d011425 (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) = 0} := by
    ext omega
    change
      _root_.GD.N0232.N0719.N0930.d011500 n (_root_.GD.N0232.N0719.N0933.d009304 (n + 1) sizes omega).1 = 0 ↔
        _root_.GD.N0232.N0719.N0860.d011425 (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) = 0
    rw [_root_.GD.N0232.N0719.N0930.d011508 n sizes omega]
  letI : IsProbabilityMeasure varianceLaw :=
    _root_.GD.N0232.N0719.N0910.d010289 sizes hsizes scales
  have hstat := _root_.GD.N0232.N0719.N0933.d009309
    (n + 1) sizes hsizes location scales
  have hfst : MeasurePreserving Prod.fst
      (meanLaw.prod varianceLaw) meanLaw := measurePreserving_fst
  calc
    _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales
          {omega | _root_.GD.N0232.N0719.N0860.d011425 (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) = 0} =
        _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales
          (_root_.GD.N0232.N0719.N0933.d009304 (n + 1) sizes ⁻¹' pairSet) := by
            rw [hpreimage]
    _ = ((_root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales).map
          (_root_.GD.N0232.N0719.N0933.d009304 (n + 1) sizes)) pairSet := by
      exact (Measure.map_apply
        (_root_.GD.N0232.N0719.N0933.d009308 (n + 1) sizes) hpairMeas).symm
    _ = (meanLaw.prod varianceLaw) pairSet := by
      rw [hstat]
    _ = (meanLaw.prod varianceLaw) (Prod.fst ⁻¹' centerSet) := rfl
    _ = (meanLaw.prod varianceLaw).map Prod.fst centerSet := by
      exact (Measure.map_apply measurable_fst hcenterMeas).symm
    _ = meanLaw centerSet := by rw [hfst.map_eq]
    _ = 0 := _root_.GD.N0232.N0719.N0930.d011507
      n sizes hsizes location scales hscales




theorem d011510
    (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin (n + 1) → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    ∀ᵐ omega ∂_root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales,
      ∀ i, 0 < (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega).meanVariance i := by
  let meanLaw := _root_.GD.N0232.N0719.N0933.d009300 (n + 1) sizes location scales
  let varianceLaw := _root_.GD.N0232.N0719.N0933.d009301 (n + 1) sizes scales
  let positiveSet : Set
      ((Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :=
    {z | ∀ i, 0 < z.2 i}
  letI : IsProbabilityMeasure varianceLaw :=
    _root_.GD.N0232.N0719.N0910.d010289 sizes hsizes scales
  have hpositiveMeas : MeasurableSet positiveSet := by
    rw [show positiveSet = ⋂ i : Fin (n + 1),
        {z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) | 0 < z.2 i} by
      ext z
      simp [positiveSet]]
    exact MeasurableSet.iInter fun i ↦
      measurableSet_lt measurable_const
        ((measurable_pi_apply i).comp measurable_snd)
  have hpair : ∀ᵐ z ∂meanLaw.prod varianceLaw, z ∈ positiveSet := by
    exact
      (Measure.quasiMeasurePreserving_snd
        (μ := meanLaw) (ν := varianceLaw)).ae
          (_root_.GD.N0232.N0719.N0910.d010288 hsizes hscales)
  have hstat := _root_.GD.N0232.N0719.N0933.d009309
    (n + 1) sizes hsizes location scales
  have hmap :
      ∀ᵐ z ∂(_root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales).map
          (_root_.GD.N0232.N0719.N0933.d009304 (n + 1) sizes),
        z ∈ positiveSet := by
    rw [hstat]
    exact hpair
  have hraw :=
    (ae_map_iff
      (_root_.GD.N0232.N0719.N0933.d009308 (n + 1) sizes).aemeasurable
      hpositiveMeas).1 hmap
  filter_upwards [hraw] with omega homega
  intro i
  exact homega i



theorem d011511
    (n : ℕ) (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1))
    (hpos : ∀ i, 0 < s.meanVariance i) :
    _root_.GD.N0232.N0719.N0860.d011429 s ≠ 0 := by
  intro hz
  have hz0 : Real.sqrt (s.meanVariance 0) = 0 := by
    simpa [_root_.GD.N0232.N0719.N0860.d011429] using
      congrArg (fun z :
        _root_.GD.N0238.N0754.d004717
          (n + 1) ↦ z.2 0) hz
  exact (Real.sqrt_pos.2 (hpos 0)).ne' hz0



theorem d011512
    (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin (n + 1) → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    ∀ᵐ omega ∂_root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales,
      _root_.GD.N0232.N0719.N0860.d011429 (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) ≠ 0 := by
  filter_upwards [_root_.GD.N0232.N0719.N0930.d011510
    n sizes hsizes location scales hscales] with omega homega
  exact _root_.GD.N0232.N0719.N0930.d011511
    n (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) homega



theorem d011513
    (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin (n + 1) → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales
        {omega |
          _root_.GD.N0232.N0719.N0860.d011425 (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) = 0 ∧
          _root_.GD.N0232.N0719.N0860.d011434 (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) = 1} = 0 := by
  apply measure_mono_null
    (show {omega |
        _root_.GD.N0232.N0719.N0860.d011425 (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) = 0 ∧
        _root_.GD.N0232.N0719.N0860.d011434 (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) = 1} ⊆
      {omega | _root_.GD.N0232.N0719.N0860.d011425 (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) = 0} by
        intro omega homega
        exact homega.1)
  exact _root_.GD.N0232.N0719.N0930.d011509
    n sizes hsizes location scales hscales



theorem d011514
    (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin (n + 1) → ℝ)
    (hscales : ∀ i, 0 < scales i) (amplitude : ℝ) :
    (fun omega ↦ _root_.GD.N0232.N0719.N0942.d011471 amplitude
      (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)) =ᵐ[
        _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales]
      (fun _ ↦ 0) := by
  change ∀ᵐ omega ∂_root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales,
    _root_.GD.N0232.N0719.N0942.d011471 amplitude
      (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) = 0
  rw [ae_iff]
  apply measure_mono_null
    (show {omega |
        _root_.GD.N0232.N0719.N0942.d011471 amplitude
          (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) ≠ 0} ⊆
      {omega |
        _root_.GD.N0232.N0719.N0860.d011425 (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) = 0 ∧
        _root_.GD.N0232.N0719.N0860.d011434 (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) = 1} by
      intro omega homega
      by_cases hslice :
          _root_.GD.N0232.N0719.N0860.d011425 (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) = 0 ∧
          _root_.GD.N0232.N0719.N0860.d011434 (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) = 1
      · exact hslice
      · have hz : _root_.GD.N0232.N0719.N0942.d011471 amplitude
            (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) = 0 := by
          simp [_root_.GD.N0232.N0719.N0942.d011471, hslice]
        exact (homega hz).elim)
  exact _root_.GD.N0232.N0719.N0930.d011513
    n sizes hsizes location scales hscales



theorem d011515
    (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 (n + 1))
    (amplitude : ℝ) :
    _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes theta
        (fun omega ↦ _root_.GD.N0232.N0719.N0942.d011471 amplitude
          (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)) =
      _root_.GD.N0232.N0719.N0859.d010840 (n + 1) sizes theta
        (fun _ ↦ 0) := by
  unfold _root_.GD.N0232.N0719.N0859.d010840
  apply lintegral_congr_ae
  have hzero := _root_.GD.N0232.N0719.N0930.d011514
    n sizes hsizes theta.location theta.scale theta.scale_pos amplitude
  change (fun omega ↦ _root_.GD.N0232.N0719.N0942.d011471 amplitude
      (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)) =ᵐ[
        _root_.GD.N0232.N0719.N0859.d010812 (n + 1) sizes theta]
      (fun _ ↦ 0) at hzero
  filter_upwards [hzero] with omega homega
  rw [homega]




theorem d011516
    (n : ℕ) (s : _root_.GD.N0232.N0719.N0900.d009096 (n + 1))
    (hs : _root_.GD.N0232.N0719.N0860.d011426 s) (hz : _root_.GD.N0232.N0719.N0860.d011429 s ≠ 0)
    (amplitude : ℝ) (hamplitude : amplitude ≠ 0) :
    _root_.GD.N0232.N0719.N0860.d011458 (Nat.succ_pos n) (_root_.GD.N0232.N0719.N0942.d011471 amplitude) s ≠
      _root_.GD.N0232.N0719.N0860.d011458 (Nat.succ_pos n) (fun _ ↦ 0) s := by
  rw [_root_.GD.N0232.N0719.N0942.d011470
      (Nat.succ_pos n) (_root_.GD.N0232.N0719.N0942.d011471 amplitude) s hs hz,
    _root_.GD.N0232.N0719.N0942.d011470
      (Nat.succ_pos n) (fun _ ↦ 0) s hs hz,
    _root_.GD.N0232.N0719.N0942.d011472 (Nat.succ_pos n)]
  simp only [mul_zero, add_zero]
  intro heq
  have hmul : _root_.GD.N0232.N0719.N0860.d011434 s * amplitude = 0 := by
    linarith
  exact (mul_ne_zero
    ((_root_.GD.N0232.N0719.N0860.d011436 s).2 hz).ne' hamplitude) hmul





theorem d011517
    (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin (n + 1) → ℝ)
    (hscales : ∀ i, 0 < scales i)
    (amplitude : ℝ) (hamplitude : amplitude ≠ 0) :
    ∀ᵐ omega ∂_root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales,
      _root_.GD.N0232.N0719.N0860.d011458 (Nat.succ_pos n) (_root_.GD.N0232.N0719.N0942.d011471 amplitude)
          (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) ≠
        _root_.GD.N0232.N0719.N0860.d011458 (Nat.succ_pos n) (fun _ ↦ 0)
          (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) := by
  filter_upwards [_root_.GD.N0232.N0719.N0930.d011512
    n sizes hsizes location scales hscales] with omega hz
  exact _root_.GD.N0232.N0719.N0930.d011516
    n (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)
      (fun i ↦ _root_.GD.N0232.N0719.N0900.d009125 hsizes omega i)
      hz amplitude hamplitude




theorem d011518
    (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin (n + 1) → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    ∃ d e : _root_.GD.N0232.N0719.N0900.d009096 (n + 1) → ℝ,
      Measurable d ∧ Measurable e ∧
      (fun omega ↦ d (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)) =ᵐ[
        _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales]
        (fun omega ↦ e (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)) ∧
      (∀ᵐ omega ∂_root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales,
        _root_.GD.N0232.N0719.N0860.d011458 (Nat.succ_pos n) d
            (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega) ≠
          _root_.GD.N0232.N0719.N0860.d011458 (Nat.succ_pos n) e
            (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)) := by
  refine ⟨_root_.GD.N0232.N0719.N0942.d011471 1, (fun _ ↦ 0),
    _root_.GD.N0232.N0719.N0930.d011494 1, measurable_const, ?_, ?_⟩
  · exact _root_.GD.N0232.N0719.N0930.d011514
      n sizes hsizes location scales hscales 1
  · exact _root_.GD.N0232.N0719.N0930.d011517
      n sizes hsizes location scales hscales 1 one_ne_zero




theorem d011519
    (n : ℕ) (sizes : Fin (n + 1) → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin (n + 1) → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    ¬ ∀ d e : _root_.GD.N0232.N0719.N0900.d009096 (n + 1) → ℝ,
      (fun omega ↦ d (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)) =ᵐ[
        _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales]
        (fun omega ↦ e (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)) →
      (fun omega ↦ _root_.GD.N0232.N0719.N0860.d011458 (Nat.succ_pos n) d
        (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)) =ᵐ[
          _root_.GD.N0232.N0719.d009176 (n + 1) sizes location scales]
        (fun omega ↦ _root_.GD.N0232.N0719.N0860.d011458 (Nat.succ_pos n) e
          (_root_.GD.N0232.N0719.N0900.d009104 (n + 1) sizes omega)) := by
  intro hext
  have heq := hext (_root_.GD.N0232.N0719.N0942.d011471 1) (fun _ ↦ 0)
    (_root_.GD.N0232.N0719.N0930.d011514
      n sizes hsizes location scales hscales 1)
  have hne := _root_.GD.N0232.N0719.N0930.d011517
    n sizes hsizes location scales hscales 1 one_ne_zero
  obtain ⟨omega, homegaEq, homegaNe⟩ := (heq.and hne).exists
  exact homegaNe homegaEq

end

end N0930
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0930.d011506
#print axioms _root_.GD.N0232.N0719.N0930.d011513
#print axioms _root_.GD.N0232.N0719.N0930.d011514
#print axioms _root_.GD.N0232.N0719.N0930.d011518
#print axioms _root_.GD.N0232.N0719.N0930.d011519
