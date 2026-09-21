import GD.Module0026
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Prod




































open Filter MeasureTheory Set

namespace GD
namespace N0230
namespace N0605

variable {G X : Type*}
  [Group G] [MeasurableSpace G] [MeasurableSpace X]
  [MulAction G X] [MulAction G ℝ]


noncomputable def d000307 (t : ℝ) : ℝ := t / (1 + |t|)



noncomputable def d000308 (u : ℝ) : ℝ := u / (1 - |u|)

theorem d000309 (t : ℝ) : 0 < 1 + |t| := by positivity

theorem d000310 (t : ℝ) : |_root_.GD.N0230.N0605.d000307 t| < 1 := by
  rw [_root_.GD.N0230.N0605.d000307, abs_div]
  have hden : 0 < 1 + |t| := _root_.GD.N0230.N0605.d000309 t
  rw [abs_of_pos hden, div_lt_one hden]
  linarith [abs_nonneg t]

theorem d000311 (t : ℝ) : _root_.GD.N0230.N0605.d000308 (_root_.GD.N0230.N0605.d000307 t) = t := by
  have hden : 0 < 1 + |t| := _root_.GD.N0230.N0605.d000309 t
  have habs : |_root_.GD.N0230.N0605.d000307 t| = |t| / (1 + |t|) := by
    rw [_root_.GD.N0230.N0605.d000307, abs_div, abs_of_pos hden]
  rw [_root_.GD.N0230.N0605.d000308, habs, _root_.GD.N0230.N0605.d000307]
  field_simp
  ring

theorem d000312 : Measurable _root_.GD.N0230.N0605.d000307 := by
  exact measurable_id.div (measurable_const.add measurable_id.norm)

theorem d000313 : Measurable _root_.GD.N0230.N0605.d000308 := by
  exact measurable_id.div (measurable_const.sub measurable_id.norm)



def d000314 (value : X → ℝ) (x : X) (g : G) : ℝ :=
  g⁻¹ • value (g • x)



theorem d000315 (value : X → ℝ) (h : G) (x : X) (g : G) :
    _root_.GD.N0230.N0605.d000314 value (h • x) g =
      h • _root_.GD.N0230.N0605.d000314 value x (g * h) := by
  simp [_root_.GD.N0230.N0605.d000314, mul_smul]

section JointMeasurableAction

variable [MeasurableInv G] [MeasurableSMul₂ G X] [MeasurableSMul₂ G ℝ]




theorem d000316
    (value : X → ℝ) (hvalue : Measurable value) :
    Measurable (fun z : X × G ↦ _root_.GD.N0230.N0605.d000314 value z.1 z.2) := by
  exact measurable_snd.inv.smul
    (hvalue.comp (measurable_snd.smul measurable_fst))

theorem d000317
    (value : X → ℝ) (hvalue : Measurable value) :
    Measurable
      (fun z : X × G ↦ _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value z.1 z.2)) :=
  _root_.GD.N0230.N0605.d000312.comp (_root_.GD.N0230.N0605.d000316 value hvalue)




theorem d000318
    (value : X → ℝ) (hvalue : Measurable value) :
    MeasurableSet {z : G × X | value (z.1 • z.2) = z.1 • value z.2} := by
  exact measurableSet_eq_fun
    (hvalue.comp (measurable_fst.smul measurable_snd))
    (measurable_fst.smul (hvalue.comp measurable_snd))

end JointMeasurableAction

section EquivalentInvariantMeasure

variable [MeasurableMul G]





theorem d000319
    (lambda haar : Measure G)
    [haar.IsMulRightInvariant]
    (hlambdaHaar : lambda ≪ haar) (hhaarLambda : haar ≪ lambda)
    (h : G) :
    Measure.QuasiMeasurePreserving (fun g : G ↦ g * h) lambda lambda := by
  exact (measurePreserving_mul_right haar h).quasiMeasurePreserving.mono
    hlambdaHaar hhaarLambda

end EquivalentInvariantMeasure

section ProbabilityGroupCoordinate

variable (lambda : Measure G) [IsProbabilityMeasure lambda]


noncomputable def d000320 (value : X → ℝ) (x : X) : ℝ :=
  ∫ g, _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g) ∂lambda


noncomputable def d000321 (value : X → ℝ) (x : X) : ℝ :=
  _root_.GD.N0230.N0605.d000308 (_root_.GD.N0230.N0605.d000320 lambda value x)


noncomputable def d000322 (value : X → ℝ) (x : X) : ℝ :=
  ∫ g, (_root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g) - _root_.GD.N0230.N0605.d000320 lambda value x) ^ 2 ∂lambda



def d000323 (value : X → ℝ) : Set X :=
  {x | _root_.GD.N0230.N0605.d000322 lambda value x = 0}

theorem d000324
    (value : X → ℝ) (x : X)
    (hmeas : AEStronglyMeasurable
      (fun g ↦ _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g)) lambda) :
    Integrable (fun g ↦ _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g)) lambda := by
  refine Integrable.of_bound hmeas 1 ?_
  filter_upwards with g
  exact (_root_.GD.N0230.N0605.d000310 _).le

theorem d000325
    (value : X → ℝ) (x : X) (y : ℝ)
    (hconst : _root_.GD.N0230.N0605.d000314 value x =ᵐ[lambda] fun _ ↦ y) :
    _root_.GD.N0230.N0605.d000320 lambda value x = _root_.GD.N0230.N0605.d000307 y := by
  rw [_root_.GD.N0230.N0605.d000320]
  calc
    (∫ g, _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g) ∂lambda) =
        ∫ _g : G, _root_.GD.N0230.N0605.d000307 y ∂lambda :=
      integral_congr_ae (hconst.fun_comp _root_.GD.N0230.N0605.d000307)
    _ = _root_.GD.N0230.N0605.d000307 y := by simp

theorem d000326
    (value : X → ℝ) (x : X) (y : ℝ)
    (hconst : _root_.GD.N0230.N0605.d000314 value x =ᵐ[lambda] fun _ ↦ y) :
    _root_.GD.N0230.N0605.d000321 lambda value x = y := by
  rw [_root_.GD.N0230.N0605.d000321, _root_.GD.N0230.N0605.d000325 lambda value x y hconst,
    _root_.GD.N0230.N0605.d000311]

theorem d000327
    (value : X → ℝ) (x : X) (y : ℝ)
    (hconst : _root_.GD.N0230.N0605.d000314 value x =ᵐ[lambda] fun _ ↦ y) :
    _root_.GD.N0230.N0605.d000322 lambda value x = 0 := by
  rw [_root_.GD.N0230.N0605.d000322, _root_.GD.N0230.N0605.d000325 lambda value x y hconst]
  apply integral_eq_zero_of_ae
  filter_upwards [hconst] with g hg
  simp [hg]

theorem d000328
    (value : X → ℝ) (x : X) (y : ℝ)
    (hconst : _root_.GD.N0230.N0605.d000314 value x =ᵐ[lambda] fun _ ↦ y) :
    x ∈ _root_.GD.N0230.N0605.d000323 lambda value :=
  _root_.GD.N0230.N0605.d000327 lambda value x y hconst



theorem d000329
    (value : X → ℝ) (x : X)
    (hmeas : AEStronglyMeasurable
      (fun g ↦ _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g)) lambda)
    (hx : x ∈ _root_.GD.N0230.N0605.d000323 lambda value) :
    _root_.GD.N0230.N0605.d000314 value x =ᵐ[lambda]
      fun _ ↦ _root_.GD.N0230.N0605.d000321 lambda value x := by
  have hmean_meas : AEStronglyMeasurable
      (fun _g : G ↦ _root_.GD.N0230.N0605.d000320 lambda value x) lambda :=
    aestronglyMeasurable_const
  have hsq_meas : AEStronglyMeasurable
      (fun g ↦ (_root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g) -
        _root_.GD.N0230.N0605.d000320 lambda value x) ^ 2) lambda :=
    (hmeas.sub hmean_meas).pow 2
  have hsq_bound : ∀ᵐ g ∂lambda,
      ‖(_root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g) -
        _root_.GD.N0230.N0605.d000320 lambda value x) ^ 2‖ ≤ 4 := by
    have hmean_bound : |_root_.GD.N0230.N0605.d000320 lambda value x| ≤ 1 := by
      rw [_root_.GD.N0230.N0605.d000320]
      calc
        |∫ g, _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g) ∂lambda| ≤
            ∫ g, |_root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g)| ∂lambda :=
          abs_integral_le_integral_abs
        _ ≤ ∫ _g : G, (1 : ℝ) ∂lambda := by
          apply integral_mono_ae
          · exact (_root_.GD.N0230.N0605.d000324 lambda value x hmeas).abs
          · exact integrable_const 1
          · filter_upwards with g
            exact (_root_.GD.N0230.N0605.d000310 _).le
        _ = 1 := by simp
    filter_upwards with g
    rw [Real.norm_eq_abs, abs_sq]
    have hdiff : |_root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g) -
        _root_.GD.N0230.N0605.d000320 lambda value x| ≤ 2 := by
      calc
        |_root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g) - _root_.GD.N0230.N0605.d000320 lambda value x| ≤
            |_root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g)| +
              |_root_.GD.N0230.N0605.d000320 lambda value x| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add (_root_.GD.N0230.N0605.d000310 _).le hmean_bound
        _ = 2 := by norm_num
    have hsquare :
        |_root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g) - _root_.GD.N0230.N0605.d000320 lambda value x| ^ 2 ≤
          (2 : ℝ) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 hdiff
    norm_num [sq_abs] at hsquare ⊢
    exact hsquare
  have hsq_int : Integrable
      (fun g ↦ (_root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g) -
        _root_.GD.N0230.N0605.d000320 lambda value x) ^ 2) lambda :=
    Integrable.of_bound hsq_meas 4 hsq_bound
  have hzero_sq :
      (fun g ↦ (_root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g) -
        _root_.GD.N0230.N0605.d000320 lambda value x) ^ 2) =ᵐ[lambda] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun g ↦ sq_nonneg
        (_root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g) - _root_.GD.N0230.N0605.d000320 lambda value x))
      hsq_int).1 hx
  filter_upwards [hzero_sq] with g hg
  have heq : _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g) = _root_.GD.N0230.N0605.d000320 lambda value x := by
    have hsub : _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g) - _root_.GD.N0230.N0605.d000320 lambda value x = 0 := by
      simpa [Pi.zero_apply, sq_eq_zero_iff] using hg
    linarith
  calc
    _root_.GD.N0230.N0605.d000314 value x g = _root_.GD.N0230.N0605.d000308 (_root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g)) :=
      (_root_.GD.N0230.N0605.d000311 _).symm
    _ = _root_.GD.N0230.N0605.d000321 lambda value x := by rw [heq]; rfl


theorem d000330
    (value : X → ℝ) (x : X)
    (hmeas : AEStronglyMeasurable
      (fun g ↦ _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g)) lambda) :
    x ∈ _root_.GD.N0230.N0605.d000323 lambda value ↔
      _root_.GD.N0230.N0605.d000314 value x =ᵐ[lambda]
        fun _ ↦ _root_.GD.N0230.N0605.d000321 lambda value x := by
  constructor
  · exact _root_.GD.N0230.N0605.d000329 lambda value x hmeas
  · exact _root_.GD.N0230.N0605.d000328 lambda value x _



theorem d000331
    (value : X → ℝ)
    (hmeas : StronglyMeasurable
      (fun z : X × G ↦ _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value z.1 z.2))) :
    StronglyMeasurable (_root_.GD.N0230.N0605.d000320 lambda value) := by
  exact hmeas.integral_prod_right'

theorem d000332
    (value : X → ℝ)
    (hmeas : Measurable
      (fun z : X × G ↦ _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value z.1 z.2))) :
    Measurable (_root_.GD.N0230.N0605.d000320 lambda value) :=
  (_root_.GD.N0230.N0605.d000331 lambda value hmeas.stronglyMeasurable).measurable

theorem d000333
    (value : X → ℝ)
    (hmeas : Measurable
      (fun z : X × G ↦ _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value z.1 z.2))) :
    Measurable (_root_.GD.N0230.N0605.d000321 lambda value) :=
  _root_.GD.N0230.N0605.d000313.comp (_root_.GD.N0230.N0605.d000332 lambda value hmeas)

theorem d000334
    (value : X → ℝ)
    (hmeas : StronglyMeasurable
      (fun z : X × G ↦ _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value z.1 z.2))) :
    StronglyMeasurable (_root_.GD.N0230.N0605.d000322 lambda value) := by
  have hmean : StronglyMeasurable (_root_.GD.N0230.N0605.d000320 lambda value) :=
    _root_.GD.N0230.N0605.d000331 lambda value hmeas
  have hjointMean : StronglyMeasurable
      (fun z : X × G ↦ _root_.GD.N0230.N0605.d000320 lambda value z.1) :=
    hmean.comp_measurable measurable_fst
  exact (hmeas.sub hjointMean).pow 2 |>.integral_prod_right'

theorem d000335
    (value : X → ℝ)
    (hmeas : Measurable
      (fun z : X × G ↦ _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value z.1 z.2))) :
    Measurable (_root_.GD.N0230.N0605.d000322 lambda value) :=
  (_root_.GD.N0230.N0605.d000334 lambda value
    hmeas.stronglyMeasurable).measurable

theorem d000336
    (value : X → ℝ)
    (hmeas : Measurable
      (fun z : X × G ↦ _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value z.1 z.2))) :
    MeasurableSet (_root_.GD.N0230.N0605.d000323 lambda value) := by
  change MeasurableSet ((_root_.GD.N0230.N0605.d000322 lambda value) ⁻¹' {0})
  exact (measurableSet_singleton (x := (0 : ℝ))).preimage
    (_root_.GD.N0230.N0605.d000335 lambda value hmeas)

section QuasiInvariant

variable (hRight : ∀ h : G,
  Measure.QuasiMeasurePreserving (fun g : G ↦ g * h) lambda lambda)

include hRight



theorem d000337
    (value : X → ℝ) (h : G) (x : X) (y : ℝ)
    (hconst : _root_.GD.N0230.N0605.d000314 value x =ᵐ[lambda] fun _ ↦ y) :
    _root_.GD.N0230.N0605.d000314 value (h • x) =ᵐ[lambda] fun _ ↦ h • y := by
  have htranslated :
      (fun g ↦ _root_.GD.N0230.N0605.d000314 value x (g * h)) =ᵐ[lambda]
        fun _ ↦ y := by
    exact (hRight h).ae_eq_comp hconst
  filter_upwards [htranslated] with g hg
  rw [_root_.GD.N0230.N0605.d000315, hg]



theorem d000338
    (value : X → ℝ)
    (hmeas : ∀ x, AEStronglyMeasurable
      (fun g ↦ _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g)) lambda)
    (h : G) (x : X) :
    h • x ∈ _root_.GD.N0230.N0605.d000323 lambda value ↔ x ∈ _root_.GD.N0230.N0605.d000323 lambda value := by
  constructor
  · intro hhx
    have hconst := _root_.GD.N0230.N0605.d000329
      lambda value (h • x) (hmeas (h • x)) hhx
    have hback := _root_.GD.N0230.N0605.d000337 lambda hRight value h⁻¹ (h • x)
      (_root_.GD.N0230.N0605.d000321 lambda value (h • x)) hconst
    have hback' : _root_.GD.N0230.N0605.d000314 value x =ᵐ[lambda]
        fun _ ↦ h⁻¹ • _root_.GD.N0230.N0605.d000321 lambda value (h • x) := by
      simpa [smul_smul] using hback
    exact _root_.GD.N0230.N0605.d000328 lambda value x
      (h⁻¹ • _root_.GD.N0230.N0605.d000321 lambda value (h • x)) hback'
  · intro hx
    have hconst := _root_.GD.N0230.N0605.d000329
      lambda value x (hmeas x) hx
    exact _root_.GD.N0230.N0605.d000328 lambda value (h • x)
      (h • _root_.GD.N0230.N0605.d000321 lambda value x)
      (_root_.GD.N0230.N0605.d000337 lambda hRight value h x _ hconst)



theorem d000339
    (value : X → ℝ)
    (hmeas : ∀ x, AEStronglyMeasurable
      (fun g ↦ _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g)) lambda) :
    _root_.GD.N0230.N0644.d000296
      (fun (h : G) (x : X) ↦ h • x)
      (fun (h : G) (y : ℝ) ↦ h • y)
      (_root_.GD.N0230.N0605.d000323 lambda value) (_root_.GD.N0230.N0605.d000321 lambda value) := by
  intro h x hx
  have hconst := _root_.GD.N0230.N0605.d000329
    lambda value x (hmeas x) hx
  have htransport := _root_.GD.N0230.N0605.d000337 lambda hRight value h x
    (_root_.GD.N0230.N0605.d000321 lambda value x) hconst
  exact _root_.GD.N0230.N0605.d000326 lambda value (h • x)
    (h • _root_.GD.N0230.N0605.d000321 lambda value x) htransport

theorem d000340
    (value : X → ℝ)
    (hmeas : ∀ x, AEStronglyMeasurable
      (fun g ↦ _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g)) lambda) :
    _root_.GD.N0230.N0644.d000295
      (fun (h : G) (x : X) ↦ h • x) (_root_.GD.N0230.N0605.d000323 lambda value) := by
  intro h x
  exact _root_.GD.N0230.N0605.d000338 lambda hRight value hmeas h x

end QuasiInvariant

end ProbabilityGroupCoordinate

section Fubini

variable (mu : Measure X) (lambda : Measure G)
  [SFinite mu] [SFinite lambda]




theorem d000341
    (value : X → ℝ)
    (hcovMeas : MeasurableSet
      {z : G × X | value (z.1 • z.2) = z.1 • value z.2})
    (hcov : ∀ g : G, (fun x ↦ value (g • x)) =ᵐ[mu]
      fun x ↦ g • value x) :
    ∀ᵐ x ∂mu, _root_.GD.N0230.N0605.d000314 value x =ᵐ[lambda] fun _ ↦ value x := by
  have hgx : ∀ᵐ g ∂lambda, ∀ᵐ x ∂mu,
      value (g • x) = g • value x := by
    exact ae_of_all lambda hcov
  have hxg : ∀ᵐ x ∂mu, ∀ᵐ g ∂lambda,
      value (g • x) = g • value x :=
    (Measure.ae_ae_comm hcovMeas).1 hgx
  filter_upwards [hxg] with x hx
  filter_upwards [hx] with g hg
  simp [_root_.GD.N0230.N0605.d000314, hg]

end Fubini

section CompleteRepair

variable (mu : Measure X) [SFinite mu]
  (lambda : Measure G) [IsProbabilityMeasure lambda]








theorem d000342
    (value fallback : X → ℝ)
    (hfallback : Measurable fallback)
    (hfallbackEquivariant :
      _root_.GD.N0230.N0644.d000297
        (fun (h : G) (x : X) ↦ h • x)
        (fun (h : G) (y : ℝ) ↦ h • y) fallback)
    (hnormMeas : Measurable
      (fun z : X × G ↦ _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value z.1 z.2)))
    (hcovMeas : MeasurableSet
      {z : G × X | value (z.1 • z.2) = z.1 • value z.2})
    (hcov : ∀ g : G, (fun x ↦ value (g • x)) =ᵐ[mu]
      fun x ↦ g • value x)
    (hRight : ∀ h : G,
      Measure.QuasiMeasurePreserving (fun g : G ↦ g * h) lambda lambda) :
    ∃ repaired : X → ℝ,
      Measurable repaired ∧
      repaired =ᵐ[mu] value ∧
      _root_.GD.N0230.N0644.d000297
        (fun (h : G) (x : X) ↦ h • x)
        (fun (h : G) (y : ℝ) ↦ h • y) repaired := by
  have hsections : ∀ x, AEStronglyMeasurable
      (fun g ↦ _root_.GD.N0230.N0605.d000307 (_root_.GD.N0230.N0605.d000314 value x g)) lambda := by
    intro x
    exact hnormMeas.comp measurable_prodMk_left |>.aestronglyMeasurable
  have hconullConst : ∀ᵐ x ∂mu,
      _root_.GD.N0230.N0605.d000314 value x =ᵐ[lambda] fun _ ↦ value x :=
    _root_.GD.N0230.N0605.d000341
      mu lambda value hcovMeas hcov
  have hconullGood : ∀ᵐ x ∂mu, x ∈ _root_.GD.N0230.N0605.d000323 lambda value := by
    filter_upwards [hconullConst] with x hx
    exact _root_.GD.N0230.N0605.d000328 lambda value x (value x) hx
  have hcenterValue : _root_.GD.N0230.N0605.d000321 lambda value =ᵐ[mu] value := by
    filter_upwards [hconullConst] with x hx
    exact _root_.GD.N0230.N0605.d000326 lambda value x (value x) hx
  exact _root_.GD.N0230.N0644.d000306
    mu (fun (h : G) (x : X) ↦ h • x)
    (fun (h : G) (y : ℝ) ↦ h • y)
    (_root_.GD.N0230.N0605.d000323 lambda value) (_root_.GD.N0230.N0605.d000321 lambda value) fallback value
    (_root_.GD.N0230.N0605.d000336 lambda value hnormMeas)
    hconullGood
    (_root_.GD.N0230.N0605.d000333 lambda value hnormMeas)
    hfallback
    (_root_.GD.N0230.N0605.d000340 lambda hRight value hsections)
    (_root_.GD.N0230.N0605.d000339 lambda hRight value hsections)
    hfallbackEquivariant
    hcenterValue




theorem d000343
    [MeasurableInv G] [MeasurableSMul₂ G X] [MeasurableSMul₂ G ℝ]
    (value fallback : X → ℝ)
    (hvalue : Measurable value)
    (hfallback : Measurable fallback)
    (hfallbackEquivariant :
      _root_.GD.N0230.N0644.d000297
        (fun (h : G) (x : X) ↦ h • x)
        (fun (h : G) (y : ℝ) ↦ h • y) fallback)
    (hcov : ∀ g : G, (fun x ↦ value (g • x)) =ᵐ[mu]
      fun x ↦ g • value x)
    (hRight : ∀ h : G,
      Measure.QuasiMeasurePreserving (fun g : G ↦ g * h) lambda lambda) :
    ∃ repaired : X → ℝ,
      Measurable repaired ∧
      repaired =ᵐ[mu] value ∧
      _root_.GD.N0230.N0644.d000297
        (fun (h : G) (x : X) ↦ h • x)
        (fun (h : G) (y : ℝ) ↦ h • y) repaired := by
  exact _root_.GD.N0230.N0605.d000342
    mu lambda value fallback hfallback hfallbackEquivariant
    (_root_.GD.N0230.N0605.d000317 value hvalue)
    (_root_.GD.N0230.N0605.d000318 value hvalue) hcov hRight

end CompleteRepair

end N0605
end N0230
end GD

#print axioms _root_.GD.N0230.N0605.d000338
#print axioms _root_.GD.N0230.N0605.d000319
#print axioms _root_.GD.N0230.N0605.d000339
#print axioms _root_.GD.N0230.N0605.d000341
#print axioms _root_.GD.N0230.N0605.d000342
#print axioms _root_.GD.N0230.N0605.d000343
