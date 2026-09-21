import GD.Module0616
import Mathlib.MeasureTheory.Integral.Prod











open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace GD
namespace N0232
namespace N0720
namespace N1040

noncomputable section

open _root_.GD.N0137
open _root_.GD.N0232.N0720.N1155

variable {A : Type*} [MeasurableSpace A]


abbrev d008967 (nu : Measure A) :
    Measure ((ℝ × ℝ) × A) :=
  _root_.GD.N0232.N0720.N1155.d008950.prod nu


abbrev d008968 (nu : Measure A) :
    Measure (ℝ × (ℝ × A)) :=
  (gaussianReal 0 1).prod ((gaussianReal 0 1).prod nu)



def d008969 (e : ℝ) :
    ((ℝ × ℝ) × A) → ℝ × (ℝ × A) :=
  fun z ↦
    (_root_.GD.N0137.d008919 e z.1,
      (_root_.GD.N0137.d008918 e z.1, z.2))

@[fun_prop]
theorem d008970 (e : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1040.d008969 (A := A) e) := by
  unfold _root_.GD.N0232.N0720.N1040.d008969
  exact (((_root_.GD.N0137.d008921 e).snd.comp
      measurable_fst).prodMk
    (((_root_.GD.N0137.d008921 e).fst.comp
      measurable_fst).prodMk measurable_snd))



theorem d008971
    (nu : Measure A) [IsProbabilityMeasure nu]
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    (_root_.GD.N0232.N0720.N1040.d008967 nu).map
        (_root_.GD.N0232.N0720.N1040.d008969 (A := A) e) =
      _root_.GD.N0232.N0720.N1040.d008968 nu := by
  let rotate : ((ℝ × ℝ) × A) → ((ℝ × ℝ) × A) :=
    Prod.map (_root_.GD.N0137.d008920 e) id
  let swapMean : ((ℝ × ℝ) × A) → ((ℝ × ℝ) × A) :=
    Prod.map Prod.swap id
  let assoc : ((ℝ × ℝ) × A) → ℝ × (ℝ × A) :=
    (MeasurableEquiv.prodAssoc : ((ℝ × ℝ) × A) ≃ᵐ (ℝ × (ℝ × A)))
  have hrotate :
      (_root_.GD.N0232.N0720.N1040.d008967 nu).map rotate =
        _root_.GD.N0232.N0720.N1040.d008967 nu := by
    calc
      (_root_.GD.N0232.N0720.N1040.d008967 nu).map rotate =
          (_root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0137.d008920 e)).prod
            (nu.map id) := by
        exact (Measure.map_prod_map _root_.GD.N0232.N0720.N1155.d008950 nu
          (_root_.GD.N0137.d008921 e) measurable_id).symm
      _ = _root_.GD.N0232.N0720.N1040.d008967 nu := by
        rw [_root_.GD.N0137.d008927 he0 he1, Measure.map_id]
  have hfun : _root_.GD.N0232.N0720.N1040.d008969 (A := A) e =
      (assoc ∘ swapMean) ∘ rotate := by
    funext z
    rfl
  rw [hfun]
  calc
    (_root_.GD.N0232.N0720.N1040.d008967 nu).map ((assoc ∘ swapMean) ∘ rotate) =
        ((_root_.GD.N0232.N0720.N1040.d008967 nu).map rotate).map
          (assoc ∘ swapMean) := by
      rw [Measure.map_map]
      · exact (by fun_prop : Measurable (assoc ∘ swapMean))
      · exact (by fun_prop : Measurable rotate)
    _ = (_root_.GD.N0232.N0720.N1040.d008967 nu).map (assoc ∘ swapMean) := by
      rw [hrotate]
    _ = ((_root_.GD.N0232.N0720.N1040.d008967 nu).map swapMean).map assoc := by
      rw [Measure.map_map]
      · exact (by fun_prop : Measurable assoc)
      · exact (by fun_prop : Measurable swapMean)
    _ = (((_root_.GD.N0232.N0720.N1155.d008950.map Prod.swap).prod (nu.map id))).map
          assoc := by
      congr 1
      exact (Measure.map_prod_map _root_.GD.N0232.N0720.N1155.d008950 nu
        measurable_swap measurable_id).symm
    _ = (_root_.GD.N0232.N0720.N1040.d008967 nu).map assoc := by
      rw [Measure.prod_swap, Measure.map_id]
    _ = _root_.GD.N0232.N0720.N1040.d008968 nu := by
      exact Measure.prodAssoc_prod



theorem d008972
    (nu : Measure A) [IsProbabilityMeasure nu] :
    (∫ z : ℝ × (ℝ × A), z.1 ^ 2
      ∂_root_.GD.N0232.N0720.N1040.d008968 nu) = 1 := by
  have hmeas : AEMeasurable (Prod.fst : ℝ × (ℝ × A) → ℝ)
      (_root_.GD.N0232.N0720.N1040.d008968 nu) := measurable_fst.aemeasurable
  have hsqMeas : AEStronglyMeasurable (fun x : ℝ ↦ x ^ 2)
      ((_root_.GD.N0232.N0720.N1040.d008968 nu).map Prod.fst) :=
    (measurable_id.pow_const 2).aestronglyMeasurable
  calc
    (∫ z : ℝ × (ℝ × A), z.1 ^ 2
        ∂_root_.GD.N0232.N0720.N1040.d008968 nu) =
        ∫ x, x ^ 2
          ∂(_root_.GD.N0232.N0720.N1040.d008968 nu).map Prod.fst := by
      exact (integral_map (φ := (Prod.fst : ℝ × (ℝ × A) → ℝ))
        (f := fun x : ℝ ↦ x ^ 2) hmeas hsqMeas).symm
    _ = ∫ x, x ^ 2 ∂gaussianReal 0 1 := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    _ = 1 := by
      have hvar := variance_fun_id_gaussianReal
        (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
      rw [variance_eq_integral measurable_id'.aemeasurable] at hvar
      simpa using hvar


theorem d008973
    (nu : Measure A) [IsProbabilityMeasure nu]
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (d : ℝ × A → ℝ) (hd : Measurable d)
    (hrisk : Integrable (fun z : ℝ × (ℝ × A) ↦
      (d z.2 -
        (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1)) ^ 2)
      (_root_.GD.N0232.N0720.N1040.d008968 nu)) :
    e * (1 - e) ≤
      ∫ z : ℝ × (ℝ × A),
        (d z.2 -
          (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1)) ^ 2
        ∂_root_.GD.N0232.N0720.N1040.d008968 nu := by
  let Q := _root_.GD.N0232.N0720.N1040.d008968 nu
  let R : ℝ × (ℝ × A) → ℝ :=
    fun z ↦ Real.sqrt (e * (1 - e)) * z.1
  let C : ℝ × (ℝ × A) → ℝ :=
    fun z ↦ d z.2 - e * z.2.1
  letI : IsProbabilityMeasure Q := by
    unfold Q _root_.GD.N0232.N0720.N1040.d008968
    infer_instance
  have heprod : 0 ≤ e * (1 - e) :=
    mul_nonneg he0.le (sub_nonneg.mpr he1.le)
  have hfstLaw : HasLaw (Prod.fst : ℝ × (ℝ × A) → ℝ)
      (gaussianReal 0 1) Q := by
    exact (measurePreserving_fst
      (μ := gaussianReal 0 1)
      (ν := (gaussianReal 0 1).prod nu)).hasLaw
  have hR : MemLp R 2 Q :=
    hfstLaw.hasGaussianLaw.memLp_two.const_mul _
  have herrorMeas : AEStronglyMeasurable
      (fun z : ℝ × (ℝ × A) ↦
        d z.2 - (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1)) Q := by
    exact ((hd.comp measurable_snd).sub
      ((measurable_const.mul measurable_snd.fst).add
        (measurable_const.mul measurable_fst))).aestronglyMeasurable
  have herror : MemLp
      (fun z : ℝ × (ℝ × A) ↦
        d z.2 - (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1))
      2 Q :=
    (memLp_two_iff_integrable_sq herrorMeas).2 hrisk
  have hdecomp : C = fun z ↦
      (d z.2 - (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1)) + R z := by
    funext z
    simp only [C, R]
    ring
  have hC : MemLp C 2 Q := by
    rw [hdecomp]
    exact herror.add hR
  have hindepBase : IndepFun
      (fun z : ℝ × (ℝ × A) ↦ z.1) (fun z ↦ z.2) Q := by
    exact indepFun_prod measurable_id measurable_id
  have hindep : IndepFun R C Q := by
    have h := hindepBase.comp
      (show Measurable (fun x : ℝ ↦
        Real.sqrt (e * (1 - e)) * x) by fun_prop)
      (show Measurable (fun z : ℝ × A ↦ d z - e * z.1) by
        exact hd.sub (measurable_const.mul measurable_fst))
    simpa [R, C, Function.comp_def] using h
  have hcentered : (∫ z, R z ∂Q) = 0 := by
    simp only [R]
    rw [integral_const_mul, hfstLaw.integral_eq,
      integral_id_gaussianReal, mul_zero]
  have hlower := _root_.GD.N0232.N0720.N1155.d008958 hR hC hindep hcentered
  have hresidualValue : (∫ z, R z ^ 2 ∂Q) = e * (1 - e) := by
    simp only [R]
    rw [show (fun z : ℝ × (ℝ × A) ↦
        (Real.sqrt (e * (1 - e)) * z.1) ^ 2) =
      fun z ↦ (e * (1 - e)) * z.1 ^ 2 by
        funext z
        rw [mul_pow, Real.sq_sqrt heprod],
      integral_const_mul,
      _root_.GD.N0232.N0720.N1040.d008972 nu,
      mul_one]
  have herrorEq : (fun z ↦ (C z - R z) ^ 2) =
      fun z : ℝ × (ℝ × A) ↦
        (d z.2 -
          (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1)) ^ 2 := by
    funext z
    simp only [C, R]
    ring
  rw [hresidualValue, herrorEq] at hlower
  exact hlower



theorem d008974
    (nu : Measure A) [IsProbabilityMeasure nu]
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (d : ℝ × A → ℝ) (hd : Measurable d)
    (hint : Integrable (fun z : (ℝ × ℝ) × A ↦
      (d (Real.sqrt e * z.1.1 + Real.sqrt (1 - e) * z.1.2, z.2) -
        Real.sqrt e * z.1.1) ^ 2) (_root_.GD.N0232.N0720.N1040.d008967 nu)) :
    e * (1 - e) ≤
      ∫ z : (ℝ × ℝ) × A,
        (d (Real.sqrt e * z.1.1 + Real.sqrt (1 - e) * z.1.2, z.2) -
          Real.sqrt e * z.1.1) ^ 2
        ∂_root_.GD.N0232.N0720.N1040.d008967 nu := by
  let rot := _root_.GD.N0232.N0720.N1040.d008969 (A := A) e
  let loss : ℝ × (ℝ × A) → ℝ := fun z ↦
    (d z.2 -
      (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1)) ^ 2
  have hrot : Measurable rot :=
    _root_.GD.N0232.N0720.N1040.d008970 (A := A) e
  have hloss : Measurable loss := by
    unfold loss
    fun_prop
  have hcomp : ∀ z : (ℝ × ℝ) × A,
      loss (rot z) =
        (d (Real.sqrt e * z.1.1 + Real.sqrt (1 - e) * z.1.2, z.2) -
          Real.sqrt e * z.1.1) ^ 2 := by
    intro z
    unfold loss rot _root_.GD.N0232.N0720.N1040.d008969
    change
      (d (_root_.GD.N0137.d008918 e z.1, z.2) - _root_.GD.N0232.N0720.N1155.d008959 e z.1) ^ 2 = _
    rw [_root_.GD.N0232.N0720.N1155.d008961 he0.le he1.le]
    rfl
  have hlossInt : Integrable loss (_root_.GD.N0232.N0720.N1040.d008968 nu) := by
    rw [← _root_.GD.N0232.N0720.N1040.d008971 nu he0.le he1.le]
    apply (integrable_map_measure hloss.aestronglyMeasurable
      hrot.aemeasurable).2
    exact hint.congr
      (Filter.Eventually.of_forall fun z ↦ (hcomp z).symm)
  have hlower := _root_.GD.N0232.N0720.N1040.d008973
    nu he0 he1 d hd hlossInt
  calc
    e * (1 - e) ≤ ∫ z, loss z
        ∂_root_.GD.N0232.N0720.N1040.d008968 nu := hlower
    _ = ∫ z, loss z
        ∂(_root_.GD.N0232.N0720.N1040.d008967 nu).map rot := by
      rw [_root_.GD.N0232.N0720.N1040.d008971 nu he0.le he1.le]
    _ = ∫ z, loss (rot z) ∂_root_.GD.N0232.N0720.N1040.d008967 nu := by
      exact integral_map hrot.aemeasurable hloss.aestronglyMeasurable
    _ = ∫ z : (ℝ × ℝ) × A,
        (d (Real.sqrt e * z.1.1 + Real.sqrt (1 - e) * z.1.2, z.2) -
          Real.sqrt e * z.1.1) ^ 2
        ∂_root_.GD.N0232.N0720.N1040.d008967 nu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hcomp



def d008975
    (nu : Measure A) (d : ℝ × A → ℝ) (mu : ℝ) : ℝ :=
  ∫ noise, (∫ a,
    (d (mu + noise, a) - mu) ^ 2 ∂nu) ∂gaussianReal 0 1



theorem d008976
    (nu : Measure A) [IsProbabilityMeasure nu]
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (d : ℝ × A → ℝ) (hd : Measurable d)
    (hint : Integrable (fun z : (ℝ × ℝ) × A ↦
      (d (_root_.GD.N0232.N0720.N1155.d008964 e * z.1.1 + z.1.2, z.2) -
        _root_.GD.N0232.N0720.N1155.d008964 e * z.1.1) ^ 2) (_root_.GD.N0232.N0720.N1040.d008967 nu)) :
    e ≤ ∫ mu, _root_.GD.N0232.N0720.N1040.d008975 nu d
        (_root_.GD.N0232.N0720.N1155.d008964 e * mu) ∂gaussianReal 0 1 := by
  let a := Real.sqrt (1 - e)
  let dUnit : ℝ × A → ℝ := fun x ↦ a * d (x.1 / a, x.2)
  have hcomp : 0 < 1 - e := sub_pos.mpr he1
  have ha : 0 < a := Real.sqrt_pos.2 hcomp
  have haSq : a ^ 2 = 1 - e := Real.sq_sqrt hcomp.le
  have hpoint : ∀ z : (ℝ × ℝ) × A,
      (dUnit (Real.sqrt e * z.1.1 + Real.sqrt (1 - e) * z.1.2, z.2) -
          Real.sqrt e * z.1.1) ^ 2 =
        (1 - e) *
          (d (_root_.GD.N0232.N0720.N1155.d008964 e * z.1.1 + z.1.2, z.2) -
            _root_.GD.N0232.N0720.N1155.d008964 e * z.1.1) ^ 2 := by
    intro z
    have harg :
        (Real.sqrt e * z.1.1 + Real.sqrt (1 - e) * z.1.2) / a =
          _root_.GD.N0232.N0720.N1155.d008964 e * z.1.1 + z.1.2 := by
      unfold a _root_.GD.N0232.N0720.N1155.d008964
      field_simp [ha.ne']
    have hmu : Real.sqrt e * z.1.1 =
        a * (_root_.GD.N0232.N0720.N1155.d008964 e * z.1.1) := by
      unfold a _root_.GD.N0232.N0720.N1155.d008964
      field_simp [ha.ne']
    have hlinear :
        dUnit (Real.sqrt e * z.1.1 + Real.sqrt (1 - e) * z.1.2, z.2) -
            Real.sqrt e * z.1.1 =
          a * (d (_root_.GD.N0232.N0720.N1155.d008964 e * z.1.1 + z.1.2, z.2) -
            _root_.GD.N0232.N0720.N1155.d008964 e * z.1.1) := by
      unfold dUnit
      rw [harg, hmu]
      ring
    rw [hlinear, mul_pow, haSq]
  have hintUnit : Integrable (fun z : (ℝ × ℝ) × A ↦
      (dUnit (Real.sqrt e * z.1.1 + Real.sqrt (1 - e) * z.1.2, z.2) -
        Real.sqrt e * z.1.1) ^ 2) (_root_.GD.N0232.N0720.N1040.d008967 nu) := by
    refine (hint.const_mul (1 - e)).congr ?_
    exact Filter.Eventually.of_forall fun z ↦ (hpoint z).symm
  have hlower := _root_.GD.N0232.N0720.N1040.d008974
    nu he0 he1 dUnit (by fun_prop) hintUnit
  have hprod := integral_prod
    (μ := _root_.GD.N0232.N0720.N1155.d008950) (ν := nu)
    (fun z : (ℝ × ℝ) × A ↦
      (d (_root_.GD.N0232.N0720.N1155.d008964 e * z.1.1 + z.1.2, z.2) -
        _root_.GD.N0232.N0720.N1155.d008964 e * z.1.1) ^ 2) hint
  have hpairInt : Integrable (fun z : ℝ × ℝ ↦
      ∫ a, (d (_root_.GD.N0232.N0720.N1155.d008964 e * z.1 + z.2, a) -
        _root_.GD.N0232.N0720.N1155.d008964 e * z.1) ^ 2 ∂nu) _root_.GD.N0232.N0720.N1155.d008950 :=
    hint.integral_prod_left
  have hprodPair := integral_prod
    (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
    (fun z : ℝ × ℝ ↦
      ∫ a, (d (_root_.GD.N0232.N0720.N1155.d008964 e * z.1 + z.2, a) -
        _root_.GD.N0232.N0720.N1155.d008964 e * z.1) ^ 2 ∂nu) hpairInt
  have hscaled :
      (∫ z : (ℝ × ℝ) × A,
        (dUnit (Real.sqrt e * z.1.1 + Real.sqrt (1 - e) * z.1.2, z.2) -
          Real.sqrt e * z.1.1) ^ 2 ∂_root_.GD.N0232.N0720.N1040.d008967 nu) =
        (1 - e) * ∫ mu, _root_.GD.N0232.N0720.N1040.d008975 nu d
          (_root_.GD.N0232.N0720.N1155.d008964 e * mu) ∂gaussianReal 0 1 := by
    calc
      _ = ∫ z : (ℝ × ℝ) × A, (1 - e) *
          (d (_root_.GD.N0232.N0720.N1155.d008964 e * z.1.1 + z.1.2, z.2) -
            _root_.GD.N0232.N0720.N1155.d008964 e * z.1.1) ^ 2
          ∂_root_.GD.N0232.N0720.N1040.d008967 nu := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = (1 - e) * ∫ z : (ℝ × ℝ) × A,
          (d (_root_.GD.N0232.N0720.N1155.d008964 e * z.1.1 + z.1.2, z.2) -
            _root_.GD.N0232.N0720.N1155.d008964 e * z.1.1) ^ 2
          ∂_root_.GD.N0232.N0720.N1040.d008967 nu := by rw [integral_const_mul]
      _ = (1 - e) * ∫ mu, _root_.GD.N0232.N0720.N1040.d008975 nu d
          (_root_.GD.N0232.N0720.N1155.d008964 e * mu) ∂gaussianReal 0 1 := by
        rw [hprod, hprodPair]
        unfold _root_.GD.N0232.N0720.N1040.d008975
        rfl
  rw [hscaled] at hlower
  exact le_of_mul_le_mul_left (by simpa [mul_comm] using hlower) hcomp






theorem d008977
    (nu : Measure A) [IsProbabilityMeasure nu]
    (d : ℝ × A → ℝ) (hd : Measurable d)
    (hsections : ∀ mu : ℝ,
      Integrable (fun z : ℝ × A ↦
        (d (mu + z.1, z.2) - mu) ^ 2)
        ((gaussianReal 0 1).prod nu))
    (hbounded : BddAbove
      (Set.range (_root_.GD.N0232.N0720.N1040.d008975 nu d)))
    (e : ℝ) :
    Integrable (fun z : (ℝ × ℝ) × A ↦
      (d (_root_.GD.N0232.N0720.N1155.d008964 e * z.1.1 + z.1.2, z.2) -
        _root_.GD.N0232.N0720.N1155.d008964 e * z.1.1) ^ 2)
      (_root_.GD.N0232.N0720.N1040.d008967 nu) := by
  let gamma : Measure ℝ := gaussianReal 0 1
  let scale := _root_.GD.N0232.N0720.N1155.d008964 e
  let lossRight : ℝ × (ℝ × A) → ℝ := fun z ↦
    (d (scale * z.1 + z.2.1, z.2.2) - scale * z.1) ^ 2
  have hlossMeas : Measurable lossRight := by
    unfold lossRight
    fun_prop
  have hriskNonneg : ∀ mu : ℝ,
      0 ≤ _root_.GD.N0232.N0720.N1040.d008975 nu d mu := by
    intro mu
    unfold _root_.GD.N0232.N0720.N1040.d008975
    apply integral_nonneg
    intro noise
    apply integral_nonneg
    intro a
    exact sq_nonneg _
  have hriskEq : ∀ mu : ℝ,
      (∫ z : ℝ × A,
          (d (mu + z.1, z.2) - mu) ^ 2
          ∂((gaussianReal 0 1).prod nu)) =
        _root_.GD.N0232.N0720.N1040.d008975 nu d mu := by
    intro mu
    rw [integral_prod _ (hsections mu)]
    rfl
  obtain ⟨U, hU⟩ := hbounded
  have hlossRight : Integrable lossRight
      (gamma.prod ((gaussianReal 0 1).prod nu)) := by
    apply (integrable_prod_iff hlossMeas.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun x ↦ by
        simpa only [lossRight, scale, gamma] using
          hsections (_root_.GD.N0232.N0720.N1155.d008964 e * x)
    · have houterMeas : AEStronglyMeasurable
          (fun x : ℝ ↦
            ∫ z : ℝ × A, ‖lossRight (x, z)‖
              ∂((gaussianReal 0 1).prod nu)) gamma :=
        hlossMeas.stronglyMeasurable.norm.integral_prod_right'
          |>.aestronglyMeasurable
      apply Integrable.of_bound houterMeas U
      exact Filter.Eventually.of_forall fun x ↦ by
        have hinner :
            (∫ z : ℝ × A, ‖lossRight (x, z)‖
                ∂((gaussianReal 0 1).prod nu)) =
              _root_.GD.N0232.N0720.N1040.d008975 nu d
                (_root_.GD.N0232.N0720.N1155.d008964 e * x) := by
          calc
            (∫ z : ℝ × A, ‖lossRight (x, z)‖
                ∂((gaussianReal 0 1).prod nu)) =
                ∫ z : ℝ × A,
                  (d (_root_.GD.N0232.N0720.N1155.d008964 e * x + z.1, z.2) -
                    _root_.GD.N0232.N0720.N1155.d008964 e * x) ^ 2
                  ∂((gaussianReal 0 1).prod nu) := by
              apply integral_congr_ae
              filter_upwards [] with z
              simp only [lossRight, scale, Real.norm_eq_abs, abs_sq]
            _ = _root_.GD.N0232.N0720.N1040.d008975 nu d
                (_root_.GD.N0232.N0720.N1155.d008964 e * x) :=
              hriskEq (_root_.GD.N0232.N0720.N1155.d008964 e * x)
        rw [hinner, Real.norm_eq_abs,
          abs_of_nonneg (hriskNonneg (_root_.GD.N0232.N0720.N1155.d008964 e * x))]
        exact hU ⟨_root_.GD.N0232.N0720.N1155.d008964 e * x, rfl⟩
  let assoc : ((ℝ × ℝ) × A) → ℝ × (ℝ × A) :=
    (MeasurableEquiv.prodAssoc : ((ℝ × ℝ) × A) ≃ᵐ ℝ × (ℝ × A))
  have hAssoc : MeasurePreserving assoc
      ((gamma.prod (gaussianReal 0 1)).prod nu)
      (gamma.prod ((gaussianReal 0 1).prod nu)) := by
    exact measurePreserving_prodAssoc gamma (gaussianReal 0 1) nu
  have hleft : Integrable (lossRight ∘ assoc)
      ((gamma.prod (gaussianReal 0 1)).prod nu) :=
    (hAssoc.integrable_comp_emb
      (MeasurableEquiv.prodAssoc :
        ((ℝ × ℝ) × A) ≃ᵐ ℝ × (ℝ × A)).measurableEmbedding).2
      hlossRight
  change Integrable
    (fun z : (ℝ × ℝ) × A ↦
      (d (_root_.GD.N0232.N0720.N1155.d008964 e * z.1.1 + z.1.2, z.2) -
        _root_.GD.N0232.N0720.N1155.d008964 e * z.1.1) ^ 2)
    (((gaussianReal 0 1).prod (gaussianReal 0 1)).prod nu)
  refine hleft.congr ?_
  filter_upwards [] with z
  rcases z with ⟨⟨x, y⟩, a⟩
  rfl


theorem d008978
    (nu : Measure A) [IsProbabilityMeasure nu]
    (d : ℝ × A → ℝ) (hd : Measurable d)
    (hbounded : BddAbove
      (Set.range (_root_.GD.N0232.N0720.N1040.d008975 nu d)))
    (hproper : ∀ e : ℝ, 0 < e → e < 1 →
      Integrable (fun z : (ℝ × ℝ) × A ↦
        (d (_root_.GD.N0232.N0720.N1155.d008964 e * z.1.1 + z.1.2, z.2) -
          _root_.GD.N0232.N0720.N1155.d008964 e * z.1.1) ^ 2)
        (_root_.GD.N0232.N0720.N1040.d008967 nu)) :
    1 ≤ ⨆ mu : ℝ, _root_.GD.N0232.N0720.N1040.d008975 nu d mu := by
  let S := ⨆ mu : ℝ, _root_.GD.N0232.N0720.N1040.d008975 nu d mu
  have hzeroNonneg : 0 ≤ _root_.GD.N0232.N0720.N1040.d008975 nu d 0 := by
    apply integral_nonneg
    intro noise
    apply integral_nonneg
    intro a
    exact sq_nonneg _
  have hzeroLe : _root_.GD.N0232.N0720.N1040.d008975 nu d 0 ≤ S :=
    le_ciSup hbounded 0
  have hS0 : 0 ≤ S := hzeroNonneg.trans hzeroLe
  by_contra hnot
  have hSlt : S < 1 := lt_of_not_ge hnot
  let e : ℝ := (S + 1) / 2
  have he0 : 0 < e := by dsimp [e]; linarith
  have he1 : e < 1 := by dsimp [e]; linarith
  have heLower := _root_.GD.N0232.N0720.N1040.d008976
    nu he0 he1 d hd (hproper e he0 he1)
  have houterInt : Integrable
      (fun z ↦ _root_.GD.N0232.N0720.N1040.d008975 nu d (_root_.GD.N0232.N0720.N1155.d008964 e * z))
      (gaussianReal 0 1) := by
    exact (hproper e he0 he1).integral_prod_left.integral_prod_left
  have hconstInt : Integrable (fun _ : ℝ ↦ S) (gaussianReal 0 1) :=
    integrable_const S
  have hupper :
      (∫ z, _root_.GD.N0232.N0720.N1040.d008975 nu d (_root_.GD.N0232.N0720.N1155.d008964 e * z)
        ∂gaussianReal 0 1) ≤ S := by
    calc
      _ ≤ ∫ _z : ℝ, S ∂gaussianReal 0 1 := by
        apply integral_mono houterInt hconstInt
        intro z
        exact le_ciSup hbounded (_root_.GD.N0232.N0720.N1155.d008964 e * z)
      _ = S := by simp
  dsimp [e] at heLower
  linarith




theorem d008979
    (nu : Measure A) [IsProbabilityMeasure nu]
    (d : ℝ × A → ℝ) (hd : Measurable d)
    (hsections : ∀ mu : ℝ,
      Integrable (fun z : ℝ × A ↦
        (d (mu + z.1, z.2) - mu) ^ 2)
        ((gaussianReal 0 1).prod nu))
    (hbounded : BddAbove
      (Set.range (_root_.GD.N0232.N0720.N1040.d008975 nu d))) :
    1 ≤ ⨆ mu : ℝ, _root_.GD.N0232.N0720.N1040.d008975 nu d mu := by
  apply _root_.GD.N0232.N0720.N1040.d008978 nu d hd hbounded
  intro e he0 he1
  exact _root_.GD.N0232.N0720.N1040.d008977
    nu d hd hsections hbounded e

end

end N1040
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1040.d008973
#print axioms _root_.GD.N0232.N0720.N1040.d008977
#print axioms _root_.GD.N0232.N0720.N1040.d008978
#print axioms _root_.GD.N0232.N0720.N1040.d008979
