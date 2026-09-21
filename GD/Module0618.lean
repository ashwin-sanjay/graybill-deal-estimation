import GD.Module0617











open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GD
namespace N0232
namespace N0720
namespace N1156

noncomputable section

open _root_.GD.N0137
open _root_.GD.N0232.N0720.N1155
open _root_.GD.N0232.N0720.N1040




theorem d008980
    {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {residual correction : Omega → ℝ}
    (hresidual : MemLp residual 2 P)
    (hcorrection : MemLp correction 2 P)
    (hindep : IndepFun residual correction P)
    (hcentered : (∫ omega, residual omega ∂P) = 0) :
    (∫ omega, (correction omega - residual omega) ^ 2 ∂P) =
      (∫ omega, residual omega ^ 2 ∂P) +
        ∫ omega, correction omega ^ 2 ∂P := by
  have hcross : Integrable (fun omega ↦
      residual omega * correction omega) P := by
    change Integrable (residual * correction) P
    exact MemLp.integrable_mul (p := 2) (q := 2) hresidual hcorrection
  have hcrossZero : (∫ omega,
      residual omega * correction omega ∂P) = 0 := by
    rw [hindep.integral_fun_mul_eq_mul_integral
      hresidual.aestronglyMeasurable hcorrection.aestronglyMeasurable,
      hcentered, zero_mul]
  have hresidualSq : Integrable (fun omega ↦ residual omega ^ 2) P :=
    hresidual.integrable_sq
  have hcorrectionSq : Integrable (fun omega ↦ correction omega ^ 2) P :=
    hcorrection.integrable_sq
  calc
    (∫ omega, (correction omega - residual omega) ^ 2 ∂P) =
        ∫ omega, correction omega ^ 2 + residual omega ^ 2 -
          2 * (residual omega * correction omega) ∂P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun omega ↦ by ring
    _ = ((∫ omega, correction omega ^ 2 ∂P) +
          ∫ omega, residual omega ^ 2 ∂P) -
        2 * ∫ omega, residual omega * correction omega ∂P := by
      have hsub := integral_sub
        (hcorrectionSq.add hresidualSq) (hcross.const_mul 2)
      have hadd := integral_add hcorrectionSq hresidualSq
      have hmul : (∫ omega,
          2 * (residual omega * correction omega) ∂P) =
          2 * ∫ omega, residual omega * correction omega ∂P := by
        rw [integral_const_mul]
      calc
        (∫ omega, correction omega ^ 2 + residual omega ^ 2 -
            2 * (residual omega * correction omega) ∂P) =
            (∫ omega, correction omega ^ 2 + residual omega ^ 2 ∂P) -
              ∫ omega, 2 * (residual omega * correction omega) ∂P := by
          simpa only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] using hsub
        _ = ((∫ omega, correction omega ^ 2 ∂P) +
              ∫ omega, residual omega ^ 2 ∂P) -
            2 * ∫ omega, residual omega * correction omega ∂P := by
          rw [hadd, hmul]
    _ = (∫ omega, residual omega ^ 2 ∂P) +
        ∫ omega, correction omega ^ 2 ∂P := by
      rw [hcrossZero]
      ring



theorem d008981
    {Omega : Type*} [MeasurableSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    {residual correction : Omega → ℝ}
    (hresidual : MemLp residual 2 P)
    (hcorrection : MemLp correction 2 P)
    (hindep : IndepFun residual correction P)
    (hcentered : (∫ omega, residual omega ∂P) = 0) :
    (∫ omega, (correction omega - residual omega) ^ 2 ∂P) =
        ∫ omega, residual omega ^ 2 ∂P ↔
      correction =ᵐ[P] 0 := by
  rw [_root_.GD.N0232.N0720.N1156.d008980 hresidual hcorrection hindep hcentered]
  constructor
  · intro h
    have hzero : (∫ omega, correction omega ^ 2 ∂P) = 0 := by
      linarith
    have hsq : (fun omega ↦ correction omega ^ 2) =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun omega ↦ sq_nonneg (correction omega))
        hcorrection.integrable_sq).1 hzero
    filter_upwards [hsq] with omega homega
    simpa using (sq_eq_zero_iff.mp homega)
  · intro hzero
    have hsq : (fun omega ↦ correction omega ^ 2) =ᵐ[P] 0 := by
      filter_upwards [hzero] with omega homega
      simp only [Pi.zero_apply] at homega
      simp [homega]
    rw [integral_congr_ae hsq]
    simp


def d008982 (e : ℝ) (d : ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun z ↦ d (_root_.GD.N0137.d008918 e z) - e * _root_.GD.N0137.d008918 e z



theorem d008983
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (d : ℝ → ℝ) (hd : Measurable d)
    (hrisk : Integrable (fun z : ℝ × ℝ ↦
      (d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z) ^ 2)
      _root_.GD.N0232.N0720.N1155.d008950) :
    (∫ z : ℝ × ℝ,
      (d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z) ^ 2
        ∂_root_.GD.N0232.N0720.N1155.d008950) =
      e * (1 - e) +
        ∫ z : ℝ × ℝ, (_root_.GD.N0232.N0720.N1156.d008982 e d z) ^ 2
          ∂_root_.GD.N0232.N0720.N1155.d008950 := by
  let R : ℝ × ℝ → ℝ :=
    fun z ↦ Real.sqrt (e * (1 - e)) * _root_.GD.N0137.d008919 e z
  let C : ℝ × ℝ → ℝ := _root_.GD.N0232.N0720.N1156.d008982 e d
  have heprod : 0 ≤ e * (1 - e) :=
    mul_nonneg he0.le (sub_nonneg.mpr he1.le)
  have hR : MemLp R 2 _root_.GD.N0232.N0720.N1155.d008950 :=
    (_root_.GD.N0232.N0720.N1155.d008955 he0.le he1.le).const_mul _
  have herrorMeas : AEStronglyMeasurable
      (fun z : ℝ × ℝ ↦
        d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z)
      _root_.GD.N0232.N0720.N1155.d008950 := by
    exact ((hd.comp (_root_.GD.N0137.d008921 e).fst).sub
      ((measurable_const.mul
          (_root_.GD.N0137.d008921 e).fst).add
        (measurable_const.mul
          (_root_.GD.N0137.d008921 e).snd))).aestronglyMeasurable
  have herror : MemLp (fun z : ℝ × ℝ ↦
      d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z) 2
      _root_.GD.N0232.N0720.N1155.d008950 :=
    (memLp_two_iff_integrable_sq herrorMeas).2 hrisk
  have hdecomp : C = fun z ↦
      (d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z) + R z := by
    funext z
    simp only [C, R, _root_.GD.N0232.N0720.N1156.d008982, _root_.GD.N0232.N0720.N1155.d008959]
    ring
  have hC : MemLp C 2 _root_.GD.N0232.N0720.N1155.d008950 := by
    rw [hdecomp]
    exact herror.add hR
  have hindepBase :=
    _root_.GD.N0232.N0720.N1155.d008951 he0.le he1.le
  have hindep : IndepFun R C _root_.GD.N0232.N0720.N1155.d008950 := by
    have h := hindepBase.symm.comp
      (show Measurable (fun x : ℝ ↦
        Real.sqrt (e * (1 - e)) * x) by fun_prop)
      (show Measurable (fun x : ℝ ↦ d x - e * x) by fun_prop)
    change IndepFun R
      (fun z ↦ d (_root_.GD.N0137.d008918 e z) - e * _root_.GD.N0137.d008918 e z)
      _root_.GD.N0232.N0720.N1155.d008950
    simpa [R, Function.comp_def] using h
  have hcentered : (∫ z, R z ∂_root_.GD.N0232.N0720.N1155.d008950) = 0 := by
    simp only [R]
    rw [integral_const_mul,
      _root_.GD.N0232.N0720.N1155.d008956 he0.le he1.le, mul_zero]
  have hpyth := _root_.GD.N0232.N0720.N1156.d008980 hR hC hindep hcentered
  have hresidualValue :
      (∫ z, R z ^ 2 ∂_root_.GD.N0232.N0720.N1155.d008950) = e * (1 - e) := by
    simp only [R]
    rw [show (fun z : ℝ × ℝ ↦
        (Real.sqrt (e * (1 - e)) * _root_.GD.N0137.d008919 e z) ^ 2) =
      fun z ↦ (e * (1 - e)) * (_root_.GD.N0137.d008919 e z) ^ 2 by
        funext z
        rw [mul_pow, Real.sq_sqrt heprod],
      integral_const_mul,
      _root_.GD.N0232.N0720.N1155.d008957 he0.le he1.le,
      mul_one]
  have herrorEq : (fun z ↦ (C z - R z) ^ 2) =
      fun z ↦
        (d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z) ^ 2 := by
    funext z
    simp only [C, R, _root_.GD.N0232.N0720.N1156.d008982, _root_.GD.N0232.N0720.N1155.d008959]
    ring
  rw [herrorEq, hresidualValue] at hpyth
  simpa only [C] using hpyth


theorem d008984
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (d : ℝ → ℝ) (hd : Measurable d)
    (hrisk : Integrable (fun z : ℝ × ℝ ↦
      (d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z) ^ 2)
      _root_.GD.N0232.N0720.N1155.d008950) :
    (∫ z : ℝ × ℝ,
      (d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z) ^ 2
        ∂_root_.GD.N0232.N0720.N1155.d008950) - e * (1 - e) =
      ∫ z : ℝ × ℝ, (_root_.GD.N0232.N0720.N1156.d008982 e d z) ^ 2
        ∂_root_.GD.N0232.N0720.N1155.d008950 := by
  rw [_root_.GD.N0232.N0720.N1156.d008983 he0 he1 d hd hrisk]
  ring



theorem d008985
    {e delta : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (d : ℝ → ℝ) (hd : Measurable d)
    (hrisk : Integrable (fun z : ℝ × ℝ ↦
      (d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z) ^ 2)
      _root_.GD.N0232.N0720.N1155.d008950)
    (hnear : (∫ z : ℝ × ℝ,
      (d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z) ^ 2
        ∂_root_.GD.N0232.N0720.N1155.d008950) ≤ e * (1 - e) + delta) :
    (∫ z : ℝ × ℝ, (_root_.GD.N0232.N0720.N1156.d008982 e d z) ^ 2
      ∂_root_.GD.N0232.N0720.N1155.d008950) ≤ delta := by
  rw [_root_.GD.N0232.N0720.N1156.d008983 he0 he1 d hd hrisk] at hnear
  linarith



theorem d008986
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (d : ℝ → ℝ) (hd : Measurable d)
    (hrisk : Integrable (fun z : ℝ × ℝ ↦
      (d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z) ^ 2)
      _root_.GD.N0232.N0720.N1155.d008950) :
    (∫ z : ℝ × ℝ,
      (d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z) ^ 2
        ∂_root_.GD.N0232.N0720.N1155.d008950) = e * (1 - e) ↔
      _root_.GD.N0232.N0720.N1156.d008982 e d =ᵐ[_root_.GD.N0232.N0720.N1155.d008950] 0 := by
  let R : ℝ × ℝ → ℝ :=
    fun z ↦ Real.sqrt (e * (1 - e)) * _root_.GD.N0137.d008919 e z
  let C : ℝ × ℝ → ℝ := _root_.GD.N0232.N0720.N1156.d008982 e d
  have hR : MemLp R 2 _root_.GD.N0232.N0720.N1155.d008950 :=
    (_root_.GD.N0232.N0720.N1155.d008955 he0.le he1.le).const_mul _
  have herrorMeas : AEStronglyMeasurable
      (fun z : ℝ × ℝ ↦
        d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z)
      _root_.GD.N0232.N0720.N1155.d008950 := by
    exact ((hd.comp (_root_.GD.N0137.d008921 e).fst).sub
      ((measurable_const.mul
          (_root_.GD.N0137.d008921 e).fst).add
        (measurable_const.mul
          (_root_.GD.N0137.d008921 e).snd))).aestronglyMeasurable
  have herror : MemLp (fun z : ℝ × ℝ ↦
      d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z) 2
      _root_.GD.N0232.N0720.N1155.d008950 :=
    (memLp_two_iff_integrable_sq herrorMeas).2 hrisk
  have hdecomp : C = fun z ↦
      (d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z) + R z := by
    funext z
    simp only [C, R, _root_.GD.N0232.N0720.N1156.d008982, _root_.GD.N0232.N0720.N1155.d008959]
    ring
  have hC : MemLp C 2 _root_.GD.N0232.N0720.N1155.d008950 := by
    rw [hdecomp]
    exact herror.add hR
  rw [_root_.GD.N0232.N0720.N1156.d008983 he0 he1 d hd hrisk]
  constructor
  · intro h
    have htax : (∫ z, C z ^ 2 ∂_root_.GD.N0232.N0720.N1155.d008950) = 0 := by
      simpa only [C] using (by linarith :
        (∫ z, _root_.GD.N0232.N0720.N1156.d008982 e d z ^ 2 ∂_root_.GD.N0232.N0720.N1155.d008950) = 0)
    have hsq : (fun z ↦ C z ^ 2) =ᵐ[_root_.GD.N0232.N0720.N1155.d008950] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun z ↦ sq_nonneg (C z))
        hC.integrable_sq).1 htax
    filter_upwards [hsq] with z hz
    simpa only [C, Pi.zero_apply] using (sq_eq_zero_iff.mp hz)
  · intro hzero
    have hsq : (fun z ↦ _root_.GD.N0232.N0720.N1156.d008982 e d z ^ 2) =ᵐ[_root_.GD.N0232.N0720.N1155.d008950] 0 := by
      filter_upwards [hzero] with z hz
      simp only [Pi.zero_apply] at hz
      simp [hz]
    rw [integral_congr_ae hsq]
    simp

variable {A : Type*} [MeasurableSpace A]


def d008987
    (e : ℝ) (d : ℝ × A → ℝ) : ℝ × (ℝ × A) → ℝ :=
  fun z ↦ d z.2 - e * z.2.1




theorem d008988
    (nu : Measure A) [IsProbabilityMeasure nu]
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (d : ℝ × A → ℝ) (hd : Measurable d)
    (hrisk : Integrable (fun z : ℝ × (ℝ × A) ↦
      (d z.2 -
        (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1)) ^ 2)
      (_root_.GD.N0232.N0720.N1040.d008968 nu)) :
    (∫ z : ℝ × (ℝ × A),
      (d z.2 -
        (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1)) ^ 2
      ∂_root_.GD.N0232.N0720.N1040.d008968 nu) =
      e * (1 - e) +
        ∫ z : ℝ × (ℝ × A),
          (_root_.GD.N0232.N0720.N1156.d008987 e d z) ^ 2
          ∂_root_.GD.N0232.N0720.N1040.d008968 nu := by
  let Q := _root_.GD.N0232.N0720.N1040.d008968 nu
  let R : ℝ × (ℝ × A) → ℝ :=
    fun z ↦ Real.sqrt (e * (1 - e)) * z.1
  let C : ℝ × (ℝ × A) → ℝ := _root_.GD.N0232.N0720.N1156.d008987 e d
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
  have hR : MemLp R 2 Q := hfstLaw.hasGaussianLaw.memLp_two.const_mul _
  have herrorMeas : AEStronglyMeasurable
      (fun z : ℝ × (ℝ × A) ↦
        d z.2 - (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1)) Q := by
    exact ((hd.comp measurable_snd).sub
      ((measurable_const.mul measurable_snd.fst).add
        (measurable_const.mul measurable_fst))).aestronglyMeasurable
  have herror : MemLp
      (fun z : ℝ × (ℝ × A) ↦
        d z.2 - (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1))
      2 Q := (memLp_two_iff_integrable_sq herrorMeas).2 hrisk
  have hdecomp : C = fun z ↦
      (d z.2 - (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1)) + R z := by
    funext z
    simp only [C, R, _root_.GD.N0232.N0720.N1156.d008987]
    ring
  have hC : MemLp C 2 Q := by
    rw [hdecomp]
    exact herror.add hR
  have hindepBase : IndepFun
      (fun z : ℝ × (ℝ × A) ↦ z.1) (fun z ↦ z.2) Q :=
    indepFun_prod measurable_id measurable_id
  have hindep : IndepFun R C Q := by
    have h := hindepBase.comp
      (show Measurable (fun x : ℝ ↦
        Real.sqrt (e * (1 - e)) * x) by fun_prop)
      (show Measurable (fun z : ℝ × A ↦ d z - e * z.1) by fun_prop)
    change IndepFun R (fun z ↦ d z.2 - e * z.2.1) Q
    simpa [R, Function.comp_def] using h
  have hcentered : (∫ z, R z ∂Q) = 0 := by
    simp only [R]
    rw [integral_const_mul, hfstLaw.integral_eq,
      integral_id_gaussianReal, mul_zero]
  have hpyth := _root_.GD.N0232.N0720.N1156.d008980 hR hC hindep hcentered
  have hresidualValue : (∫ z, R z ^ 2 ∂Q) = e * (1 - e) := by
    simp only [R]
    rw [show (fun z : ℝ × (ℝ × A) ↦
        (Real.sqrt (e * (1 - e)) * z.1) ^ 2) =
      fun z ↦ (e * (1 - e)) * z.1 ^ 2 by
        funext z
        rw [mul_pow, Real.sq_sqrt heprod],
      integral_const_mul, _root_.GD.N0232.N0720.N1040.d008972 nu, mul_one]
  have herrorEq : (fun z ↦ (C z - R z) ^ 2) =
      fun z ↦
        (d z.2 - (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1)) ^ 2 := by
    funext z
    simp only [C, R, _root_.GD.N0232.N0720.N1156.d008987]
    ring
  rw [herrorEq, hresidualValue] at hpyth
  simpa only [C, Q] using hpyth



theorem d008989
    (nu : Measure A) [IsProbabilityMeasure nu]
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (d : ℝ × A → ℝ) (hd : Measurable d)
    (hrisk : Integrable (fun z : ℝ × (ℝ × A) ↦
      (d z.2 -
        (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1)) ^ 2)
      (_root_.GD.N0232.N0720.N1040.d008968 nu)) :
    (∫ z : ℝ × (ℝ × A),
      (d z.2 -
        (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1)) ^ 2
      ∂_root_.GD.N0232.N0720.N1040.d008968 nu) - e * (1 - e) =
      ∫ z : ℝ × (ℝ × A),
        (_root_.GD.N0232.N0720.N1156.d008987 e d z) ^ 2
        ∂_root_.GD.N0232.N0720.N1040.d008968 nu := by
  rw [_root_.GD.N0232.N0720.N1156.d008988
    nu he0 he1 d hd hrisk]
  ring


theorem d008990
    (nu : Measure A) [IsProbabilityMeasure nu]
    {e delta : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (d : ℝ × A → ℝ) (hd : Measurable d)
    (hrisk : Integrable (fun z : ℝ × (ℝ × A) ↦
      (d z.2 -
        (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1)) ^ 2)
      (_root_.GD.N0232.N0720.N1040.d008968 nu))
    (hnear : (∫ z : ℝ × (ℝ × A),
      (d z.2 -
        (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1)) ^ 2
      ∂_root_.GD.N0232.N0720.N1040.d008968 nu) ≤
        e * (1 - e) + delta) :
    (∫ z : ℝ × (ℝ × A),
      (_root_.GD.N0232.N0720.N1156.d008987 e d z) ^ 2
      ∂_root_.GD.N0232.N0720.N1040.d008968 nu) ≤ delta := by
  rw [_root_.GD.N0232.N0720.N1156.d008988
    nu he0 he1 d hd hrisk] at hnear
  linarith



theorem d008991
    (nu : Measure A) [IsProbabilityMeasure nu]
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (d : ℝ × A → ℝ) (hd : Measurable d)
    (hrisk : Integrable (fun z : ℝ × (ℝ × A) ↦
      (d z.2 -
        (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1)) ^ 2)
      (_root_.GD.N0232.N0720.N1040.d008968 nu)) :
    (∫ z : ℝ × (ℝ × A),
      (d z.2 -
        (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1)) ^ 2
      ∂_root_.GD.N0232.N0720.N1040.d008968 nu) = e * (1 - e) ↔
      _root_.GD.N0232.N0720.N1156.d008987 e d =ᵐ[_root_.GD.N0232.N0720.N1040.d008968 nu] 0 := by
  have heq := _root_.GD.N0232.N0720.N1156.d008988
    nu he0 he1 d hd hrisk
  rw [heq]
  let C : ℝ × (ℝ × A) → ℝ := _root_.GD.N0232.N0720.N1156.d008987 e d
  have herrorMeas : AEStronglyMeasurable
      (fun z : ℝ × (ℝ × A) ↦
        d z.2 - (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1))
      (_root_.GD.N0232.N0720.N1040.d008968 nu) := by
    exact ((hd.comp measurable_snd).sub
      ((measurable_const.mul measurable_snd.fst).add
        (measurable_const.mul measurable_fst))).aestronglyMeasurable
  have herror : MemLp
      (fun z : ℝ × (ℝ × A) ↦
        d z.2 - (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1))
      2 (_root_.GD.N0232.N0720.N1040.d008968 nu) :=
    (memLp_two_iff_integrable_sq herrorMeas).2 hrisk
  have hR : MemLp (fun z : ℝ × (ℝ × A) ↦
      Real.sqrt (e * (1 - e)) * z.1) 2
      (_root_.GD.N0232.N0720.N1040.d008968 nu) := by
    have hfstLaw : HasLaw (Prod.fst : ℝ × (ℝ × A) → ℝ)
        (gaussianReal 0 1) (_root_.GD.N0232.N0720.N1040.d008968 nu) :=
      (measurePreserving_fst
        (μ := gaussianReal 0 1)
        (ν := (gaussianReal 0 1).prod nu)).hasLaw
    exact hfstLaw.hasGaussianLaw.memLp_two.const_mul _
  have hC : MemLp C 2 (_root_.GD.N0232.N0720.N1040.d008968 nu) := by
    have hdecomp : C = fun z ↦
        (d z.2 - (e * z.2.1 + Real.sqrt (e * (1 - e)) * z.1)) +
          Real.sqrt (e * (1 - e)) * z.1 := by
      funext z
      simp only [C, _root_.GD.N0232.N0720.N1156.d008987]
      ring
    rw [hdecomp]
    exact herror.add hR
  constructor
  · intro h
    have htax :
        (∫ z, C z ^ 2 ∂_root_.GD.N0232.N0720.N1040.d008968 nu) = 0 := by
      simpa only [C] using (by linarith :
        (∫ z, _root_.GD.N0232.N0720.N1156.d008987 e d z ^ 2
          ∂_root_.GD.N0232.N0720.N1040.d008968 nu) = 0)
    have hsq : (fun z ↦ C z ^ 2) =ᵐ[_root_.GD.N0232.N0720.N1040.d008968 nu] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun z ↦ sq_nonneg (C z))
        hC.integrable_sq).1 htax
    filter_upwards [hsq] with z hz
    simpa only [C, Pi.zero_apply] using (sq_eq_zero_iff.mp hz)
  · intro hzero
    have hsq : (fun z ↦ _root_.GD.N0232.N0720.N1156.d008987 e d z ^ 2) =ᵐ[
        _root_.GD.N0232.N0720.N1040.d008968 nu] 0 := by
      filter_upwards [hzero] with z hz
      simp only [Pi.zero_apply] at hz
      simp [hz]
    rw [integral_congr_ae hsq]
    simp

end

end N1156
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1156.d008980
#print axioms _root_.GD.N0232.N0720.N1156.d008983
#print axioms _root_.GD.N0232.N0720.N1156.d008988
