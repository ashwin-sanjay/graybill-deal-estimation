import GD.Module0615
import GD.Module0428
import Mathlib.MeasureTheory.Integral.Prod
















open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace GD
namespace N0232
namespace N0720
namespace N1155

noncomputable section

open _root_.GD.N0137


abbrev d008950 : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod (gaussianReal 0 1)

local instance : IsProbabilityMeasure _root_.GD.N0232.N0720.N1155.d008950 := by
  unfold _root_.GD.N0232.N0720.N1155.d008950
  infer_instance


theorem d008951
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    IndepFun (_root_.GD.N0137.d008918 e) (_root_.GD.N0137.d008919 e)
      _root_.GD.N0232.N0720.N1155.d008950 := by
  have hmap := _root_.GD.N0137.d008927 he0 he1
  have hO : _root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0137.d008918 e) =
      gaussianReal 0 1 := by
    calc
      _root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0137.d008918 e) =
          (_root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0137.d008920 e)).map
            Prod.fst := by
        rw [Measure.map_map]
        · rfl
        · exact measurable_fst
        · exact _root_.GD.N0137.d008921 e
      _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).map Prod.fst := by
        rw [hmap]
      _ = gaussianReal 0 1 := by
        rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hC : _root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0137.d008919 e) =
      gaussianReal 0 1 := by
    calc
      _root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0137.d008919 e) =
          (_root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0137.d008920 e)).map
            Prod.snd := by
        rw [Measure.map_map]
        · rfl
        · exact measurable_snd
        · exact _root_.GD.N0137.d008921 e
      _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).map Prod.snd := by
        rw [hmap]
      _ = gaussianReal 0 1 := by
        rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hOmeas : AEMeasurable (_root_.GD.N0137.d008918 e)
      _root_.GD.N0232.N0720.N1155.d008950 :=
    (_root_.GD.N0137.d008921 e).fst.aemeasurable
  have hCmeas : AEMeasurable (_root_.GD.N0137.d008919 e)
      _root_.GD.N0232.N0720.N1155.d008950 :=
    (_root_.GD.N0137.d008921 e).snd.aemeasurable
  rw [indepFun_iff_map_prod_eq_prod_map_map
    hOmeas hCmeas]
  change _root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0137.d008920 e) =
    (_root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0137.d008918 e)).prod
      (_root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0137.d008919 e))
  rw [hmap, hO, hC]


theorem d008952
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    _root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0137.d008918 e) = gaussianReal 0 1 := by
  have h := _root_.GD.N0232.N0720.N1155.d008951 he0 he1
  have hmap := _root_.GD.N0137.d008927 he0 he1
  calc
    _root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0137.d008918 e) =
        (_root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0137.d008920 e)).map
          Prod.fst := by
      rw [Measure.map_map]
      · rfl
      · exact measurable_fst
      · exact _root_.GD.N0137.d008921 e
    _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).map Prod.fst := by
      rw [hmap]
    _ = gaussianReal 0 1 := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]


theorem d008953
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    _root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0137.d008919 e) = gaussianReal 0 1 := by
  have hmap := _root_.GD.N0137.d008927 he0 he1
  calc
    _root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0137.d008919 e) =
        (_root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0137.d008920 e)).map
          Prod.snd := by
      rw [Measure.map_map]
      · rfl
      · exact measurable_snd
      · exact _root_.GD.N0137.d008921 e
    _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).map Prod.snd := by
      rw [hmap]
    _ = gaussianReal 0 1 := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]


theorem d008954
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    MemLp (_root_.GD.N0137.d008918 e) 2 _root_.GD.N0232.N0720.N1155.d008950 := by
  have hLaw : HasLaw (_root_.GD.N0137.d008918 e) (gaussianReal 0 1)
      _root_.GD.N0232.N0720.N1155.d008950 :=
    ⟨(_root_.GD.N0137.d008921 e).fst.aemeasurable,
      _root_.GD.N0232.N0720.N1155.d008952 he0 he1⟩
  exact hLaw.hasGaussianLaw.memLp_two


theorem d008955
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    MemLp (_root_.GD.N0137.d008919 e) 2 _root_.GD.N0232.N0720.N1155.d008950 := by
  have hLaw : HasLaw (_root_.GD.N0137.d008919 e) (gaussianReal 0 1)
      _root_.GD.N0232.N0720.N1155.d008950 :=
    ⟨(_root_.GD.N0137.d008921 e).snd.aemeasurable,
      _root_.GD.N0232.N0720.N1155.d008953 he0 he1⟩
  exact hLaw.hasGaussianLaw.memLp_two


theorem d008956
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    (∫ z, _root_.GD.N0137.d008919 e z ∂_root_.GD.N0232.N0720.N1155.d008950) = 0 := by
  have hLaw : HasLaw (_root_.GD.N0137.d008919 e) (gaussianReal 0 1)
      _root_.GD.N0232.N0720.N1155.d008950 :=
    ⟨(_root_.GD.N0137.d008921 e).snd.aemeasurable,
      _root_.GD.N0232.N0720.N1155.d008953 he0 he1⟩
  rw [hLaw.integral_eq, integral_id_gaussianReal]


theorem d008957
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    (∫ z, (_root_.GD.N0137.d008919 e z) ^ 2 ∂_root_.GD.N0232.N0720.N1155.d008950) = 1 := by
  have hmeas : AEMeasurable (_root_.GD.N0137.d008919 e)
      _root_.GD.N0232.N0720.N1155.d008950 :=
    (_root_.GD.N0137.d008921 e).snd.aemeasurable
  have hsqMeas : AEStronglyMeasurable (fun x : ℝ => x ^ 2)
      (_root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0137.d008919 e)) :=
    (measurable_id.pow_const 2).aestronglyMeasurable
  calc
    (integral _root_.GD.N0232.N0720.N1155.d008950 fun z => (_root_.GD.N0137.d008919 e z) ^ 2) =
        ∫ x, x ^ 2 ∂_root_.GD.N0232.N0720.N1155.d008950.map (_root_.GD.N0137.d008919 e) := by
      exact (integral_map (φ := _root_.GD.N0137.d008919 e)
        (f := fun x : ℝ => x ^ 2) hmeas hsqMeas).symm
    _ = ∫ x, x ^ 2 ∂gaussianReal 0 1 := by
      rw [_root_.GD.N0232.N0720.N1155.d008953 he0 he1]
    _ = 1 := by
      have hvar := variance_fun_id_gaussianReal
        (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
      rw [variance_eq_integral measurable_id'.aemeasurable] at hvar
      simpa using hvar



theorem d008958
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {residual correction : Ω → ℝ}
    (hresidual : MemLp residual 2 P)
    (hcorrection : MemLp correction 2 P)
    (hindep : IndepFun residual correction P)
    (hcentered : (∫ omega, residual omega ∂P) = 0) :
    (∫ omega, residual omega ^ 2 ∂P) ≤
      ∫ omega, (correction omega - residual omega) ^ 2 ∂P := by
  have hcross : Integrable (fun omega =>
      residual omega * correction omega) P := by
    change Integrable (residual * correction) P
    exact MemLp.integrable_mul (p := 2) (q := 2) hresidual hcorrection
  have hcrossZero : (∫ omega,
      residual omega * correction omega ∂P) = 0 := by
    rw [hindep.integral_fun_mul_eq_mul_integral
      hresidual.aestronglyMeasurable hcorrection.aestronglyMeasurable,
      hcentered, zero_mul]
  have hresidualSq : Integrable (fun omega => residual omega ^ 2) P :=
    hresidual.integrable_sq
  have hcorrectionSq : Integrable (fun omega => correction omega ^ 2) P :=
    hcorrection.integrable_sq
  calc
    (∫ omega, residual omega ^ 2 ∂P) ≤
        (∫ omega, correction omega ^ 2 ∂P) +
          ∫ omega, residual omega ^ 2 ∂P := by
      exact le_add_of_nonneg_left (integral_nonneg fun _ => sq_nonneg _)
    _ = ∫ omega, (correction omega - residual omega) ^ 2 ∂P := by
      symm
      calc
        (∫ omega, (correction omega - residual omega) ^ 2 ∂P) =
            ∫ omega, correction omega ^ 2 + residual omega ^ 2 -
              2 * (residual omega * correction omega) ∂P := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun omega => by ring
        _ = (∫ omega, correction omega ^ 2 ∂P) +
            ∫ omega, residual omega ^ 2 ∂P := by
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
            _ = (∫ omega, correction omega ^ 2 ∂P) +
                ∫ omega, residual omega ^ 2 ∂P := by
              rw [hcrossZero]
              ring


def d008959 (e : ℝ) (z : ℝ × ℝ) : ℝ :=
  e * _root_.GD.N0137.d008918 e z +
    Real.sqrt (e * (1 - e)) * _root_.GD.N0137.d008919 e z






theorem d008960
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (d : ℝ → ℝ) (hd : Measurable d)
    (hrisk : Integrable (fun z : ℝ × ℝ =>
      (d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z) ^ 2)
      _root_.GD.N0232.N0720.N1155.d008950) :
    e * (1 - e) ≤ ∫ z : ℝ × ℝ,
      (d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z) ^ 2
        ∂_root_.GD.N0232.N0720.N1155.d008950 := by
  let O : ℝ × ℝ → ℝ := _root_.GD.N0137.d008918 e
  let R : ℝ × ℝ → ℝ :=
    fun z => Real.sqrt (e * (1 - e)) * _root_.GD.N0137.d008919 e z
  let C : ℝ × ℝ → ℝ := fun z => d (O z) - e * O z
  have heprod : 0 ≤ e * (1 - e) :=
    mul_nonneg he0.le (sub_nonneg.mpr he1.le)
  have hR : MemLp R 2 _root_.GD.N0232.N0720.N1155.d008950 :=
    (_root_.GD.N0232.N0720.N1155.d008955 he0.le he1.le).const_mul _
  have herrorMeas : AEStronglyMeasurable
      (fun z : ℝ × ℝ =>
        d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z)
      _root_.GD.N0232.N0720.N1155.d008950 := by
    exact ((hd.comp (_root_.GD.N0137.d008921 e).fst).sub
      ((measurable_const.mul
          (_root_.GD.N0137.d008921 e).fst).add
        (measurable_const.mul
          (_root_.GD.N0137.d008921 e).snd))).aestronglyMeasurable
  have herror : MemLp (fun z : ℝ × ℝ =>
      d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z) 2
      _root_.GD.N0232.N0720.N1155.d008950 :=
    (memLp_two_iff_integrable_sq herrorMeas).2 hrisk
  have hdecomp : C = fun z =>
      (d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z) + R z := by
    funext z
    simp only [C, R, O, _root_.GD.N0232.N0720.N1155.d008959]
    ring
  have hC : MemLp C 2 _root_.GD.N0232.N0720.N1155.d008950 := by
    rw [hdecomp]
    exact herror.add hR
  have hindepBase :=
    _root_.GD.N0232.N0720.N1155.d008951 he0.le he1.le
  have hindep : IndepFun R C _root_.GD.N0232.N0720.N1155.d008950 := by
    have h := hindepBase.symm.comp
      (show Measurable (fun x : ℝ =>
        Real.sqrt (e * (1 - e)) * x) by fun_prop)
      (show Measurable (fun x : ℝ => d x - e * x) by fun_prop)
    simpa [R, C, O, Function.comp_def] using h
  have hcentered : (∫ z, R z ∂_root_.GD.N0232.N0720.N1155.d008950) = 0 := by
    simp only [R]
    rw [integral_const_mul,
      _root_.GD.N0232.N0720.N1155.d008956 he0.le he1.le, mul_zero]
  have hlower := _root_.GD.N0232.N0720.N1155.d008958 hR hC hindep hcentered
  have hresidualValue :
      (∫ z, R z ^ 2 ∂_root_.GD.N0232.N0720.N1155.d008950) = e * (1 - e) := by
    simp only [R]
    rw [show (fun z : ℝ × ℝ =>
        (Real.sqrt (e * (1 - e)) * _root_.GD.N0137.d008919 e z) ^ 2) =
      fun z => (e * (1 - e)) * (_root_.GD.N0137.d008919 e z) ^ 2 by
        funext z
        rw [mul_pow, Real.sq_sqrt heprod],
      integral_const_mul,
      _root_.GD.N0232.N0720.N1155.d008957 he0.le he1.le,
      mul_one]
  have herrorEq : (fun z => C z - R z) =
      fun z => d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z := by
    funext z
    simp only [C, R, O, _root_.GD.N0232.N0720.N1155.d008959]
    ring
  rw [hresidualValue] at hlower
  have herrorSq : (fun z => (C z - R z) ^ 2) =
      fun z => (d (_root_.GD.N0137.d008918 e z) - _root_.GD.N0232.N0720.N1155.d008959 e z) ^ 2 := by
    funext z
    exact congrArg (fun x : ℝ => x ^ 2) (congrFun herrorEq z)
  rw [herrorSq] at hlower
  exact hlower



theorem d008961
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) (z : ℝ × ℝ) :
    _root_.GD.N0232.N0720.N1155.d008959 e z = Real.sqrt e * z.1 := by
  have hcomp : 0 ≤ 1 - e := sub_nonneg.mpr he1
  unfold _root_.GD.N0232.N0720.N1155.d008959 _root_.GD.N0137.d008918 _root_.GD.N0137.d008919
  rw [Real.sqrt_mul he0]
  have heSq : (Real.sqrt e) ^ 2 = e := Real.sq_sqrt he0
  have hcompSq : (Real.sqrt (1 - e)) ^ 2 = 1 - e :=
    Real.sq_sqrt hcomp
  linear_combination
    (Real.sqrt e * z.1) * hcompSq -
      (Real.sqrt (1 - e) * z.2) * heSq





theorem d008962
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (d : ℝ → ℝ) (hd : Measurable d)
    (hint : Integrable (fun z : ℝ × ℝ =>
      (d (Real.sqrt e * z.1 + Real.sqrt (1 - e) * z.2) -
        Real.sqrt e * z.1) ^ 2) _root_.GD.N0232.N0720.N1155.d008950) :
    e * (1 - e) ≤
      ∫ mu, (∫ noise,
        (d (Real.sqrt e * mu + Real.sqrt (1 - e) * noise) -
          Real.sqrt e * mu) ^ 2 ∂gaussianReal 0 1)
        ∂gaussianReal 0 1 := by
  have hlower := _root_.GD.N0232.N0720.N1155.d008960 he0 he1 d hd
    (by
      simpa [_root_.GD.N0137.d008918,
        _root_.GD.N0232.N0720.N1155.d008961 he0.le he1.le] using hint)
  have hprod := integral_prod
    (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
    (fun z : ℝ × ℝ =>
      (d (Real.sqrt e * z.1 + Real.sqrt (1 - e) * z.2) -
        Real.sqrt e * z.1) ^ 2) hint
  rw [← hprod]
  simpa [_root_.GD.N0137.d008918,
    _root_.GD.N0232.N0720.N1155.d008961 he0.le he1.le] using hlower


def d008963 (d : ℝ → ℝ) (mu : ℝ) : ℝ :=
  ∫ noise, (d (mu + noise) - mu) ^ 2 ∂gaussianReal 0 1



def d008964 (e : ℝ) : ℝ :=
  Real.sqrt e / Real.sqrt (1 - e)



theorem d008965
    {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (d : ℝ → ℝ) (hd : Measurable d)
    (hint : Integrable (fun z : ℝ × ℝ =>
      (d (_root_.GD.N0232.N0720.N1155.d008964 e * z.1 + z.2) -
        _root_.GD.N0232.N0720.N1155.d008964 e * z.1) ^ 2) _root_.GD.N0232.N0720.N1155.d008950) :
    e ≤ ∫ z, _root_.GD.N0232.N0720.N1155.d008963 d (_root_.GD.N0232.N0720.N1155.d008964 e * z)
      ∂gaussianReal 0 1 := by
  let a := Real.sqrt (1 - e)
  let dUnit : ℝ → ℝ := fun x => a * d (x / a)
  have hcomp : 0 < 1 - e := sub_pos.mpr he1
  have ha : 0 < a := Real.sqrt_pos.2 hcomp
  have haSq : a ^ 2 = 1 - e := by
    exact Real.sq_sqrt hcomp.le
  have hpoint : ∀ z : ℝ × ℝ,
      (dUnit (Real.sqrt e * z.1 + Real.sqrt (1 - e) * z.2) -
          Real.sqrt e * z.1) ^ 2 =
        (1 - e) *
          (d (_root_.GD.N0232.N0720.N1155.d008964 e * z.1 + z.2) -
            _root_.GD.N0232.N0720.N1155.d008964 e * z.1) ^ 2 := by
    intro z
    have harg :
        (Real.sqrt e * z.1 + Real.sqrt (1 - e) * z.2) / a =
          _root_.GD.N0232.N0720.N1155.d008964 e * z.1 + z.2 := by
      unfold a _root_.GD.N0232.N0720.N1155.d008964
      field_simp [ha.ne']
    have hmu : Real.sqrt e * z.1 =
        a * (_root_.GD.N0232.N0720.N1155.d008964 e * z.1) := by
      unfold a _root_.GD.N0232.N0720.N1155.d008964
      field_simp [ha.ne']
    have hlinear :
        dUnit (Real.sqrt e * z.1 + Real.sqrt (1 - e) * z.2) -
            Real.sqrt e * z.1 =
          a * (d (_root_.GD.N0232.N0720.N1155.d008964 e * z.1 + z.2) -
            _root_.GD.N0232.N0720.N1155.d008964 e * z.1) := by
      unfold dUnit
      rw [harg, hmu]
      ring
    rw [hlinear, mul_pow, haSq]
  have hintUnit : Integrable (fun z : ℝ × ℝ =>
      (dUnit (Real.sqrt e * z.1 + Real.sqrt (1 - e) * z.2) -
        Real.sqrt e * z.1) ^ 2) _root_.GD.N0232.N0720.N1155.d008950 := by
    refine (hint.const_mul (1 - e)).congr ?_
    exact Filter.Eventually.of_forall fun z => (hpoint z).symm
  have hlower := _root_.GD.N0232.N0720.N1155.d008962
    he0 he1 dUnit (by fun_prop) hintUnit
  have hprod := integral_prod
    (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
    (fun z : ℝ × ℝ =>
      (d (_root_.GD.N0232.N0720.N1155.d008964 e * z.1 + z.2) -
        _root_.GD.N0232.N0720.N1155.d008964 e * z.1) ^ 2) hint
  have hscaled :
      (∫ mu, (∫ noise,
          (dUnit (Real.sqrt e * mu + Real.sqrt (1 - e) * noise) -
            Real.sqrt e * mu) ^ 2 ∂gaussianReal 0 1)
        ∂gaussianReal 0 1) =
      (1 - e) *
        ∫ mu, _root_.GD.N0232.N0720.N1155.d008963 d (_root_.GD.N0232.N0720.N1155.d008964 e * mu)
          ∂gaussianReal 0 1 := by
    calc
      (∫ mu, (∫ noise,
          (dUnit (Real.sqrt e * mu + Real.sqrt (1 - e) * noise) -
            Real.sqrt e * mu) ^ 2 ∂gaussianReal 0 1)
        ∂gaussianReal 0 1) =
          ∫ z : ℝ × ℝ,
            (dUnit (Real.sqrt e * z.1 + Real.sqrt (1 - e) * z.2) -
              Real.sqrt e * z.1) ^ 2 ∂_root_.GD.N0232.N0720.N1155.d008950 := by
        exact (integral_prod
          (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
          (fun z : ℝ × ℝ =>
            (dUnit (Real.sqrt e * z.1 + Real.sqrt (1 - e) * z.2) -
              Real.sqrt e * z.1) ^ 2) hintUnit).symm
      _ = ∫ z : ℝ × ℝ, (1 - e) *
          (d (_root_.GD.N0232.N0720.N1155.d008964 e * z.1 + z.2) -
            _root_.GD.N0232.N0720.N1155.d008964 e * z.1) ^ 2 ∂_root_.GD.N0232.N0720.N1155.d008950 := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = (1 - e) * ∫ z : ℝ × ℝ,
          (d (_root_.GD.N0232.N0720.N1155.d008964 e * z.1 + z.2) -
            _root_.GD.N0232.N0720.N1155.d008964 e * z.1) ^ 2 ∂_root_.GD.N0232.N0720.N1155.d008950 := by
        rw [integral_const_mul]
      _ = (1 - e) *
          ∫ mu, _root_.GD.N0232.N0720.N1155.d008963 d (_root_.GD.N0232.N0720.N1155.d008964 e * mu)
            ∂gaussianReal 0 1 := by
        rw [hprod]
        rfl
  rw [hscaled] at hlower
  exact le_of_mul_le_mul_left (by simpa [mul_comm] using hlower) hcomp







theorem d008966
    (d : ℝ → ℝ) (hd : Measurable d)
    (hbounded : BddAbove (Set.range (_root_.GD.N0232.N0720.N1155.d008963 d)))
    (hproper : ∀ e : ℝ, 0 < e → e < 1 →
      Integrable (fun z : ℝ × ℝ =>
        (d (_root_.GD.N0232.N0720.N1155.d008964 e * z.1 + z.2) -
          _root_.GD.N0232.N0720.N1155.d008964 e * z.1) ^ 2) _root_.GD.N0232.N0720.N1155.d008950) :
    1 ≤ ⨆ mu : ℝ, _root_.GD.N0232.N0720.N1155.d008963 d mu := by
  let S := ⨆ mu : ℝ, _root_.GD.N0232.N0720.N1155.d008963 d mu
  have hzeroNonneg : 0 ≤ _root_.GD.N0232.N0720.N1155.d008963 d 0 :=
    integral_nonneg fun _ => sq_nonneg _
  have hzeroLe : _root_.GD.N0232.N0720.N1155.d008963 d 0 ≤ S :=
    le_ciSup hbounded 0
  have hS0 : 0 ≤ S := hzeroNonneg.trans hzeroLe
  by_contra hnot
  have hSlt : S < 1 := lt_of_not_ge hnot
  let e : ℝ := (S + 1) / 2
  have he0 : 0 < e := by
    dsimp [e]
    linarith
  have he1 : e < 1 := by
    dsimp [e]
    linarith
  have heLower := _root_.GD.N0232.N0720.N1155.d008965
    he0 he1 d hd (hproper e he0 he1)
  have houterInt : Integrable
      (fun z => _root_.GD.N0232.N0720.N1155.d008963 d (_root_.GD.N0232.N0720.N1155.d008964 e * z))
      (gaussianReal 0 1) := by
    change Integrable
      (fun x => ∫ y,
        (d (_root_.GD.N0232.N0720.N1155.d008964 e * x + y) -
          _root_.GD.N0232.N0720.N1155.d008964 e * x) ^ 2 ∂gaussianReal 0 1)
      (gaussianReal 0 1)
    exact (hproper e he0 he1).integral_prod_left
  have hconstInt : Integrable (fun _ : ℝ => S) (gaussianReal 0 1) :=
    integrable_const S
  have hupper :
      (∫ z, _root_.GD.N0232.N0720.N1155.d008963 d (_root_.GD.N0232.N0720.N1155.d008964 e * z)
        ∂gaussianReal 0 1) ≤ S := by
    calc
      (∫ z, _root_.GD.N0232.N0720.N1155.d008963 d (_root_.GD.N0232.N0720.N1155.d008964 e * z)
          ∂gaussianReal 0 1) ≤
          ∫ _z : ℝ, S ∂gaussianReal 0 1 := by
        apply integral_mono houterInt hconstInt
        intro z
        exact le_ciSup hbounded (_root_.GD.N0232.N0720.N1155.d008964 e * z)
      _ = S := by simp
  dsimp [e] at heLower
  linarith

end

end N1155
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1155.d008960
#print axioms _root_.GD.N0232.N0720.N1155.d008965
#print axioms _root_.GD.N0232.N0720.N1155.d008966
