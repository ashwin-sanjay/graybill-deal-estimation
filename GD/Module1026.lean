import GD.Module0259
import GD.Module1002
import GD.Module1012
import GD.Module1025



































open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace GD
namespace N0232
namespace N0720
namespace N1490

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0720.N1501
open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0232.N0720.N1498
open _root_.GD.N0232.N0720.N1493
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0954
open _root_.GD.N0232.N0719.N0928
open _root_.GD.N0232.N0719.N0929
open _root_.GD.N0232.N0719.N0857
open _root_.GD.N0232.N0719.N0853
open _root_.GD.N0232.N0719.N0955
open _root_.GD.N0232.N0719.N1011
open _root_.GD.N0232.N0719.N0868
open _root_.GD.N0232.N0720.N1034

attribute [local instance] Measure.Subtype.measureSpace

private abbrev d016308 : Fin 2 -> Real :=
  _root_.GD.N0232.N0719.N0954.d009355 (_root_.GD.N0232.N0720.N1034.d012430 2 2)

private abbrev d016309 : Real := _root_.GD.N0232.N0720.N1034.d012428 4

private abbrev d016310 :=
  {q : _root_.GD.N0232.N0719.N0857.d009377 2 // q ∈ _root_.GD.N0232.N0719.N0955.d009607 2}

private theorem d016311 : ∀ i, 0 < _root_.GD.N0232.N0720.N1490.d016308 i := by
  apply _root_.GD.N0232.N0719.N0954.d009358
  intro i
  fin_cases i <;> norm_num [_root_.GD.N0232.N0720.N1034.d012430]

private theorem d016312 : _root_.GD.N0232.N0720.N1490.d016309 = 5 / 2 := by
  exact _root_.GD.N0232.N0720.N1486.d015858

private theorem d016313 :
    0 < _root_.GD.N0232.N0719.N0928.d009415 _root_.GD.N0232.N0720.N1490.d016308 _root_.GD.N0232.N0720.N1490.d016309 := by
  rw [_root_.GD.N0232.N0720.N1034.d012431
    2 2 (by norm_num) (by norm_num) 4]
  norm_num [_root_.GD.N0232.N0720.N1034.d012429]

private theorem d016314 :
    0 < _root_.GD.N0232.N0719.N0928.d009415 _root_.GD.N0232.N0720.N1490.d016308 (_root_.GD.N0232.N0720.N1490.d016309 - 1) := by
  norm_num [_root_.GD.N0232.N0720.N1490.d016308, _root_.GD.N0232.N0720.N1490.d016309, _root_.GD.N0232.N0719.N0928.d009415, _root_.GD.N0232.N0719.N0928.d009408,
    _root_.GD.N0232.N0719.N0954.d009355, _root_.GD.N0232.N0720.N1034.d012430, _root_.GD.N0232.N0720.N1034.d012428,
    Fin.sum_univ_two]

private theorem d016315
    (z : Set.Ioo (0 : Real) 1) :
    ∀ i, 0 < _root_.GD.N0232.N0720.N1034.d012417 (z : Real) i := by
  intro i
  fin_cases i
  · simpa [_root_.GD.N0232.N0720.N1034.d012417] using z.property.1
  · simpa [_root_.GD.N0232.N0720.N1034.d012417] using sub_pos.mpr z.property.2

private theorem d016316
    (z : Set.Ioo (0 : Real) 1) :
    ∑ i, _root_.GD.N0232.N0720.N1034.d012417 (z : Real) i = 1 := by
  simp [_root_.GD.N0232.N0720.N1034.d012417, Fin.sum_univ_two]

private theorem d016317
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i)
    (z : Set.Ioo (0 : Real) 1) :
    0 < _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0720.N1490.d016308
      (_root_.GD.N0232.N0720.N1034.d012417 (z : Real)) u.mean u.meanVariance := by
  obtain ⟨c, hc, hfloor⟩ :=
    _root_.GD.N0232.N0719.N0929.d009644
      (by norm_num : 0 < 2) _root_.GD.N0232.N0720.N1490.d016308 u.meanVariance _root_.GD.N0232.N0720.N1490.d016311 ht
  have hge := _root_.GD.N0232.N0719.N0928.d009442 _root_.GD.N0232.N0720.N1490.d016308
    (_root_.GD.N0232.N0720.N1034.d012417 (z : Real)) u.mean u.meanVariance c
    (fun i => (_root_.GD.N0232.N0720.N1490.d016315 z i).le)
    (_root_.GD.N0232.N0720.N1490.d016316 z) hfloor
  linarith







theorem d016318
    {C alpha : Real} (hC : 0 < C) (halpha : 1 < alpha) :
    IntegrableOn
      (fun q : Real => q ^ (-alpha) * Real.exp (-(C / q)))
      (Set.Ioi 0) := by
  by_contra hnot
  have hzero :
      (∫ q in Set.Ioi (0 : Real),
        q ^ (-alpha) * Real.exp (-(C / q))) = 0 :=
    integral_undef hnot
  rw [_root_.GD.N0232.N0719.N0928.d009434 hC halpha] at hzero
  exact (ne_of_gt (mul_pos
    (Real.rpow_pos_of_pos hC _)
    (Real.Gamma_pos_of_pos (by linarith : 0 < alpha - 1)))) hzero



private theorem d016319
    {q : Real} (hq : 0 < q) (center x : Real) :
    Real.sqrt (2 * Real.pi * q) *
        gaussianPDFReal center q.toNNReal x =
      Real.exp (-((x - center) ^ 2 / 2) / q) := by
  rw [gaussianPDFReal_def]
  simp only [Real.coe_toNNReal q hq.le]
  have hsqrt : Real.sqrt (2 * Real.pi * q) ≠ 0 := by positivity
  rw [← mul_assoc, mul_inv_cancel₀ hsqrt, one_mul]
  congr 1
  field_simp [hq.ne']

private theorem d016320
    {q : Real} (hq : 0 < q) (center : Real) :
    Integrable
      (fun x : Real =>
        gaussianPDFReal center q.toNNReal x * x ^ 2) := by
  let v : NNReal := q.toNNReal
  have hv : v ≠ 0 := by
    apply NNReal.ne_iff.mp
    simpa [v, Real.coe_toNNReal q hq.le] using hq.ne'
  have hmoment : Integrable (fun x : Real => x ^ 2)
      (gaussianReal center v) :=
    integrable_pow_of_mem_interior_integrableExpSet (by simp) 2
  rw [gaussianReal_of_var_ne_zero center hv,
    integrable_withDensity_iff_integrable_smul'
      (measurable_gaussianPDF center v)
      (Filter.Eventually.of_forall fun x => gaussianPDF_lt_top)] at hmoment
  simpa [v, toReal_gaussianPDF, smul_eq_mul, mul_comm] using hmoment

private theorem d016321
    {q : Real} (hq : 0 < q) (center : Real) :
    (∫ x : Real,
        gaussianPDFReal center q.toNNReal x * x ^ 2) =
      center ^ 2 + q := by
  let v : NNReal := q.toNNReal
  have hv : v ≠ 0 := by
    apply NNReal.ne_iff.mp
    simpa [v, Real.coe_toNNReal q hq.le] using hq.ne'
  have h := integral_gaussianReal_eq_integral_smul
    (v := v) (μ := center) (f := fun x : Real => x ^ 2) hv
  rw [_root_.GD.N0232.N0719.N0879.d003727] at h
  simpa [v, Real.coe_toNNReal q hq.le,
    toReal_gaussianPDF, smul_eq_mul, mul_comm] using h.symm



theorem d016322
    {I : Type*} [Fintype I]
    (shape p y t : I -> Real) (s : Real)
    {q : Real} (hq : 0 < q) :
    Integrable (fun mu : Real =>
      mu ^ 2 * _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) := by
  let C := _root_.GD.N0232.N0719.N0928.d009407 shape p y t
  let center := _root_.GD.N0232.N0719.N0928.d009405 p y
  let A := q ^ (-s) * q ^ (-_root_.GD.N0232.N0719.N0928.d009408 shape) *
    _root_.GD.N0232.N0719.N0928.d009409 shape p * Real.exp (-(C / q))
  let root := Real.sqrt (2 * Real.pi * q)
  have hpdf := _root_.GD.N0232.N0720.N1490.d016320 hq center
  have hscaled := hpdf.const_mul (A * root)
  refine hscaled.congr (ae_of_all _ fun mu => ?_)
  symm
  unfold _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0719.N0928.d009412
  have hexp :
      Real.exp
          (-((_root_.GD.N0232.N0719.N0928.d009407 shape p y t +
            (mu - _root_.GD.N0232.N0719.N0928.d009405 p y) ^ 2 / 2) / q)) =
        Real.exp (-(_root_.GD.N0232.N0719.N0928.d009407 shape p y t / q)) *
          Real.exp (-((mu - _root_.GD.N0232.N0719.N0928.d009405 p y) ^ 2 / 2) / q) := by
    rw [← Real.exp_add]
    congr 1
    field_simp [hq.ne']
    ring
  change mu ^ 2 *
      (q ^ (-s) *
        (q ^ (-_root_.GD.N0232.N0719.N0928.d009408 shape) *
          _root_.GD.N0232.N0719.N0928.d009409 shape p *
            Real.exp (-((_root_.GD.N0232.N0719.N0928.d009407 shape p y t +
              (mu - _root_.GD.N0232.N0719.N0928.d009405 p y) ^ 2 / 2) / q)))) =
    (A * root) * (gaussianPDFReal center q.toNNReal mu * mu ^ 2)
  rw [hexp]
  rw [← _root_.GD.N0232.N0720.N1490.d016319 hq center mu]
  dsimp [A, C, center, root]
  ring


theorem d016323
    {I : Type*} [Fintype I]
    (shape p y t : I -> Real) (s : Real)
    {q : Real} (hq : 0 < q) :
    (∫ mu : Real,
      mu ^ 2 * _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) =
      (_root_.GD.N0232.N0719.N0928.d009405 p y ^ 2 + q) *
        (∫ mu : Real,
          _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) := by
  let C := _root_.GD.N0232.N0719.N0928.d009407 shape p y t
  let center := _root_.GD.N0232.N0719.N0928.d009405 p y
  let A := q ^ (-s) * q ^ (-_root_.GD.N0232.N0719.N0928.d009408 shape) *
    _root_.GD.N0232.N0719.N0928.d009409 shape p * Real.exp (-(C / q))
  let root := Real.sqrt (2 * Real.pi * q)
  have hsquare := _root_.GD.N0232.N0720.N1490.d016321 hq center
  have hpoint :
      (fun mu : Real =>
        mu ^ 2 * _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) =
      fun mu => (A * root) *
        (gaussianPDFReal center q.toNNReal mu * mu ^ 2) := by
    funext mu
    unfold _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0719.N0928.d009412
    have hexp :
        Real.exp
            (-((_root_.GD.N0232.N0719.N0928.d009407 shape p y t +
              (mu - _root_.GD.N0232.N0719.N0928.d009405 p y) ^ 2 / 2) / q)) =
          Real.exp (-(_root_.GD.N0232.N0719.N0928.d009407 shape p y t / q)) *
            Real.exp (-((mu - _root_.GD.N0232.N0719.N0928.d009405 p y) ^ 2 / 2) / q) := by
      rw [← Real.exp_add]
      congr 1
      field_simp [hq.ne']
      ring
    rw [hexp]
    rw [← _root_.GD.N0232.N0720.N1490.d016319 hq center mu]
    dsimp [A, C, center, root]
    ring
  rw [hpoint, integral_const_mul, hsquare]
  rw [_root_.GD.N0232.N0719.N0928.d009426 shape p y t s hq]
  dsimp [A, C, center, root]
  ring





theorem d016324
    {I : Type*} [Fintype I]
    (shape p y t : I -> Real) (s : Real)
    (henergy : 0 < _root_.GD.N0232.N0719.N0928.d009407 shape p y t)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    IntegrableOn
      (fun q : Real => ∫ mu : Real,
        _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q)
      (Set.Ioi 0) := by
  have hradial := _root_.GD.N0232.N0720.N1490.d016318 henergy
    (show 1 < _root_.GD.N0232.N0719.N0928.d009415 shape s + 1 by linarith)
  have hscaled := hradial.const_mul
    (Real.sqrt (2 * Real.pi) * _root_.GD.N0232.N0719.N0928.d009409 shape p)
  refine IntegrableOn.congr_fun hscaled (fun q hq => ?_) measurableSet_Ioi
  rw [_root_.GD.N0232.N0719.N0928.d009426 shape p y t s hq]
  rw [_root_.GD.N0232.N0719.N0928.d009427 shape p y t s hq]

private theorem d016325
    {I : Type*} [Fintype I]
    (shape p y t : I -> Real) (s : Real)
    {q : Real} (hq : 0 < q) :
    q * (∫ mu : Real,
      _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) =
      ∫ mu : Real,
        _root_.GD.N0232.N0719.N0928.d009413 shape p y t (s - 1) mu q := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with mu
  unfold _root_.GD.N0232.N0719.N0928.d009413
  have hpow : q ^ (-(s - 1)) = q * q ^ (-s) := by
    rw [show -(s - 1) = (1 : Real) + (-s) by ring,
      Real.rpow_add hq, Real.rpow_one]
  rw [hpow]
  ring



theorem d016326
    {I : Type*} [Fintype I]
    (shape p y t : I -> Real) (s : Real)
    (henergy : 0 < _root_.GD.N0232.N0719.N0928.d009407 shape p y t)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s)
    (hpowerLower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape (s - 1)) :
    (∫ q in Set.Ioi (0 : Real), ∫ mu : Real,
      mu ^ 2 * _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) =
      _root_.GD.N0232.N0719.N0928.d009405 p y ^ 2 * _root_.GD.N0232.N0719.N0928.d009437 shape p y t s +
        _root_.GD.N0232.N0719.N0928.d009437 shape p y t (s - 1) := by
  have hmain := _root_.GD.N0232.N0720.N1490.d016324
    shape p y t s henergy hpower
  have hlower := _root_.GD.N0232.N0720.N1490.d016324
    shape p y t (s - 1) henergy hpowerLower
  calc
    (∫ q in Set.Ioi (0 : Real), ∫ mu : Real,
        mu ^ 2 * _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) =
      ∫ q in Set.Ioi (0 : Real),
        _root_.GD.N0232.N0719.N0928.d009405 p y ^ 2 *
            (∫ mu : Real,
              _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) +
          (∫ mu : Real,
            _root_.GD.N0232.N0719.N0928.d009413 shape p y t (s - 1) mu q) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro q hq
      change (∫ mu : Real,
          mu ^ 2 * _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) =
        _root_.GD.N0232.N0719.N0928.d009405 p y ^ 2 *
            (∫ mu : Real,
              _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) +
          (∫ mu : Real,
            _root_.GD.N0232.N0719.N0928.d009413 shape p y t (s - 1) mu q)
      rw [_root_.GD.N0232.N0720.N1490.d016323
        shape p y t s hq]
      rw [← _root_.GD.N0232.N0720.N1490.d016325
        shape p y t s hq]
      ring
    _ = _root_.GD.N0232.N0719.N0928.d009405 p y ^ 2 *
          (∫ q in Set.Ioi (0 : Real), ∫ mu : Real,
            _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) +
        (∫ q in Set.Ioi (0 : Real), ∫ mu : Real,
          _root_.GD.N0232.N0719.N0928.d009413 shape p y t (s - 1) mu q) := by
      rw [integral_add (hmain.const_mul _) hlower, integral_const_mul]
    _ = _ := by
      rw [_root_.GD.N0232.N0719.N0928.d009444
          shape p y t s henergy hpower,
        _root_.GD.N0232.N0719.N0928.d009444
          shape p y t (s - 1) henergy hpowerLower]





def d016327
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (z : Set.Ioo (0 : Real) 1) : Real :=
  ∫ q : Set.Ioi (0 : Real),
    (∫ mu : Real,
      mu ^ 2 * _root_.GD.N0232.N0719.N1011.d011288 2 (_root_.GD.N0232.N0720.N1034.d012430 2 2) mu
        ![_root_.GD.N0232.N0720.N1498.d012567 2 q z, _root_.GD.N0232.N0720.N1498.d012568 2 q z] u)
      ∂_root_.GD.N0232.N0720.N1486.d015866

theorem d016328
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i)
    (z : Set.Ioo (0 : Real) 1) :
    _root_.GD.N0232.N0720.N1490.d016327 u z =
      _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
        (_root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0720.N1034.d012417 (z : Real)) u.mean ^ 2 *
          _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1490.d016308
            (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
            u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309 +
          _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1490.d016308
            (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
            u.mean u.meanVariance (_root_.GD.N0232.N0720.N1490.d016309 - 1)) := by
  unfold _root_.GD.N0232.N0720.N1490.d016327 _root_.GD.N0232.N0720.N1486.d015866
  rw [integral_withDensity_eq_integral_toReal_smul
    _root_.GD.N0232.N0720.N1486.d015863
    (ae_of_all volume fun q =>
      (_root_.GD.N0232.N0720.N1486.d015865 q).lt_top)]
  have hdensity (q : Set.Ioi (0 : Real)) :
      (_root_.GD.N0232.N0720.N1486.d015860 q).toReal =
        (q : Real) ^ (-_root_.GD.N0232.N0720.N1490.d016309) := by
    rw [_root_.GD.N0232.N0720.N1486.d015860,
      ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1486.d015864 q).le,
      _root_.GD.N0232.N0720.N1486.d015859]
  simp_rw [smul_eq_mul, hdensity]
  have hradial := _root_.GD.N0232.N0720.N1490.d016326
    _root_.GD.N0232.N0720.N1490.d016308 (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
    u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309 (_root_.GD.N0232.N0720.N1490.d016317 u ht z)
    _root_.GD.N0232.N0720.N1490.d016313 _root_.GD.N0232.N0720.N1490.d016314
  calc
    (∫ q : Set.Ioi (0 : Real),
        (q : Real) ^ (-_root_.GD.N0232.N0720.N1490.d016309) *
          (∫ mu : Real,
            mu ^ 2 * _root_.GD.N0232.N0719.N1011.d011288 2
              (_root_.GD.N0232.N0720.N1034.d012430 2 2) mu
              ![_root_.GD.N0232.N0720.N1498.d012567 2 q z,
                _root_.GD.N0232.N0720.N1498.d012568 2 q z] u)) =
      ∫ q : Set.Ioi (0 : Real),
        _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
          (∫ mu : Real,
            mu ^ 2 * _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0720.N1490.d016308
              (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
              u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309 mu (q : Real)) := by
      apply integral_congr_ae
      filter_upwards with q
      rw [← integral_const_mul, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with mu
      rw [_root_.GD.N0232.N0720.N1498.d012577
        (by norm_num : 0 < 2) (by norm_num : 0 < 2)
        u mu q.property z.property.1 z.property.2]
      unfold _root_.GD.N0232.N0719.N0928.d009413
      ring
    _ = _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
        (∫ q : Set.Ioi (0 : Real), ∫ mu : Real,
          mu ^ 2 * _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0720.N1490.d016308
            (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
            u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309 mu (q : Real)) := by
      rw [integral_const_mul]
    _ = _ := by
      rw [← integral_subtype measurableSet_Ioi] at hradial
      rw [hradial]



@[fun_prop] private theorem d016329 (i : Fin 2) :
    Continuous (fun z : Set.Ioo (0 : Real) 1 =>
      _root_.GD.N0232.N0720.N1034.d012417 (z : Real) i) := by
  fin_cases i <;> simp [_root_.GD.N0232.N0720.N1034.d012417] <;> fun_prop

private theorem d016330 (u : _root_.GD.N0232.N0719.N0900.d009096 2) :
    Continuous (fun z : Set.Ioo (0 : Real) 1 =>
      _root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0720.N1034.d012417 (z : Real)) u.mean) := by
  unfold _root_.GD.N0232.N0719.N0928.d009405
  fun_prop

private theorem d016331 (u : _root_.GD.N0232.N0719.N0900.d009096 2) :
    Continuous (fun z : Set.Ioo (0 : Real) 1 =>
      _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0720.N1490.d016308 (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
        u.mean u.meanVariance) := by
  unfold _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0719.N0928.d009406 _root_.GD.N0232.N0719.N0928.d009405
  fun_prop

private theorem d016332
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i)
    (s : Real) :
    Continuous (fun z : Set.Ioo (0 : Real) 1 =>
      _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1490.d016308
        (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
        u.mean u.meanVariance s) := by
  have hmono : Continuous (fun z : Set.Ioo (0 : Real) 1 =>
      _root_.GD.N0232.N0719.N0928.d009409 _root_.GD.N0232.N0720.N1490.d016308
        (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))) := by
    unfold _root_.GD.N0232.N0719.N0928.d009409
    apply continuous_finset_prod
    intro i hi
    exact (_root_.GD.N0232.N0720.N1490.d016329 i).rpow_const
      (fun z => Or.inl (_root_.GD.N0232.N0720.N1490.d016315 z i).ne')
  have henergy := _root_.GD.N0232.N0720.N1490.d016331 u
  unfold _root_.GD.N0232.N0719.N0928.d009437
  exact (((continuous_const.mul hmono).mul
    (henergy.rpow_const fun z =>
      Or.inl (_root_.GD.N0232.N0720.N1490.d016317 u ht z).ne')).mul continuous_const)

theorem d016333
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i) :
    Measurable (_root_.GD.N0232.N0720.N1493.d016097 u) := by
  rw [show _root_.GD.N0232.N0720.N1493.d016097 u = fun z : Set.Ioo (0 : Real) 1 =>
      _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
        _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1490.d016308
          (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
          u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309 by
    funext z
    exact _root_.GD.N0232.N0720.N1493.d016099 u ht z]
  exact continuous_const.mul
    (_root_.GD.N0232.N0720.N1490.d016332 u ht _root_.GD.N0232.N0720.N1490.d016309) |>.measurable

theorem d016334
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i) :
    Measurable (_root_.GD.N0232.N0720.N1493.d016098 u) := by
  rw [show _root_.GD.N0232.N0720.N1493.d016098 u = fun z : Set.Ioo (0 : Real) 1 =>
      _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
        (_root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1490.d016308
          (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
          u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309 *
        _root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0720.N1034.d012417 (z : Real)) u.mean) by
    funext z
    exact _root_.GD.N0232.N0720.N1493.d016100 u ht z]
  exact continuous_const.mul
    ((_root_.GD.N0232.N0720.N1490.d016332 u ht _root_.GD.N0232.N0720.N1490.d016309).mul
      (_root_.GD.N0232.N0720.N1490.d016330 u)) |>.measurable

theorem d016335
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i) :
    Measurable (_root_.GD.N0232.N0720.N1490.d016327 u) := by
  rw [show _root_.GD.N0232.N0720.N1490.d016327 u =
      fun z : Set.Ioo (0 : Real) 1 =>
      _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
        (_root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0720.N1034.d012417 (z : Real)) u.mean ^ 2 *
          _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1490.d016308
            (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
            u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309 +
          _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1490.d016308
            (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
            u.mean u.meanVariance (_root_.GD.N0232.N0720.N1490.d016309 - 1)) by
    funext z
    exact _root_.GD.N0232.N0720.N1490.d016328 u ht z]
  exact continuous_const.mul
    (((_root_.GD.N0232.N0720.N1490.d016330 u).pow 2).mul
      (_root_.GD.N0232.N0720.N1490.d016332 u ht _root_.GD.N0232.N0720.N1490.d016309) |>.add
        (_root_.GD.N0232.N0720.N1490.d016332 u ht (_root_.GD.N0232.N0720.N1490.d016309 - 1))) |>.measurable

private theorem d016336
    (q : _root_.GD.N0232.N0720.N1490.d016310) :
    _root_.GD.N0232.N0720.N1034.d012417 (_root_.GD.N0232.N0720.N1493.d016102 q : Real) =
      _root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q.1 := by
  funext i
  fin_cases i
  · rfl
  · have hsum := _root_.GD.N0232.N0719.N0853.d009570 (by norm_num : 0 < 2) q.1
    rw [Fin.sum_univ_two] at hsum
    have hlast :
        _root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q.1 (1 : Fin 2) =
          1 - _root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q.1 (0 : Fin 2) := by
      linarith
    have hz : (_root_.GD.N0232.N0720.N1493.d016102 q : Real) =
        _root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q.1 (0 : Fin 2) := rfl
    rw [hz]
    exact hlast.symm

private theorem d016337
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i) :
    Integrable (fun q : _root_.GD.N0232.N0720.N1490.d016310 =>
      _root_.GD.N0232.N0720.N1493.d016097 u (_root_.GD.N0232.N0720.N1493.d016102 q)) := by
  have hkernelOn := _root_.GD.N0232.N0719.N0929.d009645
    (by norm_num : 0 < 2) _root_.GD.N0232.N0720.N1490.d016308 u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309
    _root_.GD.N0232.N0720.N1490.d016311 ht _root_.GD.N0232.N0720.N1490.d016313
  have hkernel : Integrable (fun q : _root_.GD.N0232.N0720.N1490.d016310 =>
      _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1490.d016308
        (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q.1)
        u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309) := by
    exact (integrableOn_iff_comap_subtypeVal
      (_root_.GD.N0232.N0719.N0955.d009608 2)).mp hkernelOn
  refine (hkernel.const_mul (_root_.GD.N0232.N0720.N1498.d012564 2 2 u)).congr
    (ae_of_all _ fun q => ?_)
  change _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
      _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1490.d016308
        (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q.1)
        u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309 =
    _root_.GD.N0232.N0720.N1493.d016097 u (_root_.GD.N0232.N0720.N1493.d016102 q)
  rw [_root_.GD.N0232.N0720.N1493.d016099 u ht (_root_.GD.N0232.N0720.N1493.d016102 q),
    _root_.GD.N0232.N0720.N1490.d016336]

theorem d016338
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i) :
    Integrable (_root_.GD.N0232.N0720.N1493.d016097 u) _root_.GD.N0232.N0720.N1493.d016104 := by
  unfold _root_.GD.N0232.N0720.N1493.d016104
  apply (integrable_map_measure
    (_root_.GD.N0232.N0720.N1490.d016333 u ht).aestronglyMeasurable
    _root_.GD.N0232.N0720.N1493.d016103.measurable.aemeasurable).2
  exact _root_.GD.N0232.N0720.N1490.d016337 u ht

private theorem d016339
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i) :
    Integrable (fun q : _root_.GD.N0232.N0720.N1490.d016310 =>
      _root_.GD.N0232.N0720.N1493.d016098 u (_root_.GD.N0232.N0720.N1493.d016102 q)) := by
  have hkernelOn := _root_.GD.N0232.N0719.N0929.d009651
    (by norm_num : 0 < 2) _root_.GD.N0232.N0720.N1490.d016308 u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309
    _root_.GD.N0232.N0720.N1490.d016311 ht _root_.GD.N0232.N0720.N1490.d016313
  have hkernel : Integrable (fun q : _root_.GD.N0232.N0720.N1490.d016310 =>
      _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1490.d016308
          (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q.1)
          u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309 *
        _root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q.1) u.mean) := by
    exact (integrableOn_iff_comap_subtypeVal
      (_root_.GD.N0232.N0719.N0955.d009608 2)).mp hkernelOn
  refine (hkernel.const_mul (_root_.GD.N0232.N0720.N1498.d012564 2 2 u)).congr
    (ae_of_all _ fun q => ?_)
  change _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
      (_root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1490.d016308
          (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q.1)
          u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309 *
        _root_.GD.N0232.N0719.N0928.d009405
          (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q.1) u.mean) =
    _root_.GD.N0232.N0720.N1493.d016098 u (_root_.GD.N0232.N0720.N1493.d016102 q)
  rw [_root_.GD.N0232.N0720.N1493.d016100 u ht (_root_.GD.N0232.N0720.N1493.d016102 q),
    _root_.GD.N0232.N0720.N1490.d016336]

theorem d016340
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i) :
    Integrable (_root_.GD.N0232.N0720.N1493.d016098 u)
      _root_.GD.N0232.N0720.N1493.d016104 := by
  unfold _root_.GD.N0232.N0720.N1493.d016104
  apply (integrable_map_measure
    (_root_.GD.N0232.N0720.N1490.d016334 u ht).aestronglyMeasurable
    _root_.GD.N0232.N0720.N1493.d016103.measurable.aemeasurable).2
  exact _root_.GD.N0232.N0720.N1490.d016339 u ht

private theorem d016341
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i) :
    Integrable (fun q : _root_.GD.N0232.N0720.N1490.d016310 =>
      _root_.GD.N0232.N0720.N1490.d016327 u (_root_.GD.N0232.N0720.N1493.d016102 q)) := by
  have hfirstOn :=
    _root_.GD.N0232.N0719.N0868.d009665
      (by norm_num : 0 < 2) _root_.GD.N0232.N0720.N1490.d016308 u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309
      _root_.GD.N0232.N0720.N1490.d016311 ht _root_.GD.N0232.N0720.N1490.d016313
  have hfirst : Integrable (fun q : _root_.GD.N0232.N0720.N1490.d016310 =>
      _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1490.d016308
          (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q.1)
          u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309 *
        _root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q.1) u.mean ^ 2) := by
    exact (integrableOn_iff_comap_subtypeVal
      (_root_.GD.N0232.N0719.N0955.d009608 2)).mp hfirstOn
  have hlowerOn := _root_.GD.N0232.N0719.N0929.d009645
    (by norm_num : 0 < 2) _root_.GD.N0232.N0720.N1490.d016308 u.mean u.meanVariance (_root_.GD.N0232.N0720.N1490.d016309 - 1)
    _root_.GD.N0232.N0720.N1490.d016311 ht _root_.GD.N0232.N0720.N1490.d016314
  have hlower : Integrable (fun q : _root_.GD.N0232.N0720.N1490.d016310 =>
      _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1490.d016308
        (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q.1)
        u.mean u.meanVariance (_root_.GD.N0232.N0720.N1490.d016309 - 1)) := by
    exact (integrableOn_iff_comap_subtypeVal
      (_root_.GD.N0232.N0719.N0955.d009608 2)).mp hlowerOn
  have hsum := hfirst.add hlower
  refine (hsum.const_mul (_root_.GD.N0232.N0720.N1498.d012564 2 2 u)).congr
    (ae_of_all _ fun q => ?_)
  change _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
      (_root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1490.d016308
          (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q.1)
          u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309 *
            _root_.GD.N0232.N0719.N0928.d009405
              (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q.1) u.mean ^ 2 +
        _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1490.d016308
          (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q.1)
          u.mean u.meanVariance (_root_.GD.N0232.N0720.N1490.d016309 - 1)) =
    _root_.GD.N0232.N0720.N1490.d016327 u (_root_.GD.N0232.N0720.N1493.d016102 q)
  rw [_root_.GD.N0232.N0720.N1490.d016328 u ht (_root_.GD.N0232.N0720.N1493.d016102 q),
    _root_.GD.N0232.N0720.N1490.d016336]
  ring

theorem d016342
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i) :
    Integrable (_root_.GD.N0232.N0720.N1490.d016327 u)
      _root_.GD.N0232.N0720.N1493.d016104 := by
  unfold _root_.GD.N0232.N0720.N1493.d016104
  apply (integrable_map_measure
    (_root_.GD.N0232.N0720.N1490.d016335 u ht).aestronglyMeasurable
    _root_.GD.N0232.N0720.N1493.d016103.measurable.aemeasurable).2
  exact _root_.GD.N0232.N0720.N1490.d016341 u ht



theorem d016343
    {I : Type*} [Fintype I]
    (shape p y t : I -> Real) (s : Real)
    {q : Real} (hq : 0 < q) :
    Integrable (fun mu : Real =>
      _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) := by
  let C := _root_.GD.N0232.N0719.N0928.d009407 shape p y t
  let center := _root_.GD.N0232.N0719.N0928.d009405 p y
  let A := q ^ (-s) * q ^ (-_root_.GD.N0232.N0719.N0928.d009408 shape) *
    _root_.GD.N0232.N0719.N0928.d009409 shape p * Real.exp (-(C / q))
  have hb : 0 < (1 / (2 * q) : Real) := by positivity
  have hgauss := (integrable_exp_neg_mul_sq hb).comp_sub_right center
  have hscaled := hgauss.const_mul A
  refine hscaled.congr (ae_of_all _ fun mu => ?_)
  symm
  unfold _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0719.N0928.d009412
  have hexp :
      Real.exp
          (-((_root_.GD.N0232.N0719.N0928.d009407 shape p y t +
            (mu - _root_.GD.N0232.N0719.N0928.d009405 p y) ^ 2 / 2) / q)) =
        Real.exp (-(_root_.GD.N0232.N0719.N0928.d009407 shape p y t / q)) *
          Real.exp (-((1 / (2 * q)) *
            (mu - _root_.GD.N0232.N0719.N0928.d009405 p y) ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp [hq.ne']
    ring
  change q ^ (-s) *
      (q ^ (-_root_.GD.N0232.N0719.N0928.d009408 shape) *
        _root_.GD.N0232.N0719.N0928.d009409 shape p *
          Real.exp (-((_root_.GD.N0232.N0719.N0928.d009407 shape p y t +
            (mu - _root_.GD.N0232.N0719.N0928.d009405 p y) ^ 2 / 2) / q))) =
    A * Real.exp (-(1 / (2 * q)) * (mu - center) ^ 2)
  rw [hexp]
  dsimp [A, C, center]
  ring

theorem d016344
    {I : Type*} [Fintype I]
    (shape p y t : I -> Real) (s : Real)
    (henergy : 0 < _root_.GD.N0232.N0719.N0928.d009407 shape p y t)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s)
    (hpowerLower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape (s - 1)) :
    IntegrableOn
      (fun q : Real => ∫ mu : Real,
        mu ^ 2 * _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q)
      (Set.Ioi 0) := by
  have hmain := _root_.GD.N0232.N0720.N1490.d016324
    shape p y t s henergy hpower
  have hlower := _root_.GD.N0232.N0720.N1490.d016324
    shape p y t (s - 1) henergy hpowerLower
  have hsum := (hmain.const_mul (_root_.GD.N0232.N0719.N0928.d009405 p y ^ 2)).add hlower
  refine IntegrableOn.congr_fun hsum (fun q hq => ?_) measurableSet_Ioi
  change _root_.GD.N0232.N0719.N0928.d009405 p y ^ 2 *
        (∫ mu : Real, _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) +
      (∫ mu : Real,
        _root_.GD.N0232.N0719.N0928.d009413 shape p y t (s - 1) mu q) =
    (∫ mu : Real,
      mu ^ 2 * _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q)
  rw [_root_.GD.N0232.N0720.N1490.d016323
    shape p y t s hq]
  rw [← _root_.GD.N0232.N0720.N1490.d016325 shape p y t s hq]
  ring

theorem d016345
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (z : Set.Ioo (0 : Real) 1)
    (q : Set.Ioi (0 : Real)) :
    Integrable (fun mu : Real =>
      _root_.GD.N0232.N0719.N1011.d011288 2 (_root_.GD.N0232.N0720.N1034.d012430 2 2) mu
        ![_root_.GD.N0232.N0720.N1498.d012567 2 q z, _root_.GD.N0232.N0720.N1498.d012568 2 q z] u) := by
  have h := _root_.GD.N0232.N0720.N1490.d016343
    _root_.GD.N0232.N0720.N1490.d016308 (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
    u.mean u.meanVariance 0 q.property
  refine (h.const_mul (_root_.GD.N0232.N0720.N1498.d012564 2 2 u)).congr
    (ae_of_all _ fun mu => ?_)
  change _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
      _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0720.N1490.d016308
        (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
        u.mean u.meanVariance 0 mu (q : Real) =
    _root_.GD.N0232.N0719.N1011.d011288 2 (_root_.GD.N0232.N0720.N1034.d012430 2 2) mu
      ![_root_.GD.N0232.N0720.N1498.d012567 2 q z, _root_.GD.N0232.N0720.N1498.d012568 2 q z] u
  rw [_root_.GD.N0232.N0720.N1498.d012577
    (by norm_num : 0 < 2) (by norm_num : 0 < 2)
    u mu q.property z.property.1 z.property.2]
  unfold _root_.GD.N0232.N0719.N0928.d009413
  simp

theorem d016346
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (z : Set.Ioo (0 : Real) 1)
    (q : Set.Ioi (0 : Real)) :
    Integrable (fun mu : Real =>
      mu ^ 2 * _root_.GD.N0232.N0719.N1011.d011288 2 (_root_.GD.N0232.N0720.N1034.d012430 2 2) mu
        ![_root_.GD.N0232.N0720.N1498.d012567 2 q z, _root_.GD.N0232.N0720.N1498.d012568 2 q z] u) := by
  have h := _root_.GD.N0232.N0720.N1490.d016322
    _root_.GD.N0232.N0720.N1490.d016308 (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
    u.mean u.meanVariance 0 q.property
  refine (h.const_mul (_root_.GD.N0232.N0720.N1498.d012564 2 2 u)).congr
    (ae_of_all _ fun mu => ?_)
  change _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
      (mu ^ 2 * _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0720.N1490.d016308
        (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
        u.mean u.meanVariance 0 mu (q : Real)) =
    mu ^ 2 * _root_.GD.N0232.N0719.N1011.d011288 2 (_root_.GD.N0232.N0720.N1034.d012430 2 2) mu
      ![_root_.GD.N0232.N0720.N1498.d012567 2 q z, _root_.GD.N0232.N0720.N1498.d012568 2 q z] u
  rw [_root_.GD.N0232.N0720.N1498.d012577
    (by norm_num : 0 < 2) (by norm_num : 0 < 2)
    u mu q.property z.property.1 z.property.2]
  unfold _root_.GD.N0232.N0719.N0928.d009413
  simp
  ring

theorem d016347
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i)
    (z : Set.Ioo (0 : Real) 1) :
    Integrable (fun q : Set.Ioi (0 : Real) =>
      ∫ mu : Real,
        _root_.GD.N0232.N0719.N1011.d011288 2 (_root_.GD.N0232.N0720.N1034.d012430 2 2) mu
          ![_root_.GD.N0232.N0720.N1498.d012567 2 q z, _root_.GD.N0232.N0720.N1498.d012568 2 q z] u)
      _root_.GD.N0232.N0720.N1486.d015866 := by
  have hradialOn := _root_.GD.N0232.N0720.N1490.d016324
    _root_.GD.N0232.N0720.N1490.d016308 (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
    u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309 (_root_.GD.N0232.N0720.N1490.d016317 u ht z) _root_.GD.N0232.N0720.N1490.d016313
  have hradial : Integrable (fun q : Set.Ioi (0 : Real) =>
      ∫ mu : Real,
        _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0720.N1490.d016308
          (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
          u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309 mu (q : Real)) := by
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp hradialOn
  unfold _root_.GD.N0232.N0720.N1486.d015866
  rw [integrable_withDensity_iff_integrable_smul'
    _root_.GD.N0232.N0720.N1486.d015863
    (ae_of_all volume fun q =>
      (_root_.GD.N0232.N0720.N1486.d015865 q).lt_top)]
  refine (hradial.const_mul (_root_.GD.N0232.N0720.N1498.d012564 2 2 u)).congr
    (ae_of_all _ fun q => ?_)
  change _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
      (∫ mu : Real,
        _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0720.N1490.d016308
          (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
          u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309 mu (q : Real)) =
    (_root_.GD.N0232.N0720.N1486.d015860 q).toReal •
      (∫ mu : Real,
        _root_.GD.N0232.N0719.N1011.d011288 2 (_root_.GD.N0232.N0720.N1034.d012430 2 2) mu
          ![_root_.GD.N0232.N0720.N1498.d012567 2 q z, _root_.GD.N0232.N0720.N1498.d012568 2 q z] u)
  rw [show (_root_.GD.N0232.N0720.N1486.d015860 q).toReal =
      (q : Real) ^ (-_root_.GD.N0232.N0720.N1490.d016309) by
    rw [_root_.GD.N0232.N0720.N1486.d015860,
      ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1486.d015864 q).le,
      _root_.GD.N0232.N0720.N1486.d015859]]
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with mu
  rw [_root_.GD.N0232.N0720.N1498.d012577
    (by norm_num : 0 < 2) (by norm_num : 0 < 2)
    u mu q.property z.property.1 z.property.2]
  unfold _root_.GD.N0232.N0719.N0928.d009413
  ring

theorem d016348
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i)
    (z : Set.Ioo (0 : Real) 1) :
    Integrable (fun q : Set.Ioi (0 : Real) =>
      ∫ mu : Real,
        mu ^ 2 * _root_.GD.N0232.N0719.N1011.d011288 2 (_root_.GD.N0232.N0720.N1034.d012430 2 2) mu
          ![_root_.GD.N0232.N0720.N1498.d012567 2 q z, _root_.GD.N0232.N0720.N1498.d012568 2 q z] u)
      _root_.GD.N0232.N0720.N1486.d015866 := by
  have hradialOn :=
    _root_.GD.N0232.N0720.N1490.d016344
      _root_.GD.N0232.N0720.N1490.d016308 (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
      u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309 (_root_.GD.N0232.N0720.N1490.d016317 u ht z)
      _root_.GD.N0232.N0720.N1490.d016313 _root_.GD.N0232.N0720.N1490.d016314
  have hradial : Integrable (fun q : Set.Ioi (0 : Real) =>
      ∫ mu : Real,
        mu ^ 2 * _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0720.N1490.d016308
          (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
          u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309 mu (q : Real)) := by
    exact (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp hradialOn
  unfold _root_.GD.N0232.N0720.N1486.d015866
  rw [integrable_withDensity_iff_integrable_smul'
    _root_.GD.N0232.N0720.N1486.d015863
    (ae_of_all volume fun q =>
      (_root_.GD.N0232.N0720.N1486.d015865 q).lt_top)]
  refine (hradial.const_mul (_root_.GD.N0232.N0720.N1498.d012564 2 2 u)).congr
    (ae_of_all _ fun q => ?_)
  change _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
      (∫ mu : Real,
        mu ^ 2 * _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0720.N1490.d016308
          (_root_.GD.N0232.N0720.N1034.d012417 (z : Real))
          u.mean u.meanVariance _root_.GD.N0232.N0720.N1490.d016309 mu (q : Real)) =
    (_root_.GD.N0232.N0720.N1486.d015860 q).toReal •
      (∫ mu : Real,
        mu ^ 2 * _root_.GD.N0232.N0719.N1011.d011288 2
          (_root_.GD.N0232.N0720.N1034.d012430 2 2) mu
          ![_root_.GD.N0232.N0720.N1498.d012567 2 q z, _root_.GD.N0232.N0720.N1498.d012568 2 q z] u)
  rw [show (_root_.GD.N0232.N0720.N1486.d015860 q).toReal =
      (q : Real) ^ (-_root_.GD.N0232.N0720.N1490.d016309) by
    rw [_root_.GD.N0232.N0720.N1486.d015860,
      ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1486.d015864 q).le,
      _root_.GD.N0232.N0720.N1486.d015859]]
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with mu
  rw [_root_.GD.N0232.N0720.N1498.d012577
    (by norm_num : 0 < 2) (by norm_num : 0 < 2)
    u mu q.property z.property.1 z.property.2]
  unfold _root_.GD.N0232.N0719.N0928.d009413
  ring





theorem d016349
    (theta : _root_.GD.N0232.N0720.N1173.d015933) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    _root_.GD.N0232.N0720.N1173.d015937 theta x =
      _root_.GD.N0232.N0719.N1011.d011288 2 (_root_.GD.N0232.N0720.N1034.d012430 2 2) theta.1
        ![_root_.GD.N0232.N0720.N1498.d012567 2 theta.2.1 theta.2.2,
          _root_.GD.N0232.N0720.N1498.d012568 2 theta.2.1 theta.2.2]
        (_root_.GD.N0232.N0720.N1467.d012542 2 2 x) := by
  have h := congrFun
    (_root_.GD.N0232.N0720.N1501.d016296
      2 2 (by norm_num) (by norm_num) (_root_.GD.N0232.N0720.N1173.d015935 theta)) x
  simpa [_root_.GD.N0232.N0720.N1173.d015937, _root_.GD.N0232.N0720.N1173.d015935,
    _root_.GD.N0232.N0720.N1501.d016294,
    _root_.GD.N0232.N0720.N1467.d012537, _root_.GD.N0232.N0720.N1034.d012430,
    _root_.GD.N0232.N0720.N1486.d015873] using h

@[fun_prop]
theorem d016350 (x : _root_.GD.N0232.N0720.N1173.d015936) :
    Continuous (fun theta : _root_.GD.N0232.N0720.N1173.d015933 => _root_.GD.N0232.N0720.N1173.d015937 theta x) := by
  unfold _root_.GD.N0232.N0720.N1173.d015937 _root_.GD.N0232.N0720.N1173.d015935
  exact (_root_.GD.N0232.N0720.N1499.d015007 2 2 x).comp
    (_root_.GD.N0232.N0720.N1486.d015877
      2 2 (by norm_num) (by norm_num))

private theorem d016351
    (theta : _root_.GD.N0232.N0720.N1173.d015933) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    0 <= _root_.GD.N0232.N0720.N1173.d015937 theta x := by
  exact _root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) x




theorem d016352
    (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    Integrable (fun theta : _root_.GD.N0232.N0720.N1173.d015933 => _root_.GD.N0232.N0720.N1173.d015937 theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) := by
  let u := _root_.GD.N0232.N0720.N1467.d012542 2 2 x
  let F : _root_.GD.N0232.N0720.N1173.d015933 -> Real := fun theta => _root_.GD.N0232.N0720.N1173.d015937 theta x
  have hF : StronglyMeasurable F :=
    (_root_.GD.N0232.N0720.N1490.d016350 x).stronglyMeasurable
  unfold _root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1486.d015870
  apply (integrable_prod_iff' hF.aestronglyMeasurable).2
  constructor
  · filter_upwards [] with qz
    have hloc := _root_.GD.N0232.N0720.N1490.d016345 u qz.2 qz.1
    refine hloc.congr (ae_of_all _ fun mu => ?_)
    exact (_root_.GD.N0232.N0720.N1490.d016349 (mu, qz) x).symm
  · let H : (Set.Ioi (0 : Real) × Set.Ioo (0 : Real) 1) -> Real :=
      fun qz => ∫ mu : Real, ‖F (mu, qz)‖
    have hHmeas : StronglyMeasurable H := by
      exact hF.norm.integral_prod_left'
    apply (integrable_prod_iff' hHmeas.aestronglyMeasurable).2
    constructor
    · filter_upwards [] with z
      have hradial := _root_.GD.N0232.N0720.N1490.d016347 u ht z
      refine hradial.congr (ae_of_all _ fun q => ?_)
      apply integral_congr_ae
      filter_upwards with mu
      rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0232.N0720.N1490.d016351 (mu, (q, z)) x)]
      exact (_root_.GD.N0232.N0720.N1490.d016349 (mu, (q, z)) x).symm
    · have houter := _root_.GD.N0232.N0720.N1490.d016338 u ht
      refine houter.congr (ae_of_all _ fun z => ?_)
      unfold H _root_.GD.N0232.N0720.N1493.d016097
      apply integral_congr_ae
      filter_upwards with q
      have hHnonneg : 0 <= ∫ mu : Real, ‖F (mu, (q, z))‖ :=
        integral_nonneg fun mu => norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hHnonneg]
      apply integral_congr_ae
      filter_upwards with mu
      rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0232.N0720.N1490.d016351 (mu, (q, z)) x)]
      exact (_root_.GD.N0232.N0720.N1490.d016349 (mu, (q, z)) x).symm



theorem d016353
    (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    Integrable (fun theta : _root_.GD.N0232.N0720.N1173.d015933 =>
      _root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 * _root_.GD.N0232.N0720.N1173.d015937 theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) := by
  let u := _root_.GD.N0232.N0720.N1467.d012542 2 2 x
  let F : _root_.GD.N0232.N0720.N1173.d015933 -> Real := fun theta =>
    _root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 * _root_.GD.N0232.N0720.N1173.d015937 theta x
  have hF : StronglyMeasurable F := by
    unfold F _root_.GD.N0232.N0720.N1173.d015938
    exact (continuous_fst.pow 2 |>.mul
      (_root_.GD.N0232.N0720.N1490.d016350 x)).stronglyMeasurable
  unfold _root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1486.d015870
  apply (integrable_prod_iff' hF.aestronglyMeasurable).2
  constructor
  · filter_upwards [] with qz
    have hloc := _root_.GD.N0232.N0720.N1490.d016346 u qz.2 qz.1
    refine hloc.congr (ae_of_all _ fun mu => ?_)
    unfold F _root_.GD.N0232.N0720.N1173.d015938
    change mu ^ 2 * _root_.GD.N0232.N0719.N1011.d011288 2
        (_root_.GD.N0232.N0720.N1034.d012430 2 2) mu
        ![_root_.GD.N0232.N0720.N1498.d012567 2 qz.1 qz.2,
          _root_.GD.N0232.N0720.N1498.d012568 2 qz.1 qz.2] u =
      mu ^ 2 * _root_.GD.N0232.N0720.N1173.d015937 (mu, qz) x
    rw [_root_.GD.N0232.N0720.N1490.d016349 (mu, qz) x]
  · let H : (Set.Ioi (0 : Real) × Set.Ioo (0 : Real) 1) -> Real :=
      fun qz => ∫ mu : Real, ‖F (mu, qz)‖
    have hHmeas : StronglyMeasurable H := by
      exact hF.norm.integral_prod_left'
    apply (integrable_prod_iff' hHmeas.aestronglyMeasurable).2
    constructor
    · filter_upwards [] with z
      have hradial :=
        _root_.GD.N0232.N0720.N1490.d016348 u ht z
      refine hradial.congr (ae_of_all _ fun q => ?_)
      apply integral_congr_ae
      filter_upwards with mu
      have hnonneg : 0 <= F (mu, (q, z)) := by
        unfold F _root_.GD.N0232.N0720.N1173.d015938
        exact mul_nonneg (sq_nonneg _)
          (_root_.GD.N0232.N0720.N1490.d016351 (mu, (q, z)) x)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      unfold F _root_.GD.N0232.N0720.N1173.d015938
      rw [_root_.GD.N0232.N0720.N1490.d016349 (mu, (q, z)) x]
    · have houter := _root_.GD.N0232.N0720.N1490.d016342 u ht
      refine houter.congr (ae_of_all _ fun z => ?_)
      unfold H _root_.GD.N0232.N0720.N1490.d016327
      apply integral_congr_ae
      filter_upwards with q
      have hHnonneg : 0 <= ∫ mu : Real, ‖F (mu, (q, z))‖ :=
        integral_nonneg fun mu => norm_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hHnonneg]
      apply integral_congr_ae
      filter_upwards with mu
      have hnonneg : 0 <= F (mu, (q, z)) := by
        unfold F _root_.GD.N0232.N0720.N1173.d015938
        exact mul_nonneg (sq_nonneg _)
          (_root_.GD.N0232.N0720.N1490.d016351 (mu, (q, z)) x)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      unfold F _root_.GD.N0232.N0720.N1173.d015938
      rw [_root_.GD.N0232.N0720.N1490.d016349 (mu, (q, z)) x]




theorem d016354
    (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    Integrable (fun theta : _root_.GD.N0232.N0720.N1173.d015933 =>
      _root_.GD.N0232.N0720.N1173.d015938 theta * _root_.GD.N0232.N0720.N1173.d015937 theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) := by
  have hzero := _root_.GD.N0232.N0720.N1490.d016352 x ht
  have hsecond :=
    _root_.GD.N0232.N0720.N1490.d016353 x ht
  have hmajor := hsecond.add hzero
  have hmeas : AEStronglyMeasurable (fun theta : _root_.GD.N0232.N0720.N1173.d015933 =>
      _root_.GD.N0232.N0720.N1173.d015938 theta * _root_.GD.N0232.N0720.N1173.d015937 theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) := by
    unfold _root_.GD.N0232.N0720.N1173.d015938
    exact (continuous_fst.mul
      (_root_.GD.N0232.N0720.N1490.d016350 x)).aestronglyMeasurable
  refine hmajor.mono' hmeas (ae_of_all _ fun theta => ?_)
  have hL : 0 <= _root_.GD.N0232.N0720.N1173.d015937 theta x := _root_.GD.N0232.N0720.N1490.d016351 theta x
  have habs : |_root_.GD.N0232.N0720.N1173.d015938 theta| <= _root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 + 1 := by
    have habsSq : |_root_.GD.N0232.N0720.N1173.d015938 theta| ^ 2 = _root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 :=
      sq_abs _
    nlinarith [sq_nonneg (|_root_.GD.N0232.N0720.N1173.d015938 theta| - 1 / 2)]
  have hright : 0 ≤
      _root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 * _root_.GD.N0232.N0720.N1173.d015937 theta x +
        _root_.GD.N0232.N0720.N1173.d015937 theta x :=
    add_nonneg (mul_nonneg (sq_nonneg _) hL) hL
  have hmul :
      |_root_.GD.N0232.N0720.N1173.d015938 theta| * _root_.GD.N0232.N0720.N1173.d015937 theta x ≤
        _root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 * _root_.GD.N0232.N0720.N1173.d015937 theta x +
          _root_.GD.N0232.N0720.N1173.d015937 theta x := by
    calc
      |_root_.GD.N0232.N0720.N1173.d015938 theta| * _root_.GD.N0232.N0720.N1173.d015937 theta x ≤
          (_root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 + 1) * _root_.GD.N0232.N0720.N1173.d015937 theta x :=
        mul_le_mul_of_nonneg_right habs hL
      _ = _root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 * _root_.GD.N0232.N0720.N1173.d015937 theta x +
          _root_.GD.N0232.N0720.N1173.d015937 theta x := by ring
  simpa only [Pi.add_apply, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hL, abs_of_nonneg hright] using hmul



theorem d016355
    (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    (∫ theta : _root_.GD.N0232.N0720.N1173.d015933, _root_.GD.N0232.N0720.N1173.d015937 theta x
        ∂_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) =
      _root_.GD.N0232.N0720.N1493.d016108 (_root_.GD.N0232.N0720.N1467.d012542 2 2 x) := by
  let u := _root_.GD.N0232.N0720.N1467.d012542 2 2 x
  have hfull := _root_.GD.N0232.N0720.N1490.d016352 x ht
  have houter : Integrable
      (fun qz : Set.Ioi (0 : Real) × Set.Ioo (0 : Real) 1 =>
        ∫ mu : Real, _root_.GD.N0232.N0720.N1173.d015937 (mu, qz) x)
      (_root_.GD.N0232.N0720.N1486.d015866.prod _root_.GD.N0232.N0720.N1493.d016104) := by
    simpa [_root_.GD.N0232.N0720.N1173.d015934, _root_.GD.N0232.N0720.N1486.d015870] using
      hfull.integral_prod_right
  calc
    (∫ theta : _root_.GD.N0232.N0720.N1173.d015933, _root_.GD.N0232.N0720.N1173.d015937 theta x
        ∂_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) =
      ∫ qz : Set.Ioi (0 : Real) × Set.Ioo (0 : Real) 1,
        (∫ mu : Real, _root_.GD.N0232.N0720.N1173.d015937 (mu, qz) x)
        ∂(_root_.GD.N0232.N0720.N1486.d015866.prod _root_.GD.N0232.N0720.N1493.d016104) := by
      unfold _root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1486.d015870 at hfull ⊢
      exact integral_prod_symm _ hfull
    _ = ∫ z : Set.Ioo (0 : Real) 1,
        (∫ q : Set.Ioi (0 : Real),
          (∫ mu : Real, _root_.GD.N0232.N0720.N1173.d015937 (mu, (q, z)) x)
          ∂_root_.GD.N0232.N0720.N1486.d015866
        ) ∂_root_.GD.N0232.N0720.N1493.d016104 := by
      exact integral_prod_symm _ houter
    _ = ∫ z : Set.Ioo (0 : Real) 1,
        _root_.GD.N0232.N0720.N1493.d016097 u z ∂_root_.GD.N0232.N0720.N1493.d016104 := by
      apply integral_congr_ae
      filter_upwards with z
      unfold _root_.GD.N0232.N0720.N1493.d016097
      apply integral_congr_ae
      filter_upwards with q
      apply integral_congr_ae
      filter_upwards with mu
      exact _root_.GD.N0232.N0720.N1490.d016349 (mu, (q, z)) x
    _ = ∫ q : _root_.GD.N0232.N0720.N1490.d016310,
        _root_.GD.N0232.N0720.N1493.d016097 u (_root_.GD.N0232.N0720.N1493.d016102 q) := by
      have hmap := integral_map
        (μ := (volume : Measure _root_.GD.N0232.N0720.N1490.d016310))
        _root_.GD.N0232.N0720.N1493.d016103.measurable.aemeasurable
        (_root_.GD.N0232.N0720.N1490.d016333 u ht).aestronglyMeasurable
      simpa [_root_.GD.N0232.N0720.N1493.d016104] using hmap
    _ = _root_.GD.N0232.N0720.N1493.d016108 u := rfl

theorem d016356
    (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    (∫ theta : _root_.GD.N0232.N0720.N1173.d015933,
        _root_.GD.N0232.N0720.N1173.d015938 theta * _root_.GD.N0232.N0720.N1173.d015937 theta x
        ∂_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) =
      _root_.GD.N0232.N0720.N1493.d016109 (_root_.GD.N0232.N0720.N1467.d012542 2 2 x) := by
  let u := _root_.GD.N0232.N0720.N1467.d012542 2 2 x
  have hfull :=
    _root_.GD.N0232.N0720.N1490.d016354 x ht
  have houter : Integrable
      (fun qz : Set.Ioi (0 : Real) × Set.Ioo (0 : Real) 1 =>
        ∫ mu : Real, _root_.GD.N0232.N0720.N1173.d015938 (mu, qz) * _root_.GD.N0232.N0720.N1173.d015937 (mu, qz) x)
      (_root_.GD.N0232.N0720.N1486.d015866.prod _root_.GD.N0232.N0720.N1493.d016104) := by
    simpa [_root_.GD.N0232.N0720.N1173.d015934, _root_.GD.N0232.N0720.N1486.d015870] using
      hfull.integral_prod_right
  calc
    (∫ theta : _root_.GD.N0232.N0720.N1173.d015933,
        _root_.GD.N0232.N0720.N1173.d015938 theta * _root_.GD.N0232.N0720.N1173.d015937 theta x
        ∂_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) =
      ∫ qz : Set.Ioi (0 : Real) × Set.Ioo (0 : Real) 1,
        (∫ mu : Real,
          _root_.GD.N0232.N0720.N1173.d015938 (mu, qz) * _root_.GD.N0232.N0720.N1173.d015937 (mu, qz) x)
        ∂(_root_.GD.N0232.N0720.N1486.d015866.prod _root_.GD.N0232.N0720.N1493.d016104) := by
      unfold _root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1486.d015870 at hfull ⊢
      exact integral_prod_symm _ hfull
    _ = ∫ z : Set.Ioo (0 : Real) 1,
        (∫ q : Set.Ioi (0 : Real),
          (∫ mu : Real,
            _root_.GD.N0232.N0720.N1173.d015938 (mu, (q, z)) * _root_.GD.N0232.N0720.N1173.d015937 (mu, (q, z)) x)
          ∂_root_.GD.N0232.N0720.N1486.d015866
        ) ∂_root_.GD.N0232.N0720.N1493.d016104 := by
      exact integral_prod_symm _ houter
    _ = ∫ z : Set.Ioo (0 : Real) 1,
        _root_.GD.N0232.N0720.N1493.d016098 u z
        ∂_root_.GD.N0232.N0720.N1493.d016104 := by
      apply integral_congr_ae
      filter_upwards with z
      unfold _root_.GD.N0232.N0720.N1493.d016098
      apply integral_congr_ae
      filter_upwards with q
      apply integral_congr_ae
      filter_upwards with mu
      unfold _root_.GD.N0232.N0720.N1173.d015938
      rw [_root_.GD.N0232.N0720.N1490.d016349 (mu, (q, z)) x]
    _ = ∫ q : _root_.GD.N0232.N0720.N1490.d016310,
        _root_.GD.N0232.N0720.N1493.d016098 u (_root_.GD.N0232.N0720.N1493.d016102 q) := by
      have hmap := integral_map
        (μ := (volume : Measure _root_.GD.N0232.N0720.N1490.d016310))
        _root_.GD.N0232.N0720.N1493.d016103.measurable.aemeasurable
        (_root_.GD.N0232.N0720.N1490.d016334 u ht).aestronglyMeasurable
      simpa [_root_.GD.N0232.N0720.N1493.d016104] using hmap
    _ = _root_.GD.N0232.N0720.N1493.d016109 u := rfl

#print axioms _root_.GD.N0232.N0720.N1490.d016352
#print axioms _root_.GD.N0232.N0720.N1490.d016353
#print axioms _root_.GD.N0232.N0720.N1490.d016354
#print axioms _root_.GD.N0232.N0720.N1490.d016355
#print axioms _root_.GD.N0232.N0720.N1490.d016356

end

end N1490
end N0720
end N0232
end GD
