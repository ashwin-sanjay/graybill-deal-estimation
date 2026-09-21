import GD.Module0656
import GD.Module0645
import GD.Module1000






















open MeasureTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1493

noncomputable section

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N1011
open _root_.GD.N0232.N0719.N0928
open _root_.GD.N0232.N0719.N0929
open _root_.GD.N0232.N0719.N0868
open _root_.GD.N0232.N0719.N0947
open _root_.GD.N0232.N0719.N0954
open _root_.GD.N0232.N0720.N1034
open _root_.GD.N0232.N0720.N1498
open _root_.GD.N0232.N0720.N1486

attribute [local instance] Measure.Subtype.measureSpace

private abbrev d016089 : Fin 2 → ℝ :=
  _root_.GD.N0232.N0719.N0954.d009355 (_root_.GD.N0232.N0720.N1034.d012430 2 2)

private theorem d016090 : ∀ i, 0 < _root_.GD.N0232.N0720.N1493.d016089 i := by
  apply _root_.GD.N0232.N0719.N0954.d009358
  intro i
  fin_cases i <;> norm_num [_root_.GD.N0232.N0720.N1034.d012430]

private theorem d016091 :
    0 < _root_.GD.N0232.N0719.N0928.d009415 _root_.GD.N0232.N0720.N1493.d016089 (_root_.GD.N0232.N0720.N1034.d012428 4) := by
  rw [_root_.GD.N0232.N0720.N1034.d012431
    2 2 (by norm_num) (by norm_num) 4]
  norm_num [_root_.GD.N0232.N0720.N1034.d012429]

private theorem d016092
    (z : Set.Ioo (0 : ℝ) 1) :
    ∀ i, 0 < _root_.GD.N0232.N0720.N1034.d012417 (z : ℝ) i := by
  intro i
  fin_cases i
  · simpa [_root_.GD.N0232.N0720.N1034.d012417] using z.property.1
  · simpa [_root_.GD.N0232.N0720.N1034.d012417] using sub_pos.mpr z.property.2

private theorem d016093
    (z : Set.Ioo (0 : ℝ) 1) :
    ∑ i, _root_.GD.N0232.N0720.N1034.d012417 (z : ℝ) i = 1 := by
  simp [_root_.GD.N0232.N0720.N1034.d012417, Fin.sum_univ_two]

private theorem d016094
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i)
    (z : Set.Ioo (0 : ℝ) 1) :
    0 < _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0720.N1493.d016089
      (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ)) u.mean u.meanVariance := by
  obtain ⟨c, hc, hfloor⟩ :=
    _root_.GD.N0232.N0719.N0929.d009644
      (by norm_num : 0 < 2) _root_.GD.N0232.N0720.N1493.d016089 u.meanVariance _root_.GD.N0232.N0720.N1493.d016090 ht
  have hge := _root_.GD.N0232.N0719.N0928.d009442 _root_.GD.N0232.N0720.N1493.d016089
    (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ)) u.mean u.meanVariance c
    (fun i ↦ (_root_.GD.N0232.N0720.N1493.d016092 z i).le)
    (_root_.GD.N0232.N0720.N1493.d016093 z) hfloor
  linarith





theorem d016095
    {I : Type*} [Fintype I]
    (shape p y t : I → ℝ) (s : ℝ) {q : ℝ} (hq : 0 < q) :
    (∫ mu : ℝ, mu * _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) =
      _root_.GD.N0232.N0719.N0928.d009405 p y *
        ∫ mu : ℝ, _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q := by
  let C := _root_.GD.N0232.N0719.N0928.d009407 shape p y t
  let m := _root_.GD.N0232.N0719.N0928.d009405 p y
  let A := q ^ (-s) * q ^ (-_root_.GD.N0232.N0719.N0928.d009408 shape) *
    _root_.GD.N0232.N0719.N0928.d009409 shape p * Real.exp (-(C / q))
  have hsplit :
      (fun mu ↦ _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) =
        fun mu ↦ A * Real.exp (-((mu - m) ^ 2 / 2) / q) := by
    funext mu
    unfold _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0719.N0928.d009412 A C m
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
    ring
  have hgauss :
      (∫ mu : ℝ, mu * Real.exp (-((mu - m) ^ 2 / 2) / q)) =
        m * ∫ mu : ℝ, Real.exp (-((mu - m) ^ 2 / 2) / q) := by
    have h := _root_.GD.N0232.N0719.N0947.d009465 (inv_pos.mpr hq) m
    convert h using 1
    · apply integral_congr_ae
      filter_upwards with mu
      congr 2
      field_simp [hq.ne']
      ring
    · congr 1
      apply integral_congr_ae
      filter_upwards with mu
      congr 1
      field_simp [hq.ne']
      ring
  have hweighted :
      (fun mu ↦ mu * _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) =
        fun mu ↦ A *
          (mu * Real.exp (-((mu - m) ^ 2 / 2) / q)) := by
    funext mu
    rw [congrFun hsplit mu]
    ring
  rw [hweighted, hsplit, integral_const_mul, hgauss,
    integral_const_mul]
  unfold m
  ring



theorem d016096
    {I : Type*} [Fintype I]
    (shape p y t : I → ℝ) (s : ℝ)
    (henergy : 0 < _root_.GD.N0232.N0719.N0928.d009407 shape p y t)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    (∫ q in Ioi (0 : ℝ),
        ∫ mu : ℝ,
          mu * _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) =
      _root_.GD.N0232.N0719.N0928.d009405 p y * _root_.GD.N0232.N0719.N0928.d009437 shape p y t s := by
  calc
    (∫ q in Ioi (0 : ℝ),
        ∫ mu : ℝ,
          mu * _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) =
        ∫ q in Ioi (0 : ℝ),
          _root_.GD.N0232.N0719.N0928.d009405 p y *
            ∫ mu : ℝ,
              _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro q hq
      exact _root_.GD.N0232.N0720.N1493.d016095
        shape p y t s hq
    _ = _root_.GD.N0232.N0719.N0928.d009405 p y *
        (∫ q in Ioi (0 : ℝ),
          ∫ mu : ℝ,
            _root_.GD.N0232.N0719.N0928.d009413 shape p y t s mu q) := by
      rw [integral_const_mul]
    _ = _root_.GD.N0232.N0719.N0928.d009405 p y * _root_.GD.N0232.N0719.N0928.d009437 shape p y t s := by
      rw [_root_.GD.N0232.N0719.N0928.d009444
        shape p y t s henergy hpower]





def d016097
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (z : Set.Ioo (0 : ℝ) 1) : ℝ :=
  ∫ q : Set.Ioi (0 : ℝ),
    (∫ mu : ℝ,
      _root_.GD.N0232.N0719.N1011.d011288 2 (_root_.GD.N0232.N0720.N1034.d012430 2 2) mu
        ![_root_.GD.N0232.N0720.N1498.d012567 2 q z, _root_.GD.N0232.N0720.N1498.d012568 2 q z] u)
      ∂_root_.GD.N0232.N0720.N1486.d015866


def d016098
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (z : Set.Ioo (0 : ℝ) 1) : ℝ :=
  ∫ q : Set.Ioi (0 : ℝ),
    (∫ mu : ℝ,
      mu * _root_.GD.N0232.N0719.N1011.d011288 2 (_root_.GD.N0232.N0720.N1034.d012430 2 2) mu
        ![_root_.GD.N0232.N0720.N1498.d012567 2 q z, _root_.GD.N0232.N0720.N1498.d012568 2 q z] u)
      ∂_root_.GD.N0232.N0720.N1486.d015866

theorem d016099
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i)
    (z : Set.Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1493.d016097 u z =
      _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
        _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1493.d016089
          (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ)) u.mean u.meanVariance
          (_root_.GD.N0232.N0720.N1034.d012428 4) := by
  unfold _root_.GD.N0232.N0720.N1493.d016097 _root_.GD.N0232.N0720.N1486.d015866
  rw [integral_withDensity_eq_integral_toReal_smul
    _root_.GD.N0232.N0720.N1486.d015863
    (ae_of_all volume fun q ↦
      (_root_.GD.N0232.N0720.N1486.d015865 q).lt_top)]
  have hdensity (q : Set.Ioi (0 : ℝ)) :
      (_root_.GD.N0232.N0720.N1486.d015860 q).toReal =
        (q : ℝ) ^ (-(_root_.GD.N0232.N0720.N1034.d012428 4)) := by
    rw [_root_.GD.N0232.N0720.N1486.d015860,
      ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1486.d015864 q).le,
      _root_.GD.N0232.N0720.N1486.d015859]
  simp_rw [smul_eq_mul, hdensity]
  have hradial :
      (∫ q : Set.Ioi (0 : ℝ),
          ∫ mu : ℝ,
            _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0720.N1493.d016089
              (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ))
              u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) mu (q : ℝ)) =
        _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1493.d016089
          (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ)) u.mean u.meanVariance
          (_root_.GD.N0232.N0720.N1034.d012428 4) := by
    calc
      (∫ q : Set.Ioi (0 : ℝ),
          ∫ mu : ℝ,
            _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0720.N1493.d016089
              (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ))
              u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) mu (q : ℝ)) =
          ∫ q in Ioi (0 : ℝ),
            ∫ mu : ℝ,
              _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0720.N1493.d016089
                (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ))
                u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) mu q :=
        integral_subtype (s := Ioi (0 : ℝ)) measurableSet_Ioi
          (fun q : ℝ ↦
            ∫ mu : ℝ,
              _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0720.N1493.d016089
                (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ))
                u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) mu q)
      _ = _ := _root_.GD.N0232.N0719.N0928.d009444
        _root_.GD.N0232.N0720.N1493.d016089 (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ))
        u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4)
        (_root_.GD.N0232.N0720.N1493.d016094 u ht z) _root_.GD.N0232.N0720.N1493.d016091
  calc
    (∫ q : Set.Ioi (0 : ℝ),
        (q : ℝ) ^ (-(_root_.GD.N0232.N0720.N1034.d012428 4)) *
          ∫ mu : ℝ,
            _root_.GD.N0232.N0719.N1011.d011288 2 (_root_.GD.N0232.N0720.N1034.d012430 2 2) mu
              ![_root_.GD.N0232.N0720.N1498.d012567 2 q z,
                _root_.GD.N0232.N0720.N1498.d012568 2 q z] u) =
        ∫ q : Set.Ioi (0 : ℝ),
          _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
            ∫ mu : ℝ,
              _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0720.N1493.d016089
                (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ))
                u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) mu (q : ℝ) := by
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
        (∫ q : Set.Ioi (0 : ℝ),
          ∫ mu : ℝ,
            _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0720.N1493.d016089
              (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ))
              u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) mu (q : ℝ)) := by
      rw [integral_const_mul]
    _ = _ := by rw [hradial]

theorem d016100
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i)
    (z : Set.Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1493.d016098 u z =
      _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
        (_root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1493.d016089
          (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ)) u.mean u.meanVariance
          (_root_.GD.N0232.N0720.N1034.d012428 4) *
        _root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ)) u.mean) := by
  unfold _root_.GD.N0232.N0720.N1493.d016098 _root_.GD.N0232.N0720.N1486.d015866
  rw [integral_withDensity_eq_integral_toReal_smul
    _root_.GD.N0232.N0720.N1486.d015863
    (ae_of_all volume fun q ↦
      (_root_.GD.N0232.N0720.N1486.d015865 q).lt_top)]
  have hdensity (q : Set.Ioi (0 : ℝ)) :
      (_root_.GD.N0232.N0720.N1486.d015860 q).toReal =
        (q : ℝ) ^ (-(_root_.GD.N0232.N0720.N1034.d012428 4)) := by
    rw [_root_.GD.N0232.N0720.N1486.d015860,
      ENNReal.toReal_ofReal (_root_.GD.N0232.N0720.N1486.d015864 q).le,
      _root_.GD.N0232.N0720.N1486.d015859]
  simp_rw [smul_eq_mul, hdensity]
  have hradial :
      (∫ q : Set.Ioi (0 : ℝ),
          ∫ mu : ℝ,
            mu * _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0720.N1493.d016089
              (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ))
              u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) mu (q : ℝ)) =
        _root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ)) u.mean *
          _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1493.d016089
            (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ)) u.mean u.meanVariance
            (_root_.GD.N0232.N0720.N1034.d012428 4) := by
    calc
      (∫ q : Set.Ioi (0 : ℝ),
          ∫ mu : ℝ,
            mu * _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0720.N1493.d016089
              (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ))
              u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) mu (q : ℝ)) =
          ∫ q in Ioi (0 : ℝ),
            ∫ mu : ℝ,
              mu * _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0720.N1493.d016089
                (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ))
                u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) mu q :=
        integral_subtype (s := Ioi (0 : ℝ)) measurableSet_Ioi
          (fun q : ℝ ↦
            ∫ mu : ℝ,
              mu * _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0720.N1493.d016089
                (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ))
                u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) mu q)
      _ = _ := _root_.GD.N0232.N0720.N1493.d016096
        _root_.GD.N0232.N0720.N1493.d016089 (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ))
        u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4)
        (_root_.GD.N0232.N0720.N1493.d016094 u ht z) _root_.GD.N0232.N0720.N1493.d016091
  calc
    (∫ q : Set.Ioi (0 : ℝ),
        (q : ℝ) ^ (-(_root_.GD.N0232.N0720.N1034.d012428 4)) *
          ∫ mu : ℝ,
            mu * _root_.GD.N0232.N0719.N1011.d011288 2 (_root_.GD.N0232.N0720.N1034.d012430 2 2) mu
              ![_root_.GD.N0232.N0720.N1498.d012567 2 q z,
                _root_.GD.N0232.N0720.N1498.d012568 2 q z] u) =
        ∫ q : Set.Ioi (0 : ℝ),
          _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
            ∫ mu : ℝ,
              mu * _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0720.N1493.d016089
                (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ))
                u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) mu (q : ℝ) := by
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
        (∫ q : Set.Ioi (0 : ℝ),
          ∫ mu : ℝ,
            mu * _root_.GD.N0232.N0719.N0928.d009413 _root_.GD.N0232.N0720.N1493.d016089
              (_root_.GD.N0232.N0720.N1034.d012417 (z : ℝ))
              u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) mu (q : ℝ)) := by
      rw [integral_const_mul]
    _ = _ := by
      rw [hradial]
      ring



private abbrev d016101 :=
  {q : _root_.GD.N0232.N0719.N0857.d009377 2 //
    q ∈ _root_.GD.N0232.N0719.N0955.d009607 2}


def d016102 (q : _root_.GD.N0232.N0720.N1493.d016101) : Set.Ioo (0 : ℝ) 1 := by
  let z := _root_.GD.N0232.N0719.N0853.d009567
    (by norm_num : 0 < 2) q.1 0
  have hz0 : 0 < z :=
    _root_.GD.N0232.N0719.N0929.d009631
      (by norm_num : 0 < 2) q.property 0
  have hother : 0 <
      _root_.GD.N0232.N0719.N0853.d009567
        (by norm_num : 0 < 2) q.1 1 :=
    _root_.GD.N0232.N0719.N0929.d009631
      (by norm_num : 0 < 2) q.property 1
  have hsum := _root_.GD.N0232.N0719.N0853.d009570
    (by norm_num : 0 < 2) q.1
  rw [Fin.sum_univ_two] at hsum
  exact ⟨z, hz0, by linarith⟩

@[fun_prop]
theorem d016103 : Continuous _root_.GD.N0232.N0720.N1493.d016102 := by
  exact
    ((_root_.GD.N0232.N0719.N0853.d009582
      (by norm_num : 0 < 2) 0).comp continuous_subtype_val).subtype_mk _



def d016104 : Measure (Set.Ioo (0 : ℝ) 1) :=
  volume.map _root_.GD.N0232.N0720.N1493.d016102

private noncomputable instance d016105 :
    IsFiniteMeasure (volume : Measure _root_.GD.N0232.N0720.N1493.d016101) where
  measure_univ_lt_top := by
    rw [Measure.Subtype.volume_univ
      (_root_.GD.N0232.N0719.N0955.d009608 2).nullMeasurableSet]
    exact _root_.GD.N0232.N0719.N0929.d009634 (by norm_num : 0 < 2)

noncomputable instance d016106 :
    IsFiniteMeasure _root_.GD.N0232.N0720.N1493.d016104 := by
  unfold _root_.GD.N0232.N0720.N1493.d016104
  infer_instance

private theorem d016107
    (q : _root_.GD.N0232.N0720.N1493.d016101) :
    _root_.GD.N0232.N0720.N1034.d012417 (_root_.GD.N0232.N0720.N1493.d016102 q : ℝ) =
      _root_.GD.N0232.N0719.N0853.d009567
        (by norm_num : 0 < 2) q.1 := by
  funext i
  fin_cases i
  · rfl
  · have hsum :=
      _root_.GD.N0232.N0719.N0853.d009570
        (by norm_num : 0 < 2) q.1
    rw [Fin.sum_univ_two] at hsum
    have hlast :
        _root_.GD.N0232.N0719.N0853.d009567
            (by norm_num : 0 < 2) q.1 (1 : Fin 2) =
          1 -
        _root_.GD.N0232.N0719.N0853.d009567
            (by norm_num : 0 < 2) q.1 (0 : Fin 2) := by
      linarith
    have hz : (_root_.GD.N0232.N0720.N1493.d016102 q : ℝ) =
        _root_.GD.N0232.N0719.N0853.d009567
          (by norm_num : 0 < 2) q.1 (0 : Fin 2) := rfl
    rw [hz]
    exact hlast.symm




def d016108 (u : _root_.GD.N0232.N0719.N0900.d009096 2) : ℝ :=
  ∫ q : _root_.GD.N0232.N0720.N1493.d016101,
    _root_.GD.N0232.N0720.N1493.d016097 u (_root_.GD.N0232.N0720.N1493.d016102 q)

def d016109 (u : _root_.GD.N0232.N0719.N0900.d009096 2) : ℝ :=
  ∫ q : _root_.GD.N0232.N0720.N1493.d016101,
    _root_.GD.N0232.N0720.N1493.d016098 u (_root_.GD.N0232.N0720.N1493.d016102 q)

def d016110 (u : _root_.GD.N0232.N0719.N0900.d009096 2) : ℝ :=
  _root_.GD.N0232.N0720.N1493.d016109 u / _root_.GD.N0232.N0720.N1493.d016108 u

theorem d016111
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i) :
    _root_.GD.N0232.N0720.N1493.d016108 u =
      _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
        _root_.GD.N0232.N0719.N0929.d009647 (by norm_num : 0 < 2) _root_.GD.N0232.N0720.N1493.d016089
          u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) := by
  unfold _root_.GD.N0232.N0720.N1493.d016108
  calc
    (∫ q : _root_.GD.N0232.N0720.N1493.d016101,
        _root_.GD.N0232.N0720.N1493.d016097 u (_root_.GD.N0232.N0720.N1493.d016102 q)) =
        ∫ q : _root_.GD.N0232.N0720.N1493.d016101,
          _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
            _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1493.d016089
              (_root_.GD.N0232.N0720.N1034.d012417 (_root_.GD.N0232.N0720.N1493.d016102 q : ℝ))
              u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) := by
      apply integral_congr_ae
      filter_upwards with q
      exact _root_.GD.N0232.N0720.N1493.d016099 u ht (_root_.GD.N0232.N0720.N1493.d016102 q)
    _ = _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
        ∫ q : _root_.GD.N0232.N0720.N1493.d016101,
          _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1493.d016089
            (_root_.GD.N0232.N0719.N0853.d009567
              (by norm_num : 0 < 2) q.1)
            u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) := by
      rw [integral_const_mul]
      apply congrArg
      apply integral_congr_ae
      filter_upwards with q
      rw [_root_.GD.N0232.N0720.N1493.d016107]
    _ = _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
        ∫ q in _root_.GD.N0232.N0719.N0955.d009607 2,
          _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1493.d016089
            (_root_.GD.N0232.N0719.N0853.d009567
              (by norm_num : 0 < 2) q)
            u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) := by
      congr 1
      exact integral_subtype
        (_root_.GD.N0232.N0719.N0955.d009608 2)
        (fun q ↦ _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1493.d016089
          (_root_.GD.N0232.N0719.N0853.d009567
            (by norm_num : 0 < 2) q)
          u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4))
    _ = _ := rfl

theorem d016112
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i) :
    _root_.GD.N0232.N0720.N1493.d016109 u =
      _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
        _root_.GD.N0232.N0719.N0929.d009652 (by norm_num : 0 < 2) _root_.GD.N0232.N0720.N1493.d016089
          u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) := by
  unfold _root_.GD.N0232.N0720.N1493.d016109
  calc
    (∫ q : _root_.GD.N0232.N0720.N1493.d016101,
        _root_.GD.N0232.N0720.N1493.d016098 u (_root_.GD.N0232.N0720.N1493.d016102 q)) =
        ∫ q : _root_.GD.N0232.N0720.N1493.d016101,
          _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
            (_root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1493.d016089
                (_root_.GD.N0232.N0720.N1034.d012417 (_root_.GD.N0232.N0720.N1493.d016102 q : ℝ))
                u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) *
              _root_.GD.N0232.N0719.N0928.d009405
                (_root_.GD.N0232.N0720.N1034.d012417 (_root_.GD.N0232.N0720.N1493.d016102 q : ℝ))
                u.mean) := by
      apply integral_congr_ae
      filter_upwards with q
      exact _root_.GD.N0232.N0720.N1493.d016100 u ht (_root_.GD.N0232.N0720.N1493.d016102 q)
    _ = _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
        ∫ q : _root_.GD.N0232.N0720.N1493.d016101,
          _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1493.d016089
              (_root_.GD.N0232.N0719.N0853.d009567
                (by norm_num : 0 < 2) q.1)
              u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) *
            _root_.GD.N0232.N0719.N0928.d009405
              (_root_.GD.N0232.N0719.N0853.d009567
                (by norm_num : 0 < 2) q.1)
              u.mean := by
      rw [integral_const_mul]
      apply congrArg
      apply integral_congr_ae
      filter_upwards with q
      rw [_root_.GD.N0232.N0720.N1493.d016107]
    _ = _root_.GD.N0232.N0720.N1498.d012564 2 2 u *
        ∫ q in _root_.GD.N0232.N0719.N0955.d009607 2,
          _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1493.d016089
              (_root_.GD.N0232.N0719.N0853.d009567
                (by norm_num : 0 < 2) q)
              u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) *
            _root_.GD.N0232.N0719.N0928.d009405
              (_root_.GD.N0232.N0719.N0853.d009567
                (by norm_num : 0 < 2) q)
              u.mean := by
      congr 1
      exact integral_subtype
        (_root_.GD.N0232.N0719.N0955.d009608 2)
        (fun q ↦ _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1493.d016089
              (_root_.GD.N0232.N0719.N0853.d009567
                (by norm_num : 0 < 2) q)
              u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) *
            _root_.GD.N0232.N0719.N0928.d009405
              (_root_.GD.N0232.N0719.N0853.d009567
                (by norm_num : 0 < 2) q)
              u.mean)
    _ = _ := rfl

theorem d016113
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i) :
    0 < _root_.GD.N0232.N0720.N1493.d016108 u := by
  rw [_root_.GD.N0232.N0720.N1493.d016111 u ht]
  exact mul_pos
    (_root_.GD.N0232.N0720.N1498.d012566 (by norm_num) (by norm_num) u)
    (_root_.GD.N0232.N0719.N0929.d009648 (by norm_num : 0 < 2) _root_.GD.N0232.N0720.N1493.d016089
      u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4)
      _root_.GD.N0232.N0720.N1493.d016090 ht _root_.GD.N0232.N0720.N1493.d016091)



theorem d016114
    (u : _root_.GD.N0232.N0719.N0900.d009096 2) (ht : ∀ i, 0 < u.meanVariance i) :
    _root_.GD.N0232.N0720.N1493.d016110 u =
      _root_.GD.N0232.N0719.N0929.d009653 (by norm_num : 0 < 2) _root_.GD.N0232.N0720.N1493.d016089
        u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) := by
  unfold _root_.GD.N0232.N0720.N1493.d016110
  rw [_root_.GD.N0232.N0720.N1493.d016112 u ht,
    _root_.GD.N0232.N0720.N1493.d016111 u ht]
  unfold _root_.GD.N0232.N0719.N0929.d009653
  have hobs : _root_.GD.N0232.N0720.N1498.d012564 2 2 u ≠ 0 :=
    (_root_.GD.N0232.N0720.N1498.d012566 (by norm_num) (by norm_num) u).ne'
  have houter : _root_.GD.N0232.N0719.N0929.d009647 (by norm_num : 0 < 2) _root_.GD.N0232.N0720.N1493.d016089
      u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) ≠ 0 :=
    (_root_.GD.N0232.N0719.N0929.d009648 (by norm_num : 0 < 2) _root_.GD.N0232.N0720.N1493.d016089
      u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4)
      _root_.GD.N0232.N0720.N1493.d016090 ht _root_.GD.N0232.N0720.N1493.d016091).ne'
  field_simp [hobs, houter]

end

end N1493
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1493.d016099
#print axioms _root_.GD.N0232.N0720.N1493.d016100
#print axioms _root_.GD.N0232.N0720.N1493.d016114
