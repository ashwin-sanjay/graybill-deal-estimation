import GD.Module1013
import GD.Module0817



























open MeasureTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1492

noncomputable section

open _root_.GD.N0232.N0719.N0928
open _root_.GD.N0232.N0719.N0929
open _root_.GD.N0232.N0719.N0954
open _root_.GD.N0232.N0719.N0955
open _root_.GD.N0232.N0719.N0857
open _root_.GD.N0232.N0719.N0853
open _root_.GD.N0232.N0720.N1034
open _root_.GD.N0232.N0720.N1209
open _root_.GD.N0232.N0720.N1493
open _root_.GD.N0232.N0720.N1495

attribute [local instance] Measure.Subtype.measureSpace

private abbrev d016121 : Fin 2 → ℝ :=
  _root_.GD.N0232.N0719.N0954.d009355 (_root_.GD.N0232.N0720.N1034.d012430 2 2)

private abbrev d016122 :=
  {q : _root_.GD.N0232.N0719.N0857.d009377 2 // q ∈ _root_.GD.N0232.N0719.N0955.d009607 2}





def d016123 (r s p : ℝ) : ℝ :=
  r * (1 - p) + (1 - r) * p + s * p * (1 - p)



def d016124
    (r s : ℝ) (p : Set.Ioo (0 : ℝ) 1) : ℝ :=
  (p : ℝ) * (1 - (p : ℝ)) *
    _root_.GD.N0232.N0720.N1492.d016123 r s p ^ (-3 : ℝ)



def d016125 (r s : ℝ) : ℝ :=
  ∫ p : Set.Ioo (0 : ℝ) 1, _root_.GD.N0232.N0720.N1492.d016124 r s p


def d016126 (r s : ℝ) : ℝ :=
  ∫ p : Set.Ioo (0 : ℝ) 1,
    (p : ℝ) * _root_.GD.N0232.N0720.N1492.d016124 r s p



def d016127 (r s : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1492.d016126 r s / _root_.GD.N0232.N0720.N1492.d016125 r s




def d016128 (s : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi) * Real.Gamma 3 /
    (2 * s) ^ (-3 : ℝ)

theorem d016129
    {r s : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hs : 0 < s)
    (p : Set.Ioo (0 : ℝ) 1) :
    0 < _root_.GD.N0232.N0720.N1492.d016123 r s p := by
  unfold _root_.GD.N0232.N0720.N1492.d016123
  have hp0 : 0 < (p : ℝ) := p.property.1
  have hp1 : (p : ℝ) < 1 := p.property.2
  have hrComp : 0 < 1 - r := sub_pos.mpr hr.2
  have hpComp : 0 < 1 - (p : ℝ) := sub_pos.mpr hp1
  exact add_pos
    (add_pos (mul_pos hr.1 hpComp) (mul_pos hrComp hp0))
    (mul_pos (mul_pos hs hp0) hpComp)

theorem d016130 (r s : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1492.d016124 r s) := by
  unfold _root_.GD.N0232.N0720.N1492.d016124 _root_.GD.N0232.N0720.N1492.d016123
  fun_prop

theorem d016131 (r s : ℝ) :
    Measurable
      (fun p : Set.Ioo (0 : ℝ) 1 ↦
        (p : ℝ) * _root_.GD.N0232.N0720.N1492.d016124 r s p) := by
  exact measurable_subtype_coe.mul (_root_.GD.N0232.N0720.N1492.d016130 r s)



@[simp] private theorem d016132 (i : Fin 2) :
    _root_.GD.N0232.N0720.N1492.d016121 i = 1 / 2 := by
  fin_cases i <;>
    norm_num [_root_.GD.N0232.N0720.N1492.d016121, _root_.GD.N0232.N0719.N0954.d009355, _root_.GD.N0232.N0720.N1034.d012430]

@[simp] theorem d016133 :
    _root_.GD.N0232.N0719.N0928.d009415 _root_.GD.N0232.N0720.N1492.d016121 (_root_.GD.N0232.N0720.N1034.d012428 4) = 3 := by
  unfold _root_.GD.N0232.N0719.N0928.d009415 _root_.GD.N0232.N0719.N0928.d009408 _root_.GD.N0232.N0720.N1034.d012428
  rw [Fin.sum_univ_two]
  simp [_root_.GD.N0232.N0720.N1492.d016132]
  norm_num

@[simp] theorem d016134
    (r s : ℝ) (p : Set.Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0720.N1034.d012417 (p : ℝ))
        (_root_.GD.N0232.N0720.N1209.d012463 r s 1).mean =
      (p : ℝ) := by
  unfold _root_.GD.N0232.N0719.N0928.d009405 _root_.GD.N0232.N0720.N1034.d012417 _root_.GD.N0232.N0720.N1209.d012463
    _root_.GD.N0232.N0720.N1209.d012458
  rw [Fin.sum_univ_two]
  simp

theorem d016135
    {r s : ℝ} (hs : s ≠ 0)
    (p : Set.Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0720.N1492.d016121
        (_root_.GD.N0232.N0720.N1034.d012417 (p : ℝ))
        (_root_.GD.N0232.N0720.N1209.d012463 r s 1).mean
        (_root_.GD.N0232.N0720.N1209.d012463 r s 1).meanVariance =
      _root_.GD.N0232.N0720.N1492.d016123 r s p / (2 * s) := by
  unfold _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0719.N0928.d009406 _root_.GD.N0232.N0719.N0928.d009405
    _root_.GD.N0232.N0720.N1034.d012417 _root_.GD.N0232.N0720.N1209.d012463 _root_.GD.N0232.N0720.N1209.d012458
    _root_.GD.N0232.N0720.N1492.d016123
  simp only [Fin.sum_univ_two, _root_.GD.N0232.N0720.N1492.d016132, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  field_simp [hs]
  ring

@[simp] theorem d016136
    (p : Set.Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0719.N0928.d009409 _root_.GD.N0232.N0720.N1492.d016121
        (_root_.GD.N0232.N0720.N1034.d012417 (p : ℝ)) =
      (p : ℝ) * (1 - (p : ℝ)) := by
  unfold _root_.GD.N0232.N0719.N0928.d009409 _root_.GD.N0232.N0720.N1034.d012417
  rw [Fin.prod_univ_two]
  have hhalf : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1 := by norm_num
  simp [_root_.GD.N0232.N0720.N1492.d016132, hhalf]

theorem d016137
    {s : ℝ} (hs : 0 < s) :
    0 < _root_.GD.N0232.N0720.N1492.d016128 s := by
  unfold _root_.GD.N0232.N0720.N1492.d016128
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by
    exact Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)
  have hgamma : 0 < Real.Gamma (3 : ℝ) :=
    Real.Gamma_pos_of_pos (by norm_num)
  exact div_pos (mul_pos hsqrt hgamma)
    (Real.rpow_pos_of_pos (mul_pos (by norm_num) hs) _)



theorem d016138
    {r s : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hs : 0 < s)
    (p : Set.Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1492.d016121
        (_root_.GD.N0232.N0720.N1034.d012417 (p : ℝ))
        (_root_.GD.N0232.N0720.N1209.d012463 r s 1).mean
        (_root_.GD.N0232.N0720.N1209.d012463 r s 1).meanVariance
        (_root_.GD.N0232.N0720.N1034.d012428 4) =
      _root_.GD.N0232.N0720.N1492.d016128 s *
        _root_.GD.N0232.N0720.N1492.d016124 r s p := by
  have hQ : 0 < _root_.GD.N0232.N0720.N1492.d016123 r s p :=
    _root_.GD.N0232.N0720.N1492.d016129 hr hs p
  have h2s : 0 < 2 * s := mul_pos (by norm_num) hs
  unfold _root_.GD.N0232.N0719.N0928.d009437
  rw [_root_.GD.N0232.N0720.N1492.d016136,
    _root_.GD.N0232.N0720.N1492.d016135 hs.ne',
    _root_.GD.N0232.N0720.N1492.d016133,
    Real.div_rpow hQ.le h2s.le]
  unfold _root_.GD.N0232.N0720.N1492.d016128 _root_.GD.N0232.N0720.N1492.d016124
  ring





private theorem d016139
    (q : _root_.GD.N0232.N0720.N1492.d016122) :
    _root_.GD.N0232.N0720.N1034.d012417 (_root_.GD.N0232.N0720.N1493.d016102 q : ℝ) =
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
    have hz : (_root_.GD.N0232.N0720.N1493.d016102 q : ℝ) =
        _root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q.1 (0 : Fin 2) := rfl
    rw [hz]
    exact hlast.symm



private theorem d016140
    (f : Set.Ioo (0 : ℝ) 1 → ℝ) (hf : Measurable f) :
    (∫ q : _root_.GD.N0232.N0720.N1492.d016122, f (_root_.GD.N0232.N0720.N1493.d016102 q)) =
      ∫ p : Set.Ioo (0 : ℝ) 1, f p := by
  calc
    (∫ q : _root_.GD.N0232.N0720.N1492.d016122, f (_root_.GD.N0232.N0720.N1493.d016102 q)) =
        ∫ p : Set.Ioo (0 : ℝ) 1, f p
          ∂_root_.GD.N0232.N0720.N1493.d016104 := by
      symm
      have hmap := integral_map
        (μ := (volume : Measure _root_.GD.N0232.N0720.N1492.d016122))
        _root_.GD.N0232.N0720.N1493.d016103.measurable.aemeasurable
        hf.aestronglyMeasurable
      simpa [_root_.GD.N0232.N0720.N1493.d016104] using hmap
    _ = ∫ p : Set.Ioo (0 : ℝ) 1, f p := by
      rw [_root_.GD.N0232.N0720.N1495.d016120]



theorem d016141
    {r s : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hs : 0 < s) :
    _root_.GD.N0232.N0719.N0929.d009647 (by norm_num : 0 < 2) _root_.GD.N0232.N0720.N1492.d016121
        (_root_.GD.N0232.N0720.N1209.d012463 r s 1).mean
        (_root_.GD.N0232.N0720.N1209.d012463 r s 1).meanVariance
        (_root_.GD.N0232.N0720.N1034.d012428 4) =
      _root_.GD.N0232.N0720.N1492.d016128 s *
        _root_.GD.N0232.N0720.N1492.d016125 r s := by
  unfold _root_.GD.N0232.N0719.N0929.d009647
  calc
    (∫ q in _root_.GD.N0232.N0719.N0955.d009607 2,
        _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1492.d016121
          (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q)
          (_root_.GD.N0232.N0720.N1209.d012463 r s 1).mean
          (_root_.GD.N0232.N0720.N1209.d012463 r s 1).meanVariance
          (_root_.GD.N0232.N0720.N1034.d012428 4)) =
        ∫ q : _root_.GD.N0232.N0720.N1492.d016122,
          _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1492.d016121
            (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q.1)
            (_root_.GD.N0232.N0720.N1209.d012463 r s 1).mean
            (_root_.GD.N0232.N0720.N1209.d012463 r s 1).meanVariance
            (_root_.GD.N0232.N0720.N1034.d012428 4) := by
      symm
      exact integral_subtype
        (_root_.GD.N0232.N0719.N0955.d009608 2)
        (fun q ↦ _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1492.d016121
          (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q)
          (_root_.GD.N0232.N0720.N1209.d012463 r s 1).mean
          (_root_.GD.N0232.N0720.N1209.d012463 r s 1).meanVariance
          (_root_.GD.N0232.N0720.N1034.d012428 4))
    _ = ∫ q : _root_.GD.N0232.N0720.N1492.d016122,
          _root_.GD.N0232.N0720.N1492.d016128 s *
            _root_.GD.N0232.N0720.N1492.d016124 r s (_root_.GD.N0232.N0720.N1493.d016102 q) := by
      apply integral_congr_ae
      filter_upwards with q
      rw [← _root_.GD.N0232.N0720.N1492.d016139]
      exact _root_.GD.N0232.N0720.N1492.d016138 hr hs
        (_root_.GD.N0232.N0720.N1493.d016102 q)
    _ = _root_.GD.N0232.N0720.N1492.d016128 s *
        ∫ q : _root_.GD.N0232.N0720.N1492.d016122,
          _root_.GD.N0232.N0720.N1492.d016124 r s (_root_.GD.N0232.N0720.N1493.d016102 q) := by
      rw [integral_const_mul]
    _ = _root_.GD.N0232.N0720.N1492.d016128 s *
        _root_.GD.N0232.N0720.N1492.d016125 r s := by
      rw [_root_.GD.N0232.N0720.N1492.d016140
        (_root_.GD.N0232.N0720.N1492.d016124 r s)
        (_root_.GD.N0232.N0720.N1492.d016130 r s)]
      rfl

theorem d016142
    {r s : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hs : 0 < s) :
    _root_.GD.N0232.N0719.N0929.d009652 (by norm_num : 0 < 2) _root_.GD.N0232.N0720.N1492.d016121
        (_root_.GD.N0232.N0720.N1209.d012463 r s 1).mean
        (_root_.GD.N0232.N0720.N1209.d012463 r s 1).meanVariance
        (_root_.GD.N0232.N0720.N1034.d012428 4) =
      _root_.GD.N0232.N0720.N1492.d016128 s *
        _root_.GD.N0232.N0720.N1492.d016126 r s := by
  unfold _root_.GD.N0232.N0719.N0929.d009652
  calc
    (∫ q in _root_.GD.N0232.N0719.N0955.d009607 2,
        _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1492.d016121
            (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q)
            (_root_.GD.N0232.N0720.N1209.d012463 r s 1).mean
            (_root_.GD.N0232.N0720.N1209.d012463 r s 1).meanVariance
            (_root_.GD.N0232.N0720.N1034.d012428 4) *
          _root_.GD.N0232.N0719.N0928.d009405
            (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q)
            (_root_.GD.N0232.N0720.N1209.d012463 r s 1).mean) =
        ∫ q : _root_.GD.N0232.N0720.N1492.d016122,
          _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1492.d016121
              (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q.1)
              (_root_.GD.N0232.N0720.N1209.d012463 r s 1).mean
              (_root_.GD.N0232.N0720.N1209.d012463 r s 1).meanVariance
              (_root_.GD.N0232.N0720.N1034.d012428 4) *
            _root_.GD.N0232.N0719.N0928.d009405
              (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q.1)
              (_root_.GD.N0232.N0720.N1209.d012463 r s 1).mean := by
      symm
      exact integral_subtype
        (_root_.GD.N0232.N0719.N0955.d009608 2)
        (fun q ↦ _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0720.N1492.d016121
              (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q)
              (_root_.GD.N0232.N0720.N1209.d012463 r s 1).mean
              (_root_.GD.N0232.N0720.N1209.d012463 r s 1).meanVariance
              (_root_.GD.N0232.N0720.N1034.d012428 4) *
            _root_.GD.N0232.N0719.N0928.d009405
              (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num : 0 < 2) q)
              (_root_.GD.N0232.N0720.N1209.d012463 r s 1).mean)
    _ = ∫ q : _root_.GD.N0232.N0720.N1492.d016122,
          _root_.GD.N0232.N0720.N1492.d016128 s *
            ((_root_.GD.N0232.N0720.N1493.d016102 q : ℝ) *
              _root_.GD.N0232.N0720.N1492.d016124 r s (_root_.GD.N0232.N0720.N1493.d016102 q)) := by
      apply integral_congr_ae
      filter_upwards with q
      rw [← _root_.GD.N0232.N0720.N1492.d016139,
        _root_.GD.N0232.N0720.N1492.d016138 hr hs,
        _root_.GD.N0232.N0720.N1492.d016134]
      ring
    _ = _root_.GD.N0232.N0720.N1492.d016128 s *
        ∫ q : _root_.GD.N0232.N0720.N1492.d016122,
          (_root_.GD.N0232.N0720.N1493.d016102 q : ℝ) *
            _root_.GD.N0232.N0720.N1492.d016124 r s (_root_.GD.N0232.N0720.N1493.d016102 q) := by
      rw [integral_const_mul]
    _ = _root_.GD.N0232.N0720.N1492.d016128 s *
        _root_.GD.N0232.N0720.N1492.d016126 r s := by
      rw [_root_.GD.N0232.N0720.N1492.d016140
        (fun p : Set.Ioo (0 : ℝ) 1 ↦
          (p : ℝ) * _root_.GD.N0232.N0720.N1492.d016124 r s p)
        (_root_.GD.N0232.N0720.N1492.d016131 r s)]
      rfl


theorem d016143
    {r s : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hs : 0 < s) :
    _root_.GD.N0232.N0719.N0929.d009653 (by norm_num : 0 < 2) _root_.GD.N0232.N0720.N1492.d016121
        (_root_.GD.N0232.N0720.N1209.d012463 r s 1).mean
        (_root_.GD.N0232.N0720.N1209.d012463 r s 1).meanVariance
        (_root_.GD.N0232.N0720.N1034.d012428 4) =
      _root_.GD.N0232.N0720.N1492.d016127 r s := by
  unfold _root_.GD.N0232.N0719.N0929.d009653 _root_.GD.N0232.N0720.N1492.d016127
  rw [_root_.GD.N0232.N0720.N1492.d016142 hr hs,
    _root_.GD.N0232.N0720.N1492.d016141 hr hs]
  exact mul_div_mul_left _ _
    (_root_.GD.N0232.N0720.N1492.d016137 hs).ne'



theorem d016144
    {r s : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hs : 0 < s) :
    _root_.GD.N0232.N0720.N1493.d016110 (_root_.GD.N0232.N0720.N1209.d012463 r s 1) =
      _root_.GD.N0232.N0720.N1492.d016127 r s := by
  let u := _root_.GD.N0232.N0720.N1209.d012463 r s 1
  have ht : ∀ i, 0 < u.meanVariance i := by
    intro i
    fin_cases i
    · change 0 < (1 - r) / s
      exact div_pos (sub_pos.mpr hr.2) hs
    · change 0 < r / s
      exact div_pos hr.1 hs
  calc
    _root_.GD.N0232.N0720.N1493.d016110 u =
        _root_.GD.N0232.N0719.N0929.d009653 (by norm_num : 0 < 2) _root_.GD.N0232.N0720.N1492.d016121
          u.mean u.meanVariance (_root_.GD.N0232.N0720.N1034.d012428 4) := by
      simpa [_root_.GD.N0232.N0720.N1492.d016121] using
        (_root_.GD.N0232.N0720.N1493.d016114 u ht)
    _ = _root_.GD.N0232.N0720.N1492.d016127 r s := by
      exact _root_.GD.N0232.N0720.N1492.d016143
        hr hs

end

end N1492
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1492.d016138
#print axioms _root_.GD.N0232.N0720.N1492.d016143
#print axioms _root_.GD.N0232.N0720.N1492.d016144
