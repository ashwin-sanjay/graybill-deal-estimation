import GD.Module0925
import GD.Module1235











open MeasureTheory ProbabilityTheory Set

namespace GD.N0232.N0720.N1404

open _root_.GD.N0232.N0720.N1091 _root_.GD.N0232.N0720.N1045
open _root_.GD.N0232.N0720.N1504
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1434 _root_.GD.N0232.N0720.N1398
open _root_.GD.N0232.N0720.N1399 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159

noncomputable section

def d020183 (r : ℝ) : ℝ := Real.sqrt r / (Real.sqrt r + Real.sqrt (1 - r))

theorem d020184 : Measurable _root_.GD.N0232.N0720.N1404.d020183 := by
  unfold _root_.GD.N0232.N0720.N1404.d020183
  fun_prop

theorem d020185 (r : ℝ) : _root_.GD.N0232.N0720.N1404.d020183 r ∈ Icc (0 : ℝ) 1 := by
  have hd : 0 < Real.sqrt r + Real.sqrt (1 - r) := by
    by_cases hr : 0 < r
    · exact add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 hr) (Real.sqrt_nonneg _)
    · have hother : 0 < 1 - r := by linarith
      exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (Real.sqrt_pos.2 hother)
  constructor
  · exact div_nonneg (Real.sqrt_nonneg _) hd.le
  · apply (div_le_one hd).2
    linarith [Real.sqrt_nonneg (1 - r)]

def d020186 (c r : ℝ) : ℝ := r / (r + c ^ 2 * (1 - r))


theorem d020187 {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (5 / 18 : ℝ) * (p ^ 2 / (p ^ 2 + q ^ 2)) +
      (5 / 18 : ℝ) * (p ^ 2 / (p ^ 2 + 4 * q ^ 2)) +
      (5 / 18 : ℝ) * (p ^ 2 / (4 * p ^ 2 + q ^ 2)) ≤ (p / (p + q)) ^ 2 := by
  have hs : p + q ≠ 0 := ne_of_gt (add_pos hp hq)
  have h1 : p ^ 2 + q ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have h2 : p ^ 2 + 4 * q ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have h3 : 4 * p ^ 2 + q ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have heq :
      (p / (p + q)) ^ 2 -
        ((5 / 18 : ℝ) * (p ^ 2 / (p ^ 2 + q ^ 2)) +
          (5 / 18 : ℝ) * (p ^ 2 / (p ^ 2 + 4 * q ^ 2)) +
          (5 / 18 : ℝ) * (p ^ 2 / (4 * p ^ 2 + q ^ 2))) =
      p ^ 2 * (p - q) ^ 2 *
        (3 * (p - q) ^ 4 + 8 * p * q * (p - q) ^ 2 + 9 * p ^ 2 * q ^ 2) /
        (2 * (p + q) ^ 2 * (p ^ 2 + q ^ 2) *
          (p ^ 2 + 4 * q ^ 2) * (4 * p ^ 2 + q ^ 2)) := by
    field_simp [hs, h1, h2, h3] <;> ring
  apply sub_nonneg.mp
  rw [heq]
  positivity

theorem d020188 {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    (5 / 18 : ℝ) * r + (5 / 18 : ℝ) * _root_.GD.N0232.N0720.N1404.d020186 2 r +
      (5 / 72 : ℝ) * _root_.GD.N0232.N0720.N1404.d020186 (1 / 2) r ≤ _root_.GD.N0232.N0720.N1404.d020183 r ^ 2 := by
  have hs := _root_.GD.N0232.N0720.N1404.d020187 (Real.sqrt_pos.2 hr.1)
    (Real.sqrt_pos.2 (sub_pos.mpr hr.2))
  rw [Real.sq_sqrt hr.1.le, Real.sq_sqrt (sub_nonneg.mpr hr.2.le)] at hs
  have h1 : r + (1 - r) ≠ 0 := by ring_nf; norm_num
  have h2 : r + 4 * (1 - r) ≠ 0 := ne_of_gt (by nlinarith [hr.1, hr.2])
  have h3 : 4 * r + (1 - r) ≠ 0 := ne_of_gt (by nlinarith [hr.1, hr.2])
  have h4 : r + (1 / 2 : ℝ) ^ 2 * (1 - r) ≠ 0 :=
    ne_of_gt (by nlinarith [hr.1, hr.2])
  unfold _root_.GD.N0232.N0720.N1404.d020183
  convert hs using 1
  unfold _root_.GD.N0232.N0720.N1404.d020186
  field_simp [h1, h2, h3, h4] <;> ring

theorem d020189 {k c u : ℝ}
    (hk : 0 < k) (hc : 0 < c) (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1404.d020186 c (_root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u) = _root_.GD.N0232.N0720.N1091.d012763 ((k / c) ^ 2) u := by
  have hD := ne_of_gt (_root_.GD.N0232.N0720.N1091.d012779 (sq_pos_of_pos hk) hu.1 hu.2)
  have hE := ne_of_gt (_root_.GD.N0232.N0720.N1091.d012779 (sq_pos_of_pos (div_pos hk hc)) hu.1 hu.2)
  have hR := _root_.GD.N0232.N0720.N1091.d012780 (sq_pos_of_pos hk) hu.1 hu.2
  have hRden : _root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u + c ^ 2 * (1 - _root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u) ≠ 0 :=
    ne_of_gt (add_pos hR.1 (mul_pos (sq_pos_of_pos hc) (sub_pos.mpr hR.2)))
  unfold _root_.GD.N0232.N0720.N1404.d020186
  apply (div_eq_div_iff hRden hE).2
  unfold _root_.GD.N0232.N0720.N1091.d012763
  field_simp [hD, hc.ne'] <;> ring

theorem d020190 : ∀ᵐ u ∂betaMeasure (1 / 2) (1 / 2), u ∈ Ioo (0 : ℝ) 1 := by
  unfold betaMeasure betaPDF
  rw [ae_withDensity_iff ((measurable_betaPDFReal (1 / 2) (1 / 2)).ennreal_ofReal)]
  filter_upwards with u
  intro hu
  by_contra hnot
  have hout : ¬ (0 < u ∧ u < 1) := hnot
  simp [betaPDFReal, hout] at hu

def d020191 (k : ℝ) : ℝ :=
  (5 / 18 : ℝ) * (k / (1 + k)) +
    (5 / 18 : ℝ) * ((k / 2) / (1 + k / 2)) +
    (5 / 72 : ℝ) * ((2 * k) / (1 + 2 * k))

theorem d020192 (k : ℝ) :
    Integrable (fun u ↦ _root_.GD.N0232.N0720.N1404.d020183 (_root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u))
      (betaMeasure (1 / 2) (1 / 2)) := by
  letI := isProbabilityMeasureBeta (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2)
  apply Integrable.mono' (integrable_const (1 : ℝ))
    ((_root_.GD.N0232.N0720.N1404.d020184.comp (_root_.GD.N0232.N0720.N1091.d012771 _)).aestronglyMeasurable)
  filter_upwards with u
  change ‖_root_.GD.N0232.N0720.N1404.d020183 (_root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0232.N0720.N1404.d020185 _).1]
  exact (_root_.GD.N0232.N0720.N1404.d020185 _).2

theorem d020193 (k : ℝ) :
    Integrable (fun u ↦ _root_.GD.N0232.N0720.N1404.d020183 (_root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u) ^ 2)
      (betaMeasure (1 / 2) (1 / 2)) := by
  letI := isProbabilityMeasureBeta (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2)
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (((_root_.GD.N0232.N0720.N1404.d020184.comp (_root_.GD.N0232.N0720.N1091.d012771 _)).pow_const 2).aestronglyMeasurable)
  filter_upwards with u
  change ‖_root_.GD.N0232.N0720.N1404.d020183 (_root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u) ^ 2‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply (sq_le_one_iff_abs_le_one _).2
  exact abs_le.mpr ⟨by linarith [(_root_.GD.N0232.N0720.N1404.d020185 (_root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u)).1],
    (_root_.GD.N0232.N0720.N1404.d020185 (_root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u)).2⟩


theorem d020194 {k : ℝ} (hk : 0 < k) :
    _root_.GD.N0232.N0720.N1404.d020191 k ≤ ∫ u, _root_.GD.N0232.N0720.N1404.d020183 (_root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u) ^ 2
      ∂betaMeasure (1 / 2) (1 / 2) := by
  have h1 := _root_.GD.N0232.N0720.N1045.d014456 hk
  have h2 := _root_.GD.N0232.N0720.N1045.d014456 (half_pos hk)
  have h3 := _root_.GD.N0232.N0720.N1045.d014456 (show 0 < 2 * k by positivity)
  have hlower :
      (∫ u, (5 / 18 : ℝ) * _root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u +
        (5 / 18 : ℝ) * _root_.GD.N0232.N0720.N1091.d012763 ((k / 2) ^ 2) u +
        (5 / 72 : ℝ) * _root_.GD.N0232.N0720.N1091.d012763 ((2 * k) ^ 2) u ∂betaMeasure (1 / 2) (1 / 2)) ≤
      ∫ u, _root_.GD.N0232.N0720.N1404.d020183 (_root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u) ^ 2 ∂betaMeasure (1 / 2) (1 / 2) := by
    apply integral_mono_ae (((h1.const_mul _).add (h2.const_mul _)).add (h3.const_mul _))
      (_root_.GD.N0232.N0720.N1404.d020193 k)
    filter_upwards [_root_.GD.N0232.N0720.N1404.d020190] with u hu
    change (5 / 18 : ℝ) * _root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u +
      (5 / 18 : ℝ) * _root_.GD.N0232.N0720.N1091.d012763 ((k / 2) ^ 2) u +
      (5 / 72 : ℝ) * _root_.GD.N0232.N0720.N1091.d012763 ((2 * k) ^ 2) u ≤
        _root_.GD.N0232.N0720.N1404.d020183 (_root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u) ^ 2
    have h := _root_.GD.N0232.N0720.N1404.d020188 (_root_.GD.N0232.N0720.N1091.d012780 (sq_pos_of_pos hk) hu.1 hu.2)
    rw [_root_.GD.N0232.N0720.N1404.d020189 hk (by norm_num : (0 : ℝ) < 2) hu,
      _root_.GD.N0232.N0720.N1404.d020189 hk (by norm_num : (0 : ℝ) < 1 / 2) hu] at h
    simpa only [show k / (1 / 2) = 2 * k by ring] using h
  rw [integral_add
      (f := fun u ↦ (5 / 18 : ℝ) * _root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u +
        (5 / 18 : ℝ) * _root_.GD.N0232.N0720.N1091.d012763 ((k / 2) ^ 2) u)
      (g := fun u ↦ (5 / 72 : ℝ) * _root_.GD.N0232.N0720.N1091.d012763 ((2 * k) ^ 2) u)
      ((h1.const_mul _).add (h2.const_mul _)) (h3.const_mul _),
    integral_add
      (f := fun u ↦ (5 / 18 : ℝ) * _root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u)
      (g := fun u ↦ (5 / 18 : ℝ) * _root_.GD.N0232.N0720.N1091.d012763 ((k / 2) ^ 2) u)
      (h1.const_mul _) (h2.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul,
    _root_.GD.N0232.N0720.N1045.d014454 hk,
    _root_.GD.N0232.N0720.N1045.d014454 (half_pos hk),
    _root_.GD.N0232.N0720.N1045.d014454 (show 0 < 2 * k by positivity)] at hlower
  exact hlower

theorem d020195 {k t : ℝ}
    (hk : 0 < k) (ht : 0 ≤ t) :
    _root_.GD.N0232.N0720.N1404.d020191 k - 2 * t ≤
      ∫ u, (_root_.GD.N0232.N0720.N1404.d020183 (_root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u) - t) ^ 2
        ∂betaMeasure (1 / 2) (1 / 2) := by
  letI := isProbabilityMeasureBeta (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2)
  have h1 := _root_.GD.N0232.N0720.N1404.d020192 k
  have h2 := _root_.GD.N0232.N0720.N1404.d020193 k
  have hpoint (u : ℝ) :
      (_root_.GD.N0232.N0720.N1404.d020183 (_root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u) - t) ^ 2 =
        _root_.GD.N0232.N0720.N1404.d020183 (_root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u) ^ 2 -
          (2 * t) * _root_.GD.N0232.N0720.N1404.d020183 (_root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u) + t ^ 2 := by ring
  have hmean : (∫ u, _root_.GD.N0232.N0720.N1404.d020183 (_root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u)
      ∂betaMeasure (1 / 2) (1 / 2)) ≤ 1 := by
    calc
      _ ≤ ∫ _u, (1 : ℝ) ∂betaMeasure (1 / 2) (1 / 2) :=
        integral_mono_ae h1 (integrable_const _) (ae_of_all _ fun u ↦ (_root_.GD.N0232.N0720.N1404.d020185 _).2)
      _ = 1 := by rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
  simp_rw [hpoint]
  rw [integral_add
      (f := fun u ↦ _root_.GD.N0232.N0720.N1404.d020183 (_root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u) ^ 2 -
        (2 * t) * _root_.GD.N0232.N0720.N1404.d020183 (_root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u))
      (g := fun _ ↦ t ^ 2)
      (h2.sub (h1.const_mul _)) (integrable_const _),
    integral_sub
      (f := fun u ↦ _root_.GD.N0232.N0720.N1404.d020183 (_root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u) ^ 2)
      (g := fun u ↦ (2 * t) * _root_.GD.N0232.N0720.N1404.d020183 (_root_.GD.N0232.N0720.N1091.d012763 (k ^ 2) u))
      h2 (h1.const_mul _), integral_const_mul]
  simp only [integral_const, smul_eq_mul, probReal_univ, one_mul]
  have hsecond := _root_.GD.N0232.N0720.N1404.d020194 hk
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hmean), sq_nonneg t]


theorem d020196 :
    _root_.GD.N0232.N0720.N1091.d012790 (1 / 2) (1 / 2) ((1 / 1000 : ℝ) ^ 2 / (1 + (1 / 1000 : ℝ) ^ 2)) <
      ∫ u, (_root_.GD.N0232.N0720.N1404.d020183 (_root_.GD.N0232.N0720.N1091.d012763 ((1 / 1000 : ℝ) ^ 2) u) -
        (1 / 1000 : ℝ) ^ 2 / (1 + (1 / 1000 : ℝ) ^ 2)) ^ 2
          ∂betaMeasure (1 / 2) (1 / 2) := by
  have hbound := _root_.GD.N0232.N0720.N1404.d020195
    (by norm_num : (0 : ℝ) < 1 / 1000)
    (by norm_num : (0 : ℝ) ≤ (1 / 1000 : ℝ) ^ 2 / (1 + (1 / 1000 : ℝ) ^ 2))
  apply lt_of_lt_of_le _ hbound
  rw [_root_.GD.N0232.N0720.N1045.d014459 (by norm_num : (0 : ℝ) < 1 / 1000)]
  norm_num [_root_.GD.N0232.N0720.N1404.d020191]



theorem d020197 (t : _root_.GD.N0232.N0720.N1441.d013676)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ x, f x.1 ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1) =
      ∫ u, f (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 (1 / 2) (1 / 2) t.1) u)
        ∂betaMeasure (1 / 2) (1 / 2) := by
  rw [← _root_.GD.N0232.N0720.N1425.d014723
    (m := 2) (n := 2) (by omega) (by omega) t.2.1 t.2.2
    (fun x : _root_.GD.N0232.N0720.N1436.d013217 ↦ f x.1) (hf.comp measurable_fst)]
  simp only [_root_.GD.N0232.N0720.N1436.d013207, _root_.GD.N0232.N0720.N1436.d013208, Nat.reduceSub, Nat.cast_one]
  rw [_root_.GD.N0232.N0720.N1091.d012797
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) f hf]
  have hpush := _root_.GD.N0232.N0720.N1504.d013979
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← hpush, integral_map
    (f := fun u : ℝ ↦ f (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 (1 / 2) (1 / 2) t.1) u))
    (_root_.GD.N0232.N0720.N1091.d012770 (1 / 2) (1 / 2)).aemeasurable
    ((hf.comp (_root_.GD.N0232.N0720.N1091.d012771 _)).aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1091.d012782
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    t.2.1 t.2.2] with q hq
  rw [hq]

def d020198 : _root_.GD.N0232.N0720.N1441.d013676 :=
  ⟨(1 / 1000 : ℝ) ^ 2 / (1 + (1 / 1000 : ℝ) ^ 2), by constructor <;> norm_num⟩



theorem d020199 :
    _root_.GD.N0232.N0720.N1398.d019610 _root_.GD.N0232.N0720.N1424.d014839 _root_.GD.N0232.N0720.N1404.d020198.1 <
      _root_.GD.N0232.N0720.N1398.d019610 (fun x : _root_.GD.N0232.N0720.N1436.d013217 ↦ _root_.GD.N0232.N0720.N1404.d020183 x.1) _root_.GD.N0232.N0720.N1404.d020198.1 := by
  rw [_root_.GD.N0232.N0720.N1399.d020093]
  unfold _root_.GD.N0232.N0720.N1398.d019610
  rw [_root_.GD.N0232.N0720.N1404.d020197 _root_.GD.N0232.N0720.N1404.d020198
    (fun r ↦ (_root_.GD.N0232.N0720.N1404.d020183 r - _root_.GD.N0232.N0720.N1404.d020198.1) ^ 2)
    ((_root_.GD.N0232.N0720.N1404.d020184.sub measurable_const).pow_const 2)]
  have hodds : _root_.GD.N0232.N0720.N1091.d012762 (1 / 2) (1 / 2) _root_.GD.N0232.N0720.N1404.d020198.1 =
      (1 / 1000 : ℝ) ^ 2 := by norm_num [_root_.GD.N0232.N0720.N1091.d012762, _root_.GD.N0232.N0720.N1404.d020198]
  rw [hodds]
  exact _root_.GD.N0232.N0720.N1404.d020196



theorem d020200 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) :
    ¬ (∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2, _root_.GD.N0232.N0720.N1398.d019601 d x = _root_.GD.N0232.N0720.N1404.d020183 x.1) := by
  intro heq
  have heqt : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 _root_.GD.N0232.N0720.N1404.d020198.1,
      _root_.GD.N0232.N0720.N1398.d019601 d x = _root_.GD.N0232.N0720.N1404.d020183 x.1 :=
    (_root_.GD.N0232.N0720.N1441.d013682 (by omega : 2 ≤ 2)
      (by omega : 2 ≤ 2) _root_.GD.N0232.N0720.N1404.d020198).ae_le heq
  have hloss : _root_.GD.N0232.N0720.N1398.d019610 (_root_.GD.N0232.N0720.N1398.d019601 d) _root_.GD.N0232.N0720.N1404.d020198.1 =
      _root_.GD.N0232.N0720.N1398.d019610 (fun x : _root_.GD.N0232.N0720.N1436.d013217 ↦ _root_.GD.N0232.N0720.N1404.d020183 x.1) _root_.GD.N0232.N0720.N1404.d020198.1 := by
    apply integral_congr_ae
    filter_upwards [heqt] with x hx
    rw [hx]
  have hcap := _root_.GD.N0232.N0720.N1398.d019617 hd _root_.GD.N0232.N0720.N1404.d020198
  rw [hloss] at hcap
  exact (lt_asymm hcap _root_.GD.N0232.N0720.N1404.d020199)

end
end GD.N0232.N0720.N1404

#print axioms _root_.GD.N0232.N0720.N1404.d020187
#print axioms _root_.GD.N0232.N0720.N1404.d020196
#print axioms _root_.GD.N0232.N0720.N1404.d020199
#print axioms _root_.GD.N0232.N0720.N1404.d020200
