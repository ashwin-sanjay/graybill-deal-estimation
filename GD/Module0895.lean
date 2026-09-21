import GD.Module0877
import GD.Module0868






















open MeasureTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1487

noncomputable section

open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1435
open _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1430


def d013902 (z r S : ℝ) : ℝ :=
  (1 - z) * (S + r) + z * (1 - r)


noncomputable def d013903 (z r S : ℝ) : ℝ :=
  (3 / (2 * Real.pi)) * (1 - z) ^ 2 *
    r ^ (-(1 / 2 : ℝ)) * (1 - r) ^ (-(1 / 2 : ℝ)) *
    S ^ (1 / 2 : ℝ) *
    _root_.GD.N0232.N0720.N1487.d013902 z r S ^ (-(5 / 2 : ℝ))


noncomputable def d013904 (r S : ℝ) : ℝ :=
  (3 / (2 * Real.pi)) *
    r ^ (-(1 / 2 : ℝ)) * (1 - r) ^ (-(1 / 2 : ℝ)) *
    S ^ (1 / 2 : ℝ) * (S + r) ^ (-(5 / 2 : ℝ))

private theorem d013905 (p : ℝ) :
    Measurable (fun x : ℝ ↦ x ^ p) := by
  apply measurable_of_continuousOn_compl_singleton 0
  exact continuousOn_id.rpow_const fun x hx ↦ Or.inl hx

@[fun_prop]
theorem d013906 (z : ℝ) :
    Measurable (fun x : ℝ × ℝ ↦
      _root_.GD.N0232.N0720.N1487.d013902 z x.1 x.2) := by
  unfold _root_.GD.N0232.N0720.N1487.d013902
  fun_prop

@[fun_prop]
theorem d013907 (z : ℝ) :
    Measurable (fun x : ℝ × ℝ ↦
      _root_.GD.N0232.N0720.N1487.d013903 z x.1 x.2) := by
  unfold _root_.GD.N0232.N0720.N1487.d013903
  exact (((((measurable_const.mul measurable_const).mul
      ((_root_.GD.N0232.N0720.N1487.d013905 (-(1 / 2 : ℝ))).comp
        measurable_fst)).mul
      ((_root_.GD.N0232.N0720.N1487.d013905 (-(1 / 2 : ℝ))).comp
        (measurable_const.sub measurable_fst))).mul
      ((_root_.GD.N0232.N0720.N1487.d013905 (1 / 2 : ℝ)).comp measurable_snd)).mul
      ((_root_.GD.N0232.N0720.N1487.d013905 (-(5 / 2 : ℝ))).comp
        (_root_.GD.N0232.N0720.N1487.d013906 z)))

@[fun_prop]
theorem d013908 :
    Measurable (fun x : ℝ × ℝ ↦
      _root_.GD.N0232.N0720.N1487.d013904 x.1 x.2) := by
  unfold _root_.GD.N0232.N0720.N1487.d013904
  exact ((((measurable_const.mul
      ((_root_.GD.N0232.N0720.N1487.d013905 (-(1 / 2 : ℝ))).comp
        measurable_fst)).mul
      ((_root_.GD.N0232.N0720.N1487.d013905 (-(1 / 2 : ℝ))).comp
        (measurable_const.sub measurable_fst))).mul
      ((_root_.GD.N0232.N0720.N1487.d013905 (1 / 2 : ℝ)).comp measurable_snd)).mul
      ((_root_.GD.N0232.N0720.N1487.d013905 (-(5 / 2 : ℝ))).comp
        (measurable_snd.add measurable_fst)))

theorem d013909
    {z r S : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) (hS : 0 < S) :
    0 < _root_.GD.N0232.N0720.N1487.d013902 z r S := by
  unfold _root_.GD.N0232.N0720.N1487.d013902
  exact add_pos
    (mul_pos (sub_pos.mpr hz1) (add_pos hS hr.1))
    (mul_pos hz0 (sub_pos.mpr hr.2))

theorem d013910
    {z r S : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) (hS : 0 < S) :
    0 < _root_.GD.N0232.N0720.N1487.d013903 z r S := by
  have hpi : 0 < 3 / (2 * Real.pi) := by positivity
  have hLambda := _root_.GD.N0232.N0720.N1487.d013909 hz0 hz1 hr hS
  have hwall : 0 < (1 - z) ^ 2 :=
    sq_pos_of_pos (sub_pos.mpr hz1)
  have hrpow : 0 < r ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos hr.1 _
  have hOneSubRpow : 0 < (1 - r) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (sub_pos.mpr hr.2) _
  have hSpow : 0 < S ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hS _
  have hLambdaPow :
      0 < _root_.GD.N0232.N0720.N1487.d013902 z r S ^ (-(5 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos hLambda _
  unfold _root_.GD.N0232.N0720.N1487.d013903
  exact mul_pos
    (mul_pos (mul_pos (mul_pos (mul_pos hpi hwall) hrpow) hOneSubRpow) hSpow)
    hLambdaPow

theorem d013911
    {r S : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (hS : 0 < S) :
    0 < _root_.GD.N0232.N0720.N1487.d013904 r S := by
  have hpi : 0 < 3 / (2 * Real.pi) := by positivity
  have hrpow : 0 < r ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos hr.1 _
  have hOneSubRpow : 0 < (1 - r) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (sub_pos.mpr hr.2) _
  have hSpow : 0 < S ^ (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hS _
  have hSumPow : 0 < (S + r) ^ (-(5 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (add_pos hS hr.1) _
  unfold _root_.GD.N0232.N0720.N1487.d013904
  exact mul_pos
    (mul_pos (mul_pos (mul_pos hpi hrpow) hOneSubRpow) hSpow)
    hSumPow



private theorem d013912 :
    Real.Gamma ((5 : ℝ) / 2) = 3 * Real.sqrt Real.pi / 4 := by
  have h := Real.Gamma_add_one (by norm_num : (3 / 2 : ℝ) ≠ 0)
  rw [_root_.GD.N0125.d008861] at h
  convert h using 1 <;> ring_nf

private theorem d013913 :
    (1 / 2 : ℝ) ^ (1 / 2 : ℝ) = 1 / Real.sqrt 2 := by
  rw [← Real.sqrt_eq_rpow, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
  simp

private theorem d013914 :
    (2 : ℝ) ^ (3 / 2 : ℝ) = 2 * Real.sqrt 2 := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
    ← Real.sqrt_eq_rpow]

private theorem d013915 :
    (2 : ℝ) ^ (5 / 2 : ℝ) = 4 * Real.sqrt 2 := by
  rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_two,
    ← Real.sqrt_eq_rpow]
  norm_num



theorem d013916 :
    _root_.GD.N0116.d006507 (1 / 2) (1 / 2) *
        (2 : ℝ) ^ (5 / 2 : ℝ) =
      3 / (2 * Real.pi) := by
  have hsqrtTwo : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hsqrtPi : Real.sqrt Real.pi ≠ 0 := by positivity
  have hsqrtTwoSq : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtPiSq : Real.sqrt Real.pi ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_pos.le
  unfold _root_.GD.N0116.d006507
    _root_.GD.N0116.d006506
  rw [show (1 / 2 : ℝ) + 1 / 2 + 3 / 2 = 5 / 2 by norm_num]
  rw [Real.Gamma_one_half_eq, _root_.GD.N0125.d008861,
    _root_.GD.N0232.N0720.N1487.d013912, _root_.GD.N0232.N0720.N1487.d013913, _root_.GD.N0232.N0720.N1487.d013914,
    _root_.GD.N0232.N0720.N1487.d013915]
  field_simp [hsqrtTwo, hsqrtPi, Real.pi_ne_zero]
  nlinarith



private theorem d013917
    {z r S : ℝ} (hz : z ≠ 0) :
    (1 / 2 : ℝ) * z * (1 - r) +
        (1 / 2 : ℝ) * (1 - z) * r +
        (S / z) * z * (1 - z) / 2 =
      _root_.GD.N0232.N0720.N1487.d013902 z r S / 2 := by
  unfold _root_.GD.N0232.N0720.N1487.d013902
  field_simp [hz]
  ring

private theorem d013918
    {z r S : ℝ} (hLambda : 0 < _root_.GD.N0232.N0720.N1487.d013902 z r S) :
    (_root_.GD.N0232.N0720.N1487.d013902 z r S / 2) ^ (-(5 / 2 : ℝ)) =
      (2 : ℝ) ^ (5 / 2 : ℝ) *
        _root_.GD.N0232.N0720.N1487.d013902 z r S ^ (-(5 / 2 : ℝ)) := by
  rw [Real.div_rpow hLambda.le (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show (-(5 / 2 : ℝ)) = -(5 / 2 : ℝ) by ring,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have hpow : (2 : ℝ) ^ (5 / 2 : ℝ) ≠ 0 := by positivity
  field_simp [hpow]




theorem d013919
    {z r S : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) (hS : 0 < S) :
    z ^ (-(1 / 2 : ℝ)) * (1 / z) *
        _root_.GD.N0232.N0720.N1436.d013273 2 2 z (r, S / z) =
      _root_.GD.N0232.N0720.N1487.d013903 z r S := by
  have hx : (r, S / z) ∈ _root_.GD.N0232.N0720.N1436.d013218 :=
    ⟨hr, div_pos hS hz0⟩
  rw [_root_.GD.N0232.N0720.N1435.d013489
    (by norm_num) (by norm_num) hz0 hz1 hx]
  have hLambda := _root_.GD.N0232.N0720.N1487.d013909 hz0 hz1 hr hS
  have hden := _root_.GD.N0232.N0720.N1487.d013917 (r := r) (S := S) hz0.ne'
  have hSdiv :
      (S / z) ^ (1 / 2 : ℝ) =
        S ^ (1 / 2 : ℝ) / z ^ (1 / 2 : ℝ) := by
    exact Real.div_rpow hS.le hz0.le (1 / 2 : ℝ)
  have hzHalf : z ^ (1 / 2 : ℝ) ≠ 0 := by positivity
  have hzHalfSq : (z ^ (1 / 2 : ℝ)) ^ 2 = z := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hz0.le]
  unfold _root_.GD.N0116.d006511
    _root_.GD.N0116.d006508 _root_.GD.N0116.d006509
    _root_.GD.N0232.N0720.N1436.d013207 _root_.GD.N0232.N0720.N1436.d013208
  norm_num only
  rw [hden, _root_.GD.N0232.N0720.N1487.d013918 hLambda, hSdiv,
    Real.rpow_neg hz0.le, Real.rpow_two]
  unfold _root_.GD.N0232.N0720.N1487.d013903
  rw [← _root_.GD.N0232.N0720.N1487.d013916]
  field_simp [hz0.ne', hzHalf, hzHalfSq]
  rw [hzHalfSq]
  simp only [Real.rpow_two]




theorem d013920
    {z C : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (phi : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hphi : Measurable phi)
    (hC : ∀ x, |phi x| ≤ C) :
    (∫ x in _root_.GD.N0232.N0720.N1436.d013218,
        phi x * _root_.GD.N0232.N0720.N1436.d013273 2 2 z x) =
      Real.sqrt z *
        ∫ r in Ioo (0 : ℝ) 1,
          ∫ S in Ioi (0 : ℝ),
            phi (r, S / z) * _root_.GD.N0232.N0720.N1487.d013903 z r S := by
  have hInv := _root_.GD.N0232.N0720.N1434.d013556
    (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2)
    hz0 hz1 phi hphi hC
  have hPDF : IntegrableOn
      (fun x ↦ phi x * _root_.GD.N0232.N0720.N1436.d013273 2 2 z x)
      _root_.GD.N0232.N0720.N1436.d013218 volume := by
    refine hInv.congr (ae_restrict_mem _root_.GD.N0232.N0720.N1436.d013219 |>.mono
      fun x hx ↦ ?_)
    change phi x * _root_.GD.N0116.d006511
      (1 / 2) (1 / 2) z x =
        phi x * _root_.GD.N0232.N0720.N1436.d013273 2 2 z x
    rw [_root_.GD.N0232.N0720.N1435.d013489
      (by norm_num) (by norm_num) hz0 hz1 hx]
    norm_num [_root_.GD.N0232.N0720.N1436.d013207, _root_.GD.N0232.N0720.N1436.d013208]
  rw [show _root_.GD.N0232.N0720.N1436.d013218 = Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ) by rfl]
    at hPDF ⊢
  rw [Measure.volume_eq_prod] at hPDF ⊢
  rw [setIntegral_prod _ hPDF]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  let g : ℝ → ℝ := fun F ↦
    phi (r, F) * _root_.GD.N0232.N0720.N1436.d013273 2 2 z (r, F)
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi
    (g := g) 0 (one_div_pos.mpr hz0)
  simp only [mul_zero, smul_eq_mul] at hscale
  have hsqrt : Real.sqrt z ≠ 0 := (Real.sqrt_pos.2 hz0).ne'
  have hzHalf : z ^ (1 / 2 : ℝ) = Real.sqrt z := by
    exact (Real.sqrt_eq_rpow z).symm
  calc
    (∫ F in Ioi (0 : ℝ),
        phi (r, F) * _root_.GD.N0232.N0720.N1436.d013273 2 2 z (r, F)) =
        (1 / z) *
          ∫ S in Ioi (0 : ℝ),
            phi (r, (1 / z) * S) *
              _root_.GD.N0232.N0720.N1436.d013273 2 2 z (r, (1 / z) * S) := by
      change (∫ F in Ioi (0 : ℝ), g F) =
        (1 / z) * ∫ S in Ioi (0 : ℝ), g ((1 / z) * S)
      rw [hscale]
      field_simp [hz0.ne']
    _ = Real.sqrt z *
          ∫ S in Ioi (0 : ℝ),
            phi (r, S / z) * _root_.GD.N0232.N0720.N1487.d013903 z r S := by
      rw [← integral_const_mul, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro S hS
      have hdensity :=
        _root_.GD.N0232.N0720.N1487.d013919
          hz0 hz1 hr hS
      have hinvHalf :
          z ^ (-(1 / 2 : ℝ)) = (Real.sqrt z)⁻¹ := by
        rw [Real.rpow_neg hz0.le, hzHalf]
      rw [hinvHalf] at hdensity
      have hrecover :
          (1 / z) * _root_.GD.N0232.N0720.N1436.d013273 2 2 z (r, S / z) =
            Real.sqrt z * _root_.GD.N0232.N0720.N1487.d013903 z r S := by
        calc
          (1 / z) * _root_.GD.N0232.N0720.N1436.d013273 2 2 z (r, S / z) =
              Real.sqrt z * ((Real.sqrt z)⁻¹ *
                ((1 / z) * _root_.GD.N0232.N0720.N1436.d013273 2 2 z (r, S / z))) := by
            field_simp [hsqrt]
          _ = Real.sqrt z * _root_.GD.N0232.N0720.N1487.d013903 z r S := by
            congr 1
            simpa [mul_assoc] using hdensity
      change (1 / z) *
          (phi (r, (1 / z) * S) *
            _root_.GD.N0232.N0720.N1436.d013273 2 2 z (r, (1 / z) * S)) =
        Real.sqrt z *
          (phi (r, S / z) * _root_.GD.N0232.N0720.N1487.d013903 z r S)
      rw [show (1 / z) * S = S / z by ring]
      calc
        (1 / z) *
            (phi (r, S / z) * _root_.GD.N0232.N0720.N1436.d013273 2 2 z (r, S / z)) =
          phi (r, S / z) *
            ((1 / z) * _root_.GD.N0232.N0720.N1436.d013273 2 2 z (r, S / z)) := by ring
        _ = phi (r, S / z) *
            (Real.sqrt z * _root_.GD.N0232.N0720.N1487.d013903 z r S) := by
          rw [hrecover]
        _ = _ := by ring



theorem d013921
    {z C : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (phi : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hphi : Measurable phi)
    (hC : ∀ x, |phi x| ≤ C) :
    (∫ x, phi x ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 z) =
      Real.sqrt z *
        ∫ r in Ioo (0 : ℝ) 1,
          ∫ S in Ioi (0 : ℝ),
            phi (r, S / z) * _root_.GD.N0232.N0720.N1487.d013903 z r S := by
  calc
    (∫ x, phi x ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 z) =
        _root_.GD.N0120.d008810 (1 / 2) (1 / 2) z phi := by
      simpa [_root_.GD.N0232.N0720.N1436.d013207, _root_.GD.N0232.N0720.N1436.d013208] using
        (_root_.GD.N0232.N0720.N1434.d013558
          (m := 2) (n := 2) (by norm_num) (by norm_num)
          hz0 hz1 phi hphi hC)
    _ = ∫ x in _root_.GD.N0232.N0720.N1436.d013218,
          phi x * _root_.GD.N0116.d006511
            (1 / 2) (1 / 2) z x := by
      exact _root_.GD.N0232.N0720.N1434.d013557
        (by norm_num) (by norm_num) hz0 hz1 phi hphi hC
    _ = ∫ x in _root_.GD.N0232.N0720.N1436.d013218,
          phi x * _root_.GD.N0232.N0720.N1436.d013273 2 2 z x := by
      apply setIntegral_congr_fun _root_.GD.N0232.N0720.N1436.d013219
      intro x hx
      change phi x * _root_.GD.N0116.d006511
        (1 / 2) (1 / 2) z x =
          phi x * _root_.GD.N0232.N0720.N1436.d013273 2 2 z x
      rw [_root_.GD.N0232.N0720.N1435.d013489
        (by norm_num) (by norm_num) hz0 hz1 hx]
      norm_num [_root_.GD.N0232.N0720.N1436.d013207, _root_.GD.N0232.N0720.N1436.d013208]
    _ = _ := _root_.GD.N0232.N0720.N1487.d013920
      hz0 hz1 phi hphi hC



theorem d013922
    {z r S : ℝ} (hz0 : 0 ≤ z) (hzHalf : z ≤ 1 / 2)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hS0 : 0 ≤ S) :
    (S + r) / 2 ≤ _root_.GD.N0232.N0720.N1487.d013902 z r S := by
  unfold _root_.GD.N0232.N0720.N1487.d013902
  have hOne : 1 / 2 ≤ 1 - z := by linarith
  have hmain := mul_le_mul_of_nonneg_right hOne (add_nonneg hS0 hr0)
  have hrepair : 0 ≤ z * (1 - r) :=
    mul_nonneg hz0 (sub_nonneg.mpr hr1)
  linarith

private theorem d013923
    {r S : ℝ} (hr : 0 < r) (hS : 0 < S) :
    ((S + r) / 2) ^ (-(5 / 2 : ℝ)) =
      (2 : ℝ) ^ (5 / 2 : ℝ) *
        (S + r) ^ (-(5 / 2 : ℝ)) := by
  simpa [_root_.GD.N0232.N0720.N1487.d013902] using
    (_root_.GD.N0232.N0720.N1487.d013918 (z := 0)
      (show 0 < _root_.GD.N0232.N0720.N1487.d013902 0 r S by
        simpa [_root_.GD.N0232.N0720.N1487.d013902] using add_pos hS hr))



theorem d013924
    {z r S : ℝ} (hz0 : 0 < z) (hzHalf : z ≤ 1 / 2)
    (hr : r ∈ Ioo (0 : ℝ) 1) (hS : 0 < S) :
    _root_.GD.N0232.N0720.N1487.d013903 z r S ≤
      (2 : ℝ) ^ (5 / 2 : ℝ) *
        _root_.GD.N0232.N0720.N1487.d013904 r S := by
  have hz1 : z < 1 := lt_of_le_of_lt hzHalf (by norm_num)
  have hLambda := _root_.GD.N0232.N0720.N1487.d013909 hz0 hz1 hr hS
  have hfloor := _root_.GD.N0232.N0720.N1487.d013922
    hz0.le hzHalf hr.1.le hr.2.le hS.le
  have hpow :
      _root_.GD.N0232.N0720.N1487.d013902 z r S ^ (-(5 / 2 : ℝ)) ≤
        ((S + r) / 2) ^ (-(5 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (div_pos (add_pos hS hr.1) (by norm_num))
      hfloor (by norm_num)
  rw [_root_.GD.N0232.N0720.N1487.d013923 hr.1 hS] at hpow
  have hwall : (1 - z) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg z, sq_nonneg (1 - z)]
  have hfront : 0 ≤
      (3 / (2 * Real.pi)) *
        r ^ (-(1 / 2 : ℝ)) * (1 - r) ^ (-(1 / 2 : ℝ)) *
        S ^ (1 / 2 : ℝ) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (Real.rpow_nonneg hr.1.le _))
        (Real.rpow_nonneg (sub_nonneg.mpr hr.2.le) _))
      (Real.rpow_nonneg hS.le _)
  unfold _root_.GD.N0232.N0720.N1487.d013903 _root_.GD.N0232.N0720.N1487.d013904
  calc
    (3 / (2 * Real.pi)) * (1 - z) ^ 2 *
          r ^ (-(1 / 2 : ℝ)) * (1 - r) ^ (-(1 / 2 : ℝ)) *
          S ^ (1 / 2 : ℝ) *
          _root_.GD.N0232.N0720.N1487.d013902 z r S ^ (-(5 / 2 : ℝ))
        ≤
      ((3 / (2 * Real.pi)) *
          r ^ (-(1 / 2 : ℝ)) * (1 - r) ^ (-(1 / 2 : ℝ)) *
          S ^ (1 / 2 : ℝ)) *
        _root_.GD.N0232.N0720.N1487.d013902 z r S ^ (-(5 / 2 : ℝ)) := by
      have hlast : 0 ≤
          _root_.GD.N0232.N0720.N1487.d013902 z r S ^ (-(5 / 2 : ℝ)) :=
        Real.rpow_nonneg hLambda.le _
      have hfrontLast : 0 ≤
          ((3 / (2 * Real.pi)) *
            r ^ (-(1 / 2 : ℝ)) * (1 - r) ^ (-(1 / 2 : ℝ)) *
            S ^ (1 / 2 : ℝ)) *
          _root_.GD.N0232.N0720.N1487.d013902 z r S ^ (-(5 / 2 : ℝ)) :=
        mul_nonneg hfront hlast
      calc
        _ = (1 - z) ^ 2 *
            (((3 / (2 * Real.pi)) *
              r ^ (-(1 / 2 : ℝ)) * (1 - r) ^ (-(1 / 2 : ℝ)) *
              S ^ (1 / 2 : ℝ)) *
            _root_.GD.N0232.N0720.N1487.d013902 z r S ^ (-(5 / 2 : ℝ))) := by ring
        _ ≤ 1 *
            (((3 / (2 * Real.pi)) *
              r ^ (-(1 / 2 : ℝ)) * (1 - r) ^ (-(1 / 2 : ℝ)) *
              S ^ (1 / 2 : ℝ)) *
            _root_.GD.N0232.N0720.N1487.d013902 z r S ^ (-(5 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_right hwall hfrontLast
        _ = _ := one_mul _
    _ ≤ ((3 / (2 * Real.pi)) *
          r ^ (-(1 / 2 : ℝ)) * (1 - r) ^ (-(1 / 2 : ℝ)) *
          S ^ (1 / 2 : ℝ)) *
        ((2 : ℝ) ^ (5 / 2 : ℝ) *
          (S + r) ^ (-(5 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hpow hfront
    _ = (2 : ℝ) ^ (5 / 2 : ℝ) *
        ((3 / (2 * Real.pi)) *
          r ^ (-(1 / 2 : ℝ)) * (1 - r) ^ (-(1 / 2 : ℝ)) *
          S ^ (1 / 2 : ℝ) * (S + r) ^ (-(5 / 2 : ℝ))) := by
      ring

end

end N1487
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1487.d013919
#print axioms _root_.GD.N0232.N0720.N1487.d013921
#print axioms _root_.GD.N0232.N0720.N1487.d013924
