import GD.Module0223
import GD.Module0895



















open MeasureTheory ProbabilityTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1489

noncomputable section

open _root_.GD.N0232.N0720.N1050




noncomputable def d013937 (r S : ℝ) : ℝ :=
  (3 / (2 * Real.pi)) *
    r ^ (-(1 / 2 : ℝ)) * (1 - r) ^ (-(1 / 2 : ℝ)) *
    S ^ (1 / 2 : ℝ) * (S + r) ^ (-(5 / 2 : ℝ))



theorem d013938 (r S : ℝ) :
    _root_.GD.N0232.N0720.N1489.d013937 r S =
      _root_.GD.N0232.N0720.N1487.d013904
        r S := by
  rfl


noncomputable def d013939 (r S : ℝ) : ℝ :=
  S ^ (1 / 2 : ℝ) * (S + r) ^ (-(5 / 2 : ℝ))


noncomputable def d013940 (r S : ℝ) : ℝ :=
  r * _root_.GD.N0232.N0720.N1489.d013937 r S

private theorem d013941
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn
      (fun x : ℝ ↦ x ^ (a - 1) * (1 - x) ^ (b - 1))
      (Ioo (0 : ℝ) 1) := by
  by_contra hnot
  have hzero :
      (∫ x in Ioo (0 : ℝ) 1,
        x ^ (a - 1) * (1 - x) ^ (b - 1)) = 0 :=
    integral_undef hnot
  rw [_root_.GD.N0232.N0720.N1050.d003162 a b ha hb] at hzero
  exact (ProbabilityTheory.beta_pos ha hb).ne' hzero

private theorem d013942
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn
      (fun x : ℝ ↦ x ^ (a - 1) * (1 + x) ^ (-(a + b)))
      (Ioi (0 : ℝ)) := by
  by_contra hnot
  have hzero :
      (∫ x in Ioi (0 : ℝ),
        x ^ (a - 1) * (1 + x) ^ (-(a + b))) = 0 :=
    integral_undef hnot
  rw [_root_.GD.N0232.N0720.N1050.d003164 a b ha hb] at hzero
  exact (ProbabilityTheory.beta_pos ha hb).ne' hzero

private theorem d013943 :
    ProbabilityTheory.beta (3 / 2 : ℝ) 1 = 2 / 3 := by
  have hGamma : Real.Gamma (3 / 2 : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hstep := Real.Gamma_add_one (by norm_num : (3 / 2 : ℝ) ≠ 0)
  unfold ProbabilityTheory.beta
  rw [show (3 / 2 : ℝ) + 1 = 3 / 2 + 1 by ring,
    hstep, Real.Gamma_one]
  field_simp [hGamma]

private theorem d013944 :
    ProbabilityTheory.beta (1 / 2 : ℝ) (1 / 2) = Real.pi := by
  have hsqrt : Real.sqrt Real.pi ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_pos.le
  unfold ProbabilityTheory.beta
  rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by ring,
    Real.Gamma_one_half_eq, Real.Gamma_one]
  nlinarith

private theorem d013945
    {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    _root_.GD.N0232.N0720.N1489.d013939 r (r * x) =
      r ^ (-2 : ℝ) *
        (x ^ (1 / 2 : ℝ) * (1 + x) ^ (-(5 / 2 : ℝ))) := by
  have h1x : 0 < 1 + x := by linarith
  unfold _root_.GD.N0232.N0720.N1489.d013939
  rw [Real.mul_rpow hr.le hx.le]
  have hsum : r * x + r = r * (1 + x) := by ring
  rw [hsum, Real.mul_rpow hr.le h1x.le]
  have hcollect :
      r ^ (1 / 2 : ℝ) * r ^ (-(5 / 2 : ℝ)) =
        r ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  calc
    (r ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) *
        (r ^ (-(5 / 2 : ℝ)) * (1 + x) ^ (-(5 / 2 : ℝ))) =
      (r ^ (1 / 2 : ℝ) * r ^ (-(5 / 2 : ℝ))) *
        (x ^ (1 / 2 : ℝ) * (1 + x) ^ (-(5 / 2 : ℝ))) := by
      ring
    _ = _ := by rw [hcollect]

theorem d013946
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn (_root_.GD.N0232.N0720.N1489.d013939 r) (Ioi (0 : ℝ)) := by
  have hbetaPrime : IntegrableOn
      (fun x : ℝ ↦
        x ^ (1 / 2 : ℝ) * (1 + x) ^ (-(5 / 2 : ℝ)))
      (Ioi (0 : ℝ)) := by
    convert _root_.GD.N0232.N0720.N1489.d013942
      (a := (3 / 2 : ℝ)) (b := (1 : ℝ)) (by norm_num) (by norm_num)
      using 1
    all_goals norm_num
  have hscaled := hbetaPrime.const_mul (r ^ (-2 : ℝ))
  have hcomp : IntegrableOn
      (fun x : ℝ ↦ _root_.GD.N0232.N0720.N1489.d013939 r (r * x))
      (Ioi (0 : ℝ)) := by
    apply IntegrableOn.congr_fun hscaled _ measurableSet_Ioi
    intro x hx
    exact (_root_.GD.N0232.N0720.N1489.d013945 hr hx).symm
  simpa only [mul_zero] using
    (integrableOn_Ioi_comp_mul_left_iff
      (_root_.GD.N0232.N0720.N1489.d013939 r) 0 hr).1 hcomp


theorem d013947
    {r : ℝ} (hr : 0 < r) :
    (∫ S in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1489.d013939 r S) =
      2 / (3 * r) := by
  have hscaledIntegral :
      (∫ x in Ioi (0 : ℝ),
          _root_.GD.N0232.N0720.N1489.d013939 r (r * x)) =
        r ^ (-2 : ℝ) * ProbabilityTheory.beta (3 / 2 : ℝ) 1 := by
    calc
      _ = ∫ x in Ioi (0 : ℝ),
          r ^ (-2 : ℝ) *
            (x ^ (1 / 2 : ℝ) * (1 + x) ^ (-(5 / 2 : ℝ))) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        exact _root_.GD.N0232.N0720.N1489.d013945 hr hx
      _ = r ^ (-2 : ℝ) *
          ∫ x in Ioi (0 : ℝ),
            x ^ (1 / 2 : ℝ) * (1 + x) ^ (-(5 / 2 : ℝ)) := by
        rw [integral_const_mul]
      _ = r ^ (-2 : ℝ) * ProbabilityTheory.beta (3 / 2 : ℝ) 1 := by
        congr 1
        convert _root_.GD.N0232.N0720.N1050.d003164 (3 / 2 : ℝ) 1
          (by norm_num) (by norm_num) using 1
        all_goals norm_num
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi
    (_root_.GD.N0232.N0720.N1489.d013939 r) 0 hr
  simp only [mul_zero, smul_eq_mul] at hscale
  have hrecover :
      (∫ S in Ioi (0 : ℝ), _root_.GD.N0232.N0720.N1489.d013939 r S) =
        r * ∫ x in Ioi (0 : ℝ),
          _root_.GD.N0232.N0720.N1489.d013939 r (r * x) := by
    rw [hscale]
    field_simp [hr.ne']
  rw [hrecover, hscaledIntegral, _root_.GD.N0232.N0720.N1489.d013943]
  have hrpow : r ^ (-2 : ℝ) = 1 / r ^ 2 := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
      Real.rpow_neg hr.le, Real.rpow_two]
    simp only [one_div]
  rw [hrpow]
  field_simp [hr.ne']

theorem d013948
    {r S : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (hS : 0 ≤ S) :
    0 ≤ _root_.GD.N0232.N0720.N1489.d013940 r S := by
  unfold _root_.GD.N0232.N0720.N1489.d013940
  exact mul_nonneg hr (by
    unfold _root_.GD.N0232.N0720.N1489.d013937
    positivity)

private theorem d013949 :
    Measurable (fun x : ℝ × ℝ ↦
      _root_.GD.N0232.N0720.N1489.d013940 x.1 x.2) := by
  have measurable_real_rpow_const (p : ℝ) :
      Measurable (fun x : ℝ ↦ x ^ p) := by
    apply measurable_of_continuousOn_compl_singleton 0
    exact continuousOn_id.rpow_const fun x hx ↦ Or.inl hx
  have hr : Measurable (fun x : ℝ × ℝ ↦ x.1 ^ (-(1 / 2 : ℝ))) :=
    (measurable_real_rpow_const (-(1 / 2 : ℝ))).comp measurable_fst
  have hOneSubR : Measurable
      (fun x : ℝ × ℝ ↦ (1 - x.1) ^ (-(1 / 2 : ℝ))) :=
    (measurable_real_rpow_const (-(1 / 2 : ℝ))).comp
      (measurable_const.sub measurable_fst)
  have hS : Measurable (fun x : ℝ × ℝ ↦ x.2 ^ (1 / 2 : ℝ)) :=
    (measurable_real_rpow_const (1 / 2 : ℝ)).comp measurable_snd
  have hSum : Measurable
      (fun x : ℝ × ℝ ↦ (x.2 + x.1) ^ (-(5 / 2 : ℝ))) :=
    (measurable_real_rpow_const (-(5 / 2 : ℝ))).comp
      (measurable_snd.add measurable_fst)
  unfold _root_.GD.N0232.N0720.N1489.d013940
    _root_.GD.N0232.N0720.N1489.d013937
  exact measurable_fst.mul
    ((((measurable_const.mul hr).mul hOneSubR).mul hS).mul hSum)

theorem d013950
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    (∫ S in Ioi (0 : ℝ),
        _root_.GD.N0232.N0720.N1489.d013940 r S) =
      (1 / Real.pi) *
        r ^ (-(1 / 2 : ℝ)) * (1 - r) ^ (-(1 / 2 : ℝ)) := by
  rw [show (∫ S in Ioi (0 : ℝ),
      _root_.GD.N0232.N0720.N1489.d013940 r S) =
      ((3 / (2 * Real.pi)) * r *
        r ^ (-(1 / 2 : ℝ)) * (1 - r) ^ (-(1 / 2 : ℝ))) *
        ∫ S in Ioi (0 : ℝ),
          _root_.GD.N0232.N0720.N1489.d013939 r S by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro S hS
    unfold _root_.GD.N0232.N0720.N1489.d013940
      _root_.GD.N0232.N0720.N1489.d013937
      _root_.GD.N0232.N0720.N1489.d013939
    ring]
  rw [_root_.GD.N0232.N0720.N1489.d013947 hr.1]
  have hr0 := hr.1.ne'
  field_simp [hr0, Real.pi_ne_zero]

private theorem d013951
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    IntegrableOn
      (fun S : ℝ ↦ _root_.GD.N0232.N0720.N1489.d013940 r S)
      (Ioi (0 : ℝ)) := by
  let A : ℝ := (3 / (2 * Real.pi)) * r *
    r ^ (-(1 / 2 : ℝ)) * (1 - r) ^ (-(1 / 2 : ℝ))
  have h :=
    (_root_.GD.N0232.N0720.N1489.d013946 hr.1).const_mul A
  apply IntegrableOn.congr_fun h _ measurableSet_Ioi
  intro S hS
  dsimp [A, _root_.GD.N0232.N0720.N1489.d013940,
    _root_.GD.N0232.N0720.N1489.d013937,
    _root_.GD.N0232.N0720.N1489.d013939]
  ring

private theorem d013952
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    (∫ S in Ioi (0 : ℝ),
        ‖_root_.GD.N0232.N0720.N1489.d013940 r S‖) =
      (1 / Real.pi) *
        r ^ (-(1 / 2 : ℝ)) * (1 - r) ^ (-(1 / 2 : ℝ)) := by
  calc
    (∫ S in Ioi (0 : ℝ),
        ‖_root_.GD.N0232.N0720.N1489.d013940 r S‖) =
        ∫ S in Ioi (0 : ℝ),
          _root_.GD.N0232.N0720.N1489.d013940 r S := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro S hS
      change ‖_root_.GD.N0232.N0720.N1489.d013940 r S‖ =
        _root_.GD.N0232.N0720.N1489.d013940 r S
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact _root_.GD.N0232.N0720.N1489.d013948
        hr.1.le hr.2.le hS.le
    _ = _ := _root_.GD.N0232.N0720.N1489.d013950 hr



theorem d013953 :
    Integrable
      (fun x : ℝ × ℝ ↦
        _root_.GD.N0232.N0720.N1489.d013940 x.1 x.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioi (0 : ℝ)))) := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ × ℝ ↦
        _root_.GD.N0232.N0720.N1489.d013940 x.1 x.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioi (0 : ℝ)))) :=
    _root_.GD.N0232.N0720.N1489.d013949.aestronglyMeasurable
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact _root_.GD.N0232.N0720.N1489.d013951 hr
  · have houter := (_root_.GD.N0232.N0720.N1489.d013941
        (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
        (by norm_num) (by norm_num)).const_mul (1 / Real.pi)
    refine houter.congr (ae_restrict_mem measurableSet_Ioo |>.mono
      fun r hr ↦ ?_)
    convert
      (_root_.GD.N0232.N0720.N1489.d013952 hr).symm
      using 1
    all_goals norm_num
    all_goals ring


theorem d013954 :
    (∫ x : ℝ × ℝ,
        _root_.GD.N0232.N0720.N1489.d013940 x.1 x.2
      ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioi (0 : ℝ))))) = 1 := by
  rw [integral_prod _ _root_.GD.N0232.N0720.N1489.d013953]
  calc
    (∫ r, (∫ S,
          _root_.GD.N0232.N0720.N1489.d013940 r S
          ∂volume.restrict (Ioi (0 : ℝ)))
        ∂volume.restrict (Ioo (0 : ℝ) 1)) =
        ∫ r in Ioo (0 : ℝ) 1,
          (1 / Real.pi) *
            r ^ (-(1 / 2 : ℝ)) * (1 - r) ^ (-(1 / 2 : ℝ)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact _root_.GD.N0232.N0720.N1489.d013950 hr
    _ = (1 / Real.pi) * ProbabilityTheory.beta (1 / 2 : ℝ) (1 / 2) := by
      simp_rw [mul_assoc]
      rw [integral_const_mul]
      congr 1
      convert _root_.GD.N0232.N0720.N1050.d003162 (1 / 2 : ℝ) (1 / 2)
        (by norm_num) (by norm_num) using 1
      all_goals norm_num
    _ = 1 := by
      rw [_root_.GD.N0232.N0720.N1489.d013944]
      field_simp [Real.pi_ne_zero]




theorem d013955 :
    (∫ x : ℝ × ℝ,
        x.1 *
          _root_.GD.N0232.N0720.N1487.d013904
            x.1 x.2
      ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Ioi (0 : ℝ))))) = 1 := by
  change (∫ x : ℝ × ℝ,
      _root_.GD.N0232.N0720.N1489.d013940 x.1 x.2
    ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod
      (volume.restrict (Ioi (0 : ℝ))))) = 1
  exact _root_.GD.N0232.N0720.N1489.d013954

end

end N1489
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1489.d013953
#print axioms _root_.GD.N0232.N0720.N1489.d013954
#print axioms _root_.GD.N0232.N0720.N1489.d013955
