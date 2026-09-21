import GD.Module0899
import GD.Module0274

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory Set

namespace GD.N0054
noncomputable section
open _root_.GD.N0232.N0720.N1091
open _root_.GD.N0232.N0720.N1046

def d022099 (t u : ℝ) : ℝ := 2*u+t-3*t*u

theorem d022100 {t u : ℝ} (ht : t ∈ Ioo (0:ℝ) 1)
    (hu : u ∈ Ioo (0:ℝ) 1) : 0 < _root_.GD.N0054.d022099 t u := by
  have := add_pos (mul_pos (mul_pos (by norm_num : (0:ℝ)<2) (sub_pos.mpr ht.2)) hu.1)
    (mul_pos ht.1 (sub_pos.mpr hu.2))
  unfold _root_.GD.N0054.d022099
  nlinarith

private theorem d022101 : beta (1/2:ℝ) 1 = 2 := by
  unfold beta
  rw [Real.Gamma_one, Real.Gamma_add_one (by norm_num : (1/2:ℝ) ≠ 0)]
  have h := (Real.Gamma_pos_of_pos (by norm_num : (0:ℝ)<1/2)).ne'
  field_simp

private theorem d022102 : beta 1 (1/2:ℝ) = 2 := by
  simpa [beta, add_comm, mul_comm] using _root_.GD.N0054.d022101

theorem d022103 {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    betaPDFReal (1/2) 1 u = 1/(2*Real.sqrt u) := by
  rw [betaPDFReal, if_pos (show 0<u ∧ u<1 from hu), _root_.GD.N0054.d022101]
  norm_num only
  rw [Real.rpow_neg hu.1.le, ← Real.sqrt_eq_rpow, Real.rpow_zero, mul_one]
  ring

theorem d022104 {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    betaPDFReal 1 (1/2) u = 1/(2*Real.sqrt (1-u)) := by
  rw [betaPDFReal, if_pos (show 0<u ∧ u<1 from hu), _root_.GD.N0054.d022102]
  norm_num only
  rw [Real.rpow_neg (sub_pos.mpr hu.2).le, ← Real.sqrt_eq_rpow, Real.rpow_zero, mul_one]
  ring

theorem d022105 {a b : ℝ} (ha : 0<a) (hb : 0<b)
    (f : ℝ → ℝ) :
    (∫ u, f u ∂betaMeasure a b) = ∫ u in Ioo (0:ℝ) 1, betaPDFReal a b u*f u := by
  rw [_root_.GD.N0235.d004041 ha hb]
  symm
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards with u hu
  have hu' : ¬(0<u ∧ u<1) := hu
  simp [betaPDFReal, hu']

theorem d022106 {a b ρ : ℝ} (ha : 0<a) (hb : 0<b)
    (hρ : 0<ρ) (f : ℝ → ℝ) :
    (∫ u, f (_root_.GD.N0232.N0720.N1091.d012763 ρ u) ∂betaMeasure a b) =
      ∫ u in Ioo (0:ℝ) 1,
        (ρ/_root_.GD.N0232.N0720.N1046.d013992 ρ u^2)*betaPDFReal a b (_root_.GD.N0232.N0720.N1091.d012763 ρ u)*f u := by
  rw [_root_.GD.N0054.d022105 ha hb]
  have h := integral_image_eq_integral_abs_deriv_smul
    (s := Ioo (0:ℝ) 1) (f := _root_.GD.N0232.N0720.N1091.d012763 ρ)
    (f' := fun u => -ρ/_root_.GD.N0232.N0720.N1046.d013992 ρ u^2)
    measurableSet_Ioo (fun u hu => _root_.GD.N0232.N0720.N1046.d013999 hρ hu)
    (_root_.GD.N0232.N0720.N1046.d014001 hρ) (fun u => betaPDFReal a b u*f (_root_.GD.N0232.N0720.N1091.d012763 ρ u))
  rw [_root_.GD.N0232.N0720.N1046.d014002 hρ] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  dsimp only
  rw [_root_.GD.N0232.N0720.N1046.d014000 hρ hu, smul_eq_mul, _root_.GD.N0232.N0720.N1046.d014006 hρ hu]
  ring

theorem d022107 {t u : ℝ} (ht : t ∈ Ioo (0:ℝ) 1)
    (hu : u ∈ Ioo (0:ℝ) 1) :
    ((t/(2*(1-t)))/_root_.GD.N0232.N0720.N1046.d013992 (t/(2*(1-t))) u^2)*
        betaPDFReal (1/2) 1 (_root_.GD.N0232.N0720.N1091.d012763 (t/(2*(1-t))) u) =
      Real.sqrt t*(1-t)/(Real.sqrt (1-u)*_root_.GD.N0054.d022099 t u*Real.sqrt (_root_.GD.N0054.d022099 t u)) := by
  have ht1 := sub_pos.mpr ht.2
  have hu1 := sub_pos.mpr hu.2
  have hρ : 0<t/(2*(1-t)) := div_pos ht.1 (mul_pos (by norm_num) ht1)
  have hD := _root_.GD.N0054.d022100 ht hu
  have hA := _root_.GD.N0232.N0720.N1046.d013995 hρ hu.1 hu.2
  have hW := _root_.GD.N0232.N0720.N1091.d012780 hρ hu.1 hu.2
  rw [_root_.GD.N0054.d022103 hW]
  have hden : _root_.GD.N0232.N0720.N1046.d013992 (t/(2*(1-t))) u = _root_.GD.N0054.d022099 t u/(2*(1-t)) := by
    unfold _root_.GD.N0232.N0720.N1046.d013992 _root_.GD.N0054.d022099
    field_simp
    ring
  have hweight : _root_.GD.N0232.N0720.N1091.d012763 (t/(2*(1-t))) u = t*(1-u)/_root_.GD.N0054.d022099 t u := by
    unfold _root_.GD.N0232.N0720.N1091.d012763 _root_.GD.N0054.d022099
    field_simp
    ring
  rw [hden, hweight, Real.sqrt_div (mul_nonneg ht.1.le hu1.le), Real.sqrt_mul ht.1.le]
  have hsT := Real.sq_sqrt ht.1.le
  have hsD := Real.sq_sqrt hD.le
  have hst := (Real.sqrt_pos.mpr ht.1).ne'
  have hsu := (Real.sqrt_pos.mpr hu1).ne'
  have hsd := (Real.sqrt_pos.mpr hD).ne'
  field_simp
  nlinarith [hsT, hsD]

theorem d022108 {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1)
    (f : ℝ → ℝ) :
    (∫ u, f (_root_.GD.N0232.N0720.N1091.d012763 (t/(2*(1-t))) u) ∂betaMeasure (1/2) 1) =
      Real.sqrt t*(1-t)*∫ u in Ioo (0:ℝ) 1,
        f u/(Real.sqrt (1-u)*_root_.GD.N0054.d022099 t u*Real.sqrt (_root_.GD.N0054.d022099 t u)) := by
  rw [_root_.GD.N0054.d022106 (by norm_num : (0:ℝ)<1/2)
    (by norm_num : (0:ℝ)<1) (div_pos ht.1 (mul_pos (by norm_num) (sub_pos.mpr ht.2))), ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  dsimp only
  rw [_root_.GD.N0054.d022107 ht hu]
  ring

theorem d022109 {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1)
    (f : ℝ → ℝ) :
    (∫ u, f (_root_.GD.N0232.N0720.N1091.d012763 (t/(2*(1-t))) u) ∂betaMeasure (1/2) 1) =
      (2*Real.sqrt t*(1-t))*∫ u, f u/(_root_.GD.N0054.d022099 t u*Real.sqrt (_root_.GD.N0054.d022099 t u))
        ∂betaMeasure 1 (1/2) := by
  rw [_root_.GD.N0054.d022108 ht,
    _root_.GD.N0054.d022105 (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1/2),
    ← integral_const_mul, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  dsimp only
  rw [_root_.GD.N0054.d022104 hu]
  ring

theorem d022110 {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1)
    (H : ℝ → ℝ) :
    (∫ u, (H (_root_.GD.N0232.N0720.N1091.d012763 (t/(2*(1-t))) u)-t)^2 ∂betaMeasure (1/2) 1) =
      Real.sqrt t*(1-t)*(2*∫ u, ((H u-t)/_root_.GD.N0054.d022099 t u)^2*Real.sqrt (_root_.GD.N0054.d022099 t u)
        ∂betaMeasure 1 (1/2)) := by
  rw [_root_.GD.N0054.d022109 ht (fun u => (H u-t)^2)]
  have hEq : (∫ u, (H u-t)^2/(_root_.GD.N0054.d022099 t u*Real.sqrt (_root_.GD.N0054.d022099 t u))
      ∂betaMeasure 1 (1/2)) =
      ∫ u, ((H u-t)/_root_.GD.N0054.d022099 t u)^2*Real.sqrt (_root_.GD.N0054.d022099 t u)
        ∂betaMeasure 1 (1/2) := by
    apply integral_congr_ae
    have hmem : ∀ᵐ u ∂betaMeasure 1 (1/2), u ∈ Ioo (0:ℝ) 1 := by
      unfold betaMeasure betaPDF
      rw [ae_withDensity_iff ((measurable_betaPDFReal 1 (1/2)).ennreal_ofReal)]
      filter_upwards with u
      intro hu
      by_contra hnot
      have hout : ¬(0<u ∧ u<1) := hnot
      simp [betaPDFReal, hout] at hu
    filter_upwards [hmem] with u hu
    have hD := _root_.GD.N0054.d022100 ht hu
    have hs := Real.sq_sqrt hD.le
    have hsd := (Real.sqrt_pos.mpr hD).ne'
    field_simp
    nlinarith [sq_nonneg (H u-t)]
  rw [hEq]
  ring

end
end GD.N0054

#print axioms _root_.GD.N0054.d022106
#print axioms _root_.GD.N0054.d022107
#print axioms _root_.GD.N0054.d022108
#print axioms _root_.GD.N0054.d022109
#print axioms _root_.GD.N0054.d022110
