import GD.Module0556
import GD.Module0220

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace GD.N0149.N0432
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1089
open _root_.GD.N0082.N0334

theorem d008281 (u : ℝ) : _root_.GD.N0232.N0720.N1089.d003092 u ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (sq_nonneg u) (_root_.GD.N0232.N0720.N1089.d003095 u).le
  · exact (div_le_one (_root_.GD.N0232.N0720.N1089.d003095 u)).mpr (by nlinarith [sq_nonneg (1-u)])

theorem d008282 : Measurable _root_.GD.N0232.N0720.N1089.d003092 := by
  unfold _root_.GD.N0232.N0720.N1089.d003092
  fun_prop

theorem d008283 (u : ℝ) :
    _root_.GD.N0232.N0720.N1089.d003092 (1-u) = 1 - _root_.GD.N0232.N0720.N1089.d003092 u := by
  unfold _root_.GD.N0232.N0720.N1089.d003092
  have hd := (_root_.GD.N0232.N0720.N1089.d003095 u).ne'
  have hd' := (_root_.GD.N0232.N0720.N1089.d003095 (1-u)).ne'
  field_simp [hd, hd']
  ring

theorem d008284 : _root_.GD.N0082.N0334.d008260 _root_.GD.N0232.N0720.N1089.d003092 := by
  intro u hu
  have hd := _root_.GD.N0232.N0720.N1089.d003095 u
  have hu' : 0 ≤ u * (1-u) := mul_nonneg hu.1.le (sub_nonneg.mpr hu.2.le)
  have hlo : -u * (1-u) * (u^2+(1-u)^2) ≤
      u^2 - u * (u^2+(1-u)^2) := by
    nlinarith [mul_nonneg hu' (sq_nonneg u)]
  have hhi : u^2 - u * (u^2+(1-u)^2) ≤
      u * (1-u) * (u^2+(1-u)^2) := by
    nlinarith [mul_nonneg hu' (sq_nonneg (1-u))]
  rw [abs_le]
  unfold _root_.GD.N0232.N0720.N1089.d003092
  constructor
  · apply (le_div_iff₀ hd).mpr at hlo
    convert hlo using 1 <;> field_simp
  · apply (div_le_iff₀ hd).mpr at hhi
    convert hhi using 1
    field_simp

theorem d008285 : _root_.GD.N0082.N0334.d008258 _root_.GD.N0232.N0720.N1089.d003092 0 = Real.pi / 4 := by
  rw [_root_.GD.N0082.N0334.d008270]
  calc
    _ = ∫ u in Ioo (0 : ℝ) 1, _root_.GD.N0232.N0720.N1089.d003093 u := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      unfold _root_.GD.N0232.N0720.N1089.d003092 _root_.GD.N0232.N0720.N1089.d003093
      field_simp
    _ = ∫ u in (0 : ℝ)..1, _root_.GD.N0232.N0720.N1089.d003093 u := by
      rw [← integral_Ioc_eq_integral_Ioo,
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    _ = Real.pi / 4 := _root_.GD.N0232.N0720.N1089.d003099

def d008286 (t : ℝ) : ℝ :=
  (1 + _root_.GD.N0082.N0334.d008258 _root_.GD.N0232.N0720.N1089.d003092 t) / (1 + _root_.GD.N0082.N0334.d008258 id t)

theorem d008287 : ContinuousOn _root_.GD.N0149.N0432.d008286 (Icc (0 : ℝ) 1) := by
  apply ContinuousOn.div
  · exact continuousOn_const.add (_root_.GD.N0082.N0334.d008267 _root_.GD.N0149.N0432.d008282 _root_.GD.N0149.N0432.d008284)
  · exact continuousOn_const.add (_root_.GD.N0082.N0334.d008267 measurable_id _root_.GD.N0082.N0334.d008266)
  · intro t _
    have := _root_.GD.N0082.N0334.d008268 id t
    linarith

theorem d008288 : _root_.GD.N0149.N0432.d008286 0 = 1 / 2 + Real.pi / 8 := by
  rw [_root_.GD.N0149.N0432.d008286, _root_.GD.N0149.N0432.d008285, _root_.GD.N0082.N0334.d008273]
  ring

theorem d008289 : _root_.GD.N0149.N0432.d008286 1 = 1 / 2 + Real.pi / 8 := by
  have h : _root_.GD.N0149.N0432.d008286 (1-0) = _root_.GD.N0149.N0432.d008286 0 := by
    unfold _root_.GD.N0149.N0432.d008286
    rw [_root_.GD.N0082.N0334.d008276 _root_.GD.N0149.N0432.d008283,
      _root_.GD.N0082.N0334.d008276 (H := id) (fun _ => rfl)]
  simpa using h.trans _root_.GD.N0149.N0432.d008288

theorem d008290 : _root_.GD.N0149.N0432.d008286 0 < 1 ∧ _root_.GD.N0149.N0432.d008286 1 < 1 := by
  rw [_root_.GD.N0149.N0432.d008288, _root_.GD.N0149.N0432.d008289]
  constructor <;> linarith [Real.pi_lt_four]

def d008291 (H : ℝ → ℝ) (u : ℝ) : ℝ :=
  (H u / u)^2 + ((H u - 1) / (1-u))^2

def d008292 (H : ℝ → ℝ) (u : ℝ) : ℝ :=
  ((H u - _root_.GD.N0232.N0720.N1089.d003092 u) / u)^2 +
    ((H u - _root_.GD.N0232.N0720.N1089.d003092 u) / (1-u))^2

theorem d008293 (H : ℝ → ℝ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0149.N0432.d008291 H u = _root_.GD.N0149.N0432.d008291 _root_.GD.N0232.N0720.N1089.d003092 u + _root_.GD.N0149.N0432.d008292 H u := by
  unfold _root_.GD.N0149.N0432.d008291 _root_.GD.N0149.N0432.d008292 _root_.GD.N0232.N0720.N1089.d003092
  have h0 := hu.1.ne'
  have h1 := (sub_pos.mpr hu.2).ne'
  have hd := (_root_.GD.N0232.N0720.N1089.d003095 u).ne'
  field_simp [h0, h1, hd]
  ring

theorem d008294 (H : ℝ → ℝ) (hHm : Measurable H)
    (hH : _root_.GD.N0082.N0334.d008260 H) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Integrable (fun u => ((H u-t)/_root_.GD.N0082.N0334.d008256 t u)^2)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  apply (integrable_const (4 : ℝ)).mono'
  · apply Measurable.aestronglyMeasurable
    unfold _root_.GD.N0082.N0334.d008256
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact _root_.GD.N0082.N0334.d008264 hH ht hu

theorem d008295 (H : ℝ → ℝ) (hHm : Measurable H)
    (hH : _root_.GD.N0082.N0334.d008260 H) :
    Integrable (_root_.GD.N0149.N0432.d008291 H) (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have h0 := _root_.GD.N0149.N0432.d008294 H hHm hH (t := 0) (by norm_num)
  have h1 := _root_.GD.N0149.N0432.d008294 H hHm hH (t := 1) (by norm_num)
  have heq : (fun u => ((H u - 1) / _root_.GD.N0082.N0334.d008256 1 u)^2) =
      (fun u => ((H u-1)/(1-u))^2) := by
    funext u
    have : _root_.GD.N0082.N0334.d008256 1 u = 1-u := by unfold _root_.GD.N0082.N0334.d008256; ring
    rw [this]
  simp only [_root_.GD.N0082.N0334.d008256, mul_zero, sub_zero, add_zero] at h0
  rw [heq] at h1
  exact h0.add h1

theorem d008296 (H : ℝ → ℝ) (hHm : Measurable H)
    (hH : _root_.GD.N0082.N0334.d008260 H) :
    (∫ u in Ioo (0 : ℝ) 1, _root_.GD.N0149.N0432.d008291 H u) = _root_.GD.N0082.N0334.d008258 H 0 + _root_.GD.N0082.N0334.d008258 H 1 := by
  have h0 := _root_.GD.N0149.N0432.d008294 H hHm hH (t := 0) (by norm_num)
  have h1 := _root_.GD.N0149.N0432.d008294 H hHm hH (t := 1) (by norm_num)
  unfold _root_.GD.N0082.N0334.d008258
  rw [← integral_add h0 h1]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u _
  unfold _root_.GD.N0149.N0432.d008291 _root_.GD.N0082.N0334.d008256
  congr 2 <;> ring

theorem d008297 (H : ℝ → ℝ) (hHm : Measurable H)
    (hH : _root_.GD.N0082.N0334.d008260 H) :
    Integrable (_root_.GD.N0149.N0432.d008292 H) (volume.restrict (Ioo (0 : ℝ) 1)) := by
  apply ((_root_.GD.N0149.N0432.d008295 H hHm hH).sub
    (_root_.GD.N0149.N0432.d008295 _root_.GD.N0232.N0720.N1089.d003092 _root_.GD.N0149.N0432.d008282
      _root_.GD.N0149.N0432.d008284)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have := _root_.GD.N0149.N0432.d008293 H hu
  change _root_.GD.N0149.N0432.d008291 H u - _root_.GD.N0149.N0432.d008291 _root_.GD.N0232.N0720.N1089.d003092 u = _root_.GD.N0149.N0432.d008292 H u
  linarith

theorem d008298 (H : ℝ → ℝ) (hHm : Measurable H)
    (hH : _root_.GD.N0082.N0334.d008260 H) :
    _root_.GD.N0082.N0334.d008258 H 0 + _root_.GD.N0082.N0334.d008258 H 1 = Real.pi / 2 +
      ∫ u in Ioo (0 : ℝ) 1, _root_.GD.N0149.N0432.d008292 H u := by
  have hid : (∫ u in Ioo (0 : ℝ) 1, _root_.GD.N0149.N0432.d008291 H u) =
      (∫ u in Ioo (0 : ℝ) 1, _root_.GD.N0149.N0432.d008291 _root_.GD.N0232.N0720.N1089.d003092 u) +
        ∫ u in Ioo (0 : ℝ) 1, _root_.GD.N0149.N0432.d008292 H u := by
    rw [← integral_add (_root_.GD.N0149.N0432.d008295 _root_.GD.N0232.N0720.N1089.d003092
      _root_.GD.N0149.N0432.d008282 _root_.GD.N0149.N0432.d008284) (_root_.GD.N0149.N0432.d008297 H hHm hH)]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro u hu
    exact _root_.GD.N0149.N0432.d008293 H hu
  rw [_root_.GD.N0149.N0432.d008296 H hHm hH,
    _root_.GD.N0149.N0432.d008296 _root_.GD.N0232.N0720.N1089.d003092 _root_.GD.N0149.N0432.d008282
      _root_.GD.N0149.N0432.d008284, _root_.GD.N0149.N0432.d008285] at hid
  have h1 : _root_.GD.N0082.N0334.d008258 _root_.GD.N0232.N0720.N1089.d003092 1 = Real.pi / 4 := by
    simpa using (_root_.GD.N0082.N0334.d008276 _root_.GD.N0149.N0432.d008283 0).trans _root_.GD.N0149.N0432.d008285
  rw [h1] at hid
  linarith

theorem d008299 (H : ℝ → ℝ) (hHm : Measurable H)
    (hH : _root_.GD.N0082.N0334.d008260 H) :
    1 / 2 + Real.pi / 8 ≤
      max ((1 + _root_.GD.N0082.N0334.d008258 H 0)/2) ((1 + _root_.GD.N0082.N0334.d008258 H 1)/2) := by
  have h := _root_.GD.N0149.N0432.d008298 H hHm hH
  have htax : 0 ≤ ∫ u in Ioo (0 : ℝ) 1, _root_.GD.N0149.N0432.d008292 H u :=
    integral_nonneg (fun u => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have h0 := le_max_left ((1+_root_.GD.N0082.N0334.d008258 H 0)/2) ((1+_root_.GD.N0082.N0334.d008258 H 1)/2)
  have h1 := le_max_right ((1+_root_.GD.N0082.N0334.d008258 H 0)/2) ((1+_root_.GD.N0082.N0334.d008258 H 1)/2)
  linarith

theorem d008300 (H : ℝ → ℝ) (hHm : Measurable H)
    (hH : _root_.GD.N0082.N0334.d008260 H) :
    _root_.GD.N0082.N0334.d008258 H 0 + _root_.GD.N0082.N0334.d008258 H 1 = Real.pi / 2 ↔
      H =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] _root_.GD.N0232.N0720.N1089.d003092 := by
  have heq := _root_.GD.N0149.N0432.d008298 H hHm hH
  have hi := _root_.GD.N0149.N0432.d008297 H hHm hH
  have hn : 0 ≤ _root_.GD.N0149.N0432.d008292 H := fun u =>
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  constructor
  · intro h
    have hz : (∫ u in Ioo (0 : ℝ) 1, _root_.GD.N0149.N0432.d008292 H u) = 0 := by linarith
    have hz' := (integral_eq_zero_iff_of_nonneg hn hi).mp hz
    filter_upwards [hz', ae_restrict_mem measurableSet_Ioo] with u hu huI
    have hzsq : ((H u-_root_.GD.N0232.N0720.N1089.d003092 u)/u)^2 = 0 := by
      have := sq_nonneg ((H u-_root_.GD.N0232.N0720.N1089.d003092 u)/(1-u))
      unfold _root_.GD.N0149.N0432.d008292 at hu
      dsimp only [Pi.zero_apply] at hu
      nlinarith [sq_nonneg ((H u-_root_.GD.N0232.N0720.N1089.d003092 u)/u)]
    have hzdiv := (sq_eq_zero_iff).mp hzsq
    exact sub_eq_zero.mp ((div_eq_zero_iff).mp hzdiv |>.resolve_right huI.1.ne')
  · intro h
    have ht : _root_.GD.N0149.N0432.d008292 H =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] 0 := by
      filter_upwards [h] with u hu
      simp [_root_.GD.N0149.N0432.d008292, hu]
    have hz := (integral_eq_zero_iff_of_nonneg hn hi).mpr ht
    linarith

def d008301 (H : ℝ → ℝ) : Prop := Measurable H ∧ _root_.GD.N0082.N0334.d008260 H

def d008302 (H : ℝ → ℝ) : ℝ :=
  max ((1+_root_.GD.N0082.N0334.d008258 H 0)/2) ((1+_root_.GD.N0082.N0334.d008258 H 1)/2)

theorem d008303 :
    _root_.GD.N0149.N0432.d008302 _root_.GD.N0232.N0720.N1089.d003092 = 1/2 + Real.pi/8 := by
  have h1 : _root_.GD.N0082.N0334.d008258 _root_.GD.N0232.N0720.N1089.d003092 1 = Real.pi / 4 := by
    simpa using (_root_.GD.N0082.N0334.d008276 _root_.GD.N0149.N0432.d008283 0).trans _root_.GD.N0149.N0432.d008285
  rw [_root_.GD.N0149.N0432.d008302, _root_.GD.N0149.N0432.d008285, h1, max_self]
  ring

theorem d008304 :
    IsLeast (_root_.GD.N0149.N0432.d008302 '' {H | _root_.GD.N0149.N0432.d008301 H}) (1/2 + Real.pi/8) := by
  constructor
  · exact ⟨_root_.GD.N0232.N0720.N1089.d003092, ⟨_root_.GD.N0149.N0432.d008282, _root_.GD.N0149.N0432.d008284⟩,
      _root_.GD.N0149.N0432.d008303⟩
  · rintro x ⟨H, hH, rfl⟩
    exact _root_.GD.N0149.N0432.d008299 H hH.1 hH.2

theorem d008305 (H : ℝ → ℝ) (hH : _root_.GD.N0149.N0432.d008301 H) :
    _root_.GD.N0149.N0432.d008302 H = 1/2 + Real.pi/8 ↔
      H =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] _root_.GD.N0232.N0720.N1089.d003092 := by
  constructor
  · intro hm
    apply (_root_.GD.N0149.N0432.d008300 H hH.1 hH.2).mp
    have h0 := le_max_left ((1+_root_.GD.N0082.N0334.d008258 H 0)/2) ((1+_root_.GD.N0082.N0334.d008258 H 1)/2)
    have h1 := le_max_right ((1+_root_.GD.N0082.N0334.d008258 H 0)/2) ((1+_root_.GD.N0082.N0334.d008258 H 1)/2)
    change _ ≤ _root_.GD.N0149.N0432.d008302 H at h0 h1
    rw [hm] at h0 h1
    have hp := _root_.GD.N0149.N0432.d008298 H hH.1 hH.2
    have hn : 0 ≤ ∫ u in Ioo (0 : ℝ) 1, _root_.GD.N0149.N0432.d008292 H u :=
      integral_nonneg (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
    linarith
  · intro hm
    have he (t : ℝ) : _root_.GD.N0082.N0334.d008258 H t = _root_.GD.N0082.N0334.d008258 _root_.GD.N0232.N0720.N1089.d003092 t := by
      apply integral_congr_ae
      filter_upwards [hm] with u hu
      rw [hu]
    rw [_root_.GD.N0149.N0432.d008302, he 0, he 1]
    exact _root_.GD.N0149.N0432.d008303

end
end GD.N0149.N0432

#print axioms _root_.GD.N0149.N0432.d008287
#print axioms _root_.GD.N0149.N0432.d008288
#print axioms _root_.GD.N0149.N0432.d008289
#print axioms _root_.GD.N0149.N0432.d008290
#print axioms _root_.GD.N0149.N0432.d008298
#print axioms _root_.GD.N0149.N0432.d008299
#print axioms _root_.GD.N0149.N0432.d008300
#print axioms _root_.GD.N0149.N0432.d008304
#print axioms _root_.GD.N0149.N0432.d008305
