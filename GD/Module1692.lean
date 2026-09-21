import GD.Module1691




set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace GD.N0101.N0361
noncomputable section
open _root_.GD.N0213
open _root_.GD.N0213.N0510 _root_.GD.N0213.N0508 _root_.GD.N0213.N0516 _root_.GD.N0213.N0509
open _root_.GD.N0101.N0395 _root_.GD.N0101.N0394 _root_.GD.N0101.N0389
open _root_.GD.N0101.N0403 _root_.GD.N0101.N0357 _root_.GD.N0101.N0351 _root_.GD.N0101.N0398
open _root_.GD.N0230.N0665
open _root_.GD.N0232.N0719.N0954

abbrev d028526 := Fin 2 → ℝ

def d028527 (a : ℝ) (h : _root_.GD.N0101.N0361.d028526 → ℝ) : ℝ≥0∞ :=
  ∫⁻ β, ∫⁻ t, _root_.GD.N0101.N0394.d028505 a h β t
    ∂_root_.GD.N0213.N0516.d028411 (fun _ : Fin 2 => a) β ∂_root_.GD.N0213.N0508.d028429 (fun _ : Fin 2 => a)

theorem d028528 (a : ℝ) (ha : 0 < a)
    (F : _root_.GD.N0101.N0361.d028526 → _root_.GD.N0101.N0361.d028526 → ℝ≥0∞) (hF : Measurable (fun z : _root_.GD.N0101.N0361.d028526 × _root_.GD.N0101.N0361.d028526 => F z.1 z.2)) :
    AEMeasurable (fun t => ENNReal.ofReal (_root_.GD.N0213.N0510.d023124 (fun _ : Fin 2 => a) (fun i => a*t i)) *
      ∫⁻ β, F β t ∂_root_.GD.N0213.N0510.d023126 (fun _ : Fin 2 => a) (fun i => a*t i))
      (_root_.GD.N0213.N0516.d028413 (fun _ : Fin 2 => a) 0) := by
  have hm : Measurable (fun t => ∫⁻ β, F β t
      ∂_root_.GD.N0213.N0508.d028430 (fun _ : Fin 2 => a) t) := by
    have heq (t : _root_.GD.N0101.N0361.d028526) := _root_.GD.N0213.N0508.d028432 (fun _ : Fin 2 => a) t
      (fun β => F β t) (by fun_prop)
    simp_rw [heq]
    exact _root_.GD.N0213.N0494.d028486 _ 0
      (fun β t => ENNReal.ofReal (_root_.GD.N0213.N0509.d023108 (fun _ : Fin 2 => a) β ^ 2) * F β t) (by fun_prop)
  apply hm.aemeasurable.congr
  filter_upwards [_root_.GD.N0213.N0494.d028485 (fun _ : Fin 2 => a) 0] with t ht
  exact _root_.GD.N0101.N0389.d028497 _ t (fun _ => ha) ht (fun β => F β t)

theorem d028529 (a : ℝ) (ha : 0 < a) (h : _root_.GD.N0101.N0361.d028526 → ℝ)
    (hh : Measurable h) (w : _root_.GD.N0101.N0361.d028526 → _root_.GD.N0101.N0361.d028526) (hw : Measurable w) :
    (∫⁻ β, _root_.GD.N0101.N0351.d023188 (fun _ : Fin 2 => a) w β
      ∂_root_.GD.N0101.N0403.d028436 (fun _ : Fin 2 => a) h) =
      ∫⁻ t, ENNReal.ofReal (_root_.GD.N0213.N0510.d023124 (fun _ : Fin 2 => a) (fun i => a*t i)) *
        _root_.GD.N0101.N0395.d028517 a t h (w t) ∂_root_.GD.N0213.N0516.d028413 (fun _ : Fin 2 => a) 0 := by
  have hm : Measurable (_root_.GD.N0101.N0351.d023188 (fun _ : Fin 2 => a) w) :=
    _root_.GD.N0213.N0508.d028431 _
      (fun β t => ENNReal.ofReal (_root_.GD.N0101.N0351.d023186 β (w t))) (by unfold _root_.GD.N0101.N0351.d023186; fun_prop)
  rw [_root_.GD.N0101.N0403.d028436, lintegral_withDensity_eq_lintegral_mul _
    (hh.pow_const 2).ennreal_ofReal hm]
  calc
    _ = ∫⁻ β, ∫⁻ t, ENNReal.ofReal (_root_.GD.N0101.N0351.d023186 β (w t) * h β ^ 2)
        ∂_root_.GD.N0213.N0516.d028411 (fun _ : Fin 2 => a) β ∂_root_.GD.N0213.N0508.d028429 (fun _ : Fin 2 => a) := by
      apply lintegral_congr
      intro β
      change ENNReal.ofReal (h β ^ 2) *
        (∫⁻ t, ENNReal.ofReal (_root_.GD.N0101.N0351.d023186 β (w t)) ∂_root_.GD.N0213.N0516.d028411 (fun _ : Fin 2 => a) β) = _
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro t
      rw [ENNReal.ofReal_mul' (sq_nonneg _), mul_comm]
    _ = _ := _root_.GD.N0101.N0389.d028500 _ (fun _ => ha)
      (fun β t => ENNReal.ofReal (_root_.GD.N0101.N0351.d023186 β (w t) * h β ^ 2)) (by unfold _root_.GD.N0101.N0351.d023186; fun_prop)



theorem d028530 (a : ℝ) (ha : 0 < a) (h : _root_.GD.N0101.N0361.d028526 → ℝ)
    (hh : Measurable h) (hb : ∀ β, h β ∈ Icc (0 : ℝ) 1)
    (w : _root_.GD.N0101.N0361.d028526 → _root_.GD.N0101.N0361.d028526) (hw : Measurable w) (hunit : ∀ t, ∑ i, w t i = 1) :
    (∫⁻ β, _root_.GD.N0101.N0351.d023188 (fun _ : Fin 2 => a) _root_.GD.N0230.N0665.d000407 β
      ∂_root_.GD.N0101.N0403.d028436 (fun _ : Fin 2 => a) h) ≤
      (∫⁻ β, _root_.GD.N0101.N0351.d023188 (fun _ : Fin 2 => a) w β
        ∂_root_.GD.N0101.N0403.d028436 (fun _ : Fin 2 => a) h) + _root_.GD.N0101.N0361.d028527 a h := by
  rw [_root_.GD.N0101.N0361.d028529 a ha h hh _root_.GD.N0230.N0665.d000407
    _root_.GD.N0101.N0415.d023227,
    _root_.GD.N0101.N0361.d028529 a ha h hh w hw]
  have henergy := _root_.GD.N0101.N0394.d028513 a ha h hh
  change _ = _root_.GD.N0101.N0361.d028527 a h at henergy
  rw [← henergy]
  have hm := _root_.GD.N0101.N0361.d028528 a ha
    (fun β t => ENNReal.ofReal (_root_.GD.N0101.N0351.d023186 β (w t) * h β ^ 2)) (by unfold _root_.GD.N0101.N0351.d023186; fun_prop)
  calc
    _ ≤ ∫⁻ t, ENNReal.ofReal (_root_.GD.N0213.N0510.d023124 (fun _ : Fin 2 => a) (fun i => a*t i)) *
        _root_.GD.N0101.N0395.d028517 a t h (w t) +
        ENNReal.ofReal (_root_.GD.N0213.N0510.d023124 (fun _ : Fin 2 => a) (fun i => a*t i)) *
          _root_.GD.N0101.N0394.d028506 a h t ∂_root_.GD.N0213.N0516.d028413 (fun _ : Fin 2 => a) 0 := by
      apply lintegral_mono_ae
      filter_upwards [_root_.GD.N0213.N0494.d028485 (fun _ : Fin 2 => a) 0] with t ht
      rw [← mul_add]
      exact mul_le_mul_right (_root_.GD.N0101.N0395.d028525 a ha t ht h hh hb (w t) (hunit t)) _
    _ = _ := lintegral_add_left' hm _

theorem d028531 (a : ℝ) (sizes : Fin 2 → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hshape : _root_.GD.N0232.N0719.N0954.d009355 sizes = (fun _ : Fin 2 => a)) (h : _root_.GD.N0101.N0361.d028526 → ℝ)
    (w : _root_.GD.N0101.N0361.d028526 → _root_.GD.N0101.N0361.d028526) (hw : Measurable w) (hunit : ∀ t, ∑ i, w t i = 1) :
    _root_.GD.N0101.N0398.d023335 sizes hn w =ᵐ[_root_.GD.N0101.N0403.d028436 (fun _ : Fin 2 => a) h]
      _root_.GD.N0101.N0351.d023188 (fun _ : Fin 2 => a) w := by
  filter_upwards [_root_.GD.N0101.N0403.d028442 (fun _ : Fin 2 => a) h] with β hβ
  rw [_root_.GD.N0101.N0398.d023336 sizes hn w hw hunit hβ, hshape]

theorem d028532 (a : ℝ) (sizes : Fin 2 → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hshape : _root_.GD.N0232.N0719.N0954.d009355 sizes = (fun _ : Fin 2 => a)) (h : _root_.GD.N0101.N0361.d028526 → ℝ)
    (w : _root_.GD.N0101.N0361.d028526 → _root_.GD.N0101.N0361.d028526) (hw : Measurable w) (hunit : ∀ t, ∑ i, w t i = 1) :
    AEMeasurable (_root_.GD.N0101.N0398.d023335 sizes hn w) (_root_.GD.N0101.N0403.d028436 (fun _ : Fin 2 => a) h) := by
  have hm : Measurable (_root_.GD.N0101.N0351.d023188 (fun _ : Fin 2 => a) w) :=
    _root_.GD.N0213.N0508.d028431 _
      (fun β t => ENNReal.ofReal (_root_.GD.N0101.N0351.d023186 β (w t))) (by unfold _root_.GD.N0101.N0351.d023186; fun_prop)
  exact hm.aemeasurable.congr (_root_.GD.N0101.N0361.d028531 a sizes hn hshape h w hw hunit).symm

theorem d028533 (a : ℝ) (ha : 0 < a)
    (sizes : Fin 2 → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hshape : _root_.GD.N0232.N0719.N0954.d009355 sizes = (fun _ : Fin 2 => a)) (h : _root_.GD.N0101.N0361.d028526 → ℝ)
    (hh : Measurable h) (hb : ∀ β, h β ∈ Icc (0 : ℝ) 1)
    (p w : _root_.GD.N0101.N0361.d028526 → _root_.GD.N0101.N0361.d028526) (hp : Measurable p) (hw : Measurable w)
    (hpunit : ∀ t, ∑ i, p t i = 1) (hwunit : ∀ t, ∑ i, w t i = 1)
    (hporacle : ∀ t ∈ _root_.GD.N0101.N0357.d023158, p t = _root_.GD.N0230.N0665.d000407 t) :
    (∫⁻ β, _root_.GD.N0101.N0398.d023335 sizes hn p β ∂_root_.GD.N0101.N0403.d028436 (fun _ : Fin 2 => a) h) ≤
      (∫⁻ β, _root_.GD.N0101.N0398.d023335 sizes hn w β ∂_root_.GD.N0101.N0403.d028436 (fun _ : Fin 2 => a) h) +
        _root_.GD.N0101.N0361.d028527 a h := by
  rw [lintegral_congr_ae (_root_.GD.N0101.N0361.d028531 a sizes hn hshape h p hp hpunit),
    lintegral_congr_ae (_root_.GD.N0101.N0361.d028531 a sizes hn hshape h w hw hwunit)]
  have hp_eq : _root_.GD.N0101.N0351.d023188 (fun _ : Fin 2 => a) p =ᵐ[_root_.GD.N0101.N0403.d028436 (fun _ : Fin 2 => a) h]
      _root_.GD.N0101.N0351.d023188 (fun _ : Fin 2 => a) _root_.GD.N0230.N0665.d000407 := by
    filter_upwards [_root_.GD.N0101.N0403.d028442 (fun _ : Fin 2 => a) h] with β hβ
    exact _root_.GD.N0101.N0349.d023344 _ (fun _ => ha) p hporacle hβ
  rw [lintegral_congr_ae hp_eq]
  exact _root_.GD.N0101.N0361.d028530 a ha h hh hb w hw hwunit




theorem d028534 (a : ℝ) (ha : 0 < a)
    (sizes : Fin 2 → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hshape : _root_.GD.N0232.N0719.N0954.d009355 sizes = (fun _ : Fin 2 => a)) (h : _root_.GD.N0101.N0361.d028526 → ℝ)
    (hh : Measurable h) (hb : ∀ β, h β ∈ Icc (0 : ℝ) 1)
    (p w : _root_.GD.N0101.N0361.d028526 → _root_.GD.N0101.N0361.d028526) (hp : Measurable p) (hw : Measurable w)
    (hpunit : ∀ t, ∑ i, p t i = 1) (hwunit : ∀ t, ∑ i, w t i = 1)
    (hporacle : ∀ t ∈ _root_.GD.N0101.N0357.d023158, p t = _root_.GD.N0230.N0665.d000407 t)
    (hweak : ∀ β ∈ _root_.GD.N0101.N0357.d023158, _root_.GD.N0101.N0398.d023335 sizes hn w β ≤ _root_.GD.N0101.N0398.d023335 sizes hn p β)
    (hfinite : (∫⁻ β, _root_.GD.N0101.N0398.d023335 sizes hn p β
      ∂_root_.GD.N0101.N0403.d028436 (fun _ : Fin 2 => a) h) ≠ ⊤) :
    (∫⁻ β, _root_.GD.N0101.N0398.d023335 sizes hn p β - _root_.GD.N0101.N0398.d023335 sizes hn w β
      ∂_root_.GD.N0101.N0403.d028436 (fun _ : Fin 2 => a) h) ≤ _root_.GD.N0101.N0361.d028527 a h := by
  have hle : _root_.GD.N0101.N0398.d023335 sizes hn w ≤ᵐ[_root_.GD.N0101.N0403.d028436 (fun _ : Fin 2 => a) h]
      _root_.GD.N0101.N0398.d023335 sizes hn p := by
    filter_upwards [_root_.GD.N0101.N0403.d028442 (fun _ : Fin 2 => a) h] with β hβ
    exact hweak β hβ
  have hwfinite := ne_top_of_le_ne_top hfinite (lintegral_mono_ae hle)
  rw [lintegral_sub' (_root_.GD.N0101.N0361.d028532 a sizes hn hshape h w hw hwunit) hwfinite hle]
  apply tsub_le_iff_right.mpr
  simpa only [add_comm] using _root_.GD.N0101.N0361.d028533 a ha sizes hn hshape h hh hb
    p w hp hw hpunit hwunit hporacle

end
end GD.N0101.N0361

#print axioms _root_.GD.N0101.N0361.d028529
#print axioms _root_.GD.N0101.N0361.d028530
#print axioms _root_.GD.N0101.N0361.d028533
#print axioms _root_.GD.N0101.N0361.d028534
