import GD.Module0927
import GD.Module1897

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace GD.N0149.N0436
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0076.N0313
open _root_.GD.N0082.N0334
open _root_.GD.N0082.N0335
open _root_.GD.N0082.N0336
open _root_.GD.N0149.N0431

theorem d030844 (u t : ℝ) :
    _root_.GD.N0001.d014462 u t=_root_.GD.N0082.N0334.d008256 t u := by
  unfold _root_.GD.N0001.d014462 _root_.GD.N0082.N0334.d008256
  ring

theorem d030845 (H : ℝ → ℝ) (hHm : Measurable H)
    (hHI : ∀ u ∈ Ioo (0 : ℝ) 1, H u ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun u => ((H u-t)/_root_.GD.N0082.N0334.d008256 t u)^2)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  let m := min t (1-t)
  have hm : 0 < m := lt_min ht.1 (sub_pos.mpr ht.2)
  apply (integrable_const (1/m^2)).mono'
  · apply Measurable.aestronglyMeasurable
    unfold _root_.GD.N0082.N0334.d008256
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hd := _root_.GD.N0082.N0334.d008263 ⟨ht.1.le,ht.2.le⟩ hu
    have hdm : m≤_root_.GD.N0082.N0334.d008256 t u := by
      have h1 := mul_nonneg hu.1.le (sub_nonneg.mpr (min_le_right t (1-t)))
      have h2 := mul_nonneg (sub_nonneg.mpr hu.2.le) (sub_nonneg.mpr (min_le_left t (1-t)))
      unfold _root_.GD.N0082.N0334.d008256
      dsimp [m] at *
      nlinarith
    have hn : (H u-t)^2≤1 := by
      have hU := hHI u hu
      have hlo : 0≤1+(H u-t) := by linarith [hU.1,ht.2]
      have hhi : 0≤1-(H u-t) := by linarith [hU.2,ht.1]
      nlinarith [mul_nonneg hlo hhi]
    have hd2 : m^2≤_root_.GD.N0082.N0334.d008256 t u^2 := (sq_le_sq₀ hm.le hd.le).mpr hdm
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),div_pow]
    exact (div_le_div_of_nonneg_right hn (sq_nonneg _)).trans
      (one_div_le_one_div_of_le (sq_pos_of_pos hm) hd2)

theorem d030846 (H : ℝ → ℝ) (hHm : Measurable H)
    (hHI : ∀ u ∈ Ioo (0 : ℝ) 1, H u ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0149.N0431.d014479 H t=ENNReal.ofReal (_root_.GD.N0082.N0334.d008258 H t) := by
  unfold _root_.GD.N0149.N0431.d014479 _root_.GD.N0149.N0431.d014474
  simp_rw [_root_.GD.N0149.N0436.d030844]
  exact (ofReal_integral_eq_lintegral_ofReal
    (_root_.GD.N0149.N0436.d030845 H hHm hHI ht)
    (ae_of_all _ fun _ => sq_nonneg _)).symm

theorem d030847 (H : ℝ → ℝ) (hHm : Measurable H)
    (hHI : ∀ u, H u ∈ Icc (0 : ℝ) 1)
    (hdom : ∀ θ : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H)≤
      _root_.GD.N0232.N0720.N1066.d014320 3 3 (by omega) (by omega) θ) :
    H =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] id ∧
      ∀ θ : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H)=
        _root_.GD.N0232.N0720.N1066.d014320 3 3 (by omega) (by omega) θ := by
  have hE : ∀ t ∈ Ioo (0 : ℝ) 1, _root_.GD.N0082.N0334.d008258 H t≤_root_.GD.N0082.N0334.d008258 id t := by
    intro t ht
    let θ := _root_.GD.N0232.N0720.N1219.d017942 3 3 (by omega) (by omega) t ht
    have htθ : _root_.GD.N0082.N0336.d030741 θ=t :=
      _root_.GD.N0232.N0720.N1219.d017949 3 3
        (by omega) (by omega) t ht
    have h := hdom θ
    rw [_root_.GD.N0082.N0336.d030746 H hHm hHI,_root_.GD.N0082.N0336.d030750,htθ] at h
    have hp := _root_.GD.N0082.N0336.d030744 θ
    have hb : 0≤_root_.GD.N0082.N0336.d030743 θ*(1+_root_.GD.N0082.N0334.d008258 id t) :=
      mul_nonneg hp.le (by linarith [_root_.GD.N0082.N0334.d008268 id t])
    have hr := (ENNReal.ofReal_le_ofReal_iff hb).mp h
    nlinarith
  have hae : H =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] id := by
    apply _root_.GD.N0149.N0431.d014486 H hHm
    intro t ht
    rw [_root_.GD.N0149.N0436.d030846 H hHm (fun u _ => hHI u) ht,
      _root_.GD.N0149.N0436.d030846 id measurable_id (fun _ hu => ⟨hu.1.le,hu.2.le⟩) ht]
    exact ENNReal.ofReal_le_ofReal (hE t ht)
  refine ⟨hae,fun θ => ?_⟩
  have he : _root_.GD.N0082.N0334.d008258 H (_root_.GD.N0082.N0336.d030741 θ)=_root_.GD.N0082.N0334.d008258 id (_root_.GD.N0082.N0336.d030741 θ) := by
    apply integral_congr_ae
    filter_upwards [hae] with u hu
    rw [hu]
  rw [_root_.GD.N0082.N0336.d030746 H hHm hHI,he,_root_.GD.N0082.N0336.d030750]

theorem d030848 :
    ¬∃ H : ℝ → ℝ, Measurable H ∧ (∀ u, H u ∈ Icc (0 : ℝ) 1) ∧
      (∀ θ : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H)≤
        _root_.GD.N0232.N0720.N1066.d014320 3 3 (by omega) (by omega) θ) ∧
      ∃ θ : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H)<
        _root_.GD.N0232.N0720.N1066.d014320 3 3 (by omega) (by omega) θ := by
  rintro ⟨H,hHm,hHI,hdom,θ,hstrict⟩
  rw [(_root_.GD.N0149.N0436.d030847 H hHm hHI hdom).2 θ] at hstrict
  exact hstrict.false

end
end GD.N0149.N0436

#print axioms _root_.GD.N0149.N0436.d030845
#print axioms _root_.GD.N0149.N0436.d030847
#print axioms _root_.GD.N0149.N0436.d030848
