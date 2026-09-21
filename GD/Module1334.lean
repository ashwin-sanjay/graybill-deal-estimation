import GD.Module1333
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0101.N0380
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1436


def d021698 (z : _root_.GD.N0232.N0720.N1436.d013217) : _root_.GD.N0232.N0720.N1436.d013217 :=
  (1 - z.1, z.2)



theorem d021699 (t : ℝ) (z : _root_.GD.N0232.N0720.N1436.d013217) :
    _root_.GD.N0232.N0720.N1436.d013273 2 2 (1 - t) z =
      _root_.GD.N0232.N0720.N1436.d013273 2 2 t (_root_.GD.N0101.N0380.d021698 z) := by
  rcases z with ⟨u, s⟩
  dsimp only [_root_.GD.N0101.N0380.d021698]
  have hp : _root_.GD.N0232.N0720.N1436.d013270 2 2 (1 - t) =
      _root_.GD.N0232.N0720.N1436.d013270 2 2 t := by
    unfold _root_.GD.N0232.N0720.N1436.d013270 _root_.GD.N0232.N0720.N1436.d013207 _root_.GD.N0232.N0720.N1436.d013208
    simp only [sub_sub_cancel]
    ring
  have hs : _root_.GD.N0232.N0720.N1436.d013269 2 2 (u, s) =
      _root_.GD.N0232.N0720.N1436.d013269 2 2 (1 - u, s) := by
    unfold _root_.GD.N0232.N0720.N1436.d013269 _root_.GD.N0232.N0720.N1436.d013207 _root_.GD.N0232.N0720.N1436.d013208
    dsimp only
    simp only [sub_sub_cancel]
    ring
  have hr : _root_.GD.N0232.N0720.N1436.d013268 2 2 (1 - t) (u, s) =
      _root_.GD.N0232.N0720.N1436.d013268 2 2 t (1 - u, s) := by
    unfold _root_.GD.N0232.N0720.N1436.d013268 _root_.GD.N0232.N0720.N1436.d013267
    dsimp only
    simp only [sub_sub_cancel]
    ring
  unfold _root_.GD.N0232.N0720.N1436.d013273
  rw [hp, hs, hr]


@[fun_prop]
theorem d021700 :
    Measurable (fun p : ℝ × _root_.GD.N0232.N0720.N1436.d013217 =>
      _root_.GD.N0232.N0720.N1436.d013273 2 2 p.1 p.2) := by
  unfold _root_.GD.N0232.N0720.N1436.d013273 _root_.GD.N0232.N0720.N1436.d013270 _root_.GD.N0232.N0720.N1436.d013269
    _root_.GD.N0232.N0720.N1436.d013268 _root_.GD.N0232.N0720.N1436.d013267
  fun_prop



theorem d021701
    (μ : Measure ℝ) [SFinite μ]
    (v : ℝ → ℝ) (hv : Measurable v)
    (q : ℝ → ℝ≥0∞) (hq : Measurable q)
    (F : ℝ → _root_.GD.N0232.N0720.N1436.d013217 → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F)) :
    (∫⁻ t, q t * (∫⁻ z, F t z ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 (v t)) ∂μ) =
      ∫⁻ z, ∫⁻ t,
        q t * ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 (v t) z) * F t z ∂μ
        ∂_root_.GD.N0232.N0720.N1436.d013288 := by
  letI : SFinite _root_.GD.N0232.N0720.N1436.d013288 := by
    unfold _root_.GD.N0232.N0720.N1436.d013288
    infer_instance
  let J : ℝ → _root_.GD.N0232.N0720.N1436.d013217 → ℝ≥0∞ := fun t z =>
    q t * ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 (v t) z) * F t z
  have hpdf : Measurable (fun p : ℝ × _root_.GD.N0232.N0720.N1436.d013217 =>
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 (v p.1) p.2)) :=
    (_root_.GD.N0101.N0380.d021700.comp
      ((hv.comp measurable_fst).prodMk measurable_snd)).ennreal_ofReal
  have hJ : Measurable (Function.uncurry J) :=
    ((hq.comp measurable_fst).mul hpdf).mul hF
  calc
    _ = ∫⁻ t, ∫⁻ z, J t z ∂_root_.GD.N0232.N0720.N1436.d013288 ∂μ := by
      apply lintegral_congr
      intro t
      have hFt : Measurable (F t) :=
        hF.comp (measurable_const.prodMk measurable_id)
      have hpt := (_root_.GD.N0232.N0720.N1436.d013279 2 2 (v t)).ennreal_ofReal
      rw [_root_.GD.N0232.N0720.N1436.d013289, lintegral_withDensity_eq_lintegral_mul _ hpt hFt]
      simpa only [J, Pi.mul_apply, mul_assoc] using
        (lintegral_const_mul (q t) (hpt.mul hFt)).symm
    _ = _ := lintegral_lintegral_swap hJ.aemeasurable



theorem d021702
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g) (a ε : ℝ) :
    (∫⁻ t in Ioo a ε, ENNReal.ofReal (t ^ (-(3 / 2 : ℝ))) *
      (∫⁻ z, ENNReal.ofReal ((g z - t) ^ 2) ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t)) =
      ∫⁻ z, (∫⁻ t in Ioo a ε,
        ENNReal.ofReal (t ^ (-(3 / 2 : ℝ))) *
          ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t z) *
          ENNReal.ofReal ((g z - t) ^ 2)) ∂_root_.GD.N0232.N0720.N1436.d013288 := by
  exact _root_.GD.N0101.N0380.d021701 (volume.restrict (Ioo a ε))
    id measurable_id (fun t => ENNReal.ofReal (t ^ (-(3 / 2 : ℝ)))) (by fun_prop)
    (fun t z => ENNReal.ofReal ((g z - t) ^ 2)) (by fun_prop)



theorem d021703
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g) (a ε : ℝ) :
    (∫⁻ t in Ioo a ε, ENNReal.ofReal (t ^ (-(3 / 2 : ℝ))) *
      (∫⁻ z, ENNReal.ofReal ((g z - (1 - t)) ^ 2)
        ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 (1 - t))) =
      ∫⁻ z, (∫⁻ t in Ioo a ε,
        ENNReal.ofReal (t ^ (-(3 / 2 : ℝ))) *
          ENNReal.ofReal (_root_.GD.N0232.N0720.N1436.d013273 2 2 t (_root_.GD.N0101.N0380.d021698 z)) *
          ENNReal.ofReal ((g z - (1 - t)) ^ 2)) ∂_root_.GD.N0232.N0720.N1436.d013288 := by
  have h := _root_.GD.N0101.N0380.d021701 (volume.restrict (Ioo a ε))
    (fun t => 1 - t) (by fun_prop)
    (fun t => ENNReal.ofReal (t ^ (-(3 / 2 : ℝ)))) (by fun_prop)
    (fun t z => ENNReal.ofReal ((g z - (1 - t)) ^ 2)) (by fun_prop)
  simpa only [_root_.GD.N0101.N0380.d021699] using h

end
end GD.N0101.N0380

#print axioms _root_.GD.N0101.N0380.d021699
#print axioms _root_.GD.N0101.N0380.d021700
#print axioms _root_.GD.N0101.N0380.d021701
#print axioms _root_.GD.N0101.N0380.d021702
#print axioms _root_.GD.N0101.N0380.d021703
