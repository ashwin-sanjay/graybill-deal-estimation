import GD.Module1218
import GD.Module0668
import GD.Module1226
import GD.Module1263
import GD.Module0791

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace GD.N0213.N0476

noncomputable section

open _root_.GD.N0232.N0719.N0977
open _root_.GD.N0232.N0719.N0976
open _root_.GD.N0232.N0719.N0985
open _root_.GD.N0232.N0720.N1341
open _root_.GD.N0232.N0720.N1316
open _root_.GD.N0232.N0720.N1314
open _root_.GD.N0232.N0720.N1377
open _root_.GD.N0232.N0720.N1326 (d019884)
open _root_.GD.N0230.N0615
open _root_.GD.N0213.N0479

variable {d : ℕ}

def d020406 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) (u : _root_.GD.N0232.N0720.N1341.d004415 d) : ℝ :=
  _root_.GD.N0232.N0719.N0976.d019748 ref u (h u)

def d020407 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) : C(_root_.GD.N0232.N0720.N1341.d004415 d, ℝ) where
  toFun u := 1 / Real.sqrt (_root_.GD.N0232.N0719.N0976.d019735 ref u)
  continuous_toFun := continuous_const.div
    (Real.continuous_sqrt.comp (_root_.GD.N0232.N0719.N0976.d019742 ref).continuous)
    (fun u => (Real.sqrt_pos.mpr (_root_.GD.N0232.N0719.N0976.d019736 ref u)).ne')

theorem d020408 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    Measurable (_root_.GD.N0213.N0476.d020406 ref h) := by
  unfold _root_.GD.N0213.N0476.d020406 _root_.GD.N0232.N0719.N0976.d019748
  exact (_root_.GD.N0232.N0719.N0976.d019741 ref).continuous.measurable.add
    ((Lp.stronglyMeasurable h).measurable.div
      (Real.continuous_sqrt.comp (_root_.GD.N0232.N0719.N0976.d019742 ref).continuous).measurable)

theorem d020409 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    MemLp (_root_.GD.N0213.N0476.d020406 ref h) 2 (_root_.GD.N0232.N0720.N1341.d004416 d) := by
  have hc := ContinuousMap.memLp (p := 2) (μ := _root_.GD.N0232.N0720.N1341.d004416 d) ℝ (_root_.GD.N0232.N0719.N0976.d019741 ref)
  have hi := ContinuousMap.memLp (p := ∞) (μ := _root_.GD.N0232.N0720.N1341.d004416 d) ℝ (_root_.GD.N0213.N0476.d020407 ref)
  have hm : MemLp (fun u => h u * _root_.GD.N0213.N0476.d020407 ref u) 2 (_root_.GD.N0232.N0720.N1341.d004416 d) :=
    by simpa only [mul_comm] using (Lp.memLp h).mul' hi
  convert hc.add hm using 1
  funext u
  simp [_root_.GD.N0213.N0476.d020406, _root_.GD.N0232.N0719.N0976.d019748, _root_.GD.N0213.N0476.d020407, div_eq_mul_inv, _root_.GD.N0232.N0719.N0976.d019741]

def d020410 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) (z : _root_.GD.N0232.N0719.N0977.d009764 d) : ℝ :=
  ((_root_.GD.N0232.N0719.N0977.d009768 d).symm z).1 +
    _root_.GD.N0232.N0720.N1341.d004418 (_root_.GD.N0213.N0476.d020406 ref h) ((_root_.GD.N0232.N0719.N0977.d009768 d).symm z).2

theorem d020411 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    Measurable (_root_.GD.N0213.N0476.d020410 ref h) :=
  (_root_.GD.N0232.N0719.N0977.d009768 d).symm.measurable.fst.add
    ((_root_.GD.N0232.N0720.N1326.d019884 (_root_.GD.N0213.N0476.d020408 ref h)).comp
      (_root_.GD.N0232.N0719.N0977.d009768 d).symm.measurable.snd)

theorem d020412 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d)
    (c : ℝ) (v : _root_.GD.N0232.N0719.N0977.d009765 d) :
    _root_.GD.N0213.N0476.d020410 ref h (_root_.GD.N0232.N0719.N0977.d009768 d (c, v)) =
      c + _root_.GD.N0232.N0720.N1341.d004418 (_root_.GD.N0213.N0476.d020406 ref h) v := by
  simp [_root_.GD.N0213.N0476.d020410]

theorem d020413 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    _root_.GD.N0232.N0719.N0977.d009783 d (_root_.GD.N0213.N0476.d020410 ref h) := by
  intro c a ha z
  obtain ⟨p, rfl⟩ := (_root_.GD.N0232.N0719.N0977.d009768 d).surjective z
  rw [_root_.GD.N0213.N0479.d009787, _root_.GD.N0213.N0476.d020412, _root_.GD.N0213.N0476.d020412,
    _root_.GD.N0232.N0720.N1341.d004419 (_root_.GD.N0213.N0476.d020406 ref h) a ha]
  simp only [smul_eq_mul]
  ring

theorem d020414 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) (u : _root_.GD.N0232.N0720.N1341.d004415 d) :
    _root_.GD.N0213.N0476.d020410 ref h (_root_.GD.N0232.N0719.N0977.d009773 d u) = _root_.GD.N0232.N0719.N0976.d019748 ref u (h u) := by
  have hu : _root_.GD.N0232.N0719.N0977.d009773 d u = _root_.GD.N0232.N0719.N0977.d009768 d (0, (u : _root_.GD.N0232.N0719.N0977.d009765 d)) := by
    simp [_root_.GD.N0232.N0719.N0977.d009769, _root_.GD.N0232.N0719.N0977.d009773]
  rw [hu, _root_.GD.N0213.N0476.d020412, _root_.GD.N0232.N0720.N1341.d004420, zero_add]
  rfl

theorem d020415 (tau : _root_.GD.N0232.N0719.N0976.d019733 d) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ u : _root_.GD.N0232.N0720.N1341.d004415 d, delta ≤ _root_.GD.N0232.N0719.N0977.d009778 d tau.1 u := by
  obtain ⟨delta, hdelta, hbound⟩ := isCompact_univ.exists_forall_le'
    (_root_.GD.N0232.N0719.N0976.d019739.comp (continuous_const.prodMk continuous_id)).continuousOn
    (fun u _ => _root_.GD.N0232.N0719.N0977.d009780 d tau.1 tau.2 u)
  exact ⟨delta, hdelta, fun u => hbound u (mem_univ u)⟩

theorem d020416 {v : ℝ} (hv : 0 < v) (a h m : ℝ) :
    Integrable (fun c : ℝ => (c + a * h) ^ 2 *
      Real.exp (-((c + a * m) ^ 2) / (2 * v))) := by
  let b : ℝ := 1 / (2 * v)
  have hb : 0 < b := by dsimp [b]; positivity
  have htwo : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-b * x ^ 2)) := by
    simpa only [Real.rpow_two] using integrable_rpow_mul_exp_neg_mul_sq hb
      (by norm_num : (-1 : ℝ) < 2)
  have hg : Integrable (fun x : ℝ => (x + a * (h - m)) ^ 2 * Real.exp (-b * x ^ 2)) := by
    apply ((htwo.add ((integrable_mul_exp_neg_mul_sq hb).const_mul (2 * a * (h - m)))).add
      ((integrable_exp_neg_mul_sq hb).const_mul ((a * (h - m)) ^ 2))).congr
    apply ae_of_all
    intro x
    dsimp
    ring
  have hs := (measurePreserving_add_right (volume : Measure ℝ) (a * m)).integrable_comp_of_integrable hg
  apply hs.congr
  apply ae_of_all
  intro c
  dsimp only [Function.comp_def, b]
  congr 1
  · congr 1
    ring
  · congr 1
    ring

def d020417 (tau : _root_.GD.N0232.N0719.N0976.d019733 d) (f : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ) (z : _root_.GD.N0232.N0719.N0977.d009764 d) : ℝ :=
  f z ^ 2 * Real.exp (-_root_.GD.N0232.N0719.N0977.d009777 d tau.1 z)

theorem d020418 (tau : _root_.GD.N0232.N0719.N0976.d019733 d) (f : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ) (z : _root_.GD.N0232.N0719.N0977.d009764 d) :
    0 ≤ _root_.GD.N0213.N0476.d020417 tau f z := mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem d020419 (tau : _root_.GD.N0232.N0719.N0976.d019733 d) (f : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ) (hf : Measurable f) :
    Measurable (_root_.GD.N0213.N0476.d020417 tau f) := by
  unfold _root_.GD.N0213.N0476.d020417 _root_.GD.N0232.N0719.N0977.d009777
  fun_prop

theorem d020420 (tau : _root_.GD.N0232.N0719.N0976.d019733 d) (f : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ)
    (haff : _root_.GD.N0232.N0719.N0977.d009783 d f) (u : _root_.GD.N0232.N0720.N1341.d004415 d) (a : ℝ) (ha : 0 < a) :
    (∫ c : ℝ, _root_.GD.N0213.N0476.d020417 tau f (_root_.GD.N0232.N0719.N0977.d009768 d (c, a • (u : _root_.GD.N0232.N0719.N0977.d009765 d)))) =
      Real.exp (-_root_.GD.N0232.N0719.N0977.d009778 d tau.1 u * a ^ 2) *
        (Real.sqrt (2 * Real.pi * (1 / _root_.GD.N0230.N0615.d000151 tau.1)) *
          (1 / _root_.GD.N0230.N0615.d000151 tau.1 + a ^ 2 * (f (_root_.GD.N0232.N0719.N0977.d009773 d u) - _root_.GD.N0232.N0719.N0976.d019734 tau u) ^ 2)) := by
  simp_rw [_root_.GD.N0213.N0476.d020417, _root_.GD.N0232.N0719.N0977.d009784 d tau.1
    (_root_.GD.N0232.N0719.N0977.d009779 d tau.1 tau.2) f haff u _ ha]
  rw [integral_const_mul, _root_.GD.N0232.N0719.N0985.d009753
    (by have := _root_.GD.N0232.N0719.N0977.d009779 d tau.1 tau.2; positivity)]
  rfl

theorem d020421 (tau : _root_.GD.N0232.N0719.N0976.d019733 d) (f : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ)
    (haff : _root_.GD.N0232.N0719.N0977.d009783 d f) (u : _root_.GD.N0232.N0720.N1341.d004415 d) (a : ℝ) (ha : 0 < a) :
    Integrable (fun c : ℝ => _root_.GD.N0213.N0476.d020417 tau f (_root_.GD.N0232.N0719.N0977.d009768 d (c, a • (u : _root_.GD.N0232.N0719.N0977.d009765 d)))) := by
  have h := (_root_.GD.N0213.N0476.d020416
    (by have := _root_.GD.N0232.N0719.N0977.d009779 d tau.1 tau.2; positivity : 0 < 1 / _root_.GD.N0230.N0615.d000151 tau.1)
    a (f (_root_.GD.N0232.N0719.N0977.d009773 d u)) (_root_.GD.N0232.N0719.N0976.d019734 tau u)).const_mul
      (Real.exp (-_root_.GD.N0232.N0719.N0977.d009778 d tau.1 u * a ^ 2))
  convert h using 1
  funext c
  exact _root_.GD.N0232.N0719.N0977.d009784 d tau.1 (_root_.GD.N0232.N0719.N0977.d009779 d tau.1 tau.2) f haff u c ha

theorem d020422 (tau : _root_.GD.N0232.N0719.N0976.d019733 d) (f : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ)
    (hf : Measurable f) (haff : _root_.GD.N0232.N0719.N0977.d009783 d f)
    (hshape : MemLp (fun u : _root_.GD.N0232.N0720.N1341.d004415 d => f (_root_.GD.N0232.N0719.N0977.d009773 d u)) 2 (_root_.GD.N0232.N0720.N1341.d004416 d)) :
    Integrable (_root_.GD.N0213.N0476.d020417 tau f) := by
  have hchart : Measurable (fun p : ℝ × _root_.GD.N0232.N0719.N0977.d009765 d => _root_.GD.N0213.N0476.d020417 tau f (_root_.GD.N0232.N0719.N0977.d009768 d p)) :=
    (_root_.GD.N0213.N0476.d020419 tau f hf).comp (_root_.GD.N0232.N0719.N0977.d009768 d).measurable
  apply (_root_.GD.N0232.N0719.N0977.d009772 d _).mp
  rw [Measure.volume_eq_prod]
  apply (integrable_prod_iff' hchart.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [(volume : Measure (_root_.GD.N0232.N0719.N0977.d009765 d)).ae_ne 0] with v hv
    let x : ({0}ᶜ : Set (_root_.GD.N0232.N0719.N0977.d009765 d)) := ⟨v, hv⟩
    let p := homeomorphUnitSphereProd (_root_.GD.N0232.N0719.N0977.d009765 d) x
    have hx : v = p.2.1 • (p.1 : _root_.GD.N0232.N0719.N0977.d009765 d) := by
      have hh := congrArg (fun z : ({0}ᶜ : Set (_root_.GD.N0232.N0719.N0977.d009765 d)) => z.1)
        ((homeomorphUnitSphereProd (_root_.GD.N0232.N0719.N0977.d009765 d)).symm_apply_apply x)
      simpa only [homeomorphUnitSphereProd_symm_apply_coe] using hh.symm
    rw [hx]
    exact _root_.GD.N0213.N0476.d020421 tau f haff p.1 p.2.1 p.2.2
  · rw [_root_.GD.N0232.N0720.N1341.d004423]
    obtain ⟨delta, hdelta, hbound⟩ := _root_.GD.N0213.N0476.d020415 tau
    let S := Real.sqrt (2 * Real.pi * (1 / _root_.GD.N0230.N0615.d000151 tau.1))
    let V := 1 / _root_.GD.N0230.N0615.d000151 tau.1
    have hV : 0 < V := by dsimp [V]; exact one_div_pos.mpr (_root_.GD.N0232.N0719.N0977.d009779 d tau.1 tau.2)
    have hS : 0 ≤ S := Real.sqrt_nonneg _
    have hzero : Integrable (fun r : Ioi (0 : ℝ) => Real.exp (-delta * r.1 ^ 2))
        (Measure.volumeIoiPow d) := by
      simpa [_root_.GD.N0232.N0720.N1377.d002851, show -(2 * delta) / 2 = -delta by ring, neg_mul] using (_root_.GD.N0232.N0720.N1316.d004460 (k := d) 0
        (show 0 < 2 * delta by positivity) 0)
    have htwo : Integrable (fun r : Ioi (0 : ℝ) => r.1 ^ 2 * Real.exp (-delta * r.1 ^ 2))
        (Measure.volumeIoiPow d) := by
      simpa [_root_.GD.N0232.N0720.N1377.d002851, show -(2 * delta) / 2 = -delta by ring, neg_mul] using (_root_.GD.N0232.N0720.N1316.d004460 (k := d) 2
        (show 0 < 2 * delta by positivity) 0)
    have hsquare : Integrable (fun u : _root_.GD.N0232.N0720.N1341.d004415 d => (f (_root_.GD.N0232.N0719.N0977.d009773 d u) - _root_.GD.N0232.N0719.N0976.d019734 tau u) ^ 2)
        (_root_.GD.N0232.N0720.N1341.d004416 d) := by
      exact (hshape.sub (ContinuousMap.memLp (p := 2) (μ := _root_.GD.N0232.N0720.N1341.d004416 d) ℝ (_root_.GD.N0232.N0719.N0976.d019741 tau))).integrable_sq
    have hmajor : Integrable (fun p : _root_.GD.N0232.N0720.N1341.d004415 d × Ioi (0 : ℝ) => S *
        (V * Real.exp (-delta * p.2.1 ^ 2) +
          (f (_root_.GD.N0232.N0719.N0977.d009773 d p.1) - _root_.GD.N0232.N0719.N0976.d019734 tau p.1) ^ 2 *
            (p.2.1 ^ 2 * Real.exp (-delta * p.2.1 ^ 2))))
        ((_root_.GD.N0232.N0720.N1341.d004416 d).prod (Measure.volumeIoiPow d)) :=
      (((integrable_const V).mul_prod hzero).add (hsquare.mul_prod htwo)).const_mul S
    have heq (p : _root_.GD.N0232.N0720.N1341.d004415 d × Ioi (0 : ℝ)) :
        (∫ c : ℝ, ‖_root_.GD.N0213.N0476.d020417 tau f (_root_.GD.N0232.N0719.N0977.d009768 d (c, p.2.1 • (p.1 : _root_.GD.N0232.N0719.N0977.d009765 d)))‖) =
          Real.exp (-_root_.GD.N0232.N0719.N0977.d009778 d tau.1 p.1 * p.2.1 ^ 2) *
            (S * (V + p.2.1 ^ 2 * (f (_root_.GD.N0232.N0719.N0977.d009773 d p.1) - _root_.GD.N0232.N0719.N0976.d019734 tau p.1) ^ 2)) := by
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0213.N0476.d020418 tau f _)]
      exact _root_.GD.N0213.N0476.d020420 tau f haff p.1 p.2.1 p.2.2
    simp_rw [heq]
    apply hmajor.mono'
    · have hfm : Measurable (fun u : _root_.GD.N0232.N0720.N1341.d004415 d => f (_root_.GD.N0232.N0719.N0977.d009773 d u)) :=
        hf.comp _root_.GD.N0232.N0719.N0976.d019737.measurable
      have hcenter : Measurable (_root_.GD.N0232.N0719.N0976.d019734 tau) := (_root_.GD.N0232.N0719.N0976.d019741 tau).continuous.measurable
      have henergy : Measurable (_root_.GD.N0232.N0719.N0977.d009778 d tau.1) :=
        (_root_.GD.N0232.N0719.N0976.d019739.comp (continuous_const.prodMk continuous_id)).measurable
      exact (show Measurable (fun p : _root_.GD.N0232.N0720.N1341.d004415 d × Ioi (0 : ℝ) =>
        Real.exp (-_root_.GD.N0232.N0719.N0977.d009778 d tau.1 p.1 * p.2.1 ^ 2) *
          (S * (V + p.2.1 ^ 2 * (f (_root_.GD.N0232.N0719.N0977.d009773 d p.1) - _root_.GD.N0232.N0719.N0976.d019734 tau p.1) ^ 2))) by
            fun_prop).aestronglyMeasurable
    · apply ae_of_all
      intro p
      have hexp : Real.exp (-_root_.GD.N0232.N0719.N0977.d009778 d tau.1 p.1 * p.2.1 ^ 2) ≤
          Real.exp (-delta * p.2.1 ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right (hbound p.1) (sq_nonneg p.2.1)]
      have hcoef : 0 ≤ S * (V + p.2.1 ^ 2 * (f (_root_.GD.N0232.N0719.N0977.d009773 d p.1) - _root_.GD.N0232.N0719.N0976.d019734 tau p.1) ^ 2) :=
        mul_nonneg hS (add_nonneg hV.le (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hcoef)]
      calc
        _ ≤ Real.exp (-delta * p.2.1 ^ 2) *
            (S * (V + p.2.1 ^ 2 * (f (_root_.GD.N0232.N0719.N0977.d009773 d p.1) - _root_.GD.N0232.N0719.N0976.d019734 tau p.1) ^ 2)) :=
          mul_le_mul_of_nonneg_right hexp hcoef
        _ = _ := by ring

theorem d020423 (ref tau : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    Integrable (_root_.GD.N0213.N0476.d020417 tau (_root_.GD.N0213.N0476.d020410 ref h)) := by
  apply _root_.GD.N0213.N0476.d020422 tau (_root_.GD.N0213.N0476.d020410 ref h)
    (_root_.GD.N0213.N0476.d020411 ref h) (_root_.GD.N0213.N0476.d020413 ref h)
  apply (memLp_congr_ae ?_).2 (_root_.GD.N0213.N0476.d020409 ref h)
  exact ae_of_all _ (_root_.GD.N0213.N0476.d020414 ref h)

def d020424 (ref tau : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) (u : _root_.GD.N0232.N0720.N1341.d004415 d) : ℝ :=
  _root_.GD.N0232.N0719.N0976.d019745 ref tau u * h u ^ 2 - 2 * _root_.GD.N0232.N0719.N0976.d019746 ref tau u * h u

theorem d020425 (ref tau : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    Integrable (_root_.GD.N0213.N0476.d020424 ref tau h) (_root_.GD.N0232.N0720.N1341.d004416 d) := by
  have ha := (Lp.memLp h).integrable_sq.mul_of_top_left
    (ContinuousMap.memLp (p := ∞) (μ := _root_.GD.N0232.N0720.N1341.d004416 d) ℝ (_root_.GD.N0232.N0719.N0976.d019745 ref tau))
  have hb := (Lp.memLp h).integrable_mul
    (ContinuousMap.memLp (p := 2) (μ := _root_.GD.N0232.N0720.N1341.d004416 d) ℝ (_root_.GD.N0232.N0719.N0976.d019746 ref tau))
  convert ha.sub (hb.const_mul 2) using 1
  funext u
  dsimp [_root_.GD.N0213.N0476.d020424]
  ring

theorem d020426 (ref tau : _root_.GD.N0232.N0719.N0976.d019733 d) (h : _root_.GD.N0232.N0720.N1341.d004417 d) :
    _root_.GD.N0232.N0719.N0976.d019747 ref tau h = ∫ u, _root_.GD.N0213.N0476.d020424 ref tau h u ∂_root_.GD.N0232.N0720.N1341.d004416 d := by
  have ha := (Lp.memLp h).integrable_sq.mul_of_top_left
    (ContinuousMap.memLp (p := ∞) (μ := _root_.GD.N0232.N0720.N1341.d004416 d) ℝ (_root_.GD.N0232.N0719.N0976.d019745 ref tau))
  have hb := (Lp.memLp h).integrable_mul
    (ContinuousMap.memLp (p := 2) (μ := _root_.GD.N0232.N0720.N1341.d004416 d) ℝ (_root_.GD.N0232.N0719.N0976.d019746 ref tau))
  change Integrable (fun u => h u ^ 2 * _root_.GD.N0232.N0719.N0976.d019745 ref tau u) (_root_.GD.N0232.N0720.N1341.d004416 d) at ha
  change Integrable (fun u => h u * _root_.GD.N0232.N0719.N0976.d019746 ref tau u) (_root_.GD.N0232.N0720.N1341.d004416 d) at hb
  rw [_root_.GD.N0232.N0719.N0976.d019747, _root_.GD.N0232.N0720.N1314.d019689, _root_.GD.N0232.N0720.N1316.d004476, _root_.GD.N0232.N0720.N1316.d004477,
    ← integral_const_mul, ← integral_sub ha (hb.const_mul 2)]
  apply integral_congr_ae
  exact ae_of_all _ (fun u => by dsimp [_root_.GD.N0213.N0476.d020424]; ring)

def d020427 (tau : _root_.GD.N0232.N0719.N0976.d019733 d) (f : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ) (u : _root_.GD.N0232.N0720.N1341.d004415 d) : ℝ :=
  Real.sqrt (2 * Real.pi * (1 / _root_.GD.N0230.N0615.d000151 tau.1)) *
    ((1 / _root_.GD.N0230.N0615.d000151 tau.1) * _root_.GD.N0232.N0719.N0985.d009755 (d : ℝ) (_root_.GD.N0232.N0719.N0977.d009778 d tau.1 u) +
      (f (_root_.GD.N0232.N0719.N0977.d009773 d u) - _root_.GD.N0232.N0719.N0976.d019734 tau u) ^ 2 *
        _root_.GD.N0232.N0719.N0985.d009755 ((d : ℝ) + 2) (_root_.GD.N0232.N0719.N0977.d009778 d tau.1 u))

theorem d020428 (tau : _root_.GD.N0232.N0719.N0976.d019733 d) (f : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ)
    (haff : _root_.GD.N0232.N0719.N0977.d009783 d f) (u : _root_.GD.N0232.N0720.N1341.d004415 d) :
    (∫ r : Ioi (0 : ℝ), (∫ c : ℝ,
      _root_.GD.N0213.N0476.d020417 tau f (_root_.GD.N0232.N0719.N0977.d009768 d (c, r.1 • (u : _root_.GD.N0232.N0719.N0977.d009765 d))))
        ∂Measure.volumeIoiPow d) = _root_.GD.N0213.N0476.d020427 tau f u := by
  have hV : 0 < 1 / _root_.GD.N0230.N0615.d000151 tau.1 := one_div_pos.mpr (_root_.GD.N0232.N0719.N0977.d009779 d tau.1 tau.2)
  have hD : 1 < (d : ℝ) + 2 := by have := Nat.cast_nonneg (α := ℝ) d; linarith
  have ho := _root_.GD.N0232.N0719.N0985.d009757 hD hV (_root_.GD.N0232.N0719.N0977.d009780 d tau.1 tau.2 u)
    (f (_root_.GD.N0232.N0719.N0977.d009773 d u)) (_root_.GD.N0232.N0719.N0976.d019734 tau u)
  rw [show (d : ℝ) + 2 - 2 = d by ring] at ho
  change _root_.GD.N0232.N0719.N0985.d009756 ((d : ℝ) + 2) (1 / _root_.GD.N0230.N0615.d000151 tau.1)
    (_root_.GD.N0232.N0719.N0977.d009778 d tau.1 u) (f (_root_.GD.N0232.N0719.N0977.d009773 d u)) (_root_.GD.N0232.N0719.N0976.d019734 tau u) = _root_.GD.N0213.N0476.d020427 tau f u at ho
  rw [← ho, _root_.GD.N0232.N0720.N1341.d004424 (f := fun r : ℝ => ∫ c : ℝ,
    _root_.GD.N0213.N0476.d020417 tau f (_root_.GD.N0232.N0719.N0977.d009768 d (c, r • (u : _root_.GD.N0232.N0719.N0977.d009765 d))))]
  unfold _root_.GD.N0232.N0719.N0985.d009756
  apply setIntegral_congr_fun measurableSet_Ioi
  intro a ha
  dsimp only
  rw [_root_.GD.N0213.N0476.d020420 tau f haff u a ha,
    _root_.GD.N0232.N0719.N0985.d009753 hV,
    show (d : ℝ) + 2 - 2 = d by ring, Real.rpow_natCast]
  ring

theorem d020429 (tau : _root_.GD.N0232.N0719.N0976.d019733 d) (f : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ)
    (haff : _root_.GD.N0232.N0719.N0977.d009783 d f) (hint : Integrable (_root_.GD.N0213.N0476.d020417 tau f)) :
    Integrable (_root_.GD.N0213.N0476.d020427 tau f) (_root_.GD.N0232.N0720.N1341.d004416 d) := by
  have hchart := (_root_.GD.N0232.N0719.N0977.d009772 d (_root_.GD.N0213.N0476.d020417 tau f)).mpr hint
  have hv : Integrable (fun v : _root_.GD.N0232.N0719.N0977.d009765 d => ∫ c : ℝ,
      _root_.GD.N0213.N0476.d020417 tau f (_root_.GD.N0232.N0719.N0977.d009768 d (c, v))) := hchart.integral_prod_right
  have hu := ((_root_.GD.N0232.N0720.N1341.d004423 _).mp hv).integral_prod_left
  apply hu.congr
  exact ae_of_all _ (_root_.GD.N0213.N0476.d020428 tau f haff)

def d020430 (tau : _root_.GD.N0232.N0719.N0976.d019733 d) (f : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ) : ℝ := ∫ z, _root_.GD.N0213.N0476.d020417 tau f z

theorem d020431 (tau : _root_.GD.N0232.N0719.N0976.d019733 d) (f : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ)
    (haff : _root_.GD.N0232.N0719.N0977.d009783 d f) (hint : Integrable (_root_.GD.N0213.N0476.d020417 tau f)) :
    _root_.GD.N0213.N0476.d020430 tau f = ∫ u, _root_.GD.N0213.N0476.d020427 tau f u ∂_root_.GD.N0232.N0720.N1341.d004416 d :=
  _root_.GD.N0232.N0719.N0977.d009786 d tau.1 tau.2 f haff hint

theorem d020432 (ref tau : _root_.GD.N0232.N0719.N0976.d019733 d) (h g : _root_.GD.N0232.N0720.N1341.d004417 d) (u : _root_.GD.N0232.N0720.N1341.d004415 d) :
    _root_.GD.N0213.N0476.d020427 tau (_root_.GD.N0213.N0476.d020410 ref h) u - _root_.GD.N0213.N0476.d020427 tau (_root_.GD.N0213.N0476.d020410 ref g) u =
      _root_.GD.N0213.N0476.d020424 ref tau h u - _root_.GD.N0213.N0476.d020424 ref tau g u := by
  have heq : _root_.GD.N0213.N0476.d020427 tau (_root_.GD.N0213.N0476.d020410 ref h) u - _root_.GD.N0213.N0476.d020427 tau (_root_.GD.N0213.N0476.d020410 ref g) u =
      _root_.GD.N0232.N0719.N0976.d019735 tau u * (_root_.GD.N0232.N0719.N0976.d019748 ref u (h u) - _root_.GD.N0232.N0719.N0976.d019734 tau u) ^ 2 -
        _root_.GD.N0232.N0719.N0976.d019735 tau u * (_root_.GD.N0232.N0719.N0976.d019748 ref u (g u) - _root_.GD.N0232.N0719.N0976.d019734 tau u) ^ 2 := by
    unfold _root_.GD.N0213.N0476.d020427 _root_.GD.N0232.N0719.N0976.d019735
    rw [_root_.GD.N0213.N0476.d020414, _root_.GD.N0213.N0476.d020414]
    ring
  rw [heq]
  have hh := _root_.GD.N0232.N0719.N0976.d019752 ref tau u (h u)
  have hg := _root_.GD.N0232.N0719.N0976.d019752 ref tau u (g u)
  unfold _root_.GD.N0213.N0476.d020424
  linarith

theorem d020433 (ref tau : _root_.GD.N0232.N0719.N0976.d019733 d) (h g : _root_.GD.N0232.N0720.N1341.d004417 d) :
    _root_.GD.N0213.N0476.d020430 tau (_root_.GD.N0213.N0476.d020410 ref h) - _root_.GD.N0213.N0476.d020430 tau (_root_.GD.N0213.N0476.d020410 ref g) =
      _root_.GD.N0232.N0719.N0976.d019747 ref tau h - _root_.GD.N0232.N0719.N0976.d019747 ref tau g := by
  have hh := _root_.GD.N0213.N0476.d020423 ref tau h
  have hg := _root_.GD.N0213.N0476.d020423 ref tau g
  rw [_root_.GD.N0213.N0476.d020431 tau _ (_root_.GD.N0213.N0476.d020413 ref h) hh,
    _root_.GD.N0213.N0476.d020431 tau _ (_root_.GD.N0213.N0476.d020413 ref g) hg,
    ← integral_sub (_root_.GD.N0213.N0476.d020429 tau _ (_root_.GD.N0213.N0476.d020413 ref h) hh)
      (_root_.GD.N0213.N0476.d020429 tau _ (_root_.GD.N0213.N0476.d020413 ref g) hg),
    _root_.GD.N0213.N0476.d020426, _root_.GD.N0213.N0476.d020426,
    ← integral_sub (_root_.GD.N0213.N0476.d020425 ref tau h)
      (_root_.GD.N0213.N0476.d020425 ref tau g)]
  apply integral_congr_ae
  exact ae_of_all _ (_root_.GD.N0213.N0476.d020432 ref tau h g)

def d020434 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (f : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ) (u : _root_.GD.N0232.N0720.N1341.d004415 d) : ℝ :=
  Real.sqrt (_root_.GD.N0232.N0719.N0976.d019735 ref u) * (f (_root_.GD.N0232.N0719.N0977.d009773 d u) - _root_.GD.N0232.N0719.N0976.d019734 ref u)

theorem d020435 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (f : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ) (hf : Measurable f) :
    Measurable (_root_.GD.N0213.N0476.d020434 ref f) :=
  (Real.continuous_sqrt.comp (_root_.GD.N0232.N0719.N0976.d019742 ref).continuous).measurable.mul
    ((hf.comp _root_.GD.N0232.N0719.N0976.d019737.measurable).sub (_root_.GD.N0232.N0719.N0976.d019741 ref).continuous.measurable)

theorem d020436 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (f : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ) (u : _root_.GD.N0232.N0720.N1341.d004415 d) :
    _root_.GD.N0213.N0476.d020434 ref f u ^ 2 ≤ _root_.GD.N0213.N0476.d020427 ref f u := by
  have hT := _root_.GD.N0232.N0719.N0977.d009779 d ref.1 ref.2
  have hE := _root_.GD.N0232.N0719.N0977.d009780 d ref.1 ref.2 u
  have hR : 0 < _root_.GD.N0232.N0719.N0985.d009755 (d : ℝ) (_root_.GD.N0232.N0719.N0977.d009778 d ref.1 u) :=
    _root_.GD.N0232.N0719.N0985.d009758 (by have := Nat.cast_nonneg (α := ℝ) d; linarith) hE
  have hs : _root_.GD.N0213.N0476.d020434 ref f u ^ 2 =
      _root_.GD.N0232.N0719.N0976.d019735 ref u * (f (_root_.GD.N0232.N0719.N0977.d009773 d u) - _root_.GD.N0232.N0719.N0976.d019734 ref u) ^ 2 := by
    rw [_root_.GD.N0213.N0476.d020434, mul_pow, Real.sq_sqrt (_root_.GD.N0232.N0719.N0976.d019736 ref u).le]
  rw [hs]
  unfold _root_.GD.N0213.N0476.d020427 _root_.GD.N0232.N0719.N0976.d019735
  have hbase : 0 ≤ Real.sqrt (2 * Real.pi * (1 / _root_.GD.N0230.N0615.d000151 ref.1)) *
      ((1 / _root_.GD.N0230.N0615.d000151 ref.1) * _root_.GD.N0232.N0719.N0985.d009755 (d : ℝ) (_root_.GD.N0232.N0719.N0977.d009778 d ref.1 u)) := by
    positivity
  nlinarith

theorem d020437 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (f : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ)
    (hf : Measurable f) (haff : _root_.GD.N0232.N0719.N0977.d009783 d f) (hint : Integrable (_root_.GD.N0213.N0476.d020417 ref f)) :
    MemLp (_root_.GD.N0213.N0476.d020434 ref f) 2 (_root_.GD.N0232.N0720.N1341.d004416 d) := by
  apply (memLp_two_iff_integrable_sq (_root_.GD.N0213.N0476.d020435 ref f hf).aestronglyMeasurable).mpr
  apply (_root_.GD.N0213.N0476.d020429 ref f haff hint).mono'
  · exact ((_root_.GD.N0213.N0476.d020435 ref f hf).pow_const 2).aestronglyMeasurable
  · apply ae_of_all
    intro u
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact _root_.GD.N0213.N0476.d020436 ref f u

theorem d020438 (ref : _root_.GD.N0232.N0719.N0976.d019733 d) (f : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ) (u : _root_.GD.N0232.N0720.N1341.d004415 d) :
    _root_.GD.N0232.N0719.N0976.d019748 ref u (_root_.GD.N0213.N0476.d020434 ref f u) = f (_root_.GD.N0232.N0719.N0977.d009773 d u) := by
  unfold _root_.GD.N0232.N0719.N0976.d019748 _root_.GD.N0213.N0476.d020434
  rw [mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr (_root_.GD.N0232.N0719.N0976.d019736 ref u)).ne']
  ring

theorem d020439 (ref : _root_.GD.N0232.N0719.N0976.d019733 d)
    (f : _root_.GD.N0232.N0719.N0977.d009764 d → ℝ) (hf : Measurable f) (haff : _root_.GD.N0232.N0719.N0977.d009783 d f)
    (hint : Integrable (_root_.GD.N0213.N0476.d020417 ref f)) :
    ∃ h : _root_.GD.N0232.N0720.N1341.d004417 d, _root_.GD.N0213.N0476.d020410 ref h =ᵐ[volume] f := by
  let hm := _root_.GD.N0213.N0476.d020437 ref f hf haff hint
  let h : _root_.GD.N0232.N0720.N1341.d004417 d := hm.toLp (_root_.GD.N0213.N0476.d020434 ref f)
  refine ⟨h, ?_⟩
  apply _root_.GD.N0213.N0479.d009790 (fun z => _root_.GD.N0213.N0476.d020410 ref h z = f z)
  · intro c a ha z
    rw [_root_.GD.N0213.N0476.d020413 ref h c a ha z, haff c a ha z]
    constructor <;> intro hh <;> nlinarith
  · filter_upwards [hm.coeFn_toLp] with u hu
    rw [_root_.GD.N0213.N0476.d020414, hu]
    exact _root_.GD.N0213.N0476.d020438 ref f u

end
end GD.N0213.N0476

#print axioms _root_.GD.N0213.N0476.d020408
#print axioms _root_.GD.N0213.N0476.d020409
#print axioms _root_.GD.N0213.N0476.d020411
#print axioms _root_.GD.N0213.N0476.d020412
#print axioms _root_.GD.N0213.N0476.d020413
#print axioms _root_.GD.N0213.N0476.d020414
#print axioms _root_.GD.N0213.N0476.d020415
#print axioms _root_.GD.N0213.N0476.d020416
#print axioms _root_.GD.N0213.N0476.d020418
#print axioms _root_.GD.N0213.N0476.d020419
#print axioms _root_.GD.N0213.N0476.d020420
#print axioms _root_.GD.N0213.N0476.d020421
#print axioms _root_.GD.N0213.N0476.d020422
#print axioms _root_.GD.N0213.N0476.d020423
#print axioms _root_.GD.N0213.N0476.d020425
#print axioms _root_.GD.N0213.N0476.d020426
#print axioms _root_.GD.N0213.N0476.d020428
#print axioms _root_.GD.N0213.N0476.d020429
#print axioms _root_.GD.N0213.N0476.d020431
#print axioms _root_.GD.N0213.N0476.d020432
#print axioms _root_.GD.N0213.N0476.d020433
#print axioms _root_.GD.N0213.N0476.d020435
#print axioms _root_.GD.N0213.N0476.d020436
#print axioms _root_.GD.N0213.N0476.d020437
#print axioms _root_.GD.N0213.N0476.d020438
#print axioms _root_.GD.N0213.N0476.d020439

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal BigOperators

namespace GD.N0213.N0481

noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0977 _root_.GD.N0232.N0719.N0997
open _root_.GD.N0232.N0719.N0986 _root_.GD.N0232.N0719.N0988
open _root_.GD.N0232.N0720.N1341 (d004416)
open _root_.GD.N0232.N0720.N1316
open _root_.GD.N0213.N0477
open _root_.GD.N0213.N0479
open _root_.GD.N0107

variable {k d : ℕ} (sizes : Fin k → ℕ)
  (hdim : (∑ i, sizes i) = (d + 1) + 1)

theorem d020440 (hn : ∀ i, 2 ≤ sizes i)
    (c a : ℝ) (z : _root_.GD.N0232.N0719.N0977.d009764 d) (i : Fin k) :
    _root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009774 d c a z)) i =
      a ^ 2 * _root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z) i := by
  rw [_root_.GD.N0232.N0719.N0986.d020364, _root_.GD.N0232.N0719.N0986.d020364]
  change _root_.GD.N0126.d006422
    (_root_.GD.N0107.d009018 (sizes i) c a (_root_.GD.N0213.N0477.d020379 sizes hdim z i)) / (2 * (sizes i : ℝ)) = _
  rw [_root_.GD.N0107.d009088 (by have := hn i; omega) c a]
  ring

theorem d020441 (hn : ∀ i, 2 ≤ sizes i) :
    ∀ᵐ z ∂(volume : Measure (_root_.GD.N0232.N0719.N0977.d009764 d)),
      ∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z) i := by
  let q := _root_.GD.N0232.N0719.N0988.d019778 k
  let theta : _root_.GD.N0232.N0719.N0859.d010809 k :=
    ⟨q.1, _root_.GD.N0232.N0719.N0997.d019811 q, _root_.GD.N0232.N0719.N0997.d019812 q⟩
  have hnormal : ∀ᵐ omega ∂_root_.GD.N0232.N0719.d009176 k sizes q.1 (_root_.GD.N0232.N0719.N0997.d019811 q),
      ∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes omega i := by
    have hh := ae_all_iff.mpr (fun i =>
      _root_.GD.N0232.N0719.N0832.d012011 k sizes hn theta i)
    filter_upwards [hh] with omega homega
    intro i
    rw [_root_.GD.N0232.N0719.N0986.d020364]
    apply div_pos (homega i)
    have hnpos : 0 < (sizes i : ℝ) := Nat.cast_pos.mpr (by have := hn i; omega)
    positivity
  let p := _root_.GD.N0232.N0719.N0988.d019779 (_root_.GD.N0232.N0719.N0997.d019806 sizes hdim) q
  let rho := fun x : _root_.GD.N0232.N0720.N1341.d004414 (d + 1) =>
    ENNReal.ofReal (_root_.GD.N0232.N0720.N1316.d004445 p x)
  have hrho : Measurable rho := by unfold rho _root_.GD.N0232.N0720.N1316.d004445; fun_prop
  have hrhopos : ∀ x, rho x ≠ 0 := by
    intro x
    exact (ENNReal.ofReal_pos.mpr (mul_pos (_root_.GD.N0232.N0720.N1316.d004446 p) (Real.exp_pos _))).ne'
  have hmp : MeasurePreserving (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim)
      (_root_.GD.N0232.N0719.d009176 k sizes q.1 (_root_.GD.N0232.N0719.N0997.d019811 q)) (volume.withDensity rho) :=
    ⟨(_root_.GD.N0232.N0719.N0997.d019807 sizes hdim).measurable, _root_.GD.N0232.N0719.N0997.d019814 sizes hdim q⟩
  have hflat := (MeasurePreserving.symm (_root_.GD.N0232.N0719.N0997.d019807 sizes hdim) hmp).quasiMeasurePreserving.ae hnormal
  have hac : (volume : Measure (_root_.GD.N0232.N0720.N1341.d004414 (d + 1))) ≪
      volume.withDensity rho := withDensity_absolutelyContinuous' hrho.aemeasurable (ae_of_all _ hrhopos)
  have hvol := hac.ae_le hflat
  have hraw := (PiLp.volume_preserving_toLp (Fin ((d + 1) + 1))).quasiMeasurePreserving.ae hvol
  exact hraw

theorem d020442 (hn : ∀ i, 2 ≤ sizes i) :
    ∀ᵐ u ∂_root_.GD.N0232.N0720.N1341.d004416 d,
      ∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim (_root_.GD.N0232.N0719.N0977.d009773 d u)) i := by
  apply _root_.GD.N0213.N0479.d009789
    (fun z => ∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes (_root_.GD.N0213.N0477.d020379 sizes hdim z) i)
  · intro c a ha z
    simp_rw [_root_.GD.N0213.N0481.d020440 sizes hdim hn c a z]
    exact forall_congr' (fun i => mul_pos_iff_of_pos_left (sq_pos_of_pos ha))
  · exact _root_.GD.N0213.N0481.d020441 sizes hdim hn

end
end GD.N0213.N0481

#print axioms _root_.GD.N0213.N0481.d020440
#print axioms _root_.GD.N0213.N0481.d020441
#print axioms _root_.GD.N0213.N0481.d020442
