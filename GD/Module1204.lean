import GD.Module1203
import GD.Module1198
import GD.Module1084
import GD.Module0824
import GD.Module1181

set_option warningAsError true

























open MeasureTheory Set

namespace GD.N0232.N0720.N1149

noncomputable section

open _root_.GD.N0232.N0720.N1029
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1041
open _root_.GD.N0232.N0720.N1077
open _root_.GD.N0232.N0720.N1063
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1209
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1446
open _root_.GD.N0232.N0720.N1425
open _root_.GD.N0232.N0720.N1437
open _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0720.N1470
open _root_.GD.N0232.N0720.N1475
open _root_.GD.N0232.N0720.N1476
open _root_.GD.N0232.N0720.N1491
open _root_.GD.N0232.N0720.N1500
open _root_.GD.N0232.N0720.N1501
open _root_.GD.N0232.N0720.N1505
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0644
open _root_.GD.N0232.N0719.N0860
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229
open _root_.GD.N0232.N0719.N1010






theorem d019465
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hpFinite : _root_.GD.N0232.N0720.N1159.d014637 m n p)
    (hpAffine : _root_.GD.N0232.N0720.N1159.d014652 m n p)
    (hpSummary : _root_.GD.N0232.N0720.N1501.d016291 m n p = p) :
    ∃ repaired : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ,
      Measurable repaired ∧
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        (repaired ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta]
          fun omega ↦ p omega) ∧
      _root_.GD.N0232.N0719.N0860.d011447 repaired := by
  obtain ⟨value, hvalue, hrep⟩ :=
    _root_.GD.N0232.N0720.N1501.d016306 m n p
  rw [hpSummary] at hrep
  have hfixed : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      _root_.GD.N0232.N0720.N1159.d014642 m n g p hpFinite = p :=
    (_root_.GD.N0232.N0720.N1159.d014655 m n hm hn p hpFinite).2 hpAffine
  have hmem : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      MemLp (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p)) 2
        (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    intro g
    exact _root_.GD.N0232.N0720.N1159.d014641 m n g p hpFinite
  have hcovRaw : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦
          value (g • _root_.GD.N0232.N0720.N1467.d012542 m n omega)) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        fun omega ↦ g • value (_root_.GD.N0232.N0720.N1467.d012542 m n omega) := by
    have hdecisionCov := _root_.GD.N0232.N0720.N1214.d014270
      m n p hmem hfixed
    have hdecisionRep :
        _root_.GD.N0232.N0720.N1214.d014265 m n p =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
          value ∘ _root_.GD.N0232.N0720.N1467.d012542 m n :=
      (_root_.GD.N0232.N0720.N1214.d014267 m n p).trans hrep
    intro g
    have hdecisionRepAtG :=
      (_root_.GD.N0232.N0720.N1215.d014907 m n g).ae_eq_comp hdecisionRep
    filter_upwards [hdecisionRepAtG, hdecisionCov g, hdecisionRep] with
        omega hAtG hCov hAtOne
    simp only [Function.comp_apply] at hAtG hAtOne
    rw [_root_.GD.N0232.N0720.N1475.d018975 m n (by omega) (by omega) g omega] at hAtG
    calc
      value (g • _root_.GD.N0232.N0720.N1467.d012542 m n omega) =
          _root_.GD.N0232.N0720.N1214.d014265 m n p (g • omega) := hAtG.symm
      _ = g • _root_.GD.N0232.N0720.N1214.d014265 m n p omega := hCov
      _ = g • value (_root_.GD.N0232.N0720.N1467.d012542 m n omega) := congrArg (g • ·) hAtOne
  have hcovSummary :=
    _root_.GD.N0232.N0720.N1475.d018980
      m n value hvalue hcovRaw
  obtain ⟨repaired, hrepaired, hrepairedSummary, hequivariant⟩ :=
    _root_.GD.N0230.N0605.d000343
      (G := _root_.GD.N0232.N0719.N0946.d009229) (X := _root_.GD.N0232.N0719.N0900.d009096 2)
      (_root_.GD.N0232.N0720.N1475.d018976 m n) _root_.GD.N0232.N0719.N0946.d009229.d009254
      value _root_.GD.N0232.N0719.N0900.d009110 hvalue _root_.GD.N0232.N0719.N0900.d009121
      (_root_.GD.N0232.N0719.N1010.d011421 (by norm_num))
      hcovSummary _root_.GD.N0232.N0719.N0946.d009229.d009257
  have hrepairedRef :
      (repaired ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        value ∘ _root_.GD.N0232.N0720.N1467.d012542 m n := by
    have hset : MeasurableSet
        {summary : _root_.GD.N0232.N0719.N0900.d009096 2 | repaired summary = value summary} :=
      measurableSet_eq_fun hrepaired hvalue
    exact (ae_map_iff
      (_root_.GD.N0232.N0720.N1501.d016289 m n).aemeasurable hset).1
        hrepairedSummary
  refine ⟨repaired, hrepaired, ?_, ?_⟩
  · intro theta
    exact (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le
      (hrepairedRef.trans hrep.symm)
  · intro shift dilationFactor hdilation summary
    let g : _root_.GD.N0232.N0719.N0946.d009229 := ⟨shift, Real.log dilationFactor⟩
    have hg := hequivariant g summary
    simpa [g, _root_.GD.N0232.N0719.N0946.d009229.d009244, _root_.GD.N0232.N0719.N1010.d011416,
      _root_.GD.N0232.N0719.N0946.d009229.d009239, Real.exp_log hdilation] using hg





theorem d019466
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hpFinite : _root_.GD.N0232.N0720.N1159.d014637 m n p)
    (hpAffine : _root_.GD.N0232.N0720.N1159.d014652 m n p)
    (hpSummary : _root_.GD.N0232.N0720.N1501.d016291 m n p = p)
    (hpReflection : _root_.GD.N0232.N0720.N1446.d019032 m n p = p) :
    ∃ repaired : _root_.GD.N0232.N0719.N0900.d009096 2 → ℝ,
      Measurable repaired ∧
      (∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
        (repaired ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta]
          fun omega ↦ p omega) ∧
      _root_.GD.N0232.N0719.N0860.d011447 repaired ∧
      _root_.GD.N0232.N0720.N1209.d012478 repaired := by
  obtain ⟨value, hvalue, hrep, haffine⟩ :=
    _root_.GD.N0232.N0720.N1149.d019465
      m n hm hn p hpFinite hpAffine hpSummary
  let repaired := _root_.GD.N0232.N0720.N1476.d019361 value
  refine ⟨repaired,
    _root_.GD.N0232.N0720.N1476.d019362 value hvalue, ?_,
    _root_.GD.N0232.N0720.N1476.d019363 value haffine,
    _root_.GD.N0232.N0720.N1476.d019364 value⟩
  have hfixedAE :
      (fun omega ↦ -(p (_root_.GD.N0232.N0720.N1446.d019019 m n omega))) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        fun omega ↦ p omega := by
    have hcoe := _root_.GD.N0232.N0720.N1476.d019377 m n p
    rw [hpReflection] at hcoe
    exact hcoe.symm
  have href :
      (value ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        fun omega ↦ p omega := by
    simpa [_root_.GD.N0232.N0720.N1080.d014172] using hrep _root_.GD.N0232.N0720.N1080.d014169
  have hrefNeg :=
    (_root_.GD.N0232.N0720.N1446.d019031 m n).quasiMeasurePreserving.ae_eq_comp href
  have hvalueReflect :
      (fun omega ↦ -value (_root_.GD.N0232.N0720.N1476.d019350 (_root_.GD.N0232.N0720.N1467.d012542 m n omega))) =ᵐ[
        _root_.GD.N0232.N0720.N1080.d014172 m n] fun omega ↦ p omega := by
    filter_upwards [hrefNeg, hfixedAE] with omega hrepAtNeg hfix
    rw [← _root_.GD.N0232.N0720.N1476.d019375 m n (by omega) (by omega) omega]
    exact (congrArg Neg.neg hrepAtNeg).trans hfix
  have hrepairedRef :
      (repaired ∘ _root_.GD.N0232.N0720.N1467.d012542 m n) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        fun omega ↦ p omega := by
    filter_upwards [href, hvalueReflect] with omega hone hreflected
    change (value (_root_.GD.N0232.N0720.N1467.d012542 m n omega) -
      value (_root_.GD.N0232.N0720.N1476.d019350 (_root_.GD.N0232.N0720.N1467.d012542 m n omega))) / 2 = p omega
    have hone' : value (_root_.GD.N0232.N0720.N1467.d012542 m n omega) = p omega := by
      simpa only [Function.comp_apply] using hone
    rw [hone']
    linarith
  intro theta
  exact (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le hrepairedRef





theorem d019467
    (m n : ℕ)
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014652 m n p) :
    _root_.GD.N0232.N0720.N1159.d014652 m n
      (_root_.GD.N0232.N0720.N1446.d019032 m n p) := by
  obtain ⟨raw, hrawMeasurable, hrawClass, hrawEquivariant⟩ := hp
  let reflectedRaw : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
    fun omega ↦ -raw (_root_.GD.N0232.N0720.N1446.d019019 m n omega)
  refine ⟨reflectedRaw,
    hrawMeasurable.neg.comp (_root_.GD.N0232.N0720.N1446.d019021 m n), ?_, ?_⟩
  · intro theta
    have hrawCoe : raw =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1446.d019024 theta)]
        fun omega ↦ p omega :=
      (hrawClass (_root_.GD.N0232.N0720.N1446.d019024 theta)).trans
        ((_root_.GD.N0232.N0720.N1080.d014173 m n
          (_root_.GD.N0232.N0720.N1446.d019024 theta)).ae_le
            (_root_.GD.N0232.N0720.N1214.d014267 m n p))
    have hrawMap : raw =ᵐ[(_root_.GD.N0232.N0720.N1080.d014171 m n theta).map (_root_.GD.N0232.N0720.N1446.d019019 m n)]
        fun omega ↦ p omega := by
      rw [_root_.GD.N0232.N0720.N1446.d019030 m n theta]
      exact hrawCoe
    have hrawComp := MeasureTheory.ae_eq_comp
      (_root_.GD.N0232.N0720.N1446.d019021 m n).aemeasurable hrawMap
    have hreflectCoe :=
      (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le
        (_root_.GD.N0232.N0720.N1476.d019377 m n p)
    have hcanonical :=
      (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le
        (_root_.GD.N0232.N0720.N1214.d014267 m n (_root_.GD.N0232.N0720.N1446.d019032 m n p))
    filter_upwards [hrawComp, hreflectCoe, hcanonical] with
        omega hrawOmega hreflectOmega hcanonicalOmega
    simp only [Function.comp_apply] at hrawOmega
    change -raw (_root_.GD.N0232.N0720.N1446.d019019 m n omega) =
      _root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1446.d019032 m n p) omega
    calc
      -raw (_root_.GD.N0232.N0720.N1446.d019019 m n omega) =
          -p (_root_.GD.N0232.N0720.N1446.d019019 m n omega) := congrArg Neg.neg hrawOmega
      _ = (_root_.GD.N0232.N0720.N1446.d019032 m n p) omega := hreflectOmega.symm
      _ = _root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1446.d019032 m n p) omega :=
        hcanonicalOmega.symm
  · intro g omega
    let gr : _root_.GD.N0232.N0719.N0946.d009229 := ⟨-g.shift, g.logScale⟩
    have hgrDilation : gr.d009239 = g.d009239 := rfl
    have horbit : _root_.GD.N0232.N0720.N1446.d019019 m n (g • omega) =
        gr • _root_.GD.N0232.N0720.N1446.d019019 m n omega := by
      apply Prod.ext <;> funext i <;>
        simp [_root_.GD.N0232.N0720.N1446.d019019, _root_.GD.N0232.N0720.N1214.d014259,
          _root_.GD.N0107.d009024,
          _root_.GD.N0107.d009018, _root_.GD.N0232.N0719.N0946.d009229.d009239,
          gr] <;> ring
    change -raw (_root_.GD.N0232.N0720.N1446.d019019 m n (g • omega)) =
      g • (-raw (_root_.GD.N0232.N0720.N1446.d019019 m n omega))
    rw [horbit, hrawEquivariant gr]
    simp only [_root_.GD.N0232.N0719.N0946.d009229.d009244]
    rw [hgrDilation]
    change -(-g.shift + g.d009239 * raw (_root_.GD.N0232.N0720.N1446.d019019 m n omega)) =
      g.shift + g.d009239 * -raw (_root_.GD.N0232.N0720.N1446.d019019 m n omega)
    ring






theorem d019468
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1446.d019032 m n (_root_.GD.N0232.N0720.N1029.d015364 m n hm hn) =
      _root_.GD.N0232.N0720.N1029.d015364 m n hm hn := by
  let q := _root_.GD.N0232.N0720.N1029.d015364 m n hm hn
  let r := _root_.GD.N0232.N0720.N1446.d019032 m n q
  have hqAffine : _root_.GD.N0232.N0720.N1159.d014652 m n q :=
    _root_.GD.N0232.N0720.N1505.d018995
      m n hm hn
  have hrAffine : _root_.GD.N0232.N0720.N1159.d014652 m n r :=
    _root_.GD.N0232.N0720.N1149.d019467
      m n q hqAffine
  have hqFinite : _root_.GD.N0232.N0720.N1159.d014637 m n q :=
    _root_.GD.N0232.N0720.N1029.d015371 m n hm hn
  have hrFinite : _root_.GD.N0232.N0720.N1159.d014637 m n r := by
    intro theta
    rw [show _root_.GD.N0232.N0720.N1080.d014182 m n theta r = _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1446.d019024 theta) q by
      exact _root_.GD.N0232.N0720.N1446.d019037 m n theta q]
    exact hqFinite (_root_.GD.N0232.N0720.N1446.d019024 theta)
  have hrRisk : ∀ theta, _root_.GD.N0232.N0720.N1080.d014182 m n theta r = _root_.GD.N0232.N0720.N1080.d014182 m n theta q := by
    intro theta
    rw [show _root_.GD.N0232.N0720.N1080.d014182 m n theta r = _root_.GD.N0232.N0720.N1080.d014182 m n (_root_.GD.N0232.N0720.N1446.d019024 theta) q by
      exact _root_.GD.N0232.N0720.N1446.d019037 m n theta q]
    exact _root_.GD.N0232.N0720.N1446.d019039
      m n (_root_.GD.N0232.N0720.N1029.d015372 m n hm hn) theta
  have hrLower : r ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn := by
    intro theta
    rw [hrRisk theta]
    exact _root_.GD.N0232.N0720.N1029.d015366 m n hm hn theta
  have hrFixed : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g r hrLower = r := by
    intro g
    rw [_root_.GD.N0232.N0720.N1077.d018051
      m n hm hn g r hrLower hrFinite]
    exact (_root_.GD.N0232.N0720.N1159.d014655
      m n hm hn r hrFinite).2 hrAffine g
  have hrLocus : r ∈ _root_.GD.N0232.N0720.N1029.d015357 m n hm hn :=
    (_root_.GD.N0232.N0720.N1029.d015358 m n hm hn r).2 ⟨hrLower, hrFixed⟩
  have hrMin :
      ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - r‖ =
        ⨅ w : _root_.GD.N0232.N0720.N1029.d015357 m n hm hn,
          ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - w‖ := by
    calc
      ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - r‖ = ‖r‖ := by simp
      _ = ‖q‖ := _root_.GD.N0232.N0720.N1446.d019036 m n q
      _ = ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - q‖ := by simp
      _ = ⨅ w : _root_.GD.N0232.N0720.N1029.d015357 m n hm hn,
          ‖(0 : _root_.GD.N0232.N0720.N1025.d014302 m n) - w‖ :=
        (_root_.GD.N0232.N0720.N1029.d015365 m n hm hn).2
  exact _root_.GD.N0232.N0720.N1029.d015363 m n hm hn hrLocus
    (_root_.GD.N0232.N0720.N1029.d015365 m n hm hn).1 hrMin
    (_root_.GD.N0232.N0720.N1029.d015365 m n hm hn).2






theorem d019469
    (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hpFinite : _root_.GD.N0232.N0720.N1159.d014637 2 2 p)
    (hpAffine : _root_.GD.N0232.N0720.N1159.d014652 2 2 p)
    (hpSummary : _root_.GD.N0232.N0720.N1501.d016291 2 2 p = p)
    (hpReflection : _root_.GD.N0232.N0720.N1446.d019032 2 2 p = p) :
    ∃ h : _root_.GD.N0232.N0720.N1436.d013217 → ℝ,
      Measurable h ∧ _root_.GD.N0232.N0720.N1063.d019453 p h := by
  obtain ⟨repaired, hrepairedMeasurable, hrepairedClass,
      hrepairedAffine, hrepairedReflection⟩ :=
    _root_.GD.N0232.N0720.N1149.d019466
      2 2 (by omega) (by omega) p hpFinite hpAffine hpSummary hpReflection
  let h : _root_.GD.N0232.N0720.N1436.d013217 → ℝ :=
    fun x ↦ _root_.GD.N0232.N0720.N1209.d012471 repaired x.1 x.2
  have hh : Measurable h :=
    _root_.GD.N0232.N0720.N1209.d012473 repaired hrepairedMeasurable
  refine ⟨h, hh, ?_⟩
  intro theta
  have hregularRef : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      (0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).meanVariance 0 ∧
        0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).meanVariance 1) ∧
      (_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).mean 0 -
        (_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).mean 1 ≠ 0 := by
    have hcontrast : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
        (_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).mean 0 -
          (_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).mean 1 ≠ 0 := by
      unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
      simpa [_root_.GD.N0232.N0720.N1080.d014169] using _root_.GD.N0232.N0720.N1500.d012582
    filter_upwards [_root_.GD.N0232.N0720.N1491.d017394, hcontrast] with
        omega hpositive hcontrastOmega
    exact ⟨⟨hpositive 0, hpositive 1⟩, hcontrastOmega⟩
  have hregular :=
    (_root_.GD.N0232.N0720.N1080.d014173 2 2 theta).ae_le hregularRef
  filter_upwards [hrepairedClass theta, hregular] with omega hclass hregularOmega
  have hsummary :
      _root_.GD.N0232.N0720.N1467.d012542 2 2 omega =
        _root_.GD.N0232.N0720.N1209.d012458
          ((_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).mean 0)
          ((_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).mean 1)
          ((_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).meanVariance 0)
          ((_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).meanVariance 1) := by
    apply _root_.GD.N0232.N0719.N0900.d009096.ext <;> funext i <;> fin_cases i <;> rfl
  have hnormal :
      repaired
          (_root_.GD.N0232.N0720.N1209.d012458
            ((_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).mean 0)
            ((_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).mean 1)
            ((_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).meanVariance 0)
            ((_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).meanVariance 1)) =
        (_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).mean 1 +
          ((_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).mean 0 -
            (_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).mean 1) *
            _root_.GD.N0232.N0720.N1209.d012471 repaired
              (_root_.GD.N0232.N0720.N1437.d002996
                ((_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).meanVariance 0)
                ((_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).meanVariance 1))
              (_root_.GD.N0232.N0720.N1437.d002997
                ((_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).mean 0)
                ((_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).mean 1)
                ((_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).meanVariance 0)
                ((_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).meanVariance 1)) := by
    simpa only [_root_.GD.N0232.N0720.N1209.d012459, _root_.GD.N0232.N0720.N1209.d012460,
      _root_.GD.N0232.N0720.N1209.d012461,
      _root_.GD.N0232.N0720.N1209.d012462] using
        (_root_.GD.N0232.N0720.N1209.d012485
          repaired hrepairedAffine hrepairedReflection
          (add_pos hregularOmega.1.1 hregularOmega.1.2).ne'
          hregularOmega.2)
  calc
    p omega = repaired (_root_.GD.N0232.N0720.N1467.d012542 2 2 omega) := hclass.symm
    _ = repaired
          (_root_.GD.N0232.N0720.N1209.d012458
            ((_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).mean 0)
            ((_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).mean 1)
            ((_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).meanVariance 0)
            ((_root_.GD.N0232.N0720.N1467.d012542 2 2 omega).meanVariance 1)) :=
      congrArg repaired hsummary
    _ = _ := hnormal
    _ = _root_.GD.N0232.N0720.N1425.d014719 2 2 h omega := by
      unfold _root_.GD.N0232.N0720.N1425.d014719 _root_.GD.N0232.N0720.N1437.d002998 h
      simp only [_root_.GD.N0232.N0720.N1467.d012545, _root_.GD.N0232.N0720.N1467.d012546,
        _root_.GD.N0232.N0720.N1467.d012547,
        _root_.GD.N0232.N0720.N1467.d012548,
        _root_.GD.N0232.N0720.N1084.d014252,
        _root_.GD.N0232.N0720.N1084.d014253]





theorem d019470
    (hsummary : _root_.GD.N0232.N0720.N1501.d016291 2 2
      (_root_.GD.N0232.N0720.N1029.d015364 2 2 (by omega) (by omega)) =
        _root_.GD.N0232.N0720.N1029.d015364 2 2 (by omega) (by omega)) :
    ∃ h : _root_.GD.N0232.N0720.N1436.d013217 → ℝ,
      Measurable h ∧
        _root_.GD.N0232.N0720.N1063.d019453
          (_root_.GD.N0232.N0720.N1029.d015364 2 2 (by omega) (by omega)) h := by
  apply _root_.GD.N0232.N0720.N1149.d019469
  · exact _root_.GD.N0232.N0720.N1029.d015371 2 2 (by omega) (by omega)
  · exact _root_.GD.N0232.N0720.N1505.d018995
      2 2 (by omega) (by omega)
  · exact hsummary
  · exact _root_.GD.N0232.N0720.N1149.d019468 2 2 (by omega) (by omega)

#print axioms _root_.GD.N0232.N0720.N1149.d019465
#print axioms _root_.GD.N0232.N0720.N1149.d019468
#print axioms _root_.GD.N0232.N0720.N1149.d019469
#print axioms _root_.GD.N0232.N0720.N1149.d019470

end

end GD.N0232.N0720.N1149
