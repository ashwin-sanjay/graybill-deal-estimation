import GD.Module0233
import Mathlib








set_option autoImplicit false
set_option warningAsError true

open scoped ENNReal NNReal BigOperators ProbabilityTheory
open MeasureTheory ProbabilityTheory Set

namespace GD.N0228.N0547.N0780

theorem d003384 (v : ℝ≥0) (hv : v ≠ 0) (r θ : ℝ) :
    gaussianPDFReal 0 v (r * Real.cos θ) * gaussianPDFReal 0 v (r * Real.sin θ) =
      gaussianPDFReal 0 v r * gaussianPDFReal 0 v 0 := by
  have hvR : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  rw [gaussianPDFReal, gaussianPDFReal, gaussianPDFReal, gaussianPDFReal]
  simp only [sub_zero]
  have hexp :
      -(r * Real.cos θ) ^ 2 / (2 * (v : ℝ)) +
          -(r * Real.sin θ) ^ 2 / (2 * (v : ℝ)) =
        -r ^ 2 / (2 * (v : ℝ)) := by
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq θ]
  calc
    _ = (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ ^ 2 *
          (Real.exp (-(r * Real.cos θ) ^ 2 / (2 * (v : ℝ))) *
            Real.exp (-(r * Real.sin θ) ^ 2 / (2 * (v : ℝ)))) := by ring
    _ = (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ ^ 2 *
          Real.exp (-(r * Real.cos θ) ^ 2 / (2 * (v : ℝ)) +
            -(r * Real.sin θ) ^ 2 / (2 * (v : ℝ))) := by rw [Real.exp_add]
    _ = _ := by rw [hexp]; norm_num; ring

theorem d003385 (v : ℝ≥0) (hv : v ≠ 0) (r θ : ℝ) :
    gaussianPDF 0 v (r * Real.cos θ) * gaussianPDF 0 v (r * Real.sin θ) =
      gaussianPDF 0 v r * gaussianPDF 0 v 0 := by
  simp only [gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  rw [_root_.GD.N0228.N0547.N0780.d003384 v hv]



noncomputable def d003386 (v : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ r in Ioi (0 : ℝ),
    ENNReal.ofReal r * (gaussianPDF 0 v r * gaussianPDF 0 v 0)




theorem d003387 (v : ℝ≥0) (hv : v ≠ 0) :
    _root_.GD.N0228.N0547.N0780.d003386 v * ENNReal.ofReal (2 * Real.pi) = 1 := by
  have hnorm :
      (∫⁻ z : ℝ × ℝ, gaussianPDF 0 v z.1 * gaussianPDF 0 v z.2
        ∂(volume : Measure (ℝ × ℝ))) = 1 := by
    change (∫⁻ z : ℝ × ℝ, gaussianPDF 0 v z.1 * gaussianPDF 0 v z.2
      ∂(volume.prod volume)) = 1
    rw [lintegral_prod_mul (measurable_gaussianPDF 0 v).aemeasurable
      (measurable_gaussianPDF 0 v).aemeasurable]
    simp [lintegral_gaussianPDF_eq_one 0 hv]
  rw [← lintegral_comp_polarCoord_symm] at hnorm
  have hpoint (p : ℝ × ℝ) :
      ENNReal.ofReal p.1 •
          (gaussianPDF 0 v (polarCoord.symm p).1 *
            gaussianPDF 0 v (polarCoord.symm p).2) =
        ENNReal.ofReal p.1 *
          (gaussianPDF 0 v p.1 * gaussianPDF 0 v 0) := by
    change ENNReal.ofReal p.1 *
        (gaussianPDF 0 v (p.1 * Real.cos p.2) *
          gaussianPDF 0 v (p.1 * Real.sin p.2)) = _
    rw [_root_.GD.N0228.N0547.N0780.d003385 v hv]
  simp_rw [hpoint] at hnorm
  rw [show polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi from rfl,
    Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod _ (by fun_prop)] at hnorm
  simp_rw [setLIntegral_const] at hnorm
  have hradialMeas : Measurable
      (fun r : ℝ ↦ ENNReal.ofReal r * (gaussianPDF 0 v r * gaussianPDF 0 v 0)) := by
    fun_prop
  rw [lintegral_mul_const _ hradialMeas] at hnorm
  have hvol : volume (Ioo (-Real.pi) Real.pi) = ENNReal.ofReal (2 * Real.pi) := by
    rw [Real.volume_Ioo]
    congr 1
    ring
  simpa [_root_.GD.N0228.N0547.N0780.d003386, hvol] using hnorm



theorem d003388 {t φ : ℝ} (hφ0 : 0 < φ)
    (hφhalf : φ < Real.pi / 2) (ht0 : 0 ≤ t) (hthalf : t < Real.pi / 2) :
    Real.cot φ * Real.sin t < Real.cos t ↔ t < φ := by
  have hφpi : φ < Real.pi := lt_trans hφhalf (by linarith [Real.pi_pos])
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 hφpi
  rw [Real.cot_eq_cos_div_sin, div_mul_eq_mul_div, div_lt_iff₀ hsφ]
  have hrewrite :
      Real.cos φ * Real.sin t < Real.cos t * Real.sin φ ↔
        Real.sin (t - φ) < 0 := by
    rw [← sub_lt_zero]
    simp only [Real.sin_sub]
    ring_nf
  rw [hrewrite]
  constructor
  · intro hs
    by_contra hnot
    have hφt : φ ≤ t := le_of_not_gt hnot
    rcases hφt.eq_or_lt with hEq | hlt
    · subst t
      simp at hs
    · have hpos : 0 < Real.sin (t - φ) :=
        Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hlt) (by linarith [Real.pi_pos])
      linarith
  · intro hlt
    exact Real.sin_neg_of_neg_of_neg_pi_lt (sub_neg.mpr hlt)
      (by linarith [Real.pi_pos])

theorem d003389 {t φ : ℝ} (hφ0 : 0 < φ)
    (hφhalf : φ < Real.pi / 2) (htlow : -(Real.pi / 2) < t)
    (hthigh : t < Real.pi / 2) :
    Real.cot φ * |Real.sin t| < |Real.cos t| ↔ |t| < φ := by
  have habshalf : |t| < Real.pi / 2 := (abs_lt).2 ⟨htlow, hthigh⟩
  have habspi : |t| ≤ Real.pi :=
    habshalf.le.trans (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨htlow, hthigh⟩
  rw [abs_of_pos hcos, Real.abs_sin_eq_sin_abs_of_abs_le_pi habspi]
  simpa only [Real.cos_abs] using
    _root_.GD.N0228.N0547.N0780.d003388 hφ0 hφhalf (abs_nonneg t) habshalf

theorem d003390 {t φ : ℝ} (hφ0 : 0 < φ)
    (hφhalf : φ < Real.pi / 2) (hthalf : Real.pi / 2 < t)
    (htpi : t < Real.pi) :
    Real.cot φ * |Real.sin t| < |Real.cos t| ↔ Real.pi - φ < t := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi
    (lt_trans (by positivity : 0 < Real.pi / 2) hthalf) htpi
  have hc : Real.cos t < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hthalf
    (htpi.trans (by linarith [Real.pi_pos]))
  rw [abs_of_pos hs, abs_of_neg hc, ← Real.sin_pi_sub t, ← Real.cos_pi_sub t]
  rw [_root_.GD.N0228.N0547.N0780.d003388 hφ0 hφhalf (by linarith) (by linarith)]
  constructor <;> intro h <;> linarith

theorem d003391 {t φ : ℝ} (hφ0 : 0 < φ)
    (hφhalf : φ < Real.pi / 2) (htnegpi : -Real.pi < t)
    (hthalf : t < -(Real.pi / 2)) :
    Real.cot φ * |Real.sin t| < |Real.cos t| ↔ t < -Real.pi + φ := by
  have ht0 : t < 0 := hthalf.trans (by linarith [Real.pi_pos])
  have hs : Real.sin t < 0 := Real.sin_neg_of_neg_of_neg_pi_lt ht0 htnegpi
  have hc : Real.cos t < 0 := by
    rw [← Real.cos_neg]
    exact Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith)
      (by linarith [Real.pi_pos])
  rw [abs_of_neg hs, abs_of_neg hc]
  have hsin : -Real.sin t = Real.sin (Real.pi + t) := by
    rw [add_comm, Real.sin_add_pi]
  have hcos : -Real.cos t = Real.cos (Real.pi + t) := by
    rw [add_comm, Real.cos_add_pi]
  rw [hsin, hcos,
    _root_.GD.N0228.N0547.N0780.d003388 hφ0 hφhalf (by linarith) (by linarith)]
  constructor <;> intro h <;> linarith

def d003392 (c : ℝ) : Set (ℝ × ℝ) :=
  {z | c * |z.2| < |z.1|}

def d003393 (c : ℝ) : Set ℝ :=
  {θ | c * |Real.sin θ| < |Real.cos θ|}

theorem d003394 (c : ℝ) : MeasurableSet (_root_.GD.N0228.N0547.N0780.d003392 c) := by
  exact (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet

theorem d003395 (c : ℝ) : MeasurableSet (_root_.GD.N0228.N0547.N0780.d003393 c) := by
  exact (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet

def d003396 (φ : ℝ) : Set ℝ :=
  Ioo (-φ) φ ∪ (Ioo (Real.pi - φ) Real.pi ∪ Ioo (-Real.pi) (-Real.pi + φ))



theorem d003397 (φ : ℝ) (hφ0 : 0 < φ)
    (hφhalf : φ < Real.pi / 2) :
    _root_.GD.N0228.N0547.N0780.d003393 (Real.cot φ) ∩ Ioo (-Real.pi) Real.pi = _root_.GD.N0228.N0547.N0780.d003396 φ := by
  have hφpi : φ < Real.pi := hφhalf.trans (by linarith [Real.pi_pos])
  have hsφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 hφpi
  have hcφ : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφhalf⟩
  have hcot : 0 < Real.cot φ := by
    rw [Real.cot_eq_cos_div_sin]
    positivity
  ext t
  change
    ((Real.cot φ * |Real.sin t| < |Real.cos t|) ∧
        (-Real.pi < t ∧ t < Real.pi)) ↔
      ((-φ < t ∧ t < φ) ∨
        ((Real.pi - φ < t ∧ t < Real.pi) ∨
          (-Real.pi < t ∧ t < -Real.pi + φ)))
  constructor
  · rintro ⟨hwed, hrange⟩
    by_cases hleft : t < -(Real.pi / 2)
    · have ht := (_root_.GD.N0228.N0547.N0780.d003391 hφ0 hφhalf
          hrange.1 hleft).mp hwed
      exact Or.inr (Or.inr ⟨hrange.1, ht⟩)
    · have hleftle : -(Real.pi / 2) ≤ t := le_of_not_gt hleft
      rcases hleftle.eq_or_lt with heq | hleftstrict
      · rw [← heq] at hwed
        have : Real.cot φ < 0 := by
          simpa [Real.sin_neg, Real.cos_neg] using hwed
        exact (not_lt_of_ge hcot.le this).elim
      · by_cases hcenter : t < Real.pi / 2
        · have ht := (_root_.GD.N0228.N0547.N0780.d003389 hφ0 hφhalf
              hleftstrict hcenter).mp hwed
          exact Or.inl ((abs_lt.mp ht))
        · have hrightle : Real.pi / 2 ≤ t := le_of_not_gt hcenter
          rcases hrightle.eq_or_lt with heq | hrightstrict
          · rw [← heq] at hwed
            have : Real.cot φ < 0 := by simpa using hwed
            exact (not_lt_of_ge hcot.le this).elim
          · have ht := (_root_.GD.N0228.N0547.N0780.d003390 hφ0 hφhalf
                hrightstrict hrange.2).mp hwed
            exact Or.inr (Or.inl ⟨ht, hrange.2⟩)
  · intro hintervals
    rcases hintervals with hcenter | hright | hleft
    · have htlow : -(Real.pi / 2) < t := by linarith
      have hthigh : t < Real.pi / 2 := by linarith
      refine ⟨(_root_.GD.N0228.N0547.N0780.d003389 hφ0 hφhalf
        htlow hthigh).mpr ?_, ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩⟩
      exact abs_lt.mpr hcenter
    · have hthalf : Real.pi / 2 < t := by linarith
      refine ⟨(_root_.GD.N0228.N0547.N0780.d003390 hφ0 hφhalf
        hthalf hright.2).mpr hright.1, ⟨?_, hright.2⟩⟩
      linarith [Real.pi_pos]
    · have hthalf : t < -(Real.pi / 2) := by linarith
      exact ⟨(_root_.GD.N0228.N0547.N0780.d003391 hφ0 hφhalf
        hleft.1 hthalf).mpr hleft.2, ⟨hleft.1, by linarith [Real.pi_pos]⟩⟩

theorem d003398 (φ : ℝ) (hφ0 : 0 < φ)
    (hφhalf : φ < Real.pi / 2) :
    volume (_root_.GD.N0228.N0547.N0780.d003393 (Real.cot φ) ∩ Ioo (-Real.pi) Real.pi) =
      ENNReal.ofReal (4 * φ) := by
  rw [_root_.GD.N0228.N0547.N0780.d003397 φ hφ0 hφhalf, _root_.GD.N0228.N0547.N0780.d003396]
  let C : Set ℝ := Ioo (-φ) φ
  let R : Set ℝ := Ioo (Real.pi - φ) Real.pi
  let L : Set ℝ := Ioo (-Real.pi) (-Real.pi + φ)
  have hCR : Disjoint C R := by
    refine Set.disjoint_left.mpr (fun t htC htR ↦ ?_)
    exact (not_lt_of_ge (show φ ≤ Real.pi - φ by linarith)) (htR.1.trans htC.2)
  have hCL : Disjoint C L := by
    refine Set.disjoint_left.mpr (fun t htC htL ↦ ?_)
    exact (not_lt_of_ge (show -Real.pi + φ ≤ -φ by linarith)) (htC.1.trans htL.2)
  have hRL : Disjoint R L := by
    refine Set.disjoint_left.mpr (fun t htR htL ↦ ?_)
    exact (not_lt_of_ge (show -Real.pi + φ ≤ Real.pi - φ by
      linarith [Real.pi_pos])) (htR.1.trans htL.2)
  have hC_RL : Disjoint C (R ∪ L) := by
    rw [disjoint_union_right]
    exact ⟨hCR, hCL⟩
  change volume (C ∪ (R ∪ L)) = _
  rw [measure_union hC_RL (measurableSet_Ioo.union measurableSet_Ioo),
    measure_union hRL measurableSet_Ioo, Real.volume_Ioo, Real.volume_Ioo,
    Real.volume_Ioo]
  rw [← ENNReal.ofReal_add (by linarith) (by linarith),
    ← ENNReal.ofReal_add (by linarith) (by linarith)]
  congr 1
  ring



theorem d003399 (v : ℝ≥0) (hv : v ≠ 0) (c : ℝ) :
    ((gaussianReal 0 v).prod (gaussianReal 0 v)) (_root_.GD.N0228.N0547.N0780.d003392 c) =
      _root_.GD.N0228.N0547.N0780.d003386 v * volume (_root_.GD.N0228.N0547.N0780.d003393 c ∩ Ioo (-Real.pi) Real.pi) := by
  have hprod :
      (gaussianReal 0 v).prod (gaussianReal 0 v) =
        (volume : Measure (ℝ × ℝ)).withDensity
          (fun z ↦ gaussianPDF 0 v z.1 * gaussianPDF 0 v z.2) := by
    rw [gaussianReal_of_var_ne_zero 0 hv, prod_withDensity
      (measurable_gaussianPDF 0 v) (measurable_gaussianPDF 0 v)]
    rw [← Measure.volume_eq_prod ℝ ℝ]
  rw [hprod, withDensity_apply _ (_root_.GD.N0228.N0547.N0780.d003394 c),
    ← lintegral_indicator (_root_.GD.N0228.N0547.N0780.d003394 c),
    ← lintegral_comp_polarCoord_symm]
  have hevent (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
      polarCoord.symm p ∈ _root_.GD.N0228.N0547.N0780.d003392 c ↔ p.2 ∈ _root_.GD.N0228.N0547.N0780.d003393 c := by
    have hr : 0 < p.1 := hp.1
    change c * |p.1 * Real.sin p.2| < |p.1 * Real.cos p.2| ↔
      c * |Real.sin p.2| < |Real.cos p.2|
    rw [abs_mul, abs_mul, abs_of_pos hr]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (mul_lt_mul_iff_of_pos_left hr :
        p.1 * (c * |Real.sin p.2|) < p.1 * |Real.cos p.2| ↔
          c * |Real.sin p.2| < |Real.cos p.2|)
  have hpoint (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
      ENNReal.ofReal p.1 •
          (_root_.GD.N0228.N0547.N0780.d003392 c).indicator
            (fun z ↦ gaussianPDF 0 v z.1 * gaussianPDF 0 v z.2)
            (polarCoord.symm p) =
        (ENNReal.ofReal p.1 * (gaussianPDF 0 v p.1 * gaussianPDF 0 v 0)) *
          (_root_.GD.N0228.N0547.N0780.d003393 c).indicator (fun _ ↦ (1 : ℝ≥0∞)) p.2 := by
    by_cases ha : p.2 ∈ _root_.GD.N0228.N0547.N0780.d003393 c
    · have hw : polarCoord.symm p ∈ _root_.GD.N0228.N0547.N0780.d003392 c := (hevent p hp).mpr ha
      simp only [indicator_of_mem ha, indicator_of_mem hw, smul_eq_mul, mul_one]
      change ENNReal.ofReal p.1 *
          (gaussianPDF 0 v (p.1 * Real.cos p.2) *
            gaussianPDF 0 v (p.1 * Real.sin p.2)) = _
      rw [_root_.GD.N0228.N0547.N0780.d003385 v hv]
    · have hw : polarCoord.symm p ∉ _root_.GD.N0228.N0547.N0780.d003392 c :=
        fun h ↦ ha ((hevent p hp).mp h)
      have hw' : (p.1 * Real.cos p.2, p.1 * Real.sin p.2) ∉ _root_.GD.N0228.N0547.N0780.d003392 c := by
        simpa using hw
      change ENNReal.ofReal p.1 *
          (_root_.GD.N0228.N0547.N0780.d003392 c).indicator
            (fun z ↦ gaussianPDF 0 v z.1 * gaussianPDF 0 v z.2)
            (p.1 * Real.cos p.2, p.1 * Real.sin p.2) = _
      simp [Set.indicator, ha, hw']
  rw [show polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi from rfl]
  refine (setLIntegral_congr_fun
    (measurableSet_Ioi.prod measurableSet_Ioo) hpoint).trans ?_
  have hradialMeas : Measurable
      (fun r : ℝ ↦ ENNReal.ofReal r * (gaussianPDF 0 v r * gaussianPDF 0 v 0)) := by
    fun_prop
  have hangularMeas : Measurable
      ((_root_.GD.N0228.N0547.N0780.d003393 c).indicator (fun _ ↦ (1 : ℝ≥0∞))) :=
    measurable_const.indicator (_root_.GD.N0228.N0547.N0780.d003395 c)
  have hintegrandMeas : Measurable
      (fun p : ℝ × ℝ ↦
        (ENNReal.ofReal p.1 * (gaussianPDF 0 v p.1 * gaussianPDF 0 v 0)) *
          (_root_.GD.N0228.N0547.N0780.d003393 c).indicator (fun _ ↦ (1 : ℝ≥0∞)) p.2) :=
    (hradialMeas.comp measurable_fst).mul (hangularMeas.comp measurable_snd)
  rw [Measure.volume_eq_prod ℝ ℝ,
    setLIntegral_prod _ hintegrandMeas.aemeasurable]
  have hinner (r : ℝ) :
      (∫⁻ θ in Ioo (-Real.pi) Real.pi,
        (ENNReal.ofReal r * (gaussianPDF 0 v r * gaussianPDF 0 v 0)) *
          (_root_.GD.N0228.N0547.N0780.d003393 c).indicator (fun _ ↦ (1 : ℝ≥0∞)) θ) =
        (ENNReal.ofReal r * (gaussianPDF 0 v r * gaussianPDF 0 v 0)) *
          volume (_root_.GD.N0228.N0547.N0780.d003393 c ∩ Ioo (-Real.pi) Real.pi) := by
    rw [lintegral_const_mul _ (measurable_const.indicator (_root_.GD.N0228.N0547.N0780.d003395 c)),
      setLIntegral_indicator (_root_.GD.N0228.N0547.N0780.d003395 c), setLIntegral_one]
  simp_rw [hinner]
  rw [lintegral_mul_const _ hradialMeas]
  rfl



theorem d003400 (v : ℝ≥0) (hv : v ≠ 0) (c : ℝ) :
    ((gaussianReal 0 v).prod (gaussianReal 0 v)) (_root_.GD.N0228.N0547.N0780.d003392 c) =
      volume (_root_.GD.N0228.N0547.N0780.d003393 c ∩ Ioo (-Real.pi) Real.pi) /
        ENNReal.ofReal (2 * Real.pi) := by
  rw [_root_.GD.N0228.N0547.N0780.d003399 v hv c]
  have hrad : _root_.GD.N0228.N0547.N0780.d003386 v = (ENNReal.ofReal (2 * Real.pi))⁻¹ :=
    ENNReal.eq_inv_of_mul_eq_one_left (_root_.GD.N0228.N0547.N0780.d003387 v hv)
  rw [hrad]
  simp only [div_eq_mul_inv, mul_comm]


theorem d003401 (v : ℝ≥0) (hv : v ≠ 0) (φ : ℝ)
    (hφ0 : 0 < φ) (hφhalf : φ < Real.pi / 2) :
    ((gaussianReal 0 v).prod (gaussianReal 0 v))
        {z : ℝ × ℝ | Real.cot φ * |z.2| < |z.1|} =
      ENNReal.ofReal (2 * φ / Real.pi) := by
  change ((gaussianReal 0 v).prod (gaussianReal 0 v))
      (_root_.GD.N0228.N0547.N0780.d003392 (Real.cot φ)) = _
  rw [_root_.GD.N0228.N0547.N0780.d003400 v hv,
    _root_.GD.N0228.N0547.N0780.d003398 φ hφ0 hφhalf,
    ← ENNReal.ofReal_div_of_pos (by positivity : 0 < 2 * Real.pi)]
  congr 1
  field_simp [Real.pi_ne_zero]
  ring


theorem d003402 (v : ℝ≥0) (hv : v ≠ 0) (α : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1) :
    ((gaussianReal 0 v).prod (gaussianReal 0 v))
        {z : ℝ × ℝ | Real.cot (Real.pi * α / 2) * |z.2| < |z.1|} =
      ENNReal.ofReal α := by
  have hφ0 : 0 < Real.pi * α / 2 := by positivity
  have hφhalf : Real.pi * α / 2 < Real.pi / 2 := by
    nlinarith [Real.pi_pos, mul_pos Real.pi_pos (sub_pos.mpr hα1)]
  rw [_root_.GD.N0228.N0547.N0780.d003401 v hv (Real.pi * α / 2) hφ0 hφhalf]
  congr 1
  field_simp [Real.pi_ne_zero]



theorem d003403 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (E T : Ω → ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (hE : HasLaw E (gaussianReal 0 v) P)
    (hT : HasLaw T (gaussianReal 0 v) P) (hET : IndepFun E T P)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    P {ω | Real.cot (Real.pi * α / 2) * |T ω| < |E ω|} = ENNReal.ofReal α := by
  have hjoint := hET.hasLaw_prod hE hT
  have hevent : MeasurableSet
      {z : ℝ × ℝ | Real.cot (Real.pi * α / 2) * |z.2| < |z.1|} :=
    (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet
  rw [hjoint.measure_eq hevent]
  exact _root_.GD.N0228.N0547.N0780.d003402 v hv α hα0 hα1





theorem d003404 (p : ℝ) :
    Real.cot (Real.pi * (1 - p) / 2) =
      _root_.GD.N0228.N0547.N0782.d003367 p := by
  rw [show Real.pi * (1 - p) / 2 = Real.pi / 2 - Real.pi * p / 2 by ring,
    ← Real.tan_inv_eq_cot, Real.tan_pi_div_two_sub]
  simp [_root_.GD.N0228.N0547.N0782.d003367]




theorem d003405 (k : ℝ) :
    _root_.GD.N0228.N0547.N0782.d003372 k = (_root_.GD.N0228.N0547.N0780.d003392 k)ᶜ := by
  ext z
  simp [_root_.GD.N0228.N0547.N0782.d003372, _root_.GD.N0228.N0547.N0780.d003392]




theorem d003406
    (v : ℝ≥0) (hv : v ≠ 0) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ((gaussianReal 0 v).prod (gaussianReal 0 v))
        (_root_.GD.N0228.N0547.N0782.d003372
          (_root_.GD.N0228.N0547.N0782.d003367 p)) =
      ENNReal.ofReal p := by
  let μ : Measure (ℝ × ℝ) := (gaussianReal 0 v).prod (gaussianReal 0 v)
  let k : ℝ := _root_.GD.N0228.N0547.N0782.d003367 p
  have htail : μ (_root_.GD.N0228.N0547.N0780.d003392 k) = ENNReal.ofReal (1 - p) := by
    simpa only [μ, k, _root_.GD.N0228.N0547.N0780.d003392, _root_.GD.N0228.N0547.N0780.d003404] using
      _root_.GD.N0228.N0547.N0780.d003402 v hv (1 - p)
        (sub_pos.mpr hp1) (by linarith)
  have hmeas : MeasurableSet (_root_.GD.N0228.N0547.N0780.d003392 k) := _root_.GD.N0228.N0547.N0780.d003394 k
  calc
    μ (_root_.GD.N0228.N0547.N0782.d003372
          (_root_.GD.N0228.N0547.N0782.d003367 p)) =
        μ ((_root_.GD.N0228.N0547.N0780.d003392 k)ᶜ) := by
          rw [_root_.GD.N0228.N0547.N0780.d003405]
    _ = μ Set.univ - μ (_root_.GD.N0228.N0547.N0780.d003392 k) :=
      measure_compl₀ hmeas.nullMeasurableSet (measure_ne_top μ _)
    _ = 1 - ENNReal.ofReal (1 - p) := by rw [measure_univ, htail]
    _ = ENNReal.ofReal p := by
      rw [ENNReal.ofReal_sub 1 hp0.le, ENNReal.ofReal_one]
      exact ENNReal.sub_sub_cancel
        (by norm_num) (ENNReal.ofReal_le_one.mpr hp1.le)


theorem d003407
    (v : ℝ≥0) (hv : v ≠ 0) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ((gaussianReal 0 v).prod (gaussianReal 0 v)).real
        (_root_.GD.N0228.N0547.N0782.d003372
          (_root_.GD.N0228.N0547.N0782.d003367 p)) = p := by
  rw [measureReal_def, _root_.GD.N0228.N0547.N0780.d003406 v hv p hp0 hp1,
    ENNReal.toReal_ofReal hp0.le]



theorem d003408
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (hX : HasLaw X (gaussianReal 0 v) P)
    (hY : HasLaw Y (gaussianReal 0 v) P)
    (hXY : IndepFun X Y P)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    P {ω | |X ω| ≤ _root_.GD.N0228.N0547.N0782.d003367 p * |Y ω|} =
      ENNReal.ofReal p := by
  have hjoint : HasLaw (fun ω => (X ω, Y ω))
      ((gaussianReal 0 v).prod (gaussianReal 0 v)) P :=
    hXY.hasLaw_prod hX hY
  have hevent : MeasurableSet
      (_root_.GD.N0228.N0547.N0782.d003372
        (_root_.GD.N0228.N0547.N0782.d003367 p)) :=
    _root_.GD.N0228.N0547.N0782.d003375 _
  calc
    P {ω | |X ω| ≤ _root_.GD.N0228.N0547.N0782.d003367 p * |Y ω|} =
        ((gaussianReal 0 v).prod (gaussianReal 0 v))
          (_root_.GD.N0228.N0547.N0782.d003372
            (_root_.GD.N0228.N0547.N0782.d003367 p)) := by
      exact hjoint.measure_eq hevent
    _ = ENNReal.ofReal p :=
      _root_.GD.N0228.N0547.N0780.d003406 v hv p hp0 hp1

end GD.N0228.N0547.N0780

#print axioms _root_.GD.N0228.N0547.N0780.d003384
#print axioms _root_.GD.N0228.N0547.N0780.d003387
#print axioms _root_.GD.N0228.N0547.N0780.d003397
#print axioms _root_.GD.N0228.N0547.N0780.d003398
#print axioms _root_.GD.N0228.N0547.N0780.d003399
#print axioms _root_.GD.N0228.N0547.N0780.d003400
#print axioms _root_.GD.N0228.N0547.N0780.d003401
#print axioms _root_.GD.N0228.N0547.N0780.d003402
#print axioms _root_.GD.N0228.N0547.N0780.d003403
#print axioms _root_.GD.N0228.N0547.N0780.d003406
#print axioms _root_.GD.N0228.N0547.N0780.d003407
#print axioms _root_.GD.N0228.N0547.N0780.d003408
