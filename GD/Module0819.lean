import GD.Module0309
import GD.Module0629















open MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal NNReal

namespace GD.N0232.N0720.N1388

open _root_.GD.N0232.N0720.N1393
open _root_.GD.N0238.N0753
open _root_.GD.N0137 _root_.GD.N0107

noncomputable section

theorem d012491 (h : _root_.GD.N0232.N0720.N1393.d004493 → ℝ)
    (x : ({0}ᶜ : Set _root_.GD.N0232.N0720.N1393.d004492)) :
    _root_.GD.N0232.N0720.N1393.d004496 h x.1 = ‖x.1‖ * h ((homeomorphUnitSphereProd _ x).1) := by
  have hx : x.1 ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.2
  unfold _root_.GD.N0232.N0720.N1393.d004496 _root_.GD.N0238.N0753.d004402
  rw [dif_neg hx]
  change ‖x.1‖ * h _ = ‖x.1‖ * h _
  congr 1
  apply congrArg h
  apply Subtype.ext
  simp only [_root_.GD.N0238.N0753.d004399, homeomorphUnitSphereProd_apply_fst_coe]

theorem d012492 {h : _root_.GD.N0232.N0720.N1393.d004493 → ℝ} (hh : Measurable h) :
    Measurable (_root_.GD.N0232.N0720.N1393.d004496 h) := by
  apply measurable_of_measurable_on_compl_singleton 0
  change Measurable (fun x : ({0}ᶜ : Set _root_.GD.N0232.N0720.N1393.d004492) ↦
    _root_.GD.N0232.N0720.N1393.d004496 h x.1)
  simp_rw [_root_.GD.N0232.N0720.N1388.d012491]
  exact measurable_subtype_coe.norm.mul
    (hh.comp (homeomorphUnitSphereProd _).measurable.fst)

theorem d012493 (h : _root_.GD.N0232.N0720.N1393.d004495) : Measurable (_root_.GD.N0232.N0720.N1393.d004496 h) :=
  _root_.GD.N0232.N0720.N1388.d012492 (Lp.stronglyMeasurable h).measurable


def d012494 (x : _root_.GD.N0137.d008894 2) : ℝ × ℝ :=
  ((x 0 + x 1) / 2, (x 0 - x 1) / 2)

@[fun_prop]
theorem d012495 : Measurable _root_.GD.N0232.N0720.N1388.d012494 := by
  unfold _root_.GD.N0232.N0720.N1388.d012494
  fun_prop

def d012496 (s : ℝ) : ℝ≥0 := ⟨s ^ 2 / 2, by positivity⟩

def d012497 (m s : ℝ) : Measure (ℝ × ℝ) :=
  (gaussianReal m (_root_.GD.N0232.N0720.N1388.d012496 s)).prod (gaussianReal 0 (_root_.GD.N0232.N0720.N1388.d012496 s))

theorem d012498 (m s : ℝ) :
    (gaussianReal 0 1).map (fun x : ℝ ↦ m + s * x) =
      gaussianReal m ⟨s ^ 2, sq_nonneg s⟩ := by
  calc
    (gaussianReal 0 1).map (fun x : ℝ ↦ m + s * x) =
        ((gaussianReal 0 1).map (fun x : ℝ ↦ s * x)).map (fun x : ℝ ↦ m + x) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)] <;> rfl
    _ = (gaussianReal 0 ⟨s ^ 2, sq_nonneg s⟩).map (fun x : ℝ ↦ m + x) := by
      rw [gaussianReal_map_const_mul]
      simp only [mul_zero, mul_one]
      rfl
    _ = gaussianReal m ⟨s ^ 2, sq_nonneg s⟩ := by
      rw [gaussianReal_map_const_add]
      simp

def d012499 (m s : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (m + (s * Real.sqrt (1 / 2)) * p.1, (s * Real.sqrt (1 / 2)) * p.2)

@[fun_prop]
theorem d012500 (m s : ℝ) : Measurable (_root_.GD.N0232.N0720.N1388.d012499 m s) := by
  unfold _root_.GD.N0232.N0720.N1388.d012499
  fun_prop

theorem d012501 (s : ℝ) :
    (⟨(s * Real.sqrt (1 / 2)) ^ 2, sq_nonneg _⟩ : ℝ≥0) = _root_.GD.N0232.N0720.N1388.d012496 s := by
  apply Subtype.ext
  change (s * Real.sqrt (1 / 2)) ^ 2 = s ^ 2 / 2
  rw [mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  ring

theorem d012502 (m s : ℝ) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (_root_.GD.N0232.N0720.N1388.d012499 m s) =
      _root_.GD.N0232.N0720.N1388.d012497 m s := by
  have hmap := Measure.map_prod_map (gaussianReal 0 1) (gaussianReal 0 1)
    (f := fun x : ℝ ↦ m + (s * Real.sqrt (1 / 2)) * x)
    (g := fun x : ℝ ↦ 0 + (s * Real.sqrt (1 / 2)) * x)
    (by fun_prop) (by fun_prop)
  simp only [_root_.GD.N0232.N0720.N1388.d012498, _root_.GD.N0232.N0720.N1388.d012501] at hmap
  simpa only [_root_.GD.N0232.N0720.N1388.d012497, _root_.GD.N0232.N0720.N1388.d012499, Prod.map_def, zero_add] using! hmap.symm



theorem d012503 (m s : ℝ) :
    _root_.GD.N0232.N0720.N1388.d012494 ∘ _root_.GD.N0107.d009018 2 m s =
      _root_.GD.N0232.N0720.N1388.d012499 m s ∘ _root_.GD.N0137.d008920 (1 / 2) ∘
        (MeasurableEquiv.finTwoArrow : _root_.GD.N0137.d008894 2 ≃ᵐ ℝ × ℝ) := by
  funext x
  apply Prod.ext
  · change ((m + s * x 0) + (m + s * x 1)) / 2 =
      m + (s * Real.sqrt (1 / 2)) *
        (Real.sqrt (1 / 2) * x 0 + Real.sqrt (1 - 1 / 2) * x 1)
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    linear_combination -(s * (x 0 + x 1)) *
      (Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num))
  · change ((m + s * x 0) - (m + s * x 1)) / 2 =
      (s * Real.sqrt (1 / 2)) *
        (Real.sqrt (1 - 1 / 2) * x 0 - Real.sqrt (1 / 2) * x 1)
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    linear_combination -(s * (x 0 - x 1)) *
      (Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num))



theorem d012504 (m s : ℝ) :
    (_root_.GD.N0232.N0719.d009174 2 m s).map _root_.GD.N0232.N0720.N1388.d012494 =
      _root_.GD.N0232.N0720.N1388.d012497 m s := by
  unfold _root_.GD.N0232.N0719.d009174
  rw [Measure.map_map _root_.GD.N0232.N0720.N1388.d012495 (_root_.GD.N0107.d009020 2 m s),
    _root_.GD.N0232.N0720.N1388.d012503]
  rw [← Measure.map_map (_root_.GD.N0232.N0720.N1388.d012500 m s)
      ((_root_.GD.N0137.d008921 (1 / 2)).comp
        MeasurableEquiv.finTwoArrow.measurable),
    ← Measure.map_map (_root_.GD.N0137.d008921 (1 / 2))
      MeasurableEquiv.finTwoArrow.measurable]
  have hpair : (_root_.GD.N0137.d008895 2).map MeasurableEquiv.finTwoArrow =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
    exact (measurePreserving_finTwoArrow (gaussianReal 0 1)).map_eq
  rw [hpair, _root_.GD.N0137.d008927 (by norm_num) (by norm_num),
    _root_.GD.N0232.N0720.N1388.d012502]




theorem d012505 (m s t : ℝ) :
    (_root_.GD.N0107.d009030 2 2 m s t).map (Prod.map _root_.GD.N0232.N0720.N1388.d012494 _root_.GD.N0232.N0720.N1388.d012494) =
      (_root_.GD.N0232.N0720.N1388.d012497 m s).prod (_root_.GD.N0232.N0720.N1388.d012497 m t) := by
  rw [_root_.GD.N0232.N0720.d009061]
  change ((_root_.GD.N0232.N0719.d009174 2 m s).prod
    (_root_.GD.N0232.N0719.d009174 2 m t)).map
      (Prod.map _root_.GD.N0232.N0720.N1388.d012494 _root_.GD.N0232.N0720.N1388.d012494) = _
  rw [← Measure.map_prod_map _ _ _root_.GD.N0232.N0720.N1388.d012495 _root_.GD.N0232.N0720.N1388.d012495,
    _root_.GD.N0232.N0720.N1388.d012504,
    _root_.GD.N0232.N0720.N1388.d012504]




theorem d012506 (m s t : ℝ)
    (d : (ℝ × ℝ) × (ℝ × ℝ) → ℝ) (hd : Measurable d) :
    (∫⁻ x, ENNReal.ofReal ((d (_root_.GD.N0232.N0720.N1388.d012494 x.1, _root_.GD.N0232.N0720.N1388.d012494 x.2) - m) ^ 2)
      ∂_root_.GD.N0107.d009030 2 2 m s t) =
    ∫⁻ p, ENNReal.ofReal ((d p - m) ^ 2)
      ∂(_root_.GD.N0232.N0720.N1388.d012497 m s).prod (_root_.GD.N0232.N0720.N1388.d012497 m t) := by
  rw [← _root_.GD.N0232.N0720.N1388.d012505]
  symm
  exact lintegral_map (by fun_prop) (by fun_prop)

end

end GD.N0232.N0720.N1388

#print axioms _root_.GD.N0232.N0720.N1388.d012493
#print axioms _root_.GD.N0232.N0720.N1388.d012504
#print axioms _root_.GD.N0232.N0720.N1388.d012505
#print axioms _root_.GD.N0232.N0720.N1388.d012506
