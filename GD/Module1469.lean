import GD.Module0536
import GD.Module1468

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace GD.N0213.N0509
noncomputable section
open _root_.GD.N0213.N0511 _root_.GD.N0213.N0519
open _root_.GD.N0232.N0719.N0910 _root_.GD.N0051

theorem d023105 {a b r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    (∫ x, x⁻¹ * _root_.GD.N0213.N0511.d007996 a b x ^ 2 ∂gammaMeasure (a + 1) r) =
      (r / a) * (∫ x, _root_.GD.N0213.N0511.d007996 a b x ∂gammaMeasure (a + 1) r) := by
  simp_rw [_root_.GD.N0213.N0520.d023081 ha hr]
  have hi : (∫ x in Ioi (0 : ℝ), _root_.GD.N0213.N0519.d007966 a r x * (x⁻¹ * _root_.GD.N0213.N0511.d007996 a b x ^ 2)) =
      ∫ x in Ioi (0 : ℝ), _root_.GD.N0213.N0519.d007966 (a - 1) r x * _root_.GD.N0213.N0511.d007996 a b x ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [_root_.GD.N0213.N0519.d007970 a r hx]
    field_simp [ne_of_gt (show 0 < x from hx)]
  rw [hi, _root_.GD.N0213.N0511.d008009 ha hb hr]
  ring

variable {Ω : Type*} [MeasurableSpace Ω]

theorem d023106 (ν : Measure Ω) [IsFiniteMeasure ν]
    (b : Ω → ℝ) (hb : Measurable b) (hb0 : ∀ᵐ y ∂ν, 0 < b y)
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (∫ z : ℝ × Ω, z.1⁻¹ * _root_.GD.N0213.N0511.d007996 a (b z.2) z.1 ^ 2
        ∂(gammaMeasure (a + 1) r).prod ν) =
      (r / a) * (∫ z : ℝ × Ω, _root_.GD.N0213.N0511.d007996 a (b z.2) z.1
        ∂(gammaMeasure (a + 1) r).prod ν) := by
  letI := isProbabilityMeasure_gammaMeasure (by linarith : 0 < a + 1) hr
  have hpos : ∀ᵐ z : ℝ × Ω ∂(gammaMeasure (a + 1) r).prod ν,
      0 < z.1 ∧ 0 < b z.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_lt measurable_const (hb.comp measurable_snd)))).mpr
    filter_upwards [_root_.GD.N0232.N0719.N0910.d010286 (by linarith : 0 < a + 1) hr] with x hx
    filter_upwards [hb0] with y hy
    exact ⟨hx, hy⟩
  have hmeas : Measurable (fun z : ℝ × Ω => _root_.GD.N0213.N0511.d007996 a (b z.2) z.1) := by
    unfold _root_.GD.N0213.N0511.d007996
    fun_prop
  have hM : Integrable (fun z : ℝ × Ω => _root_.GD.N0213.N0511.d007996 a (b z.2) z.1)
      ((gammaMeasure (a + 1) r).prod ν) := by
    apply (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
    filter_upwards [hpos] with z hz
    exact _root_.GD.N0213.N0511.d008002 a hz.2 hz.1.le
  have hinv : Integrable (fun x : ℝ => x⁻¹) (gammaMeasure (a + 1) r) := by
    simpa only [Real.rpow_neg_one] using
      _root_.GD.N0051.d022782 (by linarith : 0 < a + 1) hr
        (u := -1) (by linarith)
  have hQ : Integrable (fun z : ℝ × Ω => z.1⁻¹ * _root_.GD.N0213.N0511.d007996 a (b z.2) z.1 ^ 2)
      ((gammaMeasure (a + 1) r).prod ν) := by
    apply (hinv.comp_fst ν).norm.mono'
      ((measurable_fst.inv.mul (hmeas.pow_const 2)).aestronglyMeasurable)
    filter_upwards [hpos] with z hz
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (_root_.GD.N0213.N0511.d008003 a hz.2 hz.1.le)
  rw [integral_prod_symm _ hQ, integral_prod_symm _ hM, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hb0] with y hy
  exact _root_.GD.N0213.N0509.d023105 ha hy hr

variable {k : ℕ}

def d023107 (a β : Fin k → ℝ) : ℝ := ∏ i, β i ^ a i

def d023108 (a β : Fin k → ℝ) : ℝ := (1 + _root_.GD.N0213.N0509.d023107 a β)⁻¹

@[fun_prop] theorem d023109 (a : Fin k → ℝ) :
    Measurable (_root_.GD.N0213.N0509.d023107 a) := by
  unfold _root_.GD.N0213.N0509.d023107
  fun_prop

@[fun_prop] theorem d023110 (a : Fin k → ℝ) :
    Measurable (_root_.GD.N0213.N0509.d023108 a) := by
  unfold _root_.GD.N0213.N0509.d023108
  fun_prop

theorem d023111 (a β : Fin k → ℝ) (hβ : ∀ i, 0 < β i) :
    0 < _root_.GD.N0213.N0509.d023107 a β :=
  Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (hβ i) (a i))

theorem d023112 (a β : Fin k → ℝ) (hβ : ∀ i, 0 < β i) :
    0 < _root_.GD.N0213.N0509.d023108 a β ∧ _root_.GD.N0213.N0509.d023108 a β ≤ 1 := by
  have hp := _root_.GD.N0213.N0509.d023111 a β hβ
  unfold _root_.GD.N0213.N0509.d023108
  exact ⟨inv_pos.mpr (by linarith), inv_le_one_of_one_le₀ (by linarith)⟩

theorem d023113 (a r : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) :
    ∀ᵐ β : Fin k → ℝ ∂Measure.pi (fun i => gammaMeasure (a i + 1) (r i)),
      0 < _root_.GD.N0213.N0509.d023108 a β ∧ _root_.GD.N0213.N0509.d023108 a β ≤ 1 := by
  filter_upwards [_root_.GD.N0232.N0719.N0910.d010287
    (shape := fun i => a i + 1) (rate := r)
    (fun i => by have := ha i; linarith) hr] with β hβ
  exact _root_.GD.N0213.N0509.d023112 a β hβ

theorem d023114 (a r : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) :
    Integrable (_root_.GD.N0213.N0509.d023108 a) (Measure.pi fun i => gammaMeasure (a i + 1) (r i)) := by
  letI (i : Fin k) :=
    isProbabilityMeasure_gammaMeasure (by have := ha i; linarith : 0 < a i + 1) (hr i)
  apply (integrable_const (1 : ℝ)).mono' (_root_.GD.N0213.N0509.d023110 a).aestronglyMeasurable
  filter_upwards [_root_.GD.N0213.N0509.d023113 a r ha hr] with β hβ
  rw [Real.norm_eq_abs, abs_of_pos hβ.1]
  exact hβ.2

theorem d023115 (a r : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) :
    Integrable (fun β => _root_.GD.N0213.N0509.d023108 a β ^ 2)
      (Measure.pi fun i => gammaMeasure (a i + 1) (r i)) := by
  letI (i : Fin k) :=
    isProbabilityMeasure_gammaMeasure (by have := ha i; linarith : 0 < a i + 1) (hr i)
  apply (integrable_const (1 : ℝ)).mono'
    ((_root_.GD.N0213.N0509.d023110 a).pow_const 2).aestronglyMeasurable
  filter_upwards [_root_.GD.N0213.N0509.d023113 a r ha hr] with β hβ
  rw [norm_pow, Real.norm_eq_abs, abs_of_pos hβ.1]
  exact pow_le_one₀ hβ.1.le hβ.2

theorem d023116 (a r : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) (i : Fin k) :
    Integrable (fun β : Fin k → ℝ => (β i)⁻¹ * _root_.GD.N0213.N0509.d023108 a β ^ 2)
      (Measure.pi fun j => gammaMeasure (a j + 1) (r j)) := by
  letI (j : Fin k) :=
    isProbabilityMeasure_gammaMeasure (by have := ha j; linarith : 0 < a j + 1) (hr j)
  have hi : Integrable (fun x : ℝ => x⁻¹) (gammaMeasure (a i + 1) (r i)) := by
    simpa only [Real.rpow_neg_one] using
      _root_.GD.N0051.d022782 (by have := ha i; linarith : 0 < a i + 1) (hr i)
        (u := -1) (by have := ha i; linarith)
  apply (integrable_comp_eval hi).norm.mono'
    (((measurable_pi_apply i).inv.mul
      ((_root_.GD.N0213.N0509.d023110 a).pow_const 2)).aestronglyMeasurable)
  filter_upwards [_root_.GD.N0213.N0509.d023113 a r ha hr] with β hβ
  rw [norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  rw [norm_pow, Real.norm_eq_abs, abs_of_pos hβ.1]
  exact pow_le_one₀ hβ.1.le hβ.2

theorem d023117 (μ : Measure Ω) [NeZero μ]
    (f : Ω → ℝ) (hf : Integrable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    0 < ∫ x, f x ∂μ := by
  apply (integral_pos_iff_support_of_nonneg_ae
    (hpos.mono (fun _ hx => hx.le)) hf).mpr
  have hs : Function.support f =ᵐ[μ] (univ : Set Ω) := by
    filter_upwards [hpos] with x hx
    change (f x ≠ 0) = True
    exact propext ⟨fun _ => trivial, fun _ => hx.ne'⟩
  rw [measure_congr hs]
  exact Measure.measure_univ_pos.mpr (NeZero.ne μ)

theorem d023118 (a r : Fin k → ℝ)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) :
    (0 < ∫ β, _root_.GD.N0213.N0509.d023108 a β ∂Measure.pi (fun i => gammaMeasure (a i + 1) (r i))) ∧
      (0 < ∫ β, _root_.GD.N0213.N0509.d023108 a β ^ 2
        ∂Measure.pi (fun i => gammaMeasure (a i + 1) (r i))) := by
  letI (i : Fin k) :=
    isProbabilityMeasure_gammaMeasure (by have := ha i; linarith : 0 < a i + 1) (hr i)
  have hp := _root_.GD.N0213.N0509.d023113 a r ha hr
  exact ⟨_root_.GD.N0213.N0509.d023117 _ _ (_root_.GD.N0213.N0509.d023114 a r ha hr)
      (hp.mono (fun _ h => h.1)),
    _root_.GD.N0213.N0509.d023117 _ _ (_root_.GD.N0213.N0509.d023115 a r ha hr)
      (hp.mono (fun _ h => sq_pos_of_pos h.1))⟩

theorem d023119 (a : Fin (k + 1) → ℝ)
    (i : Fin (k + 1)) (x : ℝ) (y : Fin k → ℝ) :
    _root_.GD.N0213.N0509.d023107 a (i.insertNth x y) =
      x ^ a i * _root_.GD.N0213.N0509.d023107 (fun j => a (i.succAbove j)) y := by
  unfold _root_.GD.N0213.N0509.d023107
  rw [Fin.prod_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

theorem d023120 (a : Fin (k + 1) → ℝ)
    (i : Fin (k + 1)) (x : ℝ) (y : Fin k → ℝ) :
    _root_.GD.N0213.N0509.d023108 a (i.insertNth x y) =
      _root_.GD.N0213.N0511.d007996 (a i) (_root_.GD.N0213.N0509.d023107 (fun j => a (i.succAbove j)) y) x := by
  unfold _root_.GD.N0213.N0509.d023108 _root_.GD.N0213.N0511.d007996
  rw [_root_.GD.N0213.N0509.d023119, mul_comm]

theorem d023121 (a r : Fin (k + 1) → ℝ)
    (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < r i) (i : Fin (k + 1)) :
    (∫ β : Fin (k + 1) → ℝ, (β i)⁻¹ * _root_.GD.N0213.N0509.d023108 a β ^ 2
        ∂Measure.pi (fun j => gammaMeasure (a j + 1) (r j))) =
      (r i / a i) * (∫ β, _root_.GD.N0213.N0509.d023108 a β
        ∂Measure.pi (fun j => gammaMeasure (a j + 1) (r j))) := by
  let μ : Fin (k + 1) → Measure ℝ := fun j => gammaMeasure (a j + 1) (r j)
  letI (j : Fin (k + 1)) : IsProbabilityMeasure (μ j) :=
    isProbabilityMeasure_gammaMeasure (by have := ha j; linarith) (hr j)
  change (∫ β, (β i)⁻¹ * _root_.GD.N0213.N0509.d023108 a β ^ 2 ∂Measure.pi μ) = _
  rw [_root_.GD.N0213.N0507.d023100 μ i,
    _root_.GD.N0213.N0507.d023100 μ i (_root_.GD.N0213.N0509.d023108 a)]
  simp_rw [_root_.GD.N0213.N0509.d023120, Fin.insertNth_apply_same]
  apply _root_.GD.N0213.N0509.d023106 (Measure.pi fun j => μ (i.succAbove j))
    (_root_.GD.N0213.N0509.d023107 (fun j => a (i.succAbove j))) (_root_.GD.N0213.N0509.d023109 _) _ (ha i) (hr i)
  filter_upwards [_root_.GD.N0232.N0719.N0910.d010287
    (shape := fun j => a (i.succAbove j) + 1) (rate := fun j => r (i.succAbove j))
    (fun j => by have := ha (i.succAbove j); linarith)
    (fun j => hr (i.succAbove j))] with β hβ
  exact _root_.GD.N0213.N0509.d023111 _ _ hβ

end
end GD.N0213.N0509

#print axioms _root_.GD.N0213.N0509.d023105
#print axioms _root_.GD.N0213.N0509.d023106
#print axioms _root_.GD.N0213.N0509.d023116
#print axioms _root_.GD.N0213.N0509.d023118
#print axioms _root_.GD.N0213.N0509.d023121
