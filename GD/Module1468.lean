import GD.Module0537
import GD.Module1465
import GD.Module1428
import GD.Module0699
import Mathlib.MeasureTheory.Integral.Pi
import GD.Module0575

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Set

namespace GD.N0213.N0507
noncomputable section
open _root_.GD.N0213.N0495 _root_.GD.N0213.N0513
open _root_.GD.N0232.N0719.N0910 _root_.GD.N0051

variable {Ω : Type*} [MeasurableSpace Ω]

theorem d023097 (ν : Measure Ω) [IsFiniteMeasure ν]
    (b : Ω → ℝ) (hb : Measurable b) (hb0 : ∀ᵐ y ∂ν, 0 ≤ b y)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    ∀ᵐ z : ℝ × Ω ∂(gammaMeasure (s + 1) r).prod ν, 0 < z.1 + b z.2 := by
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_lt measurable_const (measurable_fst.add (hb.comp measurable_snd)))).mpr
  filter_upwards [_root_.GD.N0232.N0719.N0910.d010286 (by linarith : 0 < s + 1) hr] with x hx
  filter_upwards [hb0] with y hy
  exact add_pos_of_pos_of_nonneg hx hy

theorem d023098 (ν : Measure Ω) [IsFiniteMeasure ν]
    (b : Ω → ℝ) (hb : Measurable b) (hb0 : ∀ᵐ y ∂ν, 0 ≤ b y)
    {s r L : ℝ} (hs : 0 < s) (hr : 0 < r) (hL : 0 < L) :
    (∫ z : ℝ × Ω, z.1⁻¹ * _root_.GD.N0213.N0495.d007174 L (z.1 + b z.2) ^ 2
        ∂(gammaMeasure (s + 1) r).prod ν) =
      (r / s) * (∫ z : ℝ × Ω, _root_.GD.N0213.N0495.d007174 L (z.1 + b z.2) ^ 2
        ∂(gammaMeasure (s + 1) r).prod ν) -
      (2 / s) * (∫ z : ℝ × Ω,
        _root_.GD.N0213.N0495.d007174 L (z.1 + b z.2) * _root_.GD.N0213.N0495.d007175 L (z.1 + b z.2)
        ∂(gammaMeasure (s + 1) r).prod ν) := by
  letI := isProbabilityMeasure_gammaMeasure (by linarith : 0 < s + 1) hr
  have hR : Measurable (fun z : ℝ × Ω => z.1 + b z.2) :=
    measurable_fst.add (hb.comp measurable_snd)
  have hpos := _root_.GD.N0213.N0507.d023097 ν b hb hb0 hs hr
  have hM := _root_.GD.N0213.N0513.d008013 ((gammaMeasure (s + 1) r).prod ν) _ hR L
  have hE := _root_.GD.N0213.N0513.d008015
    ((gammaMeasure (s + 1) r).prod ν) _ hR hL hpos
  have hinv : Integrable (fun x : ℝ => x⁻¹) (gammaMeasure (s + 1) r) := by
    simpa only [Real.rpow_neg_one] using
      _root_.GD.N0051.d022782 (by linarith : 0 < s + 1) hr
        (u := -1) (by linarith)
  have hQ : Integrable (fun z : ℝ × Ω => z.1⁻¹ * _root_.GD.N0213.N0495.d007174 L (z.1 + b z.2) ^ 2)
      ((gammaMeasure (s + 1) r).prod ν) := by
    apply (hinv.comp_fst ν).norm.mono'
      ((measurable_fst.inv.mul (by unfold _root_.GD.N0213.N0495.d007174; fun_prop)).aestronglyMeasurable)
    filter_upwards with z
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (_root_.GD.N0213.N0519.d007983 L _)
  rw [integral_prod_symm _ hQ, integral_prod_symm _ hM, integral_prod_symm _ hE,
    ← integral_const_mul, ← integral_const_mul,
    ← integral_sub (hM.integral_prod_right.const_mul _) (hE.integral_prod_right.const_mul _)]
  apply integral_congr_ae
  filter_upwards [hb0] with y hy
  exact _root_.GD.N0213.N0520.d023082 hs hr hL hy

theorem d023099 (ν : Measure Ω) [IsFiniteMeasure ν]
    (b : Ω → ℝ) (hb : Measurable b) (hb0 : ∀ᵐ y ∂ν, 0 ≤ b y)
    {s r L : ℝ} (hs : 0 < s) (hr : 0 < r) (hL : 0 < L) :
    (∫ z : ℝ × Ω, _root_.GD.N0213.N0495.d007174 L (z.1 + b z.2) * _root_.GD.N0213.N0495.d007175 L (z.1 + b z.2)
        ∂(gammaMeasure (s + 1) r).prod ν) ^ 2 ≤
      (∫ z : ℝ × Ω, _root_.GD.N0213.N0495.d007174 L (z.1 + b z.2) ^ 2
        ∂(gammaMeasure (s + 1) r).prod ν) *
      (∫ z : ℝ × Ω, _root_.GD.N0213.N0495.d007175 L (z.1 + b z.2) ^ 2
        ∂(gammaMeasure (s + 1) r).prod ν) := by
  letI := isProbabilityMeasure_gammaMeasure (by linarith : 0 < s + 1) hr
  exact _root_.GD.N0213.N0513.d008016 ((gammaMeasure (s + 1) r).prod ν) _
    (measurable_fst.add (hb.comp measurable_snd)) hL
    (_root_.GD.N0213.N0507.d023097 ν b hb hb0 hs hr)

theorem d023100 {k : ℕ} (μ : Fin (k + 1) → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (i : Fin (k + 1)) (f : (Fin (k + 1) → ℝ) → ℝ) :
    (∫ x, f x ∂Measure.pi μ) =
      ∫ z : ℝ × (Fin k → ℝ), f (i.insertNth z.1 z.2)
        ∂(μ i).prod (Measure.pi fun j => μ (i.succAbove j)) := by
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk] using ((measurePreserving_piFinSuccAbove μ i).symm.integral_comp' f).symm

theorem d023101 {k : ℕ} (i : Fin (k + 1)) (x : ℝ) (y : Fin k → ℝ) :
    (∑ j, i.insertNth x y j) = x + ∑ j, y j := by
  rw [Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

theorem d023102 {k : ℕ} (s r : Fin (k + 1) → ℝ)
    (hs : ∀ i, 0 < s i) (hr : ∀ i, 0 < r i) {L : ℝ} (hL : 0 < L)
    (i : Fin (k + 1)) :
    (∫ β : Fin (k + 1) → ℝ, (β i)⁻¹ * _root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2
        ∂Measure.pi (fun j => gammaMeasure (s j + 1) (r j))) =
      (r i / s i) * (∫ β : Fin (k + 1) → ℝ, _root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2
        ∂Measure.pi (fun j => gammaMeasure (s j + 1) (r j))) -
      (2 / s i) * (∫ β : Fin (k + 1) → ℝ,
        _root_.GD.N0213.N0495.d007174 L (∑ j, β j) * _root_.GD.N0213.N0495.d007175 L (∑ j, β j)
        ∂Measure.pi (fun j => gammaMeasure (s j + 1) (r j))) := by
  let μ : Fin (k + 1) → Measure ℝ := fun j => gammaMeasure (s j + 1) (r j)
  letI (j : Fin (k + 1)) : IsProbabilityMeasure (μ j) :=
    isProbabilityMeasure_gammaMeasure (by have := hs j; linarith) (hr j)
  change (∫ β, (β i)⁻¹ * _root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2 ∂Measure.pi μ) = _
  rw [_root_.GD.N0213.N0507.d023100 μ i,
    _root_.GD.N0213.N0507.d023100 μ i (fun β => _root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2),
    _root_.GD.N0213.N0507.d023100 μ i
      (fun β => _root_.GD.N0213.N0495.d007174 L (∑ j, β j) * _root_.GD.N0213.N0495.d007175 L (∑ j, β j))]
  simp_rw [_root_.GD.N0213.N0507.d023101, Fin.insertNth_apply_same]
  apply _root_.GD.N0213.N0507.d023098 (Measure.pi fun j => μ (i.succAbove j))
    (fun β => ∑ j, β j) (by fun_prop) _ (hs i) (hr i) hL
  have hpos := _root_.GD.N0232.N0719.N0910.d010287
    (shape := fun j => s (i.succAbove j) + 1) (rate := fun j => r (i.succAbove j))
    (fun j => by have := hs (i.succAbove j); linarith) (fun j => hr (i.succAbove j))
  filter_upwards [hpos] with β hβ
  exact Finset.sum_nonneg (fun j _ => (hβ j).le)

theorem d023103 {k : ℕ} (s r : Fin (k + 1) → ℝ)
    (hs : ∀ i, 0 < s i) (hr : ∀ i, 0 < r i) {L : ℝ} (hL : 0 < L) :
    (∫ β : Fin (k + 1) → ℝ,
        _root_.GD.N0213.N0495.d007174 L (∑ j, β j) * _root_.GD.N0213.N0495.d007175 L (∑ j, β j)
        ∂Measure.pi (fun j => gammaMeasure (s j + 1) (r j))) ^ 2 ≤
      (∫ β : Fin (k + 1) → ℝ, _root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2
        ∂Measure.pi (fun j => gammaMeasure (s j + 1) (r j))) *
      (∫ β : Fin (k + 1) → ℝ, _root_.GD.N0213.N0495.d007175 L (∑ j, β j) ^ 2
        ∂Measure.pi (fun j => gammaMeasure (s j + 1) (r j))) := by
  letI (j : Fin (k + 1)) :=
    isProbabilityMeasure_gammaMeasure (by have := hs j; linarith : 0 < s j + 1) (hr j)
  apply _root_.GD.N0213.N0513.d008016
    (Measure.pi fun j => gammaMeasure (s j + 1) (r j))
    (fun β : Fin (k + 1) → ℝ => ∑ j, β j) (by fun_prop) hL
  filter_upwards [_root_.GD.N0232.N0719.N0910.d010287
    (shape := fun j => s j + 1) (rate := r)
    (fun j => by have := hs j; linarith) hr] with β hβ
  exact Finset.sum_pos (fun j _ => hβ j) Finset.univ_nonempty

theorem d023104 {k : ℕ}
    (s t w : Fin (k + 1) → ℝ) {c L : ℝ}
    (hs : ∀ i, 0 < s i) (ht : ∀ i, 0 < t i) (hc : 0 < c) (hL : 0 < L)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) :
    let μ := Measure.pi fun i => gammaMeasure (s i + 1) (c * s i * t i)
    let q := fun i => ∫ β : Fin (k + 1) → ℝ, (β i)⁻¹ * _root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2 ∂μ
    let D := ∫ β : Fin (k + 1) → ℝ, _root_.GD.N0213.N0495.d007175 L (∑ j, β j) ^ 2 ∂μ
    (∑ i, q i * _root_.GD.N0230.N0665.d000407 t i ^ 2) -
      (∑ i, q i * w i ^ 2) ≤
      ∑ i, ∑ j, if i = j then 0 else
        4 * (D / s i ^ 2 + D / s j ^ 2) / (c * (t i + t j)) := by
  let r : Fin (k + 1) → ℝ := fun i => c * s i * t i
  have hr : ∀ i, 0 < r i := fun i => mul_pos (mul_pos hc (hs i)) (ht i)
  let μ := Measure.pi fun i => gammaMeasure (s i + 1) (r i)
  let m := ∫ β : Fin (k + 1) → ℝ, _root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2 ∂μ
  let e := ∫ β : Fin (k + 1) → ℝ,
    _root_.GD.N0213.N0495.d007174 L (∑ j, β j) * _root_.GD.N0213.N0495.d007175 L (∑ j, β j) ∂μ
  let D := ∫ β : Fin (k + 1) → ℝ, _root_.GD.N0213.N0495.d007175 L (∑ j, β j) ^ 2 ∂μ
  letI (i : Fin (k + 1)) :=
    isProbabilityMeasure_gammaMeasure (by have := hs i; linarith : 0 < s i + 1) (hr i)
  have hm : 0 < m := _root_.GD.N0213.N0513.d008017 μ (fun β => ∑ j, β j) (by fun_prop) L
  have hCS : e ^ 2 ≤ m * D := _root_.GD.N0213.N0507.d023103 s r hs hr hL
  have hq (i : Fin (k + 1)) :
      (∫ β : Fin (k + 1) → ℝ, (β i)⁻¹ * _root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2 ∂μ) =
        c * m * t i - 2 * e / s i := by
    rw [_root_.GD.N0213.N0507.d023102 s r hs hr hL i]
    change (c * s i * t i / s i) * m - (2 / s i) * e = _
    field_simp [(hs i).ne']
  change (∑ i, (∫ β : Fin (k + 1) → ℝ, (β i)⁻¹ * _root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2 ∂μ) *
      _root_.GD.N0230.N0665.d000407 t i ^ 2) -
    (∑ i, (∫ β : Fin (k + 1) → ℝ, (β i)⁻¹ * _root_.GD.N0213.N0495.d007174 L (∑ j, β j) ^ 2 ∂μ) * w i ^ 2) ≤ _
  simp_rw [hq]
  have hw (i : Fin (k + 1)) : w i ∈ Icc (0 : ℝ) 1 := by
    refine ⟨hw0 i, ?_⟩
    calc
      w i ≤ ∑ j, w j := Finset.single_le_sum (fun j _ => hw0 j) (Finset.mem_univ i)
      _ = 1 := hw1
  exact _root_.GD.N0213.N0506.d008441 t s
    (fun _ => e) (fun _ => D) w c m ht hs hc hm hw hw1 (fun _ => hCS)

end
end GD.N0213.N0507

#print axioms _root_.GD.N0213.N0507.d023098
#print axioms _root_.GD.N0213.N0507.d023099
#print axioms _root_.GD.N0213.N0507.d023102
#print axioms _root_.GD.N0213.N0507.d023103
#print axioms _root_.GD.N0213.N0507.d023104
