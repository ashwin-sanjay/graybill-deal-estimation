import GD.Module0758

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace GD.N0074

theorem d022920
    {α : Type*} {m m₀ : MeasurableSpace α} {μ : Measure α}
    (hm : m ≤ m₀) [IsFiniteMeasure μ] [SigmaFinite (μ.trim hm)]
    {f h : α → ℝ} (hf : Integrable f μ)
    (hh : StronglyMeasurable[m] h)
    (hprod : Integrable (h * f) μ)
    (hqprod : Integrable (h * μ[f | m]) μ) :
    (∫ x, h x * (f x - μ[f | m] x) ∂μ) = 0 := by
  have heq : (∫ x, (h * f) x ∂μ) = ∫ x, (h * μ[f | m]) x ∂μ := by
    calc
      (∫ x, (h * f) x ∂μ) = ∫ x, μ[h * f | m] x ∂μ :=
        (integral_condExp hm).symm
      _ = ∫ x, (h * μ[f | m]) x ∂μ :=
        integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hh hprod hf)
  calc
    (∫ x, h x * (f x - μ[f | m] x) ∂μ) =
        ∫ x, (h * f) x - (h * μ[f | m]) x ∂μ := by
      congr 1
      funext x
      simp only [Pi.mul_apply]
      ring
    _ = (∫ x, (h * f) x ∂μ) - ∫ x, (h * μ[f | m]) x ∂μ :=
      integral_sub hprod hqprod
    _ = 0 := sub_eq_zero.mpr heq

theorem d022921
    {α : Type*} {m m₀ : MeasurableSpace α} {μ : Measure α}
    (hm : m ≤ m₀) [IsFiniteMeasure μ] [SigmaFinite (μ.trim hm)]
    {f h : α → ℝ} (hf : Integrable f μ)
    (hh : StronglyMeasurable[m] h)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖h x‖ ≤ C) :
    (∫ x, h x * (f x - μ[f | m] x) ∂μ) = 0 := by
  exact _root_.GD.N0074.d022920 hm hf hh
    (hf.bdd_mul (hh.mono hm).aestronglyMeasurable hC)
    (integrable_condExp.bdd_mul (hh.mono hm).aestronglyMeasurable hC)

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N1012
open _root_.GD.N0230.N0602

theorem d022922
    (k : ℕ) (sizes : Fin k → ℕ)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    (fun x ↦ _root_.GD.N0232.N0719.N1012.d011399 k sizes d x) =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010813 k sizes]
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)[
        (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) | _root_.GD.N0232.N0719.N1012.d011397 k sizes] := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
    unfold _root_.GD.N0232.N0719.N0859.d010813
    infer_instance
  simpa only [_root_.GD.N0232.N0719.N1012.d011400, Lp.toLp_coeFn] using
    (Lp.memLp d).condExpL2_ae_eq_condExp
      (_root_.GD.N0232.N0719.N1012.d011398 k sizes)

theorem d022923
    (k : ℕ) (sizes : Fin k → ℕ)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (h : _root_.GD.N0232.N0719.d009173 k sizes → ℝ)
    (hh : StronglyMeasurable[_root_.GD.N0232.N0719.N1012.d011397 k sizes] h)
    (C : ℝ) (hC : ∀ᵐ x ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes,
      ‖h x‖ ≤ C) :
    (∫ x, h x * (d x - _root_.GD.N0232.N0719.N1012.d011399 k sizes d x)
      ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) = 0 := by
  letI : IsProbabilityMeasure
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
    unfold _root_.GD.N0232.N0719.N0859.d010813
    infer_instance
  calc
    _ = ∫ x, h x * (d x -
        (_root_.GD.N0232.N0719.N0859.d010813 k sizes)[
          (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) | _root_.GD.N0232.N0719.N1012.d011397 k sizes] x)
        ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes := by
      apply integral_congr_ae
      filter_upwards [_root_.GD.N0074.d022922 k sizes d] with x hx
      rw [hx]
    _ = 0 := _root_.GD.N0074.d022921 (_root_.GD.N0232.N0719.N1012.d011398 k sizes)
      ((Lp.memLp d).integrable (by norm_num)) hh C hC

theorem d022924
    (k : ℕ) (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hd : MemLp (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)) :
    MemLp (fun x ↦ _root_.GD.N0232.N0719.N1012.d011399 k sizes d x) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
    unfold _root_.GD.N0232.N0719.N0859.d010812
    infer_instance
  have hqmeas : AEStronglyMeasurable
      (fun x ↦ _root_.GD.N0232.N0719.N1012.d011399 k sizes d x) (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) :=
    (Lp.aestronglyMeasurable (_root_.GD.N0232.N0719.N1012.d011399 k sizes d)).mono_ac
      (_root_.GD.N0232.N0719.N0859.d010814 k sizes theta)
  have hcenter : MemLp (fun x ↦ d x - theta.location) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) :=
    hd.sub (memLp_const theta.location)
  have hqcentermeas : AEStronglyMeasurable
      (fun x ↦ _root_.GD.N0232.N0719.N1012.d011399 k sizes d x - theta.location) (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) :=
    hqmeas.sub aestronglyMeasurable_const
  have hfin : _root_.GD.N0232.N0719.N0859.d010821 k sizes theta d ≠ ⊤ := by
    exact (lintegral_ofReal_ne_top_iff_integrable
      hcenter.integrable_sq.aestronglyMeasurable
      (ae_of_all _ fun x ↦ sq_nonneg _)).2 hcenter.integrable_sq
  have hqfin : _root_.GD.N0232.N0719.N0859.d010821 k sizes theta (_root_.GD.N0232.N0719.N1012.d011399 k sizes d) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (_root_.GD.N0232.N0719.N1012.d011407 k sizes hsizes theta d)
  have hqcenter : MemLp
      (fun x ↦ _root_.GD.N0232.N0719.N1012.d011399 k sizes d x - theta.location) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
    apply (memLp_two_iff_integrable_sq hqcentermeas).2
    exact (lintegral_ofReal_ne_top_iff_integrable
      (hqcentermeas.pow 2) (ae_of_all _ fun x ↦ sq_nonneg _)).1 hqfin
  refine MemLp.ae_eq (ae_of_all _ fun x ↦ ?_)
    (hqcenter.add (memLp_const theta.location))
  simp only [Pi.add_apply, sub_add_cancel]

theorem d022925
    (k : ℕ) (sizes : Fin k → ℕ)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    ∃ g : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ, Measurable g ∧
      ∀ theta : _root_.GD.N0232.N0719.N0859.d010809 k,
        (fun x ↦ _root_.GD.N0232.N0719.N1012.d011399 k sizes d x) =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes theta]
          g ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes := by
  have hp := _root_.GD.N0232.N0719.N1012.d011401 k sizes d
  obtain ⟨g, hg, hfactor⟩ := hp.stronglyMeasurable_mk.exists_eq_measurable_comp
  refine ⟨g, hg.measurable, fun theta ↦ ?_⟩
  have hae := (_root_.GD.N0232.N0719.N0859.d010814 k sizes theta).ae_le hp.ae_eq_mk
  filter_upwards [hae] with x hx
  exact hx.trans (congrFun hfactor x)

theorem d022926
    (k : ℕ) (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hd : MemLp (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta))
    (c : ℝ) :
    (∫ x, (d x - c) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) =
      (∫ x, (_root_.GD.N0232.N0719.N1012.d011399 k sizes d x - c) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) +
        ∫ x, (d x - _root_.GD.N0232.N0719.N1012.d011399 k sizes d x) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
    unfold _root_.GD.N0232.N0719.N0859.d010813
    infer_instance
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
    unfold _root_.GD.N0232.N0719.N0859.d010812
    infer_instance
  let w := _root_.GD.N0232.N0719.N0865.d011217 k sizes theta
  have hw : Measurable w :=
    _root_.GD.N0232.N0719.N0865.d011218 k sizes theta
  have hw0 : ∀ x, 0 ≤ w x :=
    _root_.GD.N0232.N0719.N0865.d011219 k sizes theta
  have hwm : StronglyMeasurable[_root_.GD.N0232.N0719.N1012.d011397 k sizes] w :=
    (_root_.GD.N0232.N0719.N1011.d011294
      k sizes hsizes theta).stronglyMeasurable
  have hchange (g : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) :
      (∫ x, g x ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) =
        ∫ x, w x * g x ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes := by
    exact _root_.GD.N0230.N0591.d000135
      w g (_root_.GD.N0232.N0719.N0865.d011220 k sizes theta) hw hw0
  have hfull : Integrable (fun x ↦ w x * (d x - c) ^ 2)
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
    have H := (hd.sub (memLp_const c)).integrable_sq
    rw [_root_.GD.N0232.N0719.N0865.d011220 k sizes theta,
      integrable_withDensity_iff_integrable_smul' hw.ennreal_ofReal
        (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)] at H
    refine H.congr (ae_of_all _ fun x ↦ ?_)
    simp only [ENNReal.toReal_ofReal (hw0 x), smul_eq_mul, Pi.sub_apply]
  have H := _root_.GD.N0230.N0716.d001323
      (_root_.GD.N0232.N0719.N1012.d011398 k sizes) c (Lp.memLp d) hwm
      (ae_of_all _ hw0) hfull
  have hcenter :
      (∫ x, w x * ((_root_.GD.N0232.N0719.N0859.d010813 k sizes)[
        (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) |
          _root_.GD.N0232.N0719.N1012.d011397 k sizes] x - c) ^ 2
        ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) =
      ∫ x, w x * (_root_.GD.N0232.N0719.N1012.d011399 k sizes d x - c) ^ 2
        ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes := by
    apply integral_congr_ae
    filter_upwards [_root_.GD.N0074.d022922 k sizes d] with x hx
    rw [hx]
  have hresidual :
      (∫ x, w x * (d x - (_root_.GD.N0232.N0719.N0859.d010813 k sizes)[
        (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) |
          _root_.GD.N0232.N0719.N1012.d011397 k sizes] x) ^ 2
        ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes) =
      ∫ x, w x * (d x - _root_.GD.N0232.N0719.N1012.d011399 k sizes d x) ^ 2
        ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes := by
    apply integral_congr_ae
    filter_upwards [_root_.GD.N0074.d022922 k sizes d] with x hx
    rw [hx]
  rw [hcenter, hresidual] at H
  rw [hchange, hchange, hchange]
  exact H

end GD.N0074

#print axioms _root_.GD.N0074.d022920
#print axioms _root_.GD.N0074.d022924
#print axioms _root_.GD.N0074.d022923
#print axioms _root_.GD.N0074.d022925
#print axioms _root_.GD.N0074.d022926
