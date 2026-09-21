import GD.Module0231
import GD.Module0251
import GD.Module0637
import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Integral.Pi
































open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace GD.N0232.N0719.N0954

noncomputable section





def d009342 {k : ℕ}
    (shape rate : Fin k → ℝ) : Measure (Fin k → ℝ) :=
  Measure.pi fun i => gammaMeasure (shape i) (rate i)


def d009343 {k : ℕ}
    (shape rate : Fin k → ℝ) (t : Fin k → ℝ) : ℝ :=
  ∏ i, gammaPDFReal (shape i) (rate i) (t i)



def d009344 (k : ℕ) (hk : 0 < k) :
    _root_.GD.N0232.N0719.N0953.d003305 (k - 1) ≃ Fin k :=
  finSumFinEquiv.trans
    (finCongr (Nat.sub_add_cancel hk))


def d009345 (k : ℕ) (hk : 0 < k) :
    _root_.GD.N0232.N0719.N0953.d003306 (k - 1) ≃ᵐ (Fin k → ℝ) :=
  MeasurableEquiv.piCongrLeft
    (fun _ : Fin k => ℝ) (_root_.GD.N0232.N0719.N0954.d009344 k hk)



def d009346 {k : ℕ} (hk : 0 < k)
    (t : Fin k → ℝ) : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) :=
  (_root_.GD.N0232.N0719.N0954.d009345 k hk).symm t


def d009347 {k : ℕ} (hk : 0 < k)
    (t : Fin k → ℝ) : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) :=
  _root_.GD.N0232.N0719.N0953.d003314 (_root_.GD.N0232.N0719.N0954.d009346 hk t)


def d009348 {k : ℕ} (hk : 0 < k)
    (t : Fin k → ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0953.d003308 (_root_.GD.N0232.N0719.N0954.d009347 hk t)



def d009349 {k : ℕ} (hk : 0 < k)
    (t : Fin k → ℝ) (i : Fin k) : ℝ :=
  _root_.GD.N0232.N0719.N0953.d003334 (_root_.GD.N0232.N0719.N0954.d009347 hk t)
    ((_root_.GD.N0232.N0719.N0954.d009344 k hk).symm i)


def d009350 {k : ℕ} (hk : 0 < k)
    (f : Fin k → ℝ) : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) :=
  fun i => f (_root_.GD.N0232.N0719.N0954.d009344 k hk i)





theorem d009351
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (G : ℝ → ℝ) :
    (∫ x, G x ∂gammaMeasure a r) =
      ∫ x, gammaPDFReal a r x * G x := by
  rw [gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (f := gammaPDF a r)
      ((measurable_gammaPDFReal a r).ennreal_ofReal)
      (by simp [gammaPDF])]
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul, gammaPDF, ENNReal.toReal_ofReal
    (gammaPDFReal_nonneg ha hr x)]


theorem d009352
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Integrable (gammaPDFReal a r) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (stronglyMeasurable_gammaPDFReal a r).aestronglyMeasurable
    (ae_of_all volume fun x =>
      gammaPDFReal_nonneg ha hr x)).1
  change (∫⁻ x, gammaPDF a r x) ≠ ⊤
  rw [lintegral_gammaPDF_eq_one ha hr]
  exact ENNReal.one_ne_top




theorem d009353
    {a r c x : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hc : 0 < c) :
    c⁻¹ * gammaPDFReal a r (c⁻¹ * x) =
      gammaPDFReal a (r / c) x := by
  by_cases hx : 0 ≤ x
  · have hci : 0 < c⁻¹ := inv_pos.mpr hc
    have harg : 0 ≤ c⁻¹ * x := mul_nonneg hci.le hx
    have hcPower :
        c⁻¹ * (c⁻¹) ^ (a - 1) = (c ^ a)⁻¹ := by
      calc
        c⁻¹ * (c⁻¹) ^ (a - 1) =
            (c ^ (1 : ℝ))⁻¹ * (c ^ (a - 1))⁻¹ := by
          rw [Real.inv_rpow hc.le (a - 1), Real.rpow_one]
        _ = (c ^ (1 : ℝ) * c ^ (a - 1))⁻¹ := by
          rw [mul_inv]
        _ = (c ^ (1 + (a - 1)))⁻¹ := by
          exact congrArg Inv.inv
            (Real.rpow_add hc (1 : ℝ) (a - 1)).symm
        _ = (c ^ a)⁻¹ := by
          congr 2
          ring
    have hexponent :
        r * (c⁻¹ * x) = (r / c) * x := by
      field_simp [hc.ne']
    simp only [gammaPDFReal, if_pos hx, if_pos harg]
    rw [Real.mul_rpow hci.le hx,
      Real.div_rpow hr.le hc.le, hexponent]
    simp only [div_eq_mul_inv]
    calc
      _ = (c⁻¹ * (c⁻¹) ^ (a - 1)) *
          (r ^ a * (Real.Gamma a)⁻¹ * x ^ (a - 1) *
            Real.exp (-(r * c⁻¹ * x))) := by
        ac_rfl
      _ = _ := by
        rw [hcPower]
        ac_rfl
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hargneg : c⁻¹ * x < 0 :=
      mul_neg_of_pos_of_neg (inv_pos.mpr hc) hxneg
    simp [gammaPDFReal, not_le.mpr hxneg,
      not_le.mpr hargneg]


theorem d009354
    {a r c : ℝ}
    (ha : 0 < a) (hr : 0 < r) (hc : 0 < c) :
    (gammaMeasure a r).map (c * ·) =
      gammaMeasure a (r / c) := by
  let e : ℝ ≃ᵐ ℝ :=
    (Homeomorph.mulLeft₀ c hc.ne').symm.toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e ((fun _ => c⁻¹) x) x := by
    intro x
    simpa [e, Homeomorph.mulLeft₀] using
      (hasDerivAt_id x).const_mul c⁻¹
  change (gammaMeasure a r).map e.symm =
    gammaMeasure a (r / c)
  ext s hs
  change
    (volume.withDensity
        (fun x => ENNReal.ofReal (gammaPDFReal a r x))).map e.symm s =
      (volume.withDensity
        (fun x => ENNReal.ofReal
          (gammaPDFReal a (r / c) x))) s
  rw [
    e.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul'
      hs he'
      (ae_of_all volume fun x => gammaPDFReal_nonneg ha hr x)
      (_root_.GD.N0232.N0719.N0954.d009352 ha hr)]
  rw [withDensity_apply _ hs]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (_root_.GD.N0232.N0719.N0954.d009352 ha (div_pos hr hc)).integrableOn
    (ae_restrict_of_ae
      (ae_of_all volume fun x =>
        gammaPDFReal_nonneg ha (div_pos hr hc) x))]
  congr 1
  apply setIntegral_congr_fun hs
  intro x _
  simp only [e, Homeomorph.mulLeft₀,
    Equiv.mulLeft₀_symm_apply,
    Homeomorph.toMeasurableEquiv_coe,
    Homeomorph.homeomorph_mk_coe_symm,
    abs_inv, abs_of_pos hc]
  exact _root_.GD.N0232.N0719.N0954.d009353 ha hr hc


def d009355 {k : ℕ} (sizes : Fin k → ℕ)
    (i : Fin k) : ℝ :=
  (((sizes i - 1 : ℕ) : ℝ) / 2)


def d009356 {k : ℕ}
    (sizes : Fin k → ℕ) (scales : Fin k → ℝ)
    (i : Fin k) : ℝ :=
  scales i ^ 2 / sizes i


def d009357 {k : ℕ}
    (sizes : Fin k → ℕ) (scales : Fin k → ℝ)
    (i : Fin k) : ℝ :=
  _root_.GD.N0232.N0719.N0954.d009355 sizes i / _root_.GD.N0232.N0719.N0954.d009356 sizes scales i

theorem d009358
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 2 ≤ sizes i) (i : Fin k) :
    0 < _root_.GD.N0232.N0719.N0954.d009355 sizes i := by
  unfold _root_.GD.N0232.N0719.N0954.d009355
  have hni : 2 ≤ sizes i := hsizes i
  have hsub : 0 < sizes i - 1 := by omega
  have hsubR : 0 < ((sizes i - 1 : ℕ) : ℝ) := by
    exact_mod_cast hsub
  exact div_pos hsubR (by norm_num)

theorem d009359
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 2 ≤ sizes i)
    {scales : Fin k → ℝ}
    (hscales : ∀ i, 0 < scales i) (i : Fin k) :
    0 < _root_.GD.N0232.N0719.N0954.d009356 sizes scales i := by
  unfold _root_.GD.N0232.N0719.N0954.d009356
  have hni : 2 ≤ sizes i := hsizes i
  have hn : 0 < sizes i := by omega
  exact div_pos
    (pow_pos (hscales i) 2)
    (by exact_mod_cast hn)

theorem d009360
    {k : ℕ} {sizes : Fin k → ℕ}
    (hsizes : ∀ i, 2 ≤ sizes i)
    {scales : Fin k → ℝ}
    (hscales : ∀ i, 0 < scales i) (i : Fin k) :
    0 < _root_.GD.N0232.N0719.N0954.d009357 sizes scales i :=
  div_pos (_root_.GD.N0232.N0719.N0954.d009358 hsizes i)
    (_root_.GD.N0232.N0719.N0954.d009359 hsizes hscales i)



theorem d009361
    {n : ℕ} (hn : 2 ≤ n)
    {scale : ℝ} (hscale : 0 < scale) :
    _root_.GD.N0232.N0719.N0933.d009289 n scale =
      gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
        ((((n - 1 : ℕ) : ℝ) / 2) /
          (scale ^ 2 / n)) := by
  have ha : 0 < (((n - 1 : ℕ) : ℝ) / 2) := by
    have : 0 < n - 1 := by omega
    positivity
  have hv : 0 < scale ^ 2 / (n : ℝ) := by
    have hnpos : 0 < n := by omega
    positivity
  unfold _root_.GD.N0232.N0719.N0933.d009289 _root_.GD.N0232.N0719.N0933.d009287
  simpa using _root_.GD.N0232.N0719.N0954.d009354 ha ha hv






theorem d009362
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (scales : Fin k → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0232.N0719.N0933.d009301 k sizes scales =
      _root_.GD.N0232.N0719.N0954.d009342
        (_root_.GD.N0232.N0719.N0954.d009355 sizes)
        (_root_.GD.N0232.N0719.N0954.d009357 sizes scales) := by
  unfold _root_.GD.N0232.N0719.N0933.d009301 _root_.GD.N0232.N0719.N0954.d009342
  congr 1
  funext i
  simpa [_root_.GD.N0232.N0719.N0954.d009355, _root_.GD.N0232.N0719.N0954.d009357,
    _root_.GD.N0232.N0719.N0954.d009356] using
    _root_.GD.N0232.N0719.N0954.d009361
      (hsizes i) (hscales i)








theorem d009363
    {k : ℕ} {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i) :
    _root_.GD.N0232.N0719.N0954.d009342 shape rate =
      volume.withDensity
        (fun t => ENNReal.ofReal
          (_root_.GD.N0232.N0719.N0954.d009343 shape rate t)) := by
  apply Measure.pi_eq
  intro s hs
  have hrect :
      MeasurableSet (Set.pi Set.univ s) :=
    MeasurableSet.pi Set.countable_univ fun i _ => hs i
  rw [withDensity_apply _ hrect]
  have hcoord_nonneg :
      ∀ i x, 0 ≤ gammaPDFReal (shape i) (rate i) x :=
    fun i x => gammaPDFReal_nonneg (hshape i) (hrate i) x
  have hindicator_nonneg :
      ∀ i x, 0 ≤ (s i).indicator
        (gammaPDFReal (shape i) (rate i)) x := by
    intro i x
    by_cases hx : x ∈ s i
    · simp [hx, hcoord_nonneg i x]
    · simp [hx]
  have hfactor :
      (Set.pi Set.univ s).indicator
          (_root_.GD.N0232.N0719.N0954.d009343 shape rate) =
        fun t => ∏ i,
          (s i).indicator
            (gammaPDFReal (shape i) (rate i)) (t i) := by
    funext t
    by_cases ht : t ∈ Set.pi Set.univ s
    · have hti : ∀ i, t i ∈ s i := by
        simpa [Set.mem_pi] using ht
      simp [ht, _root_.GD.N0232.N0719.N0954.d009343, hti]
    · have hnot : ∃ i, t i ∉ s i := by
        simpa [Set.mem_pi] using ht
      obtain ⟨i, hi⟩ := hnot
      simp [ht, _root_.GD.N0232.N0719.N0954.d009343, hi,
        Finset.prod_eq_zero (Finset.mem_univ i)]
  rw [← lintegral_indicator hrect]
  rw [show
      (Set.pi Set.univ s).indicator
          (fun t => ENNReal.ofReal
            (_root_.GD.N0232.N0719.N0954.d009343 shape rate t)) =
        fun t => ENNReal.ofReal
          ((Set.pi Set.univ s).indicator
            (_root_.GD.N0232.N0719.N0954.d009343 shape rate) t) by
      funext t
      by_cases ht : t ∈ Set.pi Set.univ s <;> simp [ht]]
  rw [hfactor]
  have hcoord_integrable :
      ∀ i, Integrable
        ((s i).indicator
          (gammaPDFReal (shape i) (rate i))) := by
    intro i
    exact (integrable_indicator_iff (hs i)).2
      (_root_.GD.N0232.N0719.N0954.d009352 (hshape i) (hrate i)).integrableOn
  have hproduct_integrable :
      Integrable (fun t : Fin k → ℝ =>
        ∏ i, (s i).indicator
          (gammaPDFReal (shape i) (rate i)) (t i)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod hcoord_integrable
  rw [← ofReal_integral_eq_lintegral_ofReal
    hproduct_integrable
    (ae_of_all volume fun t =>
      Finset.prod_nonneg fun i _ => hindicator_nonneg i (t i))]
  rw [integral_fintype_prod_volume_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun i _ => integral_nonneg (hindicator_nonneg i))]
  apply Finset.prod_congr rfl
  · intro i _
    calc
      ENNReal.ofReal
          (∫ x, (s i).indicator
            (gammaPDFReal (shape i) (rate i)) x) =
          ∫⁻ x, ENNReal.ofReal
            ((s i).indicator
              (gammaPDFReal (shape i) (rate i)) x) :=
        ofReal_integral_eq_lintegral_ofReal
          (hcoord_integrable i)
          (ae_of_all volume (hindicator_nonneg i))
      _ = ∫⁻ x, (s i).indicator
            (gammaPDF (shape i) (rate i)) x := by
        apply lintegral_congr
        intro x
        by_cases hx : x ∈ s i
        · simp [hx, gammaPDF, hcoord_nonneg i x]
        · simp [hx]
      _ = gammaMeasure (shape i) (rate i) (s i) := by
        rw [gammaMeasure, withDensity_apply _ (hs i),
          ← lintegral_indicator (hs i)]



theorem d009364
    {k : ℕ} {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    (G : (Fin k → ℝ) → ℝ) :
    (∫ t, G t ∂_root_.GD.N0232.N0719.N0954.d009342 shape rate) =
      ∫ t, _root_.GD.N0232.N0719.N0954.d009343 shape rate t * G t := by
  rw [_root_.GD.N0232.N0719.N0954.d009363 hshape hrate,
    integral_withDensity_eq_integral_toReal_smul
      (f := fun t => ENNReal.ofReal
        (_root_.GD.N0232.N0719.N0954.d009343 shape rate t))
      ((Finset.measurable_prod _ fun i _ =>
        (measurable_gammaPDFReal (shape i) (rate i)).comp
          (measurable_pi_apply i)).ennreal_ofReal)
      (by simp)]
  apply integral_congr_ae
  filter_upwards with t
  have hpdf :
      0 ≤ _root_.GD.N0232.N0719.N0954.d009343 shape rate t := by
    exact Finset.prod_nonneg fun i _ =>
      gammaPDFReal_nonneg (hshape i) (hrate i) (t i)
  simp [smul_eq_mul, hpdf]

end

end GD.N0232.N0719.N0954
