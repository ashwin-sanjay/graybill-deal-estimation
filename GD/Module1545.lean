import GD.Module1544
import GD.Module1531

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace GD.N0088
noncomputable section
open _root_.GD.N0051

def d023935 (p q w : ℝ) (u : _root_.GD.N0051.d023832) : ℝ :=
  _root_.GD.N0051.d022763 p q u.1.1 (Real.sqrt w * u.1.2) u.2.1 (w * u.2.2) ^ 2 / w

theorem d023936 {p q w : ℝ} (hq : 0 < q)
    (hw : 0 < w) (hw1 : w ≤ 1) (hr : 0 ≤ p / q)
    (u : _root_.GD.N0051.d023832) (hx : 0 < u.2.1) (hy : 0 < u.2.2) :
    _root_.GD.N0088.d023935 p q w u ≤
      2 * _root_.GD.N0088.d023931 (p / q) u + 2 * u.1.2 ^ 2 := by
  have he := (div_le_iff₀ hw).mp (_root_.GD.N0088.d023933 hq hw hw1 hr u hx hy)
  have hy2 : (Real.sqrt w * u.1.2) ^ 2 = w * u.1.2 ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hw.le]
  unfold _root_.GD.N0088.d023935
  apply (div_le_iff₀ hw).mpr
  nlinarith [sq_nonneg (_root_.GD.N0051.d022763 p q u.1.1 (Real.sqrt w * u.1.2)
    u.2.1 (w * u.2.2) - 2 * (Real.sqrt w * u.1.2))]

theorem d023937 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᵐ u ∂_root_.GD.N0051.d023833 a b, 0 < u.2.1 ∧ 0 < u.2.2 ∧ u.1.1 ≠ 0 := by
  letI := isProbabilityMeasure_gammaMeasure ha ha
  letI := isProbabilityMeasure_gammaMeasure hb hb
  letI := noAtoms_gaussianReal (μ := (0 : ℝ)) (v := 1) (by norm_num)
  have hx := (Measure.quasiMeasurePreserving_fst (μ := gammaMeasure a a)
    (ν := gammaMeasure b b)).ae
    (_root_.GD.N0232.N0719.N0910.d010286 ha ha)
  have hy := (Measure.quasiMeasurePreserving_snd (μ := gammaMeasure a a)
    (ν := gammaMeasure b b)).ae
    (_root_.GD.N0232.N0719.N0910.d010286 hb hb)
  have hz := (Measure.quasiMeasurePreserving_fst (μ := gaussianReal 0 1)
    (ν := gaussianReal 0 1)).ae ((gaussianReal 0 1).ae_ne 0)
  filter_upwards [
    (Measure.quasiMeasurePreserving_snd (μ := _root_.GD.N0051.d022792)).ae hx,
    (Measure.quasiMeasurePreserving_snd (μ := _root_.GD.N0051.d022792)).ae hy,
    (Measure.quasiMeasurePreserving_fst
      (ν := (gammaMeasure a a).prod (gammaMeasure b b))).ae hz] with u hu hv hz
  exact ⟨hu, hv, hz⟩

theorem d023938 {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (u : _root_.GD.N0051.d023832) (hx : 0 < u.2.1) (hz : u.1.1 ≠ 0) :
    Tendsto (fun w => _root_.GD.N0088.d023935 p q w u) (𝓝[>] 0) (𝓝 (u.1.2 ^ 2)) := by
  have heq : (fun w => _root_.GD.N0088.d023935 p q w u) =ᶠ[𝓝[>] 0]
      (fun _ => u.1.2 ^ 2) := by
    filter_upwards [_root_.GD.N0088.d023934 (y := u.2.2) (z₂ := u.1.2) hp hq hx hz,
      self_mem_nhdsWithin] with w he hw
    dsimp only [_root_.GD.N0088.d023935]
    rw [he, mul_pow, Real.sq_sqrt (show 0 ≤ w from le_of_lt hw)]
    exact mul_div_cancel_left₀ _ (ne_of_gt hw)
  exact tendsto_const_nhds.congr' heq.symm




theorem d023939 {a b p q : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (hq : 0 < q) (hra : p / q < a) :
    Tendsto (fun w : ℝ =>
      (∫ u, _root_.GD.N0051.d022763 p q u.1.1 (Real.sqrt w * u.1.2) u.2.1 (w * u.2.2) ^ 2
        ∂_root_.GD.N0051.d023833 a b) / w) (𝓝[>] 0) (𝓝 1) := by
  letI := isProbabilityMeasure_gammaMeasure ha ha
  letI := isProbabilityMeasure_gammaMeasure hb hb
  have hr : 0 ≤ p / q := (div_pos hp hq).le
  have hZ : Integrable (fun z : ℝ × ℝ => z.2 ^ 2) _root_.GD.N0051.d022792 :=
    (_root_.GD.N0232.N0719.N0886.d003647 1 2).comp_snd _
  have hZi : Integrable (fun u : _root_.GD.N0051.d023832 => u.1.2 ^ 2) (_root_.GD.N0051.d023833 a b) :=
    hZ.comp_fst _
  have hZeq : (∫ u : _root_.GD.N0051.d023832, u.1.2 ^ 2 ∂_root_.GD.N0051.d023833 a b) = 1 := by
    rw [integral_fun_fst (fun z : ℝ × ℝ => z.2 ^ 2), probReal_univ, one_smul,
      integral_fun_snd (fun z : ℝ => z ^ 2), probReal_univ, one_smul]
    exact _root_.GD.N0232.N0719.N0886.d003646 1
  have hmeas (w : ℝ) : Measurable (_root_.GD.N0088.d023935 p q w) := by
    have hf : Measurable (fun u : _root_.GD.N0051.d023832 =>
        _root_.GD.N0051.d022763 p q u.1.1 (Real.sqrt w * u.1.2) u.2.1 (w * u.2.2)) :=
      (_root_.GD.N0051.d022771 p q).comp (show Measurable (fun u : _root_.GD.N0051.d023832 =>
        ((u.1.1, Real.sqrt w * u.1.2), (u.2.1, w * u.2.2))) by fun_prop)
    exact (hf.pow_const 2).div_const w
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := _root_.GD.N0051.d023833 a b) (F := _root_.GD.N0088.d023935 p q)
    (f := fun u : _root_.GD.N0051.d023832 => u.1.2 ^ 2)
    (fun u => 2 * _root_.GD.N0088.d023931 (p / q) u + 2 * u.1.2 ^ 2)
    (Eventually.of_forall fun w => (hmeas w).aestronglyMeasurable)
    (show ∀ᶠ w in 𝓝[>] (0 : ℝ), ∀ᵐ u ∂_root_.GD.N0051.d023833 a b,
        ‖_root_.GD.N0088.d023935 p q w u‖ ≤
          2 * _root_.GD.N0088.d023931 (p / q) u + 2 * u.1.2 ^ 2 from by
      filter_upwards [self_mem_nhdsWithin,
        (tendsto_id.mono_left nhdsWithin_le_nhds).eventually_lt_const (by norm_num : (0 : ℝ) < 1)]
        with w hw hw1
      filter_upwards [_root_.GD.N0088.d023937 ha hb] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ _root_.GD.N0088.d023935 p q w u from
        div_nonneg (sq_nonneg _) (le_of_lt hw))]
      exact _root_.GD.N0088.d023936 hq hw hw1.le hr u hu.1 hu.2.1)
    (((_root_.GD.N0088.d023932 ha hb hr hra).const_mul 2).add (hZi.const_mul 2))
    (show ∀ᵐ u ∂_root_.GD.N0051.d023833 a b,
        Tendsto (fun w => _root_.GD.N0088.d023935 p q w u) (𝓝[>] 0) (𝓝 (u.1.2 ^ 2)) from by
      filter_upwards [_root_.GD.N0088.d023937 ha hb] with u hu
      exact _root_.GD.N0088.d023938 hp hq u hu.1 hu.2.2)
  rw [hZeq] at hlim
  simpa only [_root_.GD.N0088.d023935, integral_div] using hlim


theorem d023940 {a b p q : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (hq : 0 < q) (hra : p / q < a) :
    Tendsto (fun w : ℝ =>
      (∫ u, _root_.GD.N0051.d023841 p q (_root_.GD.N0051.d023834 0 1 w u) ^ 2
        ∂_root_.GD.N0051.d023833 a b) / w) (𝓝[>] 0) (𝓝 1) := by
  simpa only [_root_.GD.N0051.d023841, _root_.GD.N0051.d023834, Real.sqrt_one, one_mul, zero_add]
    using _root_.GD.N0088.d023939 ha hb hp hq hra


theorem d023941 {a b p q : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hp : 0 < p) (hq : 0 < q) (hra : p / q < a) :
    Tendsto (fun w : ℝ =>
      (∫ u, _root_.GD.N0051.d023841 p q (_root_.GD.N0051.d023834 0 1 w u) ^ 2
        ∂_root_.GD.N0051.d023833 a b) / (w / (1 + w))) (𝓝[>] 0) (𝓝 1) := by
  have hf : Tendsto (fun w : ℝ => 1 + w) (𝓝[>] 0) (𝓝 1) := by
    have hid : Tendsto (fun w : ℝ => w) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [add_zero] using hid.const_add (1 : ℝ)
  have h := (_root_.GD.N0088.d023940 ha hb hp hq hra).mul hf
  simpa only [one_mul, div_div_eq_mul_div, div_mul_eq_mul_div] using h

#print axioms _root_.GD.N0088.d023936
#print axioms _root_.GD.N0088.d023937
#print axioms _root_.GD.N0088.d023938
#print axioms _root_.GD.N0088.d023939
#print axioms _root_.GD.N0088.d023940
#print axioms _root_.GD.N0088.d023941
end
end GD.N0088
