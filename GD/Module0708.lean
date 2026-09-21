import GD.Module0685
import GD.Module0684
import GD.Module0680
import GD.Module0628
import GD.Module0254
import GD.Module0660
import GD.Module0659
import GD.Module0700
import GD.Module0158
import GD.Module0670
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod


















open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0232.N0719.N0924

noncomputable section

open _root_.GD.N0232.N0719.N0923
open _root_.GD.N0232.N0719.N0922
open _root_.GD.N0232.N0719.N0921
open _root_.GD.N0232.N0719.N0883
open _root_.GD.N0232.N0719.N0909
open _root_.GD.N0232.N0719.N0908
open _root_.GD.N0232.N0719.N0867
open _root_.GD.N0232.N0719.N0949
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0928
open _root_.GD.N0232.N0719.N0929




theorem d010432
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Integrable (fun x : ℝ ↦ x ^ 2) (gammaMeasure a r) := by
  rw [gammaMeasure]
  change Integrable (fun x : ℝ ↦ x ^ 2)
    (volume.withDensity
      (fun x ↦ ENNReal.ofReal (gammaPDFReal a r x)))
  rw [integrable_withDensity_iff_integrable_smul'
    ((measurable_gammaPDFReal a r).ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  have hkernel :
      IntegrableOn
        (fun x : ℝ ↦
          (r ^ a / Real.Gamma a) *
            (x ^ (a + 1) * Real.exp (-(r * x))))
        (Set.Ioi 0) := by
    have hbase :=
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := a + 1) (b := r)
        (by linarith) (by norm_num) hr
    have hbase' :
        IntegrableOn
          (fun x : ℝ ↦ x ^ (a + 1) * Real.exp (-(r * x)))
          (Set.Ioi 0) := by
      simpa only [Real.rpow_one, neg_mul] using hbase
    exact hbase'.const_mul _
  have hkernelActual :
      IntegrableOn
        (fun x : ℝ ↦ gammaPDFReal a r x * x ^ 2)
        (Set.Ioi 0) := by
    apply hkernel.congr_fun
    · intro x hx
      have hxpos : 0 < x := by simpa only [Set.mem_Ioi] using hx
      have hxpow :
          x ^ (a - 1) * x ^ 2 = x ^ (a + 1) := by
        calc
          x ^ (a - 1) * x ^ 2 =
              x ^ (a - 1) * x ^ (2 : ℝ) := by
                rw [Real.rpow_two]
          _ = x ^ ((a - 1) + 2) := by rw [Real.rpow_add hxpos]
          _ = x ^ (a + 1) := by ring_nf
      symm
      calc
        gammaPDFReal a r x * x ^ 2 =
            (r ^ a / Real.Gamma a) *
              (x ^ (a - 1) * x ^ 2) * Real.exp (-(r * x)) := by
                simp only [gammaPDFReal, if_pos hxpos.le]
                ring
        _ = (r ^ a / Real.Gamma a) *
              (x ^ (a + 1) * Real.exp (-(r * x))) := by
                rw [hxpow]
                ring
    · exact measurableSet_Ioi
  have hdensity :
      Integrable (fun x : ℝ ↦ gammaPDFReal a r x * x ^ 2) := by
    apply hkernelActual.integrable_of_forall_notMem_eq_zero
    intro x hx
    have hxle : x ≤ 0 := le_of_not_gt hx
    by_cases hxzero : x = 0
    · simp [hxzero]
    · have hxneg : x < 0 := lt_of_le_of_ne hxle hxzero
      simp [gammaPDFReal, not_le.mpr hxneg]
  apply hdensity.congr'
  · fun_prop
  filter_upwards with x
  have hpdf : 0 ≤ gammaPDFReal a r x :=
    gammaPDFReal_nonneg ha hr x
  simp only [smul_eq_mul, gammaPDF,
    ENNReal.toReal_ofReal hpdf]


theorem d010433
    {a r : ℝ} (ha : 2 < a) (hr : 0 < r) :
    Integrable (fun x : ℝ ↦ x⁻¹ ^ 2) (gammaMeasure a r) := by
  have ha0 : 0 < a := by linarith
  rw [gammaMeasure]
  change Integrable (fun x : ℝ ↦ x⁻¹ ^ 2)
    (volume.withDensity
      (fun x ↦ ENNReal.ofReal (gammaPDFReal a r x)))
  rw [integrable_withDensity_iff_integrable_smul'
    ((measurable_gammaPDFReal a r).ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  have hkernel :
      IntegrableOn
        (fun x : ℝ ↦
          (r ^ a / Real.Gamma a) *
            (x ^ (a - 3) * Real.exp (-(r * x))))
        (Set.Ioi 0) := by
    have hbase :=
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := a - 3) (b := r)
        (by linarith) (by norm_num) hr
    have hbase' :
        IntegrableOn
          (fun x : ℝ ↦ x ^ (a - 3) * Real.exp (-(r * x)))
          (Set.Ioi 0) := by
      simpa only [Real.rpow_one, neg_mul] using hbase
    exact hbase'.const_mul _
  have hkernelActual :
      IntegrableOn
        (fun x : ℝ ↦ gammaPDFReal a r x * x⁻¹ ^ 2)
        (Set.Ioi 0) := by
    apply hkernel.congr_fun
    · intro x hx
      have hxpos : 0 < x := by simpa only [Set.mem_Ioi] using hx
      have hxpow :
          x ^ (a - 1) * x⁻¹ ^ 2 = x ^ (a - 3) := by
        rw [← _root_.GD.N0232.N0719.N0908.d009686 hxpos]
        calc
          x ^ (a - 1) * x ^ (-2 : ℝ) =
              x ^ ((a - 1) + (-2 : ℝ)) :=
                (Real.rpow_add hxpos (a - 1) (-2 : ℝ)).symm
          _ = x ^ (a - 3) := by ring_nf
      symm
      calc
        gammaPDFReal a r x * x⁻¹ ^ 2 =
            (r ^ a / Real.Gamma a) *
              (x ^ (a - 1) * x⁻¹ ^ 2) * Real.exp (-(r * x)) := by
                simp only [gammaPDFReal, if_pos hxpos.le]
                ring
        _ = (r ^ a / Real.Gamma a) *
              (x ^ (a - 3) * Real.exp (-(r * x))) := by
                rw [hxpow]
                ring
    · exact measurableSet_Ioi
  have hdensity :
      Integrable (fun x : ℝ ↦ gammaPDFReal a r x * x⁻¹ ^ 2) := by
    apply hkernelActual.integrable_of_forall_notMem_eq_zero
    intro x hx
    have hxle : x ≤ 0 := le_of_not_gt hx
    by_cases hxzero : x = 0
    · simp [hxzero]
    · have hxneg : x < 0 := lt_of_le_of_ne hxle hxzero
      simp [gammaPDFReal, not_le.mpr hxneg]
  apply hdensity.congr'
  · fun_prop
  filter_upwards with x
  have hpdf : 0 ≤ gammaPDFReal a r x :=
    gammaPDFReal_nonneg ha0 hr x
  simp only [smul_eq_mul, gammaPDF,
    ENNReal.toReal_ofReal hpdf]





def d010434 (ε : ℝ) (w : _root_.GD.N0232.N0719.N0923.d009974 × _root_.GD.N0232.N0719.N0923.d009974) : _root_.GD.N0232.N0719.N0900.d009096 3 :=
  _root_.GD.N0232.N0719.N0922.d009943 (_root_.GD.N0232.N0719.N0923.d009981 ε w.1) (_root_.GD.N0232.N0719.N0923.d009982 ε w.2)


def d010435 (ε : ℝ) (w : _root_.GD.N0232.N0719.N0923.d009974 × _root_.GD.N0232.N0719.N0923.d009974) : ℝ :=
  _root_.GD.N0232.N0719.N0867.d010306 (by norm_num) _root_.GD.N0232.N0719.N0922.d009915 (5 / 2)
    (_root_.GD.N0232.N0719.N0924.d010434 ε w)


def d010436 (ε : ℝ) (w : _root_.GD.N0232.N0719.N0923.d009974 × _root_.GD.N0232.N0719.N0923.d009974) : ℝ :=
  _root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0924.d010434 ε w)



def d010437 (ε : ℝ) : ℝ :=
  ∫ w, _root_.GD.N0232.N0719.N0924.d010435 ε w ^ 2 ∂_root_.GD.N0232.N0719.N0923.d009977



def d010438 (ε : ℝ) : ℝ :=
  ∫ w, _root_.GD.N0232.N0719.N0924.d010436 ε w ^ 2 ∂_root_.GD.N0232.N0719.N0923.d009977


def d010439 : ℝ :=
  (_root_.GD.N0232.N0719.N0923.d009977 _root_.GD.N0232.N0719.N0923.d009980).toReal


def d010440 : ℝ :=
  _root_.GD.N0232.N0719.N0922.d009965 / (144 * (256 * _root_.GD.N0232.N0719.N0922.d009948))


def d010441 (ε : ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0924.d010440 / Real.log ((ε + 1) / ε) ^ 2

theorem d010442 : 0 < _root_.GD.N0232.N0719.N0924.d010439 := by
  unfold _root_.GD.N0232.N0719.N0924.d010439
  exact ENNReal.toReal_pos
    _root_.GD.N0232.N0719.N0923.d009986.ne'
    (measure_lt_top _root_.GD.N0232.N0719.N0923.d009977 _root_.GD.N0232.N0719.N0923.d009980).ne

theorem d010443 : 0 < _root_.GD.N0232.N0719.N0924.d010440 := by
  unfold _root_.GD.N0232.N0719.N0924.d010440
  exact div_pos _root_.GD.N0232.N0719.N0922.d009966
    (mul_pos (by norm_num) (mul_pos (by norm_num) _root_.GD.N0232.N0719.N0922.d009949))

theorem d010444 { ε : ℝ } (hε : 0 < ε) :
    0 < Real.log ((ε + 1) / ε) := by
  apply Real.log_pos
  rw [one_lt_div hε]
  linarith

theorem d010445 { ε : ℝ } (hε : 0 < ε) :
    0 < _root_.GD.N0232.N0719.N0924.d010441 ε := by
  unfold _root_.GD.N0232.N0719.N0924.d010441
  exact div_pos _root_.GD.N0232.N0719.N0924.d010443
    (sq_pos_of_pos (_root_.GD.N0232.N0719.N0924.d010444 hε))



theorem d010446
    {ε : ℝ} {y t : Fin 3 → ℝ} (hE : _root_.GD.N0232.N0719.N0922.d009928 ε y t) :
    _root_.GD.N0232.N0719.N0867.d010301 (_root_.GD.N0232.N0719.N0922.d009943 y t) := by
  rcases hE with
    ⟨hε, _hε1, ht0l, _ht0u, ht1l, _ht1u, ht2l, _ht2u,
      _hy1l, _hy1u, _hy2l, _hy2u⟩
  intro i
  fin_cases i
  · simpa [_root_.GD.N0232.N0719.N0922.d009943] using hε.trans_le ht0l
  · simpa [_root_.GD.N0232.N0719.N0922.d009943] using (lt_of_lt_of_le zero_lt_one ht1l)
  · simpa [_root_.GD.N0232.N0719.N0922.d009943] using (lt_of_lt_of_le zero_lt_one ht2l)



theorem d010447
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {w : _root_.GD.N0232.N0719.N0923.d009974 × _root_.GD.N0232.N0719.N0923.d009974} (hw : w ∈ _root_.GD.N0232.N0719.N0923.d009980) :
    _root_.GD.N0232.N0719.N0924.d010441 ε ≤ _root_.GD.N0232.N0719.N0924.d010435 ε w := by
  have hE := _root_.GD.N0232.N0719.N0923.d009987 hε hε1 hw
  have hpos := _root_.GD.N0232.N0719.N0924.d010446 hE
  have hcap := _root_.GD.N0232.N0719.N0922.d009973 hE
  have hy0 : 0 ≤ _root_.GD.N0232.N0719.N0923.d009981 ε w.1 0 := by
    rcases hw.1 with ⟨hz0, hz1, hz2⟩
    exact mul_nonneg (Real.sqrt_nonneg ε) hz0.1
  have hdevform :
      _root_.GD.N0232.N0719.N0924.d010441 ε =
        _root_.GD.N0232.N0719.N0922.d009965 /
          (144 * (256 * _root_.GD.N0232.N0719.N0922.d009948 *
            Real.log ((ε + 1) / ε) ^ 2)) := by
    unfold _root_.GD.N0232.N0719.N0924.d010441 _root_.GD.N0232.N0719.N0924.d010440
    field_simp [_root_.GD.N0232.N0719.N0922.d009949.ne', (_root_.GD.N0232.N0719.N0924.d010444 hε).ne']
    <;> ring
  rw [hdevform]
  calc
    _root_.GD.N0232.N0719.N0922.d009965 /
          (144 * (256 * _root_.GD.N0232.N0719.N0922.d009948 *
            Real.log ((ε + 1) / ε) ^ 2)) ≤
        _root_.GD.N0232.N0719.N0929.d009653 (by norm_num) _root_.GD.N0232.N0719.N0922.d009915
            (_root_.GD.N0232.N0719.N0923.d009981 ε w.1) (_root_.GD.N0232.N0719.N0923.d009982 ε w.2) (5 / 2) -
          _root_.GD.N0232.N0719.N0923.d009981 ε w.1 0 := hcap
    _ ≤ _root_.GD.N0232.N0719.N0929.d009653 (by norm_num) _root_.GD.N0232.N0719.N0922.d009915
            (_root_.GD.N0232.N0719.N0923.d009981 ε w.1) (_root_.GD.N0232.N0719.N0923.d009982 ε w.2) (5 / 2) := by
          linarith
    _ = _root_.GD.N0232.N0719.N0924.d010435 ε w := by
      unfold _root_.GD.N0232.N0719.N0924.d010435 _root_.GD.N0232.N0719.N0924.d010434
      rw [_root_.GD.N0232.N0719.N0867.d010307
        (by norm_num) _root_.GD.N0232.N0719.N0922.d009915 (5 / 2) _ hpos]
      rfl


theorem d010448
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {w : _root_.GD.N0232.N0719.N0923.d009974 × _root_.GD.N0232.N0719.N0923.d009974} (hw : w ∈ _root_.GD.N0232.N0719.N0923.d009980) :
    _root_.GD.N0232.N0719.N0924.d010441 ε ^ 2 ≤ _root_.GD.N0232.N0719.N0924.d010435 ε w ^ 2 := by
  have hdev := (_root_.GD.N0232.N0719.N0924.d010445 hε).le
  have hcand := hdev.trans
    (_root_.GD.N0232.N0719.N0924.d010447 hε hε1 hw)
  exact (sq_le_sq₀ hdev hcand).2
    (_root_.GD.N0232.N0719.N0924.d010447 hε hε1 hw)



noncomputable instance d010449 :
    IsProbabilityMeasure _root_.GD.N0232.N0719.N0923.d009975 := by
  unfold _root_.GD.N0232.N0719.N0923.d009975
  infer_instance

noncomputable instance d010450 :
    IsProbabilityMeasure _root_.GD.N0232.N0719.N0923.d009976 := by
  unfold _root_.GD.N0232.N0719.N0923.d009976
  letI : IsProbabilityMeasure
      (gammaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure
      (gammaMeasure (5 / 2 : ℝ) (5 / 2 : ℝ)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  infer_instance

@[fun_prop]
theorem d010451 (ε : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0924.d010434 ε) := by
  rw [measurable_iff_comap_le]
  change
    (_root_.GD.N0232.N0719.N0900.d009098 3).comap
      (_root_.GD.N0232.N0719.N0924.d010434 ε) ≤
        (inferInstance : MeasurableSpace (_root_.GD.N0232.N0719.N0923.d009974 × _root_.GD.N0232.N0719.N0923.d009974))
  rw [_root_.GD.N0232.N0719.N0900.d009098,
    MeasurableSpace.comap_comp]
  exact (show Measurable
      (_root_.GD.N0232.N0719.N0900.d009097 ∘ _root_.GD.N0232.N0719.N0924.d010434 ε) by
        unfold _root_.GD.N0232.N0719.N0924.d010434 _root_.GD.N0232.N0719.N0922.d009943 _root_.GD.N0232.N0719.N0923.d009981
          _root_.GD.N0232.N0719.N0923.d009982 _root_.GD.N0232.N0719.N0900.d009097
        fun_prop).comap_le

@[fun_prop]
theorem d010452 (ε : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0924.d010435 ε) := by
  exact
    (_root_.GD.N0232.N0719.N0867.d010309
      (by norm_num) _root_.GD.N0232.N0719.N0922.d009915 (5 / 2)).comp
        (_root_.GD.N0232.N0719.N0924.d010451 ε)

@[fun_prop]
theorem d010453 (ε : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0924.d010436 ε) := by
  exact _root_.GD.N0232.N0719.N0900.d009121.comp (_root_.GD.N0232.N0719.N0924.d010451 ε)


theorem d010454 (ε : ℝ) :
    MemLp
      (fun z : _root_.GD.N0232.N0719.N0923.d009974 ↦
        ‖Real.sqrt ε * z.1‖ + ‖z.2.1‖ + ‖z.2.2‖)
      2 _root_.GD.N0232.N0719.N0923.d009975 := by
  let μ0 : Measure ℝ := gaussianReal 0 1
  let μ1 : Measure ℝ := gaussianReal 0 1
  let μ2 : Measure ℝ := gaussianReal 0 1
  have h0 : MemLp (fun z : _root_.GD.N0232.N0719.N0923.d009974 ↦ z.1) 2 _root_.GD.N0232.N0719.N0923.d009975 := by
    exact (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2).comp_fst
      ((gaussianReal 0 1).prod (gaussianReal 0 1))
  have h1tail : MemLp (fun z : ℝ × ℝ ↦ z.1) 2
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    exact (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2).comp_fst
      (gaussianReal 0 1)
  have h1 : MemLp (fun z : _root_.GD.N0232.N0719.N0923.d009974 ↦ z.2.1) 2 _root_.GD.N0232.N0719.N0923.d009975 := by
    exact h1tail.comp_snd (gaussianReal 0 1)
  have h2tail : MemLp (fun z : ℝ × ℝ ↦ z.2) 2
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    exact (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2).comp_snd
      (gaussianReal 0 1)
  have h2 : MemLp (fun z : _root_.GD.N0232.N0719.N0923.d009974 ↦ z.2.2) 2 _root_.GD.N0232.N0719.N0923.d009975 := by
    exact h2tail.comp_snd (gaussianReal 0 1)
  have hs0 : MemLp (fun z : _root_.GD.N0232.N0719.N0923.d009974 ↦ ‖Real.sqrt ε * z.1‖) 2
      _root_.GD.N0232.N0719.N0923.d009975 := by
    simpa using (h0.const_mul (Real.sqrt ε)).norm
  have hs1 : MemLp (fun z : _root_.GD.N0232.N0719.N0923.d009974 ↦ ‖z.2.1‖) 2
      _root_.GD.N0232.N0719.N0923.d009975 := by
    simpa using h1.norm
  have hs2 : MemLp (fun z : _root_.GD.N0232.N0719.N0923.d009974 ↦ ‖z.2.2‖) 2
      _root_.GD.N0232.N0719.N0923.d009975 := by
    simpa using h2.norm
  exact (hs0.add hs1).add hs2



theorem d010455 (ε : ℝ) :
    MemLp (_root_.GD.N0232.N0719.N0924.d010435 ε) 2 _root_.GD.N0232.N0719.N0923.d009977 := by
  have hmajorant :=
    (_root_.GD.N0232.N0719.N0924.d010454 ε).comp_fst _root_.GD.N0232.N0719.N0923.d009976
  apply hmajorant.mono'
  · exact (_root_.GD.N0232.N0719.N0924.d010452 ε).aestronglyMeasurable
  · filter_upwards with w
    have hbound :=
      _root_.GD.N0232.N0719.N0867.d010313
        (by norm_num) _root_.GD.N0232.N0719.N0922.d009915 (5 / 2) 0
        (by intro i; fin_cases i <;> simp)
        (by simp)
        (_root_.GD.N0232.N0719.N0924.d010434 ε w)
    simpa [_root_.GD.N0232.N0719.N0924.d010435, _root_.GD.N0232.N0719.N0924.d010434,
      _root_.GD.N0232.N0719.N0910.d010278, _root_.GD.N0232.N0719.N0923.d009981, Real.norm_eq_abs,
      _root_.GD.N0232.N0719.N0922.d009943, Fin.sum_univ_three, abs_mul]
      using hbound



theorem d010456 (ε : ℝ) :
    MemLp (_root_.GD.N0232.N0719.N0924.d010436 ε) 2 _root_.GD.N0232.N0719.N0923.d009977 := by
  have hmajorant :=
    (_root_.GD.N0232.N0719.N0924.d010454 ε).comp_fst _root_.GD.N0232.N0719.N0923.d009976
  apply hmajorant.mono'
  · exact (_root_.GD.N0232.N0719.N0924.d010453 ε).aestronglyMeasurable
  · filter_upwards with w
    have hbound := _root_.GD.N0232.N0719.N0910.d010281
      (by norm_num : 0 < 3) 0 (_root_.GD.N0232.N0719.N0924.d010434 ε w)
    simpa [_root_.GD.N0232.N0719.N0924.d010436, _root_.GD.N0232.N0719.N0924.d010434,
      _root_.GD.N0232.N0719.N0910.d010278, _root_.GD.N0232.N0719.N0923.d009981, Real.norm_eq_abs,
      _root_.GD.N0232.N0719.N0922.d009943, Fin.sum_univ_three, abs_mul]
      using hbound

theorem d010457 : MeasurableSet _root_.GD.N0232.N0719.N0923.d009980 := by
  unfold _root_.GD.N0232.N0719.N0923.d009980 _root_.GD.N0232.N0719.N0923.d009978 _root_.GD.N0232.N0719.N0923.d009979
  exact
    (measurableSet_Icc.prod
      (measurableSet_Icc.prod measurableSet_Icc)).prod
      (measurableSet_Icc.prod
        (measurableSet_Icc.prod measurableSet_Icc))



theorem d010458
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    _root_.GD.N0232.N0719.N0924.d010439 * _root_.GD.N0232.N0719.N0924.d010441 ε ^ 2 ≤ _root_.GD.N0232.N0719.N0924.d010437 ε := by
  have hcandInt : Integrable
      (fun w ↦ _root_.GD.N0232.N0719.N0924.d010435 ε w ^ 2)
      _root_.GD.N0232.N0719.N0923.d009977 :=
    (_root_.GD.N0232.N0719.N0924.d010455 ε).integrable_sq
  have hconstInt : IntegrableOn
      (fun _ : _root_.GD.N0232.N0719.N0923.d009974 × _root_.GD.N0232.N0719.N0923.d009974 ↦ _root_.GD.N0232.N0719.N0924.d010441 ε ^ 2)
      _root_.GD.N0232.N0719.N0923.d009980 _root_.GD.N0232.N0719.N0923.d009977 :=
    integrableOn_const
      (measure_lt_top _root_.GD.N0232.N0719.N0923.d009977 _root_.GD.N0232.N0719.N0923.d009980).ne
  calc
    _root_.GD.N0232.N0719.N0924.d010439 * _root_.GD.N0232.N0719.N0924.d010441 ε ^ 2 =
        ∫ _w : _root_.GD.N0232.N0719.N0923.d009974 × _root_.GD.N0232.N0719.N0923.d009974 in _root_.GD.N0232.N0719.N0923.d009980,
          _root_.GD.N0232.N0719.N0924.d010441 ε ^ 2 ∂_root_.GD.N0232.N0719.N0923.d009977 := by
      rw [setIntegral_const, smul_eq_mul, Measure.real]
      rfl
    _ ≤ ∫ w in _root_.GD.N0232.N0719.N0923.d009980,
          _root_.GD.N0232.N0719.N0924.d010435 ε w ^ 2
          ∂_root_.GD.N0232.N0719.N0923.d009977 := by
      exact setIntegral_mono_on hconstInt hcandInt.integrableOn
        _root_.GD.N0232.N0719.N0924.d010457
        (fun w hw ↦
          _root_.GD.N0232.N0719.N0924.d010448
            hε hε1 hw)
    _ ≤ ∫ w, _root_.GD.N0232.N0719.N0924.d010435 ε w ^ 2
          ∂_root_.GD.N0232.N0719.N0923.d009977 := by
      exact setIntegral_le_integral hcandInt
        (ae_of_all _ fun w ↦ sq_nonneg (_root_.GD.N0232.N0719.N0924.d010435 ε w))
    _ = _root_.GD.N0232.N0719.N0924.d010437 ε := rfl





def d010459 (ε : ℝ) (q : _root_.GD.N0232.N0719.N0923.d009974) : _root_.GD.N0232.N0719.N0900.d009096 3 :=
  _root_.GD.N0232.N0719.N0922.d009943 ![0, 0, 0] (_root_.GD.N0232.N0719.N0923.d009982 ε q)

theorem d010460
    (ε : ℝ) (z q : _root_.GD.N0232.N0719.N0923.d009974) (i : Fin 3) :
    _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0924.d010434 ε (z, q)) i =
      _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0924.d010459 ε q) i := by
  rfl



theorem d010461
    (ε : ℝ) (z q : _root_.GD.N0232.N0719.N0923.d009974) :
    _root_.GD.N0232.N0719.N0924.d010436 ε (z, q) =
      _root_.GD.N0232.N0719.N0886.d003653
        (Real.sqrt ε * _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0924.d010459 ε q) 0)
        (_root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0924.d010459 ε q) 1)
        (_root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0924.d010459 ε q) 2) z := by
  unfold _root_.GD.N0232.N0719.N0924.d010436 _root_.GD.N0232.N0719.N0900.d009110
  rw [Fin.sum_univ_three]
  rw [_root_.GD.N0232.N0719.N0924.d010460, _root_.GD.N0232.N0719.N0924.d010460,
    _root_.GD.N0232.N0719.N0924.d010460]
  simp only [_root_.GD.N0232.N0719.N0924.d010434, _root_.GD.N0232.N0719.N0922.d009943, _root_.GD.N0232.N0719.N0923.d009981, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Fin.isValue]
  simp only [Matrix.vecHead, Matrix.vecTail]
  unfold _root_.GD.N0232.N0719.N0886.d003653 _root_.GD.N0232.N0719.N0886.d003650
    _root_.GD.N0232.N0719.N0886.d003651 _root_.GD.N0232.N0719.N0886.d003652
  simp [Function.comp_apply] <;> ring



theorem d010462
    {ε : ℝ} (hε : 0 ≤ ε) (q : _root_.GD.N0232.N0719.N0923.d009974) :
    (∫ z : _root_.GD.N0232.N0719.N0923.d009974, _root_.GD.N0232.N0719.N0924.d010436 ε (z, q) ^ 2
      ∂_root_.GD.N0232.N0719.N0923.d009975) =
      _root_.GD.N0232.N0719.N0921.d009169 ε (_root_.GD.N0232.N0719.N0924.d010459 ε q) := by
  simp_rw [_root_.GD.N0232.N0719.N0924.d010461]
  change
    (∫ z : _root_.GD.N0232.N0719.N0923.d009974,
      _root_.GD.N0232.N0719.N0886.d003653
        (Real.sqrt ε * _root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0924.d010459 ε q) 0)
        (_root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0924.d010459 ε q) 1)
        (_root_.GD.N0232.N0719.N0900.d009108 (_root_.GD.N0232.N0719.N0924.d010459 ε q) 2) z ^ 2
      ∂_root_.GD.N0232.N0719.N0886.d003649 1 1 1) = _
  rw [_root_.GD.N0232.N0719.N0883.d003666]
  unfold _root_.GD.N0232.N0719.N0921.d009169
  have hsqrt : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε
  norm_num
  rw [mul_pow, hsqrt]


theorem d010463 :
    ∀ᵐ q ∂_root_.GD.N0232.N0719.N0923.d009976,
      0 < q.1 ∧ 0 < q.2.1 ∧ 0 < q.2.2 := by
  unfold _root_.GD.N0232.N0719.N0923.d009976
  have houter : MeasurableSet
      {q : _root_.GD.N0232.N0719.N0923.d009974 | 0 < q.1 ∧ 0 < q.2.1 ∧ 0 < q.2.2} := by
    exact (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_const
        (measurable_fst.comp measurable_snd)).inter
        (measurableSet_lt measurable_const
          (measurable_snd.comp measurable_snd)))
  apply (Measure.ae_prod_iff_ae_ae houter).2
  filter_upwards
    [_root_.GD.N0232.N0719.N0910.d010286
      (a := (1 / 2 : ℝ)) (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)]
      with q0 hq0
  have htail : MeasurableSet
      {q : ℝ × ℝ | 0 < q0 ∧ 0 < q.1 ∧ 0 < q.2} := by
    have hset : MeasurableSet
        ({q : ℝ × ℝ | (0 : ℝ) < q.1} ∩
          {q : ℝ × ℝ | (0 : ℝ) < q.2}) :=
      (measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_lt measurable_const measurable_snd)
    convert hset using 1
    ext q
    simp [hq0]
  apply (Measure.ae_prod_iff_ae_ae htail).2
  filter_upwards
    [_root_.GD.N0232.N0719.N0910.d010286
      (a := (5 / 2 : ℝ)) (r := (5 / 2 : ℝ)) (by norm_num) (by norm_num)]
      with q1 hq1
  filter_upwards
    [_root_.GD.N0232.N0719.N0910.d010286
      (a := (5 / 2 : ℝ)) (r := (5 / 2 : ℝ)) (by norm_num) (by norm_num)]
      with q2 hq2
  exact ⟨hq0, hq1, hq2⟩


def d010464 (ε : ℝ) (q : _root_.GD.N0232.N0719.N0923.d009974) : ℝ :=
  ε + ε ^ 2 * q.1 ^ 2 * (q.2.1⁻¹ ^ 2 + q.2.2⁻¹ ^ 2)


theorem d010465
    {ε : ℝ} (hε : 0 < ε) {q : _root_.GD.N0232.N0719.N0923.d009974}
    (hq : 0 < q.1 ∧ 0 < q.2.1 ∧ 0 < q.2.2) :
    _root_.GD.N0232.N0719.N0921.d009169 ε (_root_.GD.N0232.N0719.N0924.d010459 ε q) ≤
      _root_.GD.N0232.N0719.N0924.d010464 ε q := by
  exact _root_.GD.N0232.N0719.N0921.d009171 hε hq.1 hq.2.1 hq.2.2
    (_root_.GD.N0232.N0719.N0924.d010459 ε q)
    (by simp [_root_.GD.N0232.N0719.N0924.d010459, _root_.GD.N0232.N0719.N0922.d009943, _root_.GD.N0232.N0719.N0923.d009982])
    (by simp [_root_.GD.N0232.N0719.N0924.d010459, _root_.GD.N0232.N0719.N0922.d009943, _root_.GD.N0232.N0719.N0923.d009982])
    (by simp [_root_.GD.N0232.N0719.N0924.d010459, _root_.GD.N0232.N0719.N0922.d009943, _root_.GD.N0232.N0719.N0923.d009982])

theorem d010466 (ε : ℝ) :
    Integrable (_root_.GD.N0232.N0719.N0924.d010464 ε) _root_.GD.N0232.N0719.N0923.d009976 := by
  let μ0 : Measure ℝ := gammaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)
  let μ1 : Measure ℝ := gammaMeasure (5 / 2 : ℝ) (5 / 2 : ℝ)
  let μ2 : Measure ℝ := gammaMeasure (5 / 2 : ℝ) (5 / 2 : ℝ)
  letI : IsProbabilityMeasure μ0 :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure μ1 :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure μ2 :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  have h0 : Integrable (fun x : ℝ ↦ x ^ 2) μ0 :=
    _root_.GD.N0232.N0719.N0924.d010432 (by norm_num) (by norm_num)
  have h1 : Integrable (fun x : ℝ ↦ x⁻¹ ^ 2) μ1 :=
    _root_.GD.N0232.N0719.N0924.d010433 (by norm_num) (by norm_num)
  have h2 : Integrable (fun x : ℝ ↦ x⁻¹ ^ 2) μ2 :=
    _root_.GD.N0232.N0719.N0924.d010433 (by norm_num) (by norm_num)
  have htail : Integrable
      (fun q : ℝ × ℝ ↦ q.1⁻¹ ^ 2 + q.2⁻¹ ^ 2) (μ1.prod μ2) :=
    (h1.comp_fst μ2).add (h2.comp_snd μ1)
  have hprod : Integrable
      (fun q : ℝ × (ℝ × ℝ) ↦
        q.1 ^ 2 * (q.2.1⁻¹ ^ 2 + q.2.2⁻¹ ^ 2))
      (μ0.prod (μ1.prod μ2)) := h0.mul_prod htail
  have hresult := (integrable_const (μ := μ0.prod (μ1.prod μ2)) ε).add
    (hprod.const_mul (ε ^ 2))
  change Integrable (_root_.GD.N0232.N0719.N0924.d010464 ε) (μ0.prod (μ1.prod μ2))
  have hfun :
      _root_.GD.N0232.N0719.N0924.d010464 ε =
        (fun q : ℝ × (ℝ × ℝ) ↦
          ε + ε ^ 2 *
            (q.1 ^ 2 * (q.2.1⁻¹ ^ 2 + q.2.2⁻¹ ^ 2))) := by
    funext q
    unfold _root_.GD.N0232.N0719.N0924.d010464
    ring
  rw [hfun]
  exact hresult



theorem d010467 :
    (∫ q : ℝ × ℝ, q.1⁻¹ ^ 2 + q.2⁻¹ ^ 2
      ∂((gammaMeasure (5 / 2 : ℝ) (5 / 2 : ℝ)).prod
        (gammaMeasure (5 / 2 : ℝ) (5 / 2 : ℝ)))) = 50 / 3 := by
  let μ : Measure ℝ := gammaMeasure (5 / 2 : ℝ) (5 / 2 : ℝ)
  letI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  have hi : Integrable (fun x : ℝ ↦ x⁻¹ ^ 2) μ :=
    _root_.GD.N0232.N0719.N0924.d010433 (by norm_num) (by norm_num)
  have hfst :
      (∫ q : ℝ × ℝ, q.1⁻¹ ^ 2 ∂(μ.prod μ)) = 25 / 3 := by
    calc
      (∫ q : ℝ × ℝ, q.1⁻¹ ^ 2 ∂(μ.prod μ)) =
          ∫ q : ℝ × ℝ,
            (fun x : ℝ ↦ x⁻¹ ^ 2) q.1 * (fun _ : ℝ ↦ 1) q.2
            ∂(μ.prod μ) := by simp
      _ = (∫ x : ℝ, x⁻¹ ^ 2 ∂μ) * ∫ _x : ℝ, 1 ∂μ := by
        exact integral_prod_mul (μ := μ) (ν := μ)
          (fun x : ℝ ↦ x⁻¹ ^ 2) (fun _ : ℝ ↦ 1)
      _ = 25 / 3 := by
        dsimp [μ]
        rw [_root_.GD.N0232.N0719.N0908.d009689]
        simp
  have hsnd :
      (∫ q : ℝ × ℝ, q.2⁻¹ ^ 2 ∂(μ.prod μ)) = 25 / 3 := by
    calc
      (∫ q : ℝ × ℝ, q.2⁻¹ ^ 2 ∂(μ.prod μ)) =
          ∫ q : ℝ × ℝ,
            (fun _ : ℝ ↦ 1) q.1 * (fun x : ℝ ↦ x⁻¹ ^ 2) q.2
            ∂(μ.prod μ) := by simp
      _ = (∫ _x : ℝ, 1 ∂μ) * ∫ x : ℝ, x⁻¹ ^ 2 ∂μ := by
        exact integral_prod_mul (μ := μ) (ν := μ)
          (fun _ : ℝ ↦ 1) (fun x : ℝ ↦ x⁻¹ ^ 2)
      _ = 25 / 3 := by
        dsimp [μ]
        rw [_root_.GD.N0232.N0719.N0908.d009689]
        simp
  have hsumInt : Integrable
      (fun q : ℝ × ℝ ↦ q.1⁻¹ ^ 2 + q.2⁻¹ ^ 2) (μ.prod μ) :=
    (hi.comp_fst μ).add (hi.comp_snd μ)
  change (∫ q : ℝ × ℝ, q.1⁻¹ ^ 2 + q.2⁻¹ ^ 2
      ∂(μ.prod μ)) = 50 / 3
  rw [integral_add (hi.comp_fst μ) (hi.comp_snd μ), hfst, hsnd]
  norm_num


theorem d010468 (ε : ℝ) :
    (∫ q, _root_.GD.N0232.N0719.N0924.d010464 ε q ∂_root_.GD.N0232.N0719.N0923.d009976) =
      ε + 50 * ε ^ 2 := by
  let μ0 : Measure ℝ := gammaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)
  let μt : Measure (ℝ × ℝ) :=
    (gammaMeasure (5 / 2 : ℝ) (5 / 2 : ℝ)).prod
      (gammaMeasure (5 / 2 : ℝ) (5 / 2 : ℝ))
  letI : IsProbabilityMeasure μ0 :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure μt := by
    dsimp [μt]
    letI : IsProbabilityMeasure
        (gammaMeasure (5 / 2 : ℝ) (5 / 2 : ℝ)) :=
      isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
    infer_instance
  have h0 : Integrable (fun x : ℝ ↦ x ^ 2) μ0 :=
    _root_.GD.N0232.N0719.N0924.d010432 (by norm_num) (by norm_num)
  have ht : Integrable
      (fun q : ℝ × ℝ ↦ q.1⁻¹ ^ 2 + q.2⁻¹ ^ 2) μt := by
    dsimp [μt]
    have hi := _root_.GD.N0232.N0719.N0924.d010433
      (a := (5 / 2 : ℝ)) (r := (5 / 2 : ℝ)) (by norm_num) (by norm_num)
    letI : IsProbabilityMeasure
        (gammaMeasure (5 / 2 : ℝ) (5 / 2 : ℝ)) :=
      isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
    exact (hi.comp_fst _).add (hi.comp_snd _)
  have hprod : Integrable
      (fun q : ℝ × (ℝ × ℝ) ↦
        q.1 ^ 2 * (q.2.1⁻¹ ^ 2 + q.2.2⁻¹ ^ 2))
      (μ0.prod μt) := h0.mul_prod ht
  change
    (∫ q : ℝ × (ℝ × ℝ),
      ε + ε ^ 2 * q.1 ^ 2 * (q.2.1⁻¹ ^ 2 + q.2.2⁻¹ ^ 2)
      ∂(μ0.prod μt)) = ε + 50 * ε ^ 2
  have hfun :
      (fun q : ℝ × (ℝ × ℝ) ↦
        ε + ε ^ 2 * q.1 ^ 2 * (q.2.1⁻¹ ^ 2 + q.2.2⁻¹ ^ 2)) =
        fun q ↦ ε + ε ^ 2 *
          (q.1 ^ 2 * (q.2.1⁻¹ ^ 2 + q.2.2⁻¹ ^ 2)) := by
    funext q
    ring
  rw [hfun]
  rw [integral_add (integrable_const ε) (hprod.const_mul (ε ^ 2)),
    integral_const, integral_const_mul]
  have hmass : (μ0.prod μt).real Set.univ = 1 := by simp
  rw [hmass, one_smul]
  have hsep :
      (∫ a : ℝ × (ℝ × ℝ),
          a.1 ^ 2 * (a.2.1⁻¹ ^ 2 + a.2.2⁻¹ ^ 2) ∂(μ0.prod μt)) =
        (∫ x : ℝ, x ^ 2 ∂μ0) *
          ∫ q : ℝ × ℝ, q.1⁻¹ ^ 2 + q.2⁻¹ ^ 2 ∂μt := by
    exact integral_prod_mul (μ := μ0) (ν := μt)
      (fun x : ℝ ↦ x ^ 2)
      (fun q : ℝ × ℝ ↦ q.1⁻¹ ^ 2 + q.2⁻¹ ^ 2)
  rw [hsep]
  have h0mom : (∫ x : ℝ, x ^ 2 ∂μ0) = 3 := by
    exact _root_.GD.N0232.N0719.N0909.d009691
  have htmom :
      (∫ q : ℝ × ℝ, q.1⁻¹ ^ 2 + q.2⁻¹ ^ 2 ∂μt) = 50 / 3 := by
    exact _root_.GD.N0232.N0719.N0924.d010467
  rw [h0mom, htmom]
  simp
  ring



theorem d010469
    {ε : ℝ} (hε : 0 ≤ ε) :
    _root_.GD.N0232.N0719.N0924.d010438 ε =
      ∫ q, _root_.GD.N0232.N0719.N0921.d009169 ε (_root_.GD.N0232.N0719.N0924.d010459 ε q)
        ∂_root_.GD.N0232.N0719.N0923.d009976 := by
  have hfull : Integrable
      (fun w : _root_.GD.N0232.N0719.N0923.d009974 × _root_.GD.N0232.N0719.N0923.d009974 ↦ _root_.GD.N0232.N0719.N0924.d010436 ε w ^ 2)
      _root_.GD.N0232.N0719.N0923.d009977 :=
    (_root_.GD.N0232.N0719.N0924.d010456 ε).integrable_sq
  unfold _root_.GD.N0232.N0719.N0924.d010438 _root_.GD.N0232.N0719.N0923.d009977
  rw [integral_prod_symm _ hfull]
  apply integral_congr_ae
  filter_upwards with q
  exact _root_.GD.N0232.N0719.N0924.d010462 hε q



theorem d010470
    {ε : ℝ} (hε : 0 < ε) :
    _root_.GD.N0232.N0719.N0924.d010438 ε ≤ ε + 50 * ε ^ 2 := by
  have hfull : Integrable
      (fun w : _root_.GD.N0232.N0719.N0923.d009974 × _root_.GD.N0232.N0719.N0923.d009974 ↦ _root_.GD.N0232.N0719.N0924.d010436 ε w ^ 2)
      _root_.GD.N0232.N0719.N0923.d009977 :=
    (_root_.GD.N0232.N0719.N0924.d010456 ε).integrable_sq
  have hcond : Integrable
      (fun q ↦ _root_.GD.N0232.N0719.N0921.d009169 ε (_root_.GD.N0232.N0719.N0924.d010459 ε q))
      _root_.GD.N0232.N0719.N0923.d009976 := by
    have hinner := hfull.integral_prod_right
    exact hinner.congr (ae_of_all _ fun q ↦
      _root_.GD.N0232.N0719.N0924.d010462 hε.le q)
  rw [_root_.GD.N0232.N0719.N0924.d010469 hε.le,
    ← _root_.GD.N0232.N0719.N0924.d010468 ε]
  exact integral_mono_ae hcond (_root_.GD.N0232.N0719.N0924.d010466 ε)
    (_root_.GD.N0232.N0719.N0924.d010463.mono fun q hq ↦
      _root_.GD.N0232.N0719.N0924.d010465 hε hq)



theorem d010471
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    _root_.GD.N0232.N0719.N0924.d010438 ε ≤ 51 * ε := by
  refine (_root_.GD.N0232.N0719.N0924.d010470 hε).trans ?_
  nlinarith [mul_self_le_mul_self hε.le hε1]




def d010472 : ℝ := Real.exp (-1)


def d010473 (n : ℕ) : ℝ := _root_.GD.N0232.N0719.N0924.d010472 ^ (n + 1)


def d010474 (n : ℕ) : ℝ :=
  Real.log ((_root_.GD.N0232.N0719.N0924.d010473 n + 1) / _root_.GD.N0232.N0719.N0924.d010473 n)

theorem d010475 : 0 < _root_.GD.N0232.N0719.N0924.d010472 := by
  unfold _root_.GD.N0232.N0719.N0924.d010472
  positivity

theorem d010476 : _root_.GD.N0232.N0719.N0924.d010472 < 1 := by
  unfold _root_.GD.N0232.N0719.N0924.d010472
  rw [Real.exp_lt_one_iff]
  norm_num

theorem d010477 (n : ℕ) : 0 < _root_.GD.N0232.N0719.N0924.d010473 n := by
  exact pow_pos _root_.GD.N0232.N0719.N0924.d010475 _

theorem d010478 (n : ℕ) : _root_.GD.N0232.N0719.N0924.d010473 n ≤ 1 := by
  exact pow_le_one₀ _root_.GD.N0232.N0719.N0924.d010475.le _root_.GD.N0232.N0719.N0924.d010476.le

theorem d010479 (n : ℕ) :
    _root_.GD.N0232.N0719.N0924.d010473 n = Real.exp (-((n + 1 : ℕ) : ℝ)) := by
  unfold _root_.GD.N0232.N0719.N0924.d010473 _root_.GD.N0232.N0719.N0924.d010472
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem d010480 (n : ℕ) : 0 < _root_.GD.N0232.N0719.N0924.d010474 n := by
  unfold _root_.GD.N0232.N0719.N0924.d010474
  exact _root_.GD.N0232.N0719.N0924.d010444 (_root_.GD.N0232.N0719.N0924.d010477 n)




theorem d010481 (n : ℕ) :
    _root_.GD.N0232.N0719.N0924.d010474 n ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
  let m : ℝ := ((n + 1 : ℕ) : ℝ)
  have hm1 : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega : n + 1 ≠ 0)
  have hm0 : 0 ≤ m := zero_le_one.trans hm1
  have heps : _root_.GD.N0232.N0719.N0924.d010473 n = Real.exp (-m) := by
    simpa [m] using _root_.GD.N0232.N0719.N0924.d010479 n
  have hratio :
      (_root_.GD.N0232.N0719.N0924.d010473 n + 1) / _root_.GD.N0232.N0719.N0924.d010473 n = 1 + Real.exp m := by
    rw [heps]
    calc
      (Real.exp (-m) + 1) / Real.exp (-m) =
          1 + (Real.exp (-m))⁻¹ := by
            field_simp [Real.exp_ne_zero]
      _ = 1 + Real.exp m := by simp [Real.exp_neg]
  have hexpTwo : (2 : ℝ) ≤ Real.exp m := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by
      simpa using (Real.two_mul_le_exp (x := (1 : ℝ)))
    exact htwo.trans (Real.exp_le_exp.mpr hm1)
  have hratioPos : 0 < (_root_.GD.N0232.N0719.N0924.d010473 n + 1) / _root_.GD.N0232.N0719.N0924.d010473 n := by
    exact div_pos (add_pos (_root_.GD.N0232.N0719.N0924.d010477 n) zero_lt_one)
      (_root_.GD.N0232.N0719.N0924.d010477 n)
  unfold _root_.GD.N0232.N0719.N0924.d010474
  apply (Real.log_le_iff_le_exp hratioPos).2
  rw [hratio, show 2 * m = m + m by ring, Real.exp_add]
  calc
    1 + Real.exp m ≤ 2 * Real.exp m := by
      nlinarith [Real.one_le_exp hm0]
    _ ≤ Real.exp m * Real.exp m := by
      exact mul_le_mul_of_nonneg_right hexpTwo (Real.exp_pos m).le



theorem d010482 (n : ℕ) :
    _root_.GD.N0232.N0719.N0924.d010438 (_root_.GD.N0232.N0719.N0924.d010473 n) ≤
      51 * _root_.GD.N0232.N0719.N0924.d010472 ^ (n + 1) := by
  exact _root_.GD.N0232.N0719.N0924.d010471
    (_root_.GD.N0232.N0719.N0924.d010477 n) (_root_.GD.N0232.N0719.N0924.d010478 n)


theorem d010483 (n : ℕ) :
    _root_.GD.N0232.N0719.N0924.d010439 * _root_.GD.N0232.N0719.N0924.d010441 (_root_.GD.N0232.N0719.N0924.d010473 n) ^ 2 ≤
      _root_.GD.N0232.N0719.N0924.d010437 (_root_.GD.N0232.N0719.N0924.d010473 n) := by
  exact _root_.GD.N0232.N0719.N0924.d010458
    (_root_.GD.N0232.N0719.N0924.d010477 n) (_root_.GD.N0232.N0719.N0924.d010478 n)







theorem d010484 :
    ¬ ∀ n : ℕ,
      _root_.GD.N0232.N0719.N0924.d010437 (_root_.GD.N0232.N0719.N0924.d010473 n) ≤
        _root_.GD.N0232.N0719.N0924.d010438 (_root_.GD.N0232.N0719.N0924.d010473 n) := by
  apply
    _root_.GD.N0232.N0719.N0949.d001792
      (theta := _root_.GD.N0232.N0719.N0924.d010472)
      (p := _root_.GD.N0232.N0719.N0924.d010439)
      (b := _root_.GD.N0232.N0719.N0924.d010440)
      (L := 2)
      (C := 51)
      _root_.GD.N0232.N0719.N0924.d010475.le _root_.GD.N0232.N0719.N0924.d010476
      _root_.GD.N0232.N0719.N0924.d010442 _root_.GD.N0232.N0719.N0924.d010443 (by norm_num)
      _root_.GD.N0232.N0719.N0924.d010474
      (fun _ ↦ _root_.GD.N0232.N0719.N0924.d010439)
      (fun n ↦ _root_.GD.N0232.N0719.N0924.d010441 (_root_.GD.N0232.N0719.N0924.d010473 n))
      (fun n ↦ _root_.GD.N0232.N0719.N0924.d010437 (_root_.GD.N0232.N0719.N0924.d010473 n))
      (fun n ↦ _root_.GD.N0232.N0719.N0924.d010438 (_root_.GD.N0232.N0719.N0924.d010473 n))
  · exact _root_.GD.N0232.N0719.N0924.d010480
  · exact _root_.GD.N0232.N0719.N0924.d010481
  · intro n
    exact le_rfl
  · intro n
    rfl
  · intro n
    exact (_root_.GD.N0232.N0719.N0924.d010445 (_root_.GD.N0232.N0719.N0924.d010477 n)).le
  · exact _root_.GD.N0232.N0719.N0924.d010483
  · exact _root_.GD.N0232.N0719.N0924.d010482



theorem d010485 :
    ∃ n : ℕ,
      _root_.GD.N0232.N0719.N0924.d010438 (_root_.GD.N0232.N0719.N0924.d010473 n) <
        _root_.GD.N0232.N0719.N0924.d010437 (_root_.GD.N0232.N0719.N0924.d010473 n) := by
  by_contra h
  push Not at h
  exact _root_.GD.N0232.N0719.N0924.d010484 h



open _root_.GD.N0232.N0719.N0933
open _root_.GD.N0232.N0719.N0927



def d010486 (ε : ℝ) : Fin 3 → ℝ :=
  ![Real.sqrt 2 * Real.sqrt ε, Real.sqrt 6, Real.sqrt 6]



def d010487 : (Fin 3 → ℝ) ≃ᵐ _root_.GD.N0232.N0719.N0923.d009974 where
  toEquiv :=
    { toFun := _root_.GD.N0232.N0719.N1004.d009804
      invFun := fun z ↦ ![z.1, z.2.1, z.2.2]
      left_inv := by
        intro y
        funext i
        fin_cases i <;> rfl
      right_inv := by
        intro z
        rcases z with ⟨z0, z1, z2⟩
        rfl }
  measurable_toFun := _root_.GD.N0232.N0719.N1004.d009805
  measurable_invFun := by
    change Measurable (fun z : _root_.GD.N0232.N0719.N0923.d009974 ↦ ![z.1, z.2.1, z.2.2])
    refine measurable_pi_lambda _ fun i ↦ ?_
    fin_cases i <;> fun_prop

theorem d010488
    {ε : ℝ} (hε : 0 ≤ ε) (z : ℝ) :
    _root_.GD.N0232.N0719.N0933.d009286 2 0 (Real.sqrt 2 * Real.sqrt ε) z =
      Real.sqrt ε * z := by
  unfold _root_.GD.N0232.N0719.N0933.d009286
  have h2 : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  field_simp [h2] <;> ring

theorem d010489 (z : ℝ) :
    _root_.GD.N0232.N0719.N0933.d009286 6 0 (Real.sqrt 6) z = z := by
  unfold _root_.GD.N0232.N0719.N0933.d009286
  have h6 : Real.sqrt (6 : ℝ) ≠ 0 := by positivity
  field_simp [h6] <;> ring

theorem d010490
    {ε : ℝ} (hε : 0 ≤ ε) (q : ℝ) :
    _root_.GD.N0232.N0719.N0933.d009287 2 (Real.sqrt 2 * Real.sqrt ε) q = ε * q := by
  unfold _root_.GD.N0232.N0719.N0933.d009287
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have he := Real.sq_sqrt hε
  rw [mul_pow, h2, he]
  ring

theorem d010491 (q : ℝ) :
    _root_.GD.N0232.N0719.N0933.d009287 6 (Real.sqrt 6) q = q := by
  unfold _root_.GD.N0232.N0719.N0933.d009287
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
  norm_num



def d010492 (ε : ℝ) (z : _root_.GD.N0232.N0719.N0923.d009974) : Fin 3 → ℝ :=
  _root_.GD.N0232.N0719.N0924.d010487.symm
    (_root_.GD.N0232.N0719.N0933.d009286 2 0 (_root_.GD.N0232.N0719.N0924.d010486 ε 0) z.1,
      (_root_.GD.N0232.N0719.N0933.d009286 6 0 (_root_.GD.N0232.N0719.N0924.d010486 ε 1) z.2.1,
        _root_.GD.N0232.N0719.N0933.d009286 6 0 (_root_.GD.N0232.N0719.N0924.d010486 ε 2) z.2.2))


def d010493 (ε : ℝ) (q : _root_.GD.N0232.N0719.N0923.d009974) : Fin 3 → ℝ :=
  _root_.GD.N0232.N0719.N0924.d010487.symm
    (_root_.GD.N0232.N0719.N0933.d009287 2 (_root_.GD.N0232.N0719.N0924.d010486 ε 0) q.1,
      (_root_.GD.N0232.N0719.N0933.d009287 6 (_root_.GD.N0232.N0719.N0924.d010486 ε 1) q.2.1,
        _root_.GD.N0232.N0719.N0933.d009287 6 (_root_.GD.N0232.N0719.N0924.d010486 ε 2) q.2.2))

@[fun_prop]
theorem d010494 (ε : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0924.d010492 ε) := by
  unfold _root_.GD.N0232.N0719.N0924.d010492
  fun_prop

@[fun_prop]
theorem d010495 (ε : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0924.d010493 ε) := by
  unfold _root_.GD.N0232.N0719.N0924.d010493
  fun_prop

theorem d010496
    {ε : ℝ} (hε : 0 ≤ ε) (z : _root_.GD.N0232.N0719.N0923.d009974) :
    _root_.GD.N0232.N0719.N0924.d010492 ε z = _root_.GD.N0232.N0719.N0923.d009981 ε z := by
  funext i
  fin_cases i
  · simpa [_root_.GD.N0232.N0719.N0924.d010492, _root_.GD.N0232.N0719.N0924.d010487, _root_.GD.N0232.N0719.N0924.d010486,
      _root_.GD.N0232.N0719.N0923.d009981] using _root_.GD.N0232.N0719.N0924.d010488 hε z.1
  · simpa [_root_.GD.N0232.N0719.N0924.d010492, _root_.GD.N0232.N0719.N0924.d010487, _root_.GD.N0232.N0719.N0924.d010486,
      _root_.GD.N0232.N0719.N0923.d009981] using _root_.GD.N0232.N0719.N0924.d010489 z.2.1
  · simpa [_root_.GD.N0232.N0719.N0924.d010492, _root_.GD.N0232.N0719.N0924.d010487, _root_.GD.N0232.N0719.N0924.d010486,
      _root_.GD.N0232.N0719.N0923.d009981] using _root_.GD.N0232.N0719.N0924.d010489 z.2.2

theorem d010497
    {ε : ℝ} (hε : 0 ≤ ε) (q : _root_.GD.N0232.N0719.N0923.d009974) :
    _root_.GD.N0232.N0719.N0924.d010493 ε q = _root_.GD.N0232.N0719.N0923.d009982 ε q := by
  funext i
  fin_cases i
  · simpa [_root_.GD.N0232.N0719.N0924.d010493, _root_.GD.N0232.N0719.N0924.d010487, _root_.GD.N0232.N0719.N0924.d010486,
      _root_.GD.N0232.N0719.N0923.d009982] using _root_.GD.N0232.N0719.N0924.d010490 hε q.1
  · simpa [_root_.GD.N0232.N0719.N0924.d010493, _root_.GD.N0232.N0719.N0924.d010487, _root_.GD.N0232.N0719.N0924.d010486,
      _root_.GD.N0232.N0719.N0923.d009982] using _root_.GD.N0232.N0719.N0924.d010491 q.2.1
  · simpa [_root_.GD.N0232.N0719.N0924.d010493, _root_.GD.N0232.N0719.N0924.d010487, _root_.GD.N0232.N0719.N0924.d010486,
      _root_.GD.N0232.N0719.N0923.d009982] using _root_.GD.N0232.N0719.N0924.d010491 q.2.2



theorem d010498
    (mu : Fin 3 → Measure ℝ) [∀ i, SigmaFinite (mu i)] :
    MeasurePreserving _root_.GD.N0232.N0719.N0924.d010487 (Measure.pi mu)
      ((mu 0).prod ((mu 1).prod (mu 2))) := by
  simpa [_root_.GD.N0232.N0719.N0924.d010487] using
    _root_.GD.N0232.N0719.N1004.d009806 mu



theorem d010499
    (mu : Fin 3 → Measure ℝ) [∀ i, SigmaFinite (mu i)] :
    MeasurePreserving _root_.GD.N0232.N0719.N0924.d010487.symm
      ((mu 0).prod ((mu 1).prod (mu 2))) (Measure.pi mu) := by
  exact MeasurePreserving.symm _root_.GD.N0232.N0719.N0924.d010487
    (_root_.GD.N0232.N0719.N0924.d010498 mu)



theorem d010500 (ε : ℝ) :
    MeasurePreserving (_root_.GD.N0232.N0719.N0924.d010492 ε)
      _root_.GD.N0232.N0719.N0923.d009975
      (_root_.GD.N0232.N0719.N0933.d009300 3 _root_.GD.N0232.N0719.N0927.d009909 0 (_root_.GD.N0232.N0719.N0924.d010486 ε)) := by
  let mu : Fin 3 → Measure ℝ := fun i ↦
    _root_.GD.N0232.N0719.N0933.d009288 (_root_.GD.N0232.N0719.N0927.d009909 i) 0 (_root_.GD.N0232.N0719.N0924.d010486 ε i)
  have h0 : MeasurePreserving
      (_root_.GD.N0232.N0719.N0933.d009286 2 0 (_root_.GD.N0232.N0719.N0924.d010486 ε 0))
      (gaussianReal 0 1) (mu 0) := by
    simpa [mu, _root_.GD.N0232.N0719.N0933.d009288, _root_.GD.N0232.N0719.N0927.d009909] using
      (_root_.GD.N0232.N0719.N0933.d009293 2 0 (_root_.GD.N0232.N0719.N0924.d010486 ε 0)).measurePreserving
        (gaussianReal 0 1)
  have h1 : MeasurePreserving
      (_root_.GD.N0232.N0719.N0933.d009286 6 0 (_root_.GD.N0232.N0719.N0924.d010486 ε 1))
      (gaussianReal 0 1) (mu 1) := by
    simpa [mu, _root_.GD.N0232.N0719.N0933.d009288, _root_.GD.N0232.N0719.N0927.d009909] using
      (_root_.GD.N0232.N0719.N0933.d009293 6 0 (_root_.GD.N0232.N0719.N0924.d010486 ε 1)).measurePreserving
        (gaussianReal 0 1)
  have h2 : MeasurePreserving
      (_root_.GD.N0232.N0719.N0933.d009286 6 0 (_root_.GD.N0232.N0719.N0924.d010486 ε 2))
      (gaussianReal 0 1) (mu 2) := by
    simpa [mu, _root_.GD.N0232.N0719.N0933.d009288, _root_.GD.N0232.N0719.N0927.d009909] using
      (_root_.GD.N0232.N0719.N0933.d009293 6 0 (_root_.GD.N0232.N0719.N0924.d010486 ε 2)).measurePreserving
        (gaussianReal 0 1)
  have hnested := h0.prod (h1.prod h2)
  have hvector := _root_.GD.N0232.N0719.N0924.d010499 mu
  have hcomp := hvector.comp hnested
  have hfun :
      (_root_.GD.N0232.N0719.N0924.d010487.symm ∘
        Prod.map
          (_root_.GD.N0232.N0719.N0933.d009286 2 0 (_root_.GD.N0232.N0719.N0924.d010486 ε 0))
          (Prod.map
            (_root_.GD.N0232.N0719.N0933.d009286 6 0 (_root_.GD.N0232.N0719.N0924.d010486 ε 1))
            (_root_.GD.N0232.N0719.N0933.d009286 6 0 (_root_.GD.N0232.N0719.N0924.d010486 ε 2)))) =
        _root_.GD.N0232.N0719.N0924.d010492 ε := by
    rfl
  rw [hfun] at hcomp
  simpa [_root_.GD.N0232.N0719.N0923.d009975, _root_.GD.N0232.N0719.N0933.d009300, mu] using hcomp



theorem d010501 (ε : ℝ) :
    MeasurePreserving (_root_.GD.N0232.N0719.N0924.d010493 ε)
      _root_.GD.N0232.N0719.N0923.d009976
      (_root_.GD.N0232.N0719.N0933.d009301 3 _root_.GD.N0232.N0719.N0927.d009909 (_root_.GD.N0232.N0719.N0924.d010486 ε)) := by
  letI : IsProbabilityMeasure
      (gammaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  letI : IsProbabilityMeasure
      (gammaMeasure (5 / 2 : ℝ) (5 / 2 : ℝ)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  let mu : Fin 3 → Measure ℝ := fun i ↦
    _root_.GD.N0232.N0719.N0933.d009289 (_root_.GD.N0232.N0719.N0927.d009909 i) (_root_.GD.N0232.N0719.N0924.d010486 ε i)
  have h0 : MeasurePreserving
      (_root_.GD.N0232.N0719.N0933.d009287 2 (_root_.GD.N0232.N0719.N0924.d010486 ε 0))
      (gammaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)) (mu 0) := by
    simpa [mu, _root_.GD.N0232.N0719.N0933.d009289, _root_.GD.N0232.N0719.N0927.d009909] using
      (_root_.GD.N0232.N0719.N0933.d009294 2 (_root_.GD.N0232.N0719.N0924.d010486 ε 0)).measurePreserving
        (gammaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ))
  have h1 : MeasurePreserving
      (_root_.GD.N0232.N0719.N0933.d009287 6 (_root_.GD.N0232.N0719.N0924.d010486 ε 1))
      (gammaMeasure (5 / 2 : ℝ) (5 / 2 : ℝ)) (mu 1) := by
    simpa [mu, _root_.GD.N0232.N0719.N0933.d009289, _root_.GD.N0232.N0719.N0927.d009909] using
      (_root_.GD.N0232.N0719.N0933.d009294 6 (_root_.GD.N0232.N0719.N0924.d010486 ε 1)).measurePreserving
        (gammaMeasure (5 / 2 : ℝ) (5 / 2 : ℝ))
  have h2 : MeasurePreserving
      (_root_.GD.N0232.N0719.N0933.d009287 6 (_root_.GD.N0232.N0719.N0924.d010486 ε 2))
      (gammaMeasure (5 / 2 : ℝ) (5 / 2 : ℝ)) (mu 2) := by
    simpa [mu, _root_.GD.N0232.N0719.N0933.d009289, _root_.GD.N0232.N0719.N0927.d009909] using
      (_root_.GD.N0232.N0719.N0933.d009294 6 (_root_.GD.N0232.N0719.N0924.d010486 ε 2)).measurePreserving
        (gammaMeasure (5 / 2 : ℝ) (5 / 2 : ℝ))
  have hnested := h0.prod (h1.prod h2)
  letI hmu0 : IsProbabilityMeasure (mu 0) := ⟨by
    rw [← h0.map_eq]
    exact (Measure.isProbabilityMeasure_map
      h0.measurable.aemeasurable).measure_univ⟩
  letI hmu1 : IsProbabilityMeasure (mu 1) := ⟨by
    rw [← h1.map_eq]
    exact (Measure.isProbabilityMeasure_map
      h1.measurable.aemeasurable).measure_univ⟩
  letI hmu2 : IsProbabilityMeasure (mu 2) := ⟨by
    rw [← h2.map_eq]
    exact (Measure.isProbabilityMeasure_map
      h2.measurable.aemeasurable).measure_univ⟩
  letI : ∀ i, IsProbabilityMeasure (mu i) := fun i ↦ by
    fin_cases i
    · simpa using hmu0
    · simpa using hmu1
    · simpa using hmu2
  have hvector := _root_.GD.N0232.N0719.N0924.d010499 mu
  have hcomp := hvector.comp hnested
  have hfun :
      (_root_.GD.N0232.N0719.N0924.d010487.symm ∘
        Prod.map
          (_root_.GD.N0232.N0719.N0933.d009287 2 (_root_.GD.N0232.N0719.N0924.d010486 ε 0))
          (Prod.map
            (_root_.GD.N0232.N0719.N0933.d009287 6 (_root_.GD.N0232.N0719.N0924.d010486 ε 1))
            (_root_.GD.N0232.N0719.N0933.d009287 6 (_root_.GD.N0232.N0719.N0924.d010486 ε 2)))) =
        _root_.GD.N0232.N0719.N0924.d010493 ε := by
    rfl
  rw [hfun] at hcomp
  simpa [_root_.GD.N0232.N0719.N0923.d009976, _root_.GD.N0232.N0719.N0933.d009301, mu] using hcomp


theorem d010502
    {ε : ℝ} (hε : 0 ≤ ε) :
    MeasurePreserving
      (fun w : _root_.GD.N0232.N0719.N0923.d009974 × _root_.GD.N0232.N0719.N0923.d009974 ↦
        (_root_.GD.N0232.N0719.N0923.d009981 ε w.1, _root_.GD.N0232.N0719.N0923.d009982 ε w.2))
      _root_.GD.N0232.N0719.N0923.d009977
      ((_root_.GD.N0232.N0719.N0933.d009300 3 _root_.GD.N0232.N0719.N0927.d009909 0 (_root_.GD.N0232.N0719.N0924.d010486 ε)).prod
        (_root_.GD.N0232.N0719.N0933.d009301 3 _root_.GD.N0232.N0719.N0927.d009909 (_root_.GD.N0232.N0719.N0924.d010486 ε))) := by
  have hprod :=
    (_root_.GD.N0232.N0719.N0924.d010500 ε).prod
      (_root_.GD.N0232.N0719.N0924.d010501 ε)
  have hfun :
      Prod.map (_root_.GD.N0232.N0719.N0924.d010492 ε) (_root_.GD.N0232.N0719.N0924.d010493 ε) =
        fun w : _root_.GD.N0232.N0719.N0923.d009974 × _root_.GD.N0232.N0719.N0923.d009974 ↦
          (_root_.GD.N0232.N0719.N0923.d009981 ε w.1, _root_.GD.N0232.N0719.N0923.d009982 ε w.2) := by
    funext w
    apply Prod.ext
    · exact _root_.GD.N0232.N0719.N0924.d010496 hε w.1
    · exact _root_.GD.N0232.N0719.N0924.d010497 hε w.2
  rw [← hfun]
  exact hprod


def d010503 (ε : ℝ) :
    _root_.GD.N0232.N0719.N0900.d009094 3 _root_.GD.N0232.N0719.N0927.d009909 → ℝ :=
  _root_.GD.N0232.N0719.N0867.d010315 (by norm_num) _root_.GD.N0232.N0719.N0922.d009915 (5 / 2) _root_.GD.N0232.N0719.N0927.d009909


def d010504 :
    _root_.GD.N0232.N0719.N0900.d009094 3 _root_.GD.N0232.N0719.N0927.d009909 → ℝ :=
  _root_.GD.N0232.N0719.N0900.d009111 3 _root_.GD.N0232.N0719.N0927.d009909


def d010505 (ε : ℝ) : ℝ :=
  _root_.GD.N0141.d006684
    (_root_.GD.N0232.N0719.d009176 3 _root_.GD.N0232.N0719.N0927.d009909 0 (_root_.GD.N0232.N0719.N0924.d010486 ε))
    (_root_.GD.N0232.N0719.N0924.d010503 ε)


def d010506 (ε : ℝ) : ℝ :=
  _root_.GD.N0141.d006684
    (_root_.GD.N0232.N0719.d009176 3 _root_.GD.N0232.N0719.N0927.d009909 0 (_root_.GD.N0232.N0719.N0924.d010486 ε))
    _root_.GD.N0232.N0719.N0924.d010504

@[fun_prop]
theorem d010507 (ε : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0924.d010503 ε) := by
  exact _root_.GD.N0232.N0719.N0867.d010316
    (by norm_num) _root_.GD.N0232.N0719.N0922.d009915 (5 / 2) _root_.GD.N0232.N0719.N0927.d009909

@[fun_prop]
theorem d010508 :
    Measurable _root_.GD.N0232.N0719.N0924.d010504 := by
  exact _root_.GD.N0232.N0719.N0900.d009122 3 _root_.GD.N0232.N0719.N0927.d009909



theorem d010509
    {ε : ℝ} (hε : 0 ≤ ε) :
    _root_.GD.N0232.N0719.N0924.d010505 ε = _root_.GD.N0232.N0719.N0924.d010437 ε := by
  let F : _root_.GD.N0232.N0719.N0900.d009096 3 → ℝ := fun u ↦
    _root_.GD.N0232.N0719.N0867.d010306 (by norm_num) _root_.GD.N0232.N0719.N0922.d009915 (5 / 2) u ^ 2
  have hF : Measurable F := by
    exact (_root_.GD.N0232.N0719.N0867.d010309
      (by norm_num) _root_.GD.N0232.N0719.N0922.d009915 (5 / 2)).pow_const 2
  have hraw :=
    _root_.GD.N0232.N0719.N0933.d009310
      3 _root_.GD.N0232.N0719.N0927.d009909
      (by intro i; fin_cases i <;> norm_num [_root_.GD.N0232.N0719.N0927.d009909])
      0 (_root_.GD.N0232.N0719.N0924.d010486 ε) F hF
  have hmp := _root_.GD.N0232.N0719.N0924.d010502 hε
  have hvectorTransport :
      (∫ z, F (_root_.GD.N0232.N0719.N0933.d009305 3 z)
        ∂((_root_.GD.N0232.N0719.N0933.d009300 3 _root_.GD.N0232.N0719.N0927.d009909 0 (_root_.GD.N0232.N0719.N0924.d010486 ε)).prod
          (_root_.GD.N0232.N0719.N0933.d009301 3 _root_.GD.N0232.N0719.N0927.d009909 (_root_.GD.N0232.N0719.N0924.d010486 ε)))) =
        ∫ w, F (_root_.GD.N0232.N0719.N0924.d010434 ε w) ∂_root_.GD.N0232.N0719.N0923.d009977 := by
    rw [← hmp.map_eq]
    simpa [Function.comp_def, _root_.GD.N0232.N0719.N0924.d010434, _root_.GD.N0232.N0719.N0933.d009305,
      _root_.GD.N0232.N0719.N0922.d009943] using
      (integral_map_of_stronglyMeasurable
        (μ := _root_.GD.N0232.N0719.N0923.d009977) hmp.measurable
        ((hF.comp (_root_.GD.N0232.N0719.N0933.d009306 3)).stronglyMeasurable))
  unfold _root_.GD.N0232.N0719.N0924.d010505 _root_.GD.N0141.d006684
  change
    (∫ x,
      F (_root_.GD.N0232.N0719.N0900.d009104 3 _root_.GD.N0232.N0719.N0927.d009909 x)
        ∂_root_.GD.N0232.N0719.d009176 3 _root_.GD.N0232.N0719.N0927.d009909 0 (_root_.GD.N0232.N0719.N0924.d010486 ε)) = _
  rw [hraw, hvectorTransport]
  rfl



theorem d010510
    {ε : ℝ} (hε : 0 ≤ ε) :
    _root_.GD.N0232.N0719.N0924.d010506 ε = _root_.GD.N0232.N0719.N0924.d010438 ε := by
  let F : _root_.GD.N0232.N0719.N0900.d009096 3 → ℝ := fun u ↦ _root_.GD.N0232.N0719.N0900.d009110 u ^ 2
  have hF : Measurable F := _root_.GD.N0232.N0719.N0900.d009121.pow_const 2
  have hraw :=
    _root_.GD.N0232.N0719.N0933.d009310
      3 _root_.GD.N0232.N0719.N0927.d009909
      (by intro i; fin_cases i <;> norm_num [_root_.GD.N0232.N0719.N0927.d009909])
      0 (_root_.GD.N0232.N0719.N0924.d010486 ε) F hF
  have hmp := _root_.GD.N0232.N0719.N0924.d010502 hε
  have hvectorTransport :
      (∫ z, F (_root_.GD.N0232.N0719.N0933.d009305 3 z)
        ∂((_root_.GD.N0232.N0719.N0933.d009300 3 _root_.GD.N0232.N0719.N0927.d009909 0 (_root_.GD.N0232.N0719.N0924.d010486 ε)).prod
          (_root_.GD.N0232.N0719.N0933.d009301 3 _root_.GD.N0232.N0719.N0927.d009909 (_root_.GD.N0232.N0719.N0924.d010486 ε)))) =
        ∫ w, F (_root_.GD.N0232.N0719.N0924.d010434 ε w) ∂_root_.GD.N0232.N0719.N0923.d009977 := by
    rw [← hmp.map_eq]
    simpa [Function.comp_def, _root_.GD.N0232.N0719.N0924.d010434, _root_.GD.N0232.N0719.N0933.d009305,
      _root_.GD.N0232.N0719.N0922.d009943] using
      (integral_map_of_stronglyMeasurable
        (μ := _root_.GD.N0232.N0719.N0923.d009977) hmp.measurable
        ((hF.comp (_root_.GD.N0232.N0719.N0933.d009306 3)).stronglyMeasurable))
  unfold _root_.GD.N0232.N0719.N0924.d010506 _root_.GD.N0141.d006684
  change
    (∫ x,
      F (_root_.GD.N0232.N0719.N0900.d009104 3 _root_.GD.N0232.N0719.N0927.d009909 x)
        ∂_root_.GD.N0232.N0719.d009176 3 _root_.GD.N0232.N0719.N0927.d009909 0 (_root_.GD.N0232.N0719.N0924.d010486 ε)) = _
  rw [hraw, hvectorTransport]
  rfl





theorem d010511 :
    ∃ n : ℕ,
      _root_.GD.N0232.N0719.N0924.d010506 (_root_.GD.N0232.N0719.N0924.d010473 n) <
        _root_.GD.N0232.N0719.N0924.d010505 (_root_.GD.N0232.N0719.N0924.d010473 n) := by
  obtain ⟨n, hn⟩ := _root_.GD.N0232.N0719.N0924.d010485
  refine ⟨n, ?_⟩
  rw [_root_.GD.N0232.N0719.N0924.d010510
      (_root_.GD.N0232.N0719.N0924.d010477 n).le,
    _root_.GD.N0232.N0719.N0924.d010509
      (_root_.GD.N0232.N0719.N0924.d010477 n).le]
  exact hn

end

end GD.N0232.N0719.N0924

#print axioms _root_.GD.N0232.N0719.N0924.d010432
#print axioms _root_.GD.N0232.N0719.N0924.d010433
#print axioms _root_.GD.N0232.N0719.N0924.d010458
#print axioms _root_.GD.N0232.N0719.N0924.d010470
#print axioms _root_.GD.N0232.N0719.N0924.d010484
#print axioms _root_.GD.N0232.N0719.N0924.d010485
#print axioms _root_.GD.N0232.N0719.N0924.d010502
#print axioms _root_.GD.N0232.N0719.N0924.d010509
#print axioms _root_.GD.N0232.N0719.N0924.d010510
#print axioms _root_.GD.N0232.N0719.N0924.d010511
