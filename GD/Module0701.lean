import GD.Module0699
import GD.Module0288
import Mathlib.Topology.Order.Monotone
















open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal ProbabilityTheory

namespace GD.N0232.N0719.N0875

noncomputable section

open _root_.GD.N0232.N0719.N1009 _root_.GD.N0232.N0719.N0933 _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0910
open _root_.GD.N0235.N0744



def d010319 (zq : ℝ × ℝ) : ℝ :=
  zq.1 / Real.sqrt zq.2

@[fun_prop]
theorem d010320 : Measurable _root_.GD.N0232.N0719.N0875.d010319 := by
  unfold _root_.GD.N0232.N0719.N0875.d010319
  fun_prop


noncomputable def d010321 (n : ℕ) : Measure ℝ :=
  (_root_.GD.N0232.N0719.N1009.d009275 n).map _root_.GD.N0232.N0719.N0875.d010319

theorem d010322
    {n : ℕ} (hn : 2 ≤ n) :
    IsProbabilityMeasure (_root_.GD.N0232.N0719.N0875.d010321 n) := by
  unfold _root_.GD.N0232.N0719.N0875.d010321 _root_.GD.N0232.N0719.N1009.d009275
  have hshape : 0 < (((n - 1 : ℕ) : ℝ) / 2) := by
    have hnsub : 0 < n - 1 := by omega
    have : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hnsub
    positivity
  letI : IsProbabilityMeasure
      (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
        (((n - 1 : ℕ) : ℝ) / 2)) :=
    isProbabilityMeasure_gammaMeasure hshape hshape
  exact Measure.isProbabilityMeasure_map _root_.GD.N0232.N0719.N0875.d010320.aemeasurable




theorem d010323
    {n : ℕ} (hn : 2 ≤ n) (x : ℝ) :
    _root_.GD.N0232.N0719.N0875.d010321 n {x} = 0 := by
  let a : ℝ := ((n - 1 : ℕ) : ℝ) / 2
  have ha : 0 < a := by
    have hnsub : 0 < n - 1 := by omega
    have : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hnsub
    dsimp [a]
    positivity
  let γ : Measure ℝ := gammaMeasure a a
  letI : IsProbabilityMeasure γ :=
    isProbabilityMeasure_gammaMeasure ha ha
  have hgauss : NoAtoms (gaussianReal 0 1) :=
    noAtoms_gaussianReal (by norm_num)
  letI : NoAtoms (gaussianReal 0 1) := hgauss
  have hpre : MeasurableSet (_root_.GD.N0232.N0719.N0875.d010319 ⁻¹' {x}) :=
    (measurableSet_singleton x).preimage _root_.GD.N0232.N0719.N0875.d010320
  unfold _root_.GD.N0232.N0719.N0875.d010321 _root_.GD.N0232.N0719.N1009.d009275
  change (((gaussianReal 0 1).prod γ).map _root_.GD.N0232.N0719.N0875.d010319) {x} = 0
  rw [Measure.map_apply _root_.GD.N0232.N0719.N0875.d010320 (measurableSet_singleton x)]
  rw [Measure.prod_apply_symm hpre]
  rw [lintegral_eq_zero_iff]
  · filter_upwards [_root_.GD.N0232.N0719.N0910.d010286 ha ha] with q hq
    have hsqrt : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
    have hsection :
        (Prod.mk · q) ⁻¹' (_root_.GD.N0232.N0719.N0875.d010319 ⁻¹' {x}) =
          {x * Real.sqrt q} := by
      ext z
      simp only [mem_preimage, mem_singleton_iff]
      unfold _root_.GD.N0232.N0719.N0875.d010319
      simp only
      constructor
      · intro hz
        apply (div_eq_iff hsqrt).mp
        simpa [mul_comm] using hz
      · intro hz
        rw [hz]
        field_simp
    simp [hsection]
  · exact measurable_measure_prodMk_right hpre

theorem d010324
    {n : ℕ} (hn : 2 ≤ n) :
    NoAtoms (_root_.GD.N0232.N0719.N0875.d010321 n) where
  measure_singleton := _root_.GD.N0232.N0719.N0875.d010323 hn




theorem d010325
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] :
    Continuous (ProbabilityTheory.cdf μ) := by
  rw [continuous_iff_continuousAt]
  intro x
  apply (ProbabilityTheory.monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim.2
  rw [(ProbabilityTheory.cdf μ).rightLim_eq]
  apply le_antisymm
  · exact (ProbabilityTheory.monotone_cdf μ).leftLim_le le_rfl
  · have hzero :
        ENNReal.ofReal
            (ProbabilityTheory.cdf μ x -
              Function.leftLim (ProbabilityTheory.cdf μ) x) = 0 := by
      rw [← (ProbabilityTheory.cdf μ).measure_singleton]
      rw [ProbabilityTheory.measure_cdf μ]
      exact measure_singleton x
    have hle :
        ProbabilityTheory.cdf μ x -
            Function.leftLim (ProbabilityTheory.cdf μ) x ≤ 0 :=
      ENNReal.ofReal_eq_zero.mp hzero
    linarith


theorem d010326
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ x : ℝ, ProbabilityTheory.cdf μ x = p := by
  have hbelow :
      ∀ᶠ x : ℝ in atBot, ProbabilityTheory.cdf μ x < p :=
    (tendsto_order.1 (ProbabilityTheory.tendsto_cdf_atBot μ)).2 p hp0
  have habove :
      ∀ᶠ x : ℝ in atTop, p < ProbabilityTheory.cdf μ x :=
    (tendsto_order.1 (ProbabilityTheory.tendsto_cdf_atTop μ)).1 p hp1
  obtain ⟨a, ha⟩ := hbelow.exists
  obtain ⟨b, hb⟩ := habove.exists
  have hab : a ≤ b := by
    by_contra hba
    have hmono := ProbabilityTheory.monotone_cdf μ (le_of_not_ge hba)
    linarith
  have hpI : p ∈ Set.Icc
      (ProbabilityTheory.cdf μ a) (ProbabilityTheory.cdf μ b) :=
    ⟨ha.le, hb.le⟩
  exact (intermediate_value_univ a b
    (_root_.GD.N0232.N0719.N0875.d010325 μ) hpI)



theorem d010327
    (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ProbabilityTheory.cdf μ (_root_.GD.N0235.N0744.d004268 μ p) = p := by
  let F : ℝ → ℝ := ProbabilityTheory.cdf μ
  let A : Set ℝ := _root_.GD.N0235.N0744.d004257 F p
  have hfinite : _root_.GD.N0235.N0744.d004259 F p :=
    _root_.GD.N0235.N0744.d004272 μ hp0 hp1
  obtain ⟨x, hx⟩ := _root_.GD.N0232.N0719.N0875.d010326 μ hp0 hp1
  have hxA : x ∈ A := by
    change p ≤ ProbabilityTheory.cdf μ x
    rw [hx]
  have himage_nonempty : (F '' A).Nonempty := hfinite.1.image F
  have hp_lower : p ∈ lowerBounds (F '' A) := by
    rintro y ⟨z, hz, rfl⟩
    exact hz
  have hp_image : p ∈ F '' A := ⟨x, hxA, hx⟩
  have hcontinuous : Continuous F := by
    simpa [F] using _root_.GD.N0232.N0719.N0875.d010325 μ
  have hmonotone : Monotone F := by
    simpa [F] using ProbabilityTheory.monotone_cdf μ
  change F (sInf A) = p
  rw [hmonotone.map_csInf_of_continuousAt
    hcontinuous.continuousAt hfinite.1 hfinite.2]
  exact le_antisymm
    (csInf_le ⟨p, hp_lower⟩ hp_image)
    (le_csInf himage_nonempty hp_lower)



theorem d010328
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {p q : ℝ} (hp0 : 0 < p) (hq1 : q < 1) (hpq : p ≤ q) :
    _root_.GD.N0235.N0744.d004268 μ p ≤ _root_.GD.N0235.N0744.d004268 μ q := by
  have hq0 : 0 < q := hp0.trans_le hpq
  have hp1 : p < 1 := lt_of_le_of_lt hpq hq1
  have hpfinite := _root_.GD.N0235.N0744.d004272 μ hp0 hp1
  have hqfinite := _root_.GD.N0235.N0744.d004272 μ hq0 hq1
  unfold _root_.GD.N0235.N0744.d004268 _root_.GD.N0235.N0744.d004258
  apply csInf_le_csInf hpfinite.2 hqfinite.1
  intro x hx
  exact hpq.trans hx




def d010329 (location : ℝ) (yt : ℝ × ℝ) : ℝ :=
  (yt.1 - location) / Real.sqrt yt.2

@[fun_prop]
theorem d010330 (location : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0875.d010329 location) := by
  unfold _root_.GD.N0232.N0719.N0875.d010329
  fun_prop



theorem d010331
    {n : ℕ} (hn : 2 ≤ n) {scale : ℝ} (hscale : 0 < scale)
    (location : ℝ) (zq : ℝ × ℝ) (hq : 0 < zq.2) :
    _root_.GD.N0232.N0719.N0875.d010329 location (_root_.GD.N0232.N0719.N1009.d009274 n location scale zq) =
      _root_.GD.N0232.N0719.N0875.d010319 zq := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hcoef : 0 < scale / Real.sqrt (n : ℝ) :=
    div_pos hscale hsqrtn
  have hsqrtq : Real.sqrt zq.2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have hsqrtvar :
      Real.sqrt ((scale ^ 2 / (n : ℝ)) * zq.2) =
        (scale / Real.sqrt (n : ℝ)) * Real.sqrt zq.2 := by
    rw [Real.sqrt_mul (div_nonneg (sq_nonneg scale) hnR.le)]
    rw [Real.sqrt_div (sq_nonneg scale)]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hscale]
  unfold _root_.GD.N0232.N0719.N0875.d010329 _root_.GD.N0232.N0719.N1009.d009274 _root_.GD.N0232.N0719.N0875.d010319
  simp only [add_sub_cancel_left, hsqrtvar]
  field_simp



theorem d010332
    {n : ℕ} (hn : 2 ≤ n) (location : ℝ)
    {scale : ℝ} (hscale : 0 < scale) :
    (_root_.GD.N0232.N0719.N1009.d009276 n location scale).map (_root_.GD.N0232.N0719.N0875.d010329 location) =
      _root_.GD.N0232.N0719.N0875.d010321 n := by
  let a : ℝ := ((n - 1 : ℕ) : ℝ) / 2
  have ha : 0 < a := by
    have hnsub : 0 < n - 1 := by omega
    have : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hnsub
    dsimp [a]
    positivity
  let γ : Measure ℝ := gammaMeasure a a
  letI : IsProbabilityMeasure γ :=
    isProbabilityMeasure_gammaMeasure ha ha
  have hqpos :
      ∀ᵐ zq ∂(gaussianReal 0 1).prod γ, 0 < zq.2 :=
    (Measure.quasiMeasurePreserving_snd
      (μ := gaussianReal 0 1) (ν := γ)).ae
      (_root_.GD.N0232.N0719.N0910.d010286 ha ha)
  unfold _root_.GD.N0232.N0719.N1009.d009276 _root_.GD.N0232.N0719.N0875.d010321
    _root_.GD.N0232.N0719.N1009.d009275
  change
    (((gaussianReal 0 1).prod γ).map
      (_root_.GD.N0232.N0719.N1009.d009274 n location scale)).map
        (_root_.GD.N0232.N0719.N0875.d010329 location) =
      ((gaussianReal 0 1).prod γ).map _root_.GD.N0232.N0719.N0875.d010319
  rw [Measure.map_map
    (_root_.GD.N0232.N0719.N0875.d010330 location)
    (_root_.GD.N0232.N0719.N1009.d009279 n location scale)]
  apply Measure.map_congr
  filter_upwards [hqpos] with zq hq
  exact _root_.GD.N0232.N0719.N0875.d010331 hn hscale location zq hq



def d010333 {k : ℕ} (j : Fin k) (s : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ × ℝ :=
  (s.mean j, s.meanVariance j)

@[fun_prop]
theorem d010334 {k : ℕ} (j : Fin k) :
    Measurable (_root_.GD.N0232.N0719.N0875.d010333 j) := by
  unfold _root_.GD.N0232.N0719.N0875.d010333
  fun_prop

theorem d010335
    {k : ℕ} (sizes : Fin k → ℕ) (j : Fin k)
    (ω : _root_.GD.N0232.N0719.d009173 k sizes) :
    _root_.GD.N0232.N0719.N0875.d010333 j (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω) =
      _root_.GD.N0232.N0719.N1009.d009272 (sizes j) (ω j) := by
  rfl



theorem d010336
    {k : ℕ} (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (j : Fin k) (location : ℝ) (scales : Fin k → ℝ) :
    (_root_.GD.N0232.N0719.d009176 k sizes location scales).map
        (_root_.GD.N0232.N0719.N0875.d010333 j ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes) =
      _root_.GD.N0232.N0719.N1009.d009276 (sizes j) location (scales j) := by
  have heval :
      (_root_.GD.N0232.N0719.d009176 k sizes location scales).map
          (fun ω => ω j) =
        _root_.GD.N0232.N0719.d009175 (sizes j) location (scales j) := by
    unfold _root_.GD.N0232.N0719.d009176
    exact (measurePreserving_eval
      (fun i => _root_.GD.N0232.N0719.d009175 (sizes i) location (scales i)) j).map_eq
  calc
    (_root_.GD.N0232.N0719.d009176 k sizes location scales).map
        (_root_.GD.N0232.N0719.N0875.d010333 j ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes) =
      (_root_.GD.N0232.N0719.d009176 k sizes location scales).map
        (_root_.GD.N0232.N0719.N1009.d009272 (sizes j) ∘ fun ω => ω j) := by
          rfl
    _ = ((_root_.GD.N0232.N0719.d009176 k sizes location scales).map
        (fun ω => ω j)).map (_root_.GD.N0232.N0719.N1009.d009272 (sizes j)) := by
          rw [Measure.map_map
            (_root_.GD.N0232.N0719.N1009.d009277 (sizes j))
            (measurable_pi_apply j)]
    _ = (_root_.GD.N0232.N0719.d009175 (sizes j) location (scales j)).map
        (_root_.GD.N0232.N0719.N1009.d009272 (sizes j)) := by rw [heval]
    _ = _root_.GD.N0232.N0719.N1009.d009276 (sizes j) location (scales j) :=
      _root_.GD.N0232.N0719.N1009.d009281 (hsizes j) location (scales j)



theorem d010337
    {k : ℕ} (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (j : Fin k) (location : ℝ) (scales : Fin k → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    (_root_.GD.N0232.N0719.d009176 k sizes location scales).map
        (_root_.GD.N0232.N0719.N0875.d010329 location ∘ _root_.GD.N0232.N0719.N0875.d010333 j ∘
          _root_.GD.N0232.N0719.N0900.d009104 k sizes) =
      _root_.GD.N0232.N0719.N0875.d010321 (sizes j) := by
  rw [← _root_.GD.N0232.N0719.N0875.d010332
    (hsizes j) location (hscales j)]
  rw [← _root_.GD.N0232.N0719.N0875.d010336 sizes hsizes j location scales]
  rw [Measure.map_map
    (_root_.GD.N0232.N0719.N0875.d010330 location)
    ((_root_.GD.N0232.N0719.N0875.d010334 j).comp
      (_root_.GD.N0232.N0719.N0900.d009115 k sizes))]




noncomputable def d010338 (n : ℕ) (alpha : ℝ) : ℝ :=
  _root_.GD.N0235.N0744.d004268 (_root_.GD.N0232.N0719.N0875.d010321 n) (alpha / 2)


noncomputable def d010339 (n : ℕ) (alpha : ℝ) : ℝ :=
  _root_.GD.N0235.N0744.d004268 (_root_.GD.N0232.N0719.N0875.d010321 n) (1 - alpha / 2)


noncomputable def d010340
    {k : ℕ} (n : ℕ) (j : Fin k) (alpha : ℝ) (s : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ :=
  s.mean j - _root_.GD.N0232.N0719.N0875.d010339 n alpha * Real.sqrt (s.meanVariance j)


noncomputable def d010341
    {k : ℕ} (n : ℕ) (j : Fin k) (alpha : ℝ) (s : _root_.GD.N0232.N0719.N0900.d009096 k) : ℝ :=
  s.mean j - _root_.GD.N0232.N0719.N0875.d010338 n alpha * Real.sqrt (s.meanVariance j)

@[fun_prop]
theorem d010342
    {k : ℕ} (n : ℕ) (j : Fin k) (alpha : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0875.d010340 n j alpha) := by
  unfold _root_.GD.N0232.N0719.N0875.d010340
  fun_prop

@[fun_prop]
theorem d010343
    {k : ℕ} (n : ℕ) (j : Fin k) (alpha : ℝ) :
    Measurable (_root_.GD.N0232.N0719.N0875.d010341 n j alpha) := by
  unfold _root_.GD.N0232.N0719.N0875.d010341
  fun_prop

theorem d010344
    {n : ℕ} (hn : 2 ≤ n) {alpha : ℝ}
    (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    _root_.GD.N0232.N0719.N0875.d010338 n alpha ≤ _root_.GD.N0232.N0719.N0875.d010339 n alpha := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0875.d010321 n) :=
    _root_.GD.N0232.N0719.N0875.d010322 hn
  unfold _root_.GD.N0232.N0719.N0875.d010338 _root_.GD.N0232.N0719.N0875.d010339
  apply _root_.GD.N0232.N0719.N0875.d010328 (_root_.GD.N0232.N0719.N0875.d010321 n)
  · positivity
  · linarith
  · linarith



theorem d010345
    {k n : ℕ} (hn : 2 ≤ n) (j : Fin k) {alpha : ℝ}
    (ha0 : 0 < alpha) (ha1 : alpha < 1) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0875.d010340 n j alpha s ≤ _root_.GD.N0232.N0719.N0875.d010341 n j alpha s := by
  unfold _root_.GD.N0232.N0719.N0875.d010340 _root_.GD.N0232.N0719.N0875.d010341
  exact sub_le_sub_left
    (mul_le_mul_of_nonneg_right (_root_.GD.N0232.N0719.N0875.d010344 hn ha0 ha1)
      (Real.sqrt_nonneg _)) _

theorem d010346
    {n : ℕ} (hn : 2 ≤ n) {alpha : ℝ}
    (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    _root_.GD.N0232.N0719.N0875.d010321 n (Set.Iio (_root_.GD.N0232.N0719.N0875.d010338 n alpha)) =
      ENNReal.ofReal (alpha / 2) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0875.d010321 n) :=
    _root_.GD.N0232.N0719.N0875.d010322 hn
  letI : NoAtoms (_root_.GD.N0232.N0719.N0875.d010321 n) := _root_.GD.N0232.N0719.N0875.d010324 hn
  have hcdf := _root_.GD.N0232.N0719.N0875.d010327
    (_root_.GD.N0232.N0719.N0875.d010321 n) (p := alpha / 2) (by positivity) (by linarith)
  have hae : Set.Iio (_root_.GD.N0232.N0719.N0875.d010338 n alpha) =ᵐ[_root_.GD.N0232.N0719.N0875.d010321 n]
      Set.Iic (_root_.GD.N0232.N0719.N0875.d010338 n alpha) := Iio_ae_eq_Iic
  rw [measure_congr hae]
  rw [← ProbabilityTheory.ofReal_cdf]
  simpa [_root_.GD.N0232.N0719.N0875.d010338] using congrArg ENNReal.ofReal hcdf

theorem d010347
    {n : ℕ} (hn : 2 ≤ n) {alpha : ℝ}
    (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    _root_.GD.N0232.N0719.N0875.d010321 n (Set.Ioi (_root_.GD.N0232.N0719.N0875.d010339 n alpha)) =
      ENNReal.ofReal (alpha / 2) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0875.d010321 n) :=
    _root_.GD.N0232.N0719.N0875.d010322 hn
  letI : NoAtoms (_root_.GD.N0232.N0719.N0875.d010321 n) := _root_.GD.N0232.N0719.N0875.d010324 hn
  have hcdf := _root_.GD.N0232.N0719.N0875.d010327
    (_root_.GD.N0232.N0719.N0875.d010321 n) (p := 1 - alpha / 2) (by linarith) (by linarith)
  rw [← ProbabilityTheory.measure_cdf (_root_.GD.N0232.N0719.N0875.d010321 n)]
  rw [(ProbabilityTheory.cdf (_root_.GD.N0232.N0719.N0875.d010321 n)).measure_Ioi
    (ProbabilityTheory.tendsto_cdf_atTop (_root_.GD.N0232.N0719.N0875.d010321 n))]
  rw [show ProbabilityTheory.cdf (_root_.GD.N0232.N0719.N0875.d010321 n)
      (_root_.GD.N0232.N0719.N0875.d010339 n alpha) = 1 - alpha / 2 by
    simpa [_root_.GD.N0232.N0719.N0875.d010339] using hcdf]
  congr 1
  ring

theorem d010348
    {n : ℕ} (hn : 2 ≤ n) {alpha : ℝ}
    (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    _root_.GD.N0232.N0719.N0875.d010321 n
        (Set.Icc (_root_.GD.N0232.N0719.N0875.d010338 n alpha) (_root_.GD.N0232.N0719.N0875.d010339 n alpha)) =
      ENNReal.ofReal (1 - alpha) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0875.d010321 n) :=
    _root_.GD.N0232.N0719.N0875.d010322 hn
  letI : NoAtoms (_root_.GD.N0232.N0719.N0875.d010321 n) := _root_.GD.N0232.N0719.N0875.d010324 hn
  have hlow := _root_.GD.N0232.N0719.N0875.d010327
    (_root_.GD.N0232.N0719.N0875.d010321 n) (p := alpha / 2) (by positivity) (by linarith)
  have hhigh := _root_.GD.N0232.N0719.N0875.d010327
    (_root_.GD.N0232.N0719.N0875.d010321 n) (p := 1 - alpha / 2) (by linarith) (by linarith)
  have hae :
      Set.Ioc (_root_.GD.N0232.N0719.N0875.d010338 n alpha) (_root_.GD.N0232.N0719.N0875.d010339 n alpha) =ᵐ[_root_.GD.N0232.N0719.N0875.d010321 n]
        Set.Icc (_root_.GD.N0232.N0719.N0875.d010338 n alpha) (_root_.GD.N0232.N0719.N0875.d010339 n alpha) :=
    Ioc_ae_eq_Icc
  rw [← measure_congr hae]
  rw [← ProbabilityTheory.measure_cdf (_root_.GD.N0232.N0719.N0875.d010321 n)]
  rw [(ProbabilityTheory.cdf (_root_.GD.N0232.N0719.N0875.d010321 n)).measure_Ioc]
  rw [show ProbabilityTheory.cdf (_root_.GD.N0232.N0719.N0875.d010321 n)
      (_root_.GD.N0232.N0719.N0875.d010338 n alpha) = alpha / 2 by
    simpa [_root_.GD.N0232.N0719.N0875.d010338] using hlow]
  rw [show ProbabilityTheory.cdf (_root_.GD.N0232.N0719.N0875.d010321 n)
      (_root_.GD.N0232.N0719.N0875.d010339 n alpha) = 1 - alpha / 2 by
    simpa [_root_.GD.N0232.N0719.N0875.d010339] using hhigh]
  congr 1
  ring

theorem d010349
    {location y t q : ℝ} (ht : 0 < t) :
    location < y - q * Real.sqrt t ↔
      q < _root_.GD.N0232.N0719.N0875.d010329 location (y, t) := by
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  unfold _root_.GD.N0232.N0719.N0875.d010329
  rw [lt_div_iff₀ hsqrt]
  constructor <;> intro h <;> linarith

theorem d010350
    {location y t q : ℝ} (ht : 0 < t) :
    y - q * Real.sqrt t < location ↔
      _root_.GD.N0232.N0719.N0875.d010329 location (y, t) < q := by
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  unfold _root_.GD.N0232.N0719.N0875.d010329
  rw [div_lt_iff₀ hsqrt]
  constructor <;> intro h <;> linarith

theorem d010351
    {location y t qlow qhigh : ℝ} (ht : 0 < t) :
    (y - qhigh * Real.sqrt t ≤ location ∧
        location ≤ y - qlow * Real.sqrt t) ↔
      _root_.GD.N0232.N0719.N0875.d010329 location (y, t) ∈ Set.Icc qlow qhigh := by
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  unfold _root_.GD.N0232.N0719.N0875.d010329
  simp only [Set.mem_Icc]
  constructor
  · rintro ⟨hl, hu⟩
    constructor
    · rw [le_div_iff₀ hsqrt]
      linarith
    · rw [div_le_iff₀ hsqrt]
      linarith
  · rintro ⟨hl, hu⟩
    constructor
    · rw [div_le_iff₀ hsqrt] at hu
      linarith
    · rw [le_div_iff₀ hsqrt] at hl
      linarith





theorem d010352
    {k : ℕ} (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    ∀ᵐ ω ∂_root_.GD.N0232.N0719.d009176 k sizes location scales,
      ∀ i, 0 < (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω).meanVariance i := by
  let μ := _root_.GD.N0232.N0719.d009176 k sizes location scales
  let μy := _root_.GD.N0232.N0719.N0933.d009300 k sizes location scales
  let μv := _root_.GD.N0232.N0719.N0933.d009301 k sizes scales
  letI : IsProbabilityMeasure μv :=
    _root_.GD.N0232.N0719.N0910.d010289 sizes hsizes scales
  have hmp : MeasurePreserving
      (_root_.GD.N0232.N0719.N0933.d009304 k sizes) μ (μy.prod μv) :=
    ⟨_root_.GD.N0232.N0719.N0933.d009308 k sizes,
      _root_.GD.N0232.N0719.N0933.d009309
        k sizes hsizes location scales⟩
  have hvar : ∀ᵐ z ∂μy.prod μv, ∀ i, 0 < z.2 i :=
    (Measure.quasiMeasurePreserving_snd (μ := μy) (ν := μv)).ae
      (_root_.GD.N0232.N0719.N0910.d010288 hsizes hscales)
  have hpull := hmp.quasiMeasurePreserving.ae hvar
  filter_upwards [hpull] with ω hω
  intro i
  rw [← _root_.GD.N0232.N0719.N0933.d009307 k sizes ω]
  exact hω i


theorem d010353
    {k : ℕ} (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (j : Fin k) {alpha : ℝ} (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (location : ℝ) (scales : Fin k → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0232.N0719.d009176 k sizes location scales
        {ω | location < _root_.GD.N0232.N0719.N0875.d010340 (sizes j) j alpha
          (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)} =
      ENNReal.ofReal (alpha / 2) := by
  let μ := _root_.GD.N0232.N0719.d009176 k sizes location scales
  let f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
    _root_.GD.N0232.N0719.N0875.d010329 location ∘ _root_.GD.N0232.N0719.N0875.d010333 j ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes
  have hf : Measurable f :=
    (_root_.GD.N0232.N0719.N0875.d010330 location).comp
      ((_root_.GD.N0232.N0719.N0875.d010334 j).comp
        (_root_.GD.N0232.N0719.N0900.d009115 k sizes))
  have hmap : μ.map f = _root_.GD.N0232.N0719.N0875.d010321 (sizes j) :=
    _root_.GD.N0232.N0719.N0875.d010337
      sizes hsizes j location scales hscales
  have hpos := _root_.GD.N0232.N0719.N0875.d010352
    sizes hsizes location scales hscales
  calc
    μ {ω | location < _root_.GD.N0232.N0719.N0875.d010340 (sizes j) j alpha
          (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)} =
        μ (f ⁻¹' Set.Ioi (_root_.GD.N0232.N0719.N0875.d010339 (sizes j) alpha)) := by
          apply measure_congr
          filter_upwards [hpos] with ω hω
          apply propext
          change
            (location <
              (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω).mean j -
                _root_.GD.N0232.N0719.N0875.d010339 (sizes j) alpha *
                  Real.sqrt ((_root_.GD.N0232.N0719.N0900.d009104 k sizes ω).meanVariance j)) ↔
              _root_.GD.N0232.N0719.N0875.d010339 (sizes j) alpha <
                _root_.GD.N0232.N0719.N0875.d010329 location
                  (_root_.GD.N0232.N0719.N0875.d010333 j (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω))
          exact _root_.GD.N0232.N0719.N0875.d010349 (hω j)
    _ = (μ.map f) (Set.Ioi (_root_.GD.N0232.N0719.N0875.d010339 (sizes j) alpha)) := by
          rw [Measure.map_apply hf measurableSet_Ioi]
    _ = _root_.GD.N0232.N0719.N0875.d010321 (sizes j)
          (Set.Ioi (_root_.GD.N0232.N0719.N0875.d010339 (sizes j) alpha)) := by rw [hmap]
    _ = ENNReal.ofReal (alpha / 2) :=
      _root_.GD.N0232.N0719.N0875.d010347 (hsizes j) ha0 ha1


theorem d010354
    {k : ℕ} (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (j : Fin k) {alpha : ℝ} (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (location : ℝ) (scales : Fin k → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0232.N0719.d009176 k sizes location scales
        {ω | _root_.GD.N0232.N0719.N0875.d010341 (sizes j) j alpha
          (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω) < location} =
      ENNReal.ofReal (alpha / 2) := by
  let μ := _root_.GD.N0232.N0719.d009176 k sizes location scales
  let f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
    _root_.GD.N0232.N0719.N0875.d010329 location ∘ _root_.GD.N0232.N0719.N0875.d010333 j ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes
  have hf : Measurable f :=
    (_root_.GD.N0232.N0719.N0875.d010330 location).comp
      ((_root_.GD.N0232.N0719.N0875.d010334 j).comp
        (_root_.GD.N0232.N0719.N0900.d009115 k sizes))
  have hmap : μ.map f = _root_.GD.N0232.N0719.N0875.d010321 (sizes j) :=
    _root_.GD.N0232.N0719.N0875.d010337
      sizes hsizes j location scales hscales
  have hpos := _root_.GD.N0232.N0719.N0875.d010352
    sizes hsizes location scales hscales
  calc
    μ {ω | _root_.GD.N0232.N0719.N0875.d010341 (sizes j) j alpha
          (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω) < location} =
        μ (f ⁻¹' Set.Iio (_root_.GD.N0232.N0719.N0875.d010338 (sizes j) alpha)) := by
          apply measure_congr
          filter_upwards [hpos] with ω hω
          apply propext
          change
            ((_root_.GD.N0232.N0719.N0900.d009104 k sizes ω).mean j -
                _root_.GD.N0232.N0719.N0875.d010338 (sizes j) alpha *
                  Real.sqrt ((_root_.GD.N0232.N0719.N0900.d009104 k sizes ω).meanVariance j) <
              location) ↔
                _root_.GD.N0232.N0719.N0875.d010329 location
                  (_root_.GD.N0232.N0719.N0875.d010333 j (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)) <
                  _root_.GD.N0232.N0719.N0875.d010338 (sizes j) alpha
          exact _root_.GD.N0232.N0719.N0875.d010350 (hω j)
    _ = (μ.map f) (Set.Iio (_root_.GD.N0232.N0719.N0875.d010338 (sizes j) alpha)) := by
          rw [Measure.map_apply hf measurableSet_Iio]
    _ = _root_.GD.N0232.N0719.N0875.d010321 (sizes j)
          (Set.Iio (_root_.GD.N0232.N0719.N0875.d010338 (sizes j) alpha)) := by rw [hmap]
    _ = ENNReal.ofReal (alpha / 2) :=
      _root_.GD.N0232.N0719.N0875.d010346 (hsizes j) ha0 ha1



theorem d010355
    {k : ℕ} (sizes : Fin k → ℕ) (hsizes : ∀ i, 2 ≤ sizes i)
    (j : Fin k) {alpha : ℝ} (ha0 : 0 < alpha) (ha1 : alpha < 1)
    (location : ℝ) (scales : Fin k → ℝ)
    (hscales : ∀ i, 0 < scales i) :
    _root_.GD.N0232.N0719.d009176 k sizes location scales
        {ω | _root_.GD.N0232.N0719.N0875.d010340 (sizes j) j alpha (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω) ≤ location ∧
          location ≤ _root_.GD.N0232.N0719.N0875.d010341 (sizes j) j alpha
            (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)} =
      ENNReal.ofReal (1 - alpha) := by
  let μ := _root_.GD.N0232.N0719.d009176 k sizes location scales
  let f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
    _root_.GD.N0232.N0719.N0875.d010329 location ∘ _root_.GD.N0232.N0719.N0875.d010333 j ∘ _root_.GD.N0232.N0719.N0900.d009104 k sizes
  have hf : Measurable f :=
    (_root_.GD.N0232.N0719.N0875.d010330 location).comp
      ((_root_.GD.N0232.N0719.N0875.d010334 j).comp
        (_root_.GD.N0232.N0719.N0900.d009115 k sizes))
  have hmap : μ.map f = _root_.GD.N0232.N0719.N0875.d010321 (sizes j) :=
    _root_.GD.N0232.N0719.N0875.d010337
      sizes hsizes j location scales hscales
  have hpos := _root_.GD.N0232.N0719.N0875.d010352
    sizes hsizes location scales hscales
  calc
    μ {ω | _root_.GD.N0232.N0719.N0875.d010340 (sizes j) j alpha (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω) ≤ location ∧
          location ≤ _root_.GD.N0232.N0719.N0875.d010341 (sizes j) j alpha
            (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)} =
        μ (f ⁻¹' Set.Icc (_root_.GD.N0232.N0719.N0875.d010338 (sizes j) alpha)
          (_root_.GD.N0232.N0719.N0875.d010339 (sizes j) alpha)) := by
          apply measure_congr
          filter_upwards [hpos] with ω hω
          apply propext
          change
            ((_root_.GD.N0232.N0719.N0900.d009104 k sizes ω).mean j -
                _root_.GD.N0232.N0719.N0875.d010339 (sizes j) alpha *
                  Real.sqrt ((_root_.GD.N0232.N0719.N0900.d009104 k sizes ω).meanVariance j) ≤ location ∧
              location ≤ (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω).mean j -
                _root_.GD.N0232.N0719.N0875.d010338 (sizes j) alpha *
                  Real.sqrt ((_root_.GD.N0232.N0719.N0900.d009104 k sizes ω).meanVariance j)) ↔
              _root_.GD.N0232.N0719.N0875.d010329 location
                  (_root_.GD.N0232.N0719.N0875.d010333 j (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)) ∈
                Set.Icc (_root_.GD.N0232.N0719.N0875.d010338 (sizes j) alpha)
                  (_root_.GD.N0232.N0719.N0875.d010339 (sizes j) alpha)
          exact _root_.GD.N0232.N0719.N0875.d010351 (hω j)
    _ = (μ.map f) (Set.Icc (_root_.GD.N0232.N0719.N0875.d010338 (sizes j) alpha)
          (_root_.GD.N0232.N0719.N0875.d010339 (sizes j) alpha)) := by
          rw [Measure.map_apply hf measurableSet_Icc]
    _ = _root_.GD.N0232.N0719.N0875.d010321 (sizes j)
          (Set.Icc (_root_.GD.N0232.N0719.N0875.d010338 (sizes j) alpha)
            (_root_.GD.N0232.N0719.N0875.d010339 (sizes j) alpha)) := by rw [hmap]
    _ = ENNReal.ofReal (1 - alpha) :=
      _root_.GD.N0232.N0719.N0875.d010348 (hsizes j) ha0 ha1



theorem d010356
    {k n : ℕ} (hn : 2 ≤ n) (j : Fin k)
    {alpha₁ alpha₂ : ℝ}
    (ha₁0 : 0 < alpha₁) (ha₂1 : alpha₂ < 1)
    (h12 : alpha₁ ≤ alpha₂) (s : _root_.GD.N0232.N0719.N0900.d009096 k) :
    _root_.GD.N0232.N0719.N0875.d010340 n j alpha₁ s ≤ _root_.GD.N0232.N0719.N0875.d010340 n j alpha₂ s ∧
      _root_.GD.N0232.N0719.N0875.d010341 n j alpha₂ s ≤ _root_.GD.N0232.N0719.N0875.d010341 n j alpha₁ s := by
  have ha₂0 : 0 < alpha₂ := ha₁0.trans_le h12
  have ha₁1 : alpha₁ < 1 := lt_of_le_of_lt h12 ha₂1
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0875.d010321 n) :=
    _root_.GD.N0232.N0719.N0875.d010322 hn
  have hlow : _root_.GD.N0232.N0719.N0875.d010338 n alpha₁ ≤ _root_.GD.N0232.N0719.N0875.d010338 n alpha₂ := by
    unfold _root_.GD.N0232.N0719.N0875.d010338
    apply _root_.GD.N0232.N0719.N0875.d010328 (_root_.GD.N0232.N0719.N0875.d010321 n)
    · positivity
    · linarith
    · linarith
  have hhigh : _root_.GD.N0232.N0719.N0875.d010339 n alpha₂ ≤ _root_.GD.N0232.N0719.N0875.d010339 n alpha₁ := by
    unfold _root_.GD.N0232.N0719.N0875.d010339
    apply _root_.GD.N0232.N0719.N0875.d010328 (_root_.GD.N0232.N0719.N0875.d010321 n)
    · linarith
    · linarith
    · linarith
  unfold _root_.GD.N0232.N0719.N0875.d010340 _root_.GD.N0232.N0719.N0875.d010341
  constructor
  · exact sub_le_sub_left
      (mul_le_mul_of_nonneg_right hhigh (Real.sqrt_nonneg _)) _
  · exact sub_le_sub_left
      (mul_le_mul_of_nonneg_right hlow (Real.sqrt_nonneg _)) _




abbrev d010357 := Set.Ioo (0 : ℝ) 1

theorem d010358
    {n : ℕ} (hn : 2 ≤ n) :
    Monotone (fun a : _root_.GD.N0232.N0719.N0875.d010357 => _root_.GD.N0232.N0719.N0875.d010338 n a.1) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0875.d010321 n) :=
    _root_.GD.N0232.N0719.N0875.d010322 hn
  intro a b hab
  apply _root_.GD.N0232.N0719.N0875.d010328 (_root_.GD.N0232.N0719.N0875.d010321 n)
  · exact div_pos a.2.1 (by norm_num)
  · linarith [b.2.2]
  · exact div_le_div_of_nonneg_right hab (by norm_num)

theorem d010359
    {n : ℕ} (hn : 2 ≤ n) :
    Antitone (fun a : _root_.GD.N0232.N0719.N0875.d010357 => _root_.GD.N0232.N0719.N0875.d010339 n a.1) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0875.d010321 n) :=
    _root_.GD.N0232.N0719.N0875.d010322 hn
  intro a b hab
  apply _root_.GD.N0232.N0719.N0875.d010328 (_root_.GD.N0232.N0719.N0875.d010321 n)
  · linarith [b.2.2]
  · linarith [a.2.1]
  · have habR : (a : ℝ) ≤ (b : ℝ) := hab
    linarith

theorem d010360
    {n : ℕ} (hn : 2 ≤ n) :
    Measurable (fun a : _root_.GD.N0232.N0719.N0875.d010357 => _root_.GD.N0232.N0719.N0875.d010338 n a.1) :=
  (_root_.GD.N0232.N0719.N0875.d010358 hn).measurable

theorem d010361
    {n : ℕ} (hn : 2 ≤ n) :
    Measurable (fun a : _root_.GD.N0232.N0719.N0875.d010357 => _root_.GD.N0232.N0719.N0875.d010339 n a.1) :=
  (_root_.GD.N0232.N0719.N0875.d010359 hn).measurable



theorem d010362
    {k n : ℕ} (hn : 2 ≤ n) (j : Fin k) :
    Measurable (fun z : _root_.GD.N0232.N0719.N0875.d010357 × _root_.GD.N0232.N0719.N0900.d009096 k =>
      _root_.GD.N0232.N0719.N0875.d010340 n j z.1.1 z.2) := by
  unfold _root_.GD.N0232.N0719.N0875.d010340
  exact
    ((_root_.GD.N0232.N0719.N0900.d009099 j).comp measurable_snd).sub
      (((_root_.GD.N0232.N0719.N0875.d010361 hn).comp measurable_fst).mul
        (((_root_.GD.N0232.N0719.N0900.d009100 j).comp measurable_snd).sqrt))



theorem d010363
    {k n : ℕ} (hn : 2 ≤ n) (j : Fin k) :
    Measurable (fun z : _root_.GD.N0232.N0719.N0875.d010357 × _root_.GD.N0232.N0719.N0900.d009096 k =>
      _root_.GD.N0232.N0719.N0875.d010341 n j z.1.1 z.2) := by
  unfold _root_.GD.N0232.N0719.N0875.d010341
  exact
    ((_root_.GD.N0232.N0719.N0900.d009099 j).comp measurable_snd).sub
      (((_root_.GD.N0232.N0719.N0875.d010360 hn).comp measurable_fst).mul
        (((_root_.GD.N0232.N0719.N0900.d009100 j).comp measurable_snd).sqrt))



def d010364 {k : ℕ} (hk : 0 < k) : Fin k :=
  ⟨0, hk⟩





theorem d010365
    (k : ℕ) (sizes : Fin k → ℕ) (hk : 2 ≤ k)
    (hsizes : ∀ i, 2 ≤ sizes i) :
    ∃ j : Fin k,
      Measurable (fun z : _root_.GD.N0232.N0719.N0875.d010357 × _root_.GD.N0232.N0719.N0900.d009096 k =>
        _root_.GD.N0232.N0719.N0875.d010340 (sizes j) j z.1.1 z.2) ∧
      Measurable (fun z : _root_.GD.N0232.N0719.N0875.d010357 × _root_.GD.N0232.N0719.N0900.d009096 k =>
        _root_.GD.N0232.N0719.N0875.d010341 (sizes j) j z.1.1 z.2) ∧
      (∀ a : _root_.GD.N0232.N0719.N0875.d010357, ∀ s,
        _root_.GD.N0232.N0719.N0875.d010340 (sizes j) j a.1 s ≤
          _root_.GD.N0232.N0719.N0875.d010341 (sizes j) j a.1 s) ∧
      (∀ a₁ a₂ : _root_.GD.N0232.N0719.N0875.d010357, a₁ ≤ a₂ → ∀ s,
        _root_.GD.N0232.N0719.N0875.d010340 (sizes j) j a₁.1 s ≤
            _root_.GD.N0232.N0719.N0875.d010340 (sizes j) j a₂.1 s ∧
          _root_.GD.N0232.N0719.N0875.d010341 (sizes j) j a₂.1 s ≤
            _root_.GD.N0232.N0719.N0875.d010341 (sizes j) j a₁.1 s) ∧
      (∀ a : _root_.GD.N0232.N0719.N0875.d010357, ∀ location scales,
        (∀ i, 0 < scales i) →
          _root_.GD.N0232.N0719.d009176 k sizes location scales
              {ω | location < _root_.GD.N0232.N0719.N0875.d010340 (sizes j) j a.1
                (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)} = ENNReal.ofReal (a.1 / 2) ∧
          _root_.GD.N0232.N0719.d009176 k sizes location scales
              {ω | _root_.GD.N0232.N0719.N0875.d010341 (sizes j) j a.1
                (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω) < location} = ENNReal.ofReal (a.1 / 2) ∧
          _root_.GD.N0232.N0719.d009176 k sizes location scales
              {ω | _root_.GD.N0232.N0719.N0875.d010340 (sizes j) j a.1 (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω) ≤ location ∧
                location ≤ _root_.GD.N0232.N0719.N0875.d010341 (sizes j) j a.1
                  (_root_.GD.N0232.N0719.N0900.d009104 k sizes ω)} = ENNReal.ofReal (1 - a.1)) := by
  let j : Fin k := _root_.GD.N0232.N0719.N0875.d010364 (lt_of_lt_of_le (by decide : 0 < 2) hk)
  refine ⟨j,
    _root_.GD.N0232.N0719.N0875.d010362 (hsizes j) j,
    _root_.GD.N0232.N0719.N0875.d010363 (hsizes j) j,
    ?_, ?_, ?_⟩
  · intro a s
    exact _root_.GD.N0232.N0719.N0875.d010345 (hsizes j) j a.2.1 a.2.2 s
  · intro a₁ a₂ h12 s
    exact _root_.GD.N0232.N0719.N0875.d010356 (hsizes j) j a₁.2.1 a₂.2.2 h12 s
  · intro a location scales hscales
    exact ⟨
      _root_.GD.N0232.N0719.N0875.d010353 sizes hsizes j a.2.1 a.2.2 location scales hscales,
      _root_.GD.N0232.N0719.N0875.d010354 sizes hsizes j a.2.1 a.2.2 location scales hscales,
      _root_.GD.N0232.N0719.N0875.d010355 sizes hsizes j a.2.1 a.2.2 location scales hscales⟩

#print axioms _root_.GD.N0232.N0719.N0875.d010323
#print axioms _root_.GD.N0232.N0719.N0875.d010327
#print axioms _root_.GD.N0232.N0719.N0875.d010337
#print axioms _root_.GD.N0232.N0719.N0875.d010353
#print axioms _root_.GD.N0232.N0719.N0875.d010354
#print axioms _root_.GD.N0232.N0719.N0875.d010355
#print axioms _root_.GD.N0232.N0719.N0875.d010356
#print axioms _root_.GD.N0232.N0719.N0875.d010362
#print axioms _root_.GD.N0232.N0719.N0875.d010363
#print axioms _root_.GD.N0232.N0719.N0875.d010365

end

end GD.N0232.N0719.N0875
