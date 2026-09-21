import GD.Module0410

open MeasureTheory ProbabilityTheory Real Set
open Filter
open scoped ENNReal NNReal ProbabilityTheory BigOperators Topology

namespace GD.N0114

noncomputable section






theorem d006372
    {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {X : Ω → ℝ} {Y : Ω' → ℝ} {ε : ℝ}
    (hε : 0 < ε)
    (hX : Measurable X) (hY : Measurable Y)
    (hXint : Ioo (-ε) ε ⊆ integrableExpSet X μ)
    (hYint : Ioo (-ε) ε ⊆ integrableExpSet Y ν)
    (hmgf : Set.EqOn (mgf X μ) (mgf Y ν) (Ioo (-ε) ε)) :
    μ.map X = ν.map Y := by
  let U : Set ℂ := {z | z.re ∈ Ioo (-ε) ε}
  have hXinterior :
      Ioo (-ε) ε ⊆ interior (integrableExpSet X μ) := by
    exact interior_maximal hXint isOpen_Ioo
  have hYinterior :
      Ioo (-ε) ε ⊆ interior (integrableExpSet Y ν) := by
    exact interior_maximal hYint isOpen_Ioo
  have hXa : AnalyticOnNhd ℂ (complexMGF X μ) U := by
    exact analyticOnNhd_complexMGF.mono fun z hz ↦
      hXinterior hz
  have hYa : AnalyticOnNhd ℂ (complexMGF Y ν) U := by
    exact analyticOnNhd_complexMGF.mono fun z hz ↦
      hYinterior hz
  have hzero : (0 : ℂ) ∈ U := by
    simp [U, hε]
  have hfreq :
      ∃ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
        complexMGF X μ z = complexMGF Y ν z := by
    rw [frequently_iff_seq_forall]
    let xs : ℕ → ℝ := fun n ↦ ε / (2 * (n + 1 : ℝ))
    refine ⟨fun n ↦ (xs n : ℂ), ?_, fun n ↦ ?_⟩
    · rw [tendsto_nhdsWithin_iff]
      constructor
      · have hbase :
            Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        apply (Complex.continuous_ofReal.tendsto 0).comp
        convert
          ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ε / 2)
            atTop (𝓝 (ε / 2))).mul hbase) using 1 <;>
          simp [xs, div_eq_mul_inv] <;> ring
      · exact Eventually.of_forall fun n ↦ by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          exact Complex.ofReal_ne_zero.mpr
            (div_ne_zero hε.ne' (by positivity))
    · have hxs_pos : 0 < xs n := by
        dsimp [xs]
        positivity
      have hxs_lt : xs n < ε := by
        dsimp [xs]
        have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
          exact le_add_of_nonneg_left (Nat.cast_nonneg n)
        have hden : 1 < 2 * (n + 1 : ℝ) := by nlinarith
        exact (div_lt_iff₀ (by positivity)).2 (by
          nlinarith)
      simpa [complexMGF_ofReal] using
        hmgf ⟨by linarith, hxs_lt⟩
  have heq : Set.EqOn (complexMGF X μ) (complexMGF Y ν) U := by
    exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
      hXa hYa ((convex_Ioo (-ε) ε).linear_preimage
        Complex.reLm).isPreconnected
      hzero hfreq
  apply Measure.ext_of_charFun
  funext t
  have hit : ((t : ℂ) * Complex.I).re ∈ Ioo (-ε) ε := by
    simp [hε]
  have hz := heq hit
  rw [complexMGF_mul_I hX.aemeasurable t,
    complexMGF_mul_I hY.aemeasurable t] at hz
  exact hz


def d006373 (μ ν : Measure ℝ) : Measure ℝ :=
  (μ.prod ν).map (fun p : ℝ × ℝ ↦ p.1 + p.2)




theorem d006374 {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (t : ℝ) :
    mgf id (_root_.GD.N0114.d006373 μ ν) t = mgf id μ t * mgf id ν t := by
  rw [_root_.GD.N0114.d006373, mgf_id_map (by fun_prop)]
  have hind :
      (fun p : ℝ × ℝ ↦ p.1) ⟂ᵢ[μ.prod ν]
        (fun p : ℝ × ℝ ↦ p.2) :=
    indepFun_prod (X := id) (Y := id) measurable_id measurable_id
  change mgf ((fun p : ℝ × ℝ ↦ p.1) + fun p : ℝ × ℝ ↦ p.2)
    (μ.prod ν) t = _
  rw [hind.mgf_add']
  · rw [← mgf_id_map (μ := μ.prod ν) (X := fun p : ℝ × ℝ ↦ p.1)
      (by fun_prop), measurePreserving_fst.map_eq]
    rw [← mgf_id_map (μ := μ.prod ν) (X := fun p : ℝ × ℝ ↦ p.2)
      (by fun_prop), measurePreserving_snd.map_eq]
  · fun_prop
  · fun_prop



theorem d006375 {a b r t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (ht : t < r) :
    mgf id (_root_.GD.N0114.d006373 (gammaMeasure a r) (gammaMeasure b r)) t =
      (r / (r - t)) ^ (a + b) := by
  letI : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  letI : IsProbabilityMeasure (gammaMeasure b r) :=
    isProbabilityMeasure_gammaMeasure hb hr
  rw [_root_.GD.N0114.d006374,
    _root_.GD.N0121.d006347 ha hr ht,
    _root_.GD.N0121.d006347 hb hr ht]
  have hbase : 0 < r / (r - t) := by positivity
  rw [← Real.rpow_add hbase]


theorem d006376 {a b r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    _root_.GD.N0114.d006373 (gammaMeasure a r) (gammaMeasure b r) =
      gammaMeasure (a + b) r := by
  letI : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  letI : IsProbabilityMeasure (gammaMeasure b r) :=
    isProbabilityMeasure_gammaMeasure hb hr
  letI : IsProbabilityMeasure (gammaMeasure (a + b) r) :=
    isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  letI : IsProbabilityMeasure
      ((gammaMeasure a r).prod (gammaMeasure b r)) := inferInstance
  have hsource :
      Ioo (-(r / 2)) (r / 2) ⊆
        integrableExpSet
          (fun p : ℝ × ℝ ↦ p.1 + p.2)
          ((gammaMeasure a r).prod (gammaMeasure b r)) := by
    intro t ht
    rcases ht with ⟨htl, htu⟩
    have htr : t < r := by linarith
    have h1 : Integrable (fun x : ℝ ↦ Real.exp (t * x))
        (gammaMeasure a r) := by
      exact (mgf_pos_iff.mp (by
        change 0 < mgf id (gammaMeasure a r) t
        rw [_root_.GD.N0121.d006347 ha hr htr]
        positivity))
    have h2 : Integrable (fun x : ℝ ↦ Real.exp (t * x))
        (gammaMeasure b r) := by
      exact (mgf_pos_iff.mp (by
        change 0 < mgf id (gammaMeasure b r) t
        rw [_root_.GD.N0121.d006347 hb hr htr]
        positivity))
    exact IndepFun.integrable_exp_mul_add
      (indepFun_prod (X := id) (Y := id) measurable_id measurable_id)
        (h1.comp_fst (gammaMeasure b r))
        (h2.comp_snd (gammaMeasure a r))
  have htarget :
      Ioo (-(r / 2)) (r / 2) ⊆
        integrableExpSet id (gammaMeasure (a + b) r) := by
    intro t ht
    rcases ht with ⟨htl, htu⟩
    have htr : t < r := by linarith
    exact mgf_pos_iff.mp (by
      change 0 < mgf id (gammaMeasure (a + b) r) t
      rw [_root_.GD.N0121.d006347
        (add_pos ha hb) hr htr]
      positivity)
  have hlocal :
      Set.EqOn
        (mgf (fun p : ℝ × ℝ ↦ p.1 + p.2)
          ((gammaMeasure a r).prod (gammaMeasure b r)))
        (mgf id (gammaMeasure (a + b) r))
        (Ioo (-(r / 2)) (r / 2)) := by
    intro t ht
    rcases ht with ⟨htl, htu⟩
    have htr : t < r := by linarith
    change mgf ((fun p : ℝ × ℝ ↦ p.1) + fun p : ℝ × ℝ ↦ p.2)
      ((gammaMeasure a r).prod (gammaMeasure b r)) t = _
    have hind :
        (fun p : ℝ × ℝ ↦ p.1) ⟂ᵢ[
          (gammaMeasure a r).prod (gammaMeasure b r)]
          (fun p : ℝ × ℝ ↦ p.2) :=
      indepFun_prod (X := id) (Y := id) measurable_id measurable_id
    rw [hind.mgf_add']
    · rw [← mgf_id_map
          (μ := (gammaMeasure a r).prod (gammaMeasure b r))
          (X := fun p : ℝ × ℝ ↦ p.1) (by fun_prop),
        measurePreserving_fst.map_eq,
        ← mgf_id_map
          (μ := (gammaMeasure a r).prod (gammaMeasure b r))
          (X := fun p : ℝ × ℝ ↦ p.2) (by fun_prop),
        measurePreserving_snd.map_eq,
        _root_.GD.N0121.d006347 ha hr htr,
        _root_.GD.N0121.d006347 hb hr htr,
        _root_.GD.N0121.d006347
          (add_pos ha hb) hr htr]
      exact (Real.rpow_add (by positivity) a b).symm
    · fun_prop
    · fun_prop
  have hmap := _root_.GD.N0114.d006372
    (μ := (gammaMeasure a r).prod (gammaMeasure b r))
    (ν := gammaMeasure (a + b) r)
    (X := fun p : ℝ × ℝ ↦ p.1 + p.2) (Y := id)
    (ε := r / 2) (by positivity)
    (by fun_prop) measurable_id hsource htarget hlocal
  simpa [_root_.GD.N0114.d006373] using hmap


theorem d006377 (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    _root_.GD.N0114.d006373 (_root_.GD.N0121.d006346 d)
        (_root_.GD.N0121.d006346 e) =
      _root_.GD.N0121.d006346 (d + e) := by
  unfold _root_.GD.N0121.d006346
  convert _root_.GD.N0114.d006376
    (a := (d : ℝ) / 2) (b := (e : ℝ) / 2) (r := 1 / 2)
    (by positivity) (by positivity) (by positivity) using 1
  norm_num
  push_cast
  ring



theorem d006378
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ} {d e : ℕ}
    (hX : Measurable X) (hY : Measurable Y) (hXY : X ⟂ᵢ[μ] Y)
    (hd : 0 < d) (he : 0 < e)
    (hXlaw : μ.map X = _root_.GD.N0121.d006346 d)
    (hYlaw : μ.map Y = _root_.GD.N0121.d006346 e) :
    μ.map (fun ω ↦ X ω + Y ω) =
      _root_.GD.N0121.d006346 (d + e) := by
  have hjoint :
      μ.map (fun ω ↦ (X ω, Y ω)) = (μ.map X).prod (μ.map Y) :=
    (indepFun_iff_map_prod_eq_prod_map_map
      hX.aemeasurable hY.aemeasurable).mp hXY
  calc
    μ.map (fun ω ↦ X ω + Y ω) =
        (μ.map (fun ω ↦ (X ω, Y ω))).map
          (fun p : ℝ × ℝ ↦ p.1 + p.2) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
    _ = ((μ.map X).prod (μ.map Y)).map
          (fun p : ℝ × ℝ ↦ p.1 + p.2) := by rw [hjoint]
    _ = _root_.GD.N0114.d006373 (_root_.GD.N0121.d006346 d)
          (_root_.GD.N0121.d006346 e) := by
            rw [hXlaw, hYlaw]
            rfl
    _ = _root_.GD.N0121.d006346 (d + e) :=
      _root_.GD.N0114.d006377 d e hd he





theorem d006379 :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (fun p : ℝ × ℝ ↦ p.1 ^ 2 + p.2 ^ 2) =
      _root_.GD.N0121.d006346 2 := by
  let μ := (gaussianReal 0 1).prod (gaussianReal 0 1)
  let X : ℝ × ℝ → ℝ := fun p ↦ p.1 ^ 2
  let Y : ℝ × ℝ → ℝ := fun p ↦ p.2 ^ 2
  have hXlaw :
      μ.map X = _root_.GD.N0121.d006346 1 := by
    calc
      μ.map X =
          ((μ.map Prod.fst).map fun z : ℝ ↦ z ^ 2) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
      _ = (gaussianReal 0 1).map (fun z : ℝ ↦ z ^ 2) := by
            rw [measurePreserving_fst.map_eq]
      _ = _root_.GD.N0121.d006346 1 :=
        _root_.GD.N0121.d006355
  have hYlaw :
      μ.map Y = _root_.GD.N0121.d006346 1 := by
    calc
      μ.map Y =
          ((μ.map Prod.snd).map fun z : ℝ ↦ z ^ 2) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
      _ = (gaussianReal 0 1).map (fun z : ℝ ↦ z ^ 2) := by
            rw [measurePreserving_snd.map_eq]
      _ = _root_.GD.N0121.d006346 1 :=
        _root_.GD.N0121.d006355
  exact _root_.GD.N0114.d006378
    (μ := μ) (X := X) (Y := Y) (d := 1) (e := 1)
    (by fun_prop) (by fun_prop)
    (indepFun_prod (X := fun z : ℝ ↦ z ^ 2)
      (Y := fun z : ℝ ↦ z ^ 2) (by fun_prop) (by fun_prop))
    (by norm_num) (by norm_num) hXlaw hYlaw

end

end GD.N0114
