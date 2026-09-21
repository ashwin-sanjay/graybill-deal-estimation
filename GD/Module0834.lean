import GD.Module0833









open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0107

noncomputable section

open _root_.GD.N0137

variable {A B C D : Type*}
  [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D]


theorem d012741
    {P : Measure A} [IsProbabilityMeasure P]
    {Q : Measure B} [IsProbabilityMeasure Q]
    {S : A → B} {f : B → C} {g : B → D}
    (hS : Measurable S) (hf : Measurable f) (hg : Measurable g)
    (hmap : P.map S = Q)
    (hfg : IndepFun f g Q) :
    IndepFun (f ∘ S) (g ∘ S) P := by
  have hfcomp : P.map (f ∘ S) = (P.map S).map f := by
    rw [Measure.map_map]
    · exact hf
    · exact hS
  have hgcomp : P.map (g ∘ S) = (P.map S).map g := by
    rw [Measure.map_map]
    · exact hg
    · exact hS
  rw [indepFun_iff_map_prod_eq_prod_map_map
    (hf.comp hS).aemeasurable (hg.comp hS).aemeasurable]
  calc
    P.map (fun x => ((f ∘ S) x, (g ∘ S) x)) =
        (P.map S).map (fun y => (f y, g y)) := by
      rw [Measure.map_map]
      · rfl
      · exact hf.prodMk hg
      · exact hS
    _ = Q.map (fun y => (f y, g y)) := by rw [hmap]
    _ = (Q.map f).prod (Q.map g) :=
      hfg.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable
    _ = ((P.map S).map f).prod ((P.map S).map g) := by rw [hmap]
    _ = (P.map (f ∘ S)).prod (P.map (g ∘ S)) := by
      rw [hfcomp, hgcomp]


theorem d012742
    {P : Measure A} {Q : Measure B}
    {S : A → B} {f : B → ℝ}
    (hS : Measurable S) (hf : Measurable f)
    (hmap : P.map S = Q) :
    (∫ x, f (S x) ∂P) = ∫ y, f y ∂Q := by
  rw [← integral_map hS.aemeasurable hf.aestronglyMeasurable, hmap]


theorem d012743
    {P : Measure A} {Q : Measure B}
    {S : A → B} {f : B → ℝ} {p : ℝ≥0∞}
    (hS : Measurable S) (hf : Measurable f)
    (hmap : P.map S = Q)
    (hLp : MemLp f p Q) :
    MemLp (f ∘ S) p P := by
  apply (memLp_map_measure_iff
    hf.aestronglyMeasurable hS.aemeasurable).mp
  rw [hmap]
  exact hLp


theorem d012744
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e Sigma : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    MemLp (_root_.GD.N0137.d008945 m n e Sigma) 2 (_root_.GD.N0137.d008914 m n) := by
  have hLaw : HasLaw (_root_.GD.N0137.d008931 m n e)
      (gaussianReal 0 1) (_root_.GD.N0137.d008914 m n) := ⟨
    (_root_.GD.N0137.d008936 m n e).aemeasurable,
    _root_.GD.N0137.d008939 m n hm hn he0 he1⟩
  have hOracle : MemLp (_root_.GD.N0137.d008931 m n e) 2 (_root_.GD.N0137.d008914 m n) :=
    hLaw.hasGaussianLaw.memLp_two
  change MemLp
    (fun ω => Real.sqrt (Sigma * e * (1 - e)) *
      _root_.GD.N0137.d008931 m n e ω) 2 (_root_.GD.N0137.d008914 m n)
  exact hOracle.const_mul _



theorem d012745
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (μ σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ) :
    IndepFun
      (_root_.GD.N0107.d012732 m n μ (_root_.GD.N0107.d009046 m n σ τ))
      (fun ω =>
        (_root_.GD.N0107.d009038 m n μ σ τ
            (_root_.GD.N0107.d009046 m n σ τ)
            (_root_.GD.N0107.d009045 m n σ τ) ω,
          (_root_.GD.N0107.d009039 m n μ σ τ
              (_root_.GD.N0107.d009046 m n σ τ) ω,
            _root_.GD.N0107.d009040 m n μ σ τ
              (_root_.GD.N0107.d009046 m n σ τ) ω)))
      (_root_.GD.N0107.d009030 m n μ σ τ) := by
  let e := _root_.GD.N0107.d009046 m n σ τ
  let Sigma := _root_.GD.N0107.d009045 m n σ τ
  have he0 : 0 ≤ e :=
    (_root_.GD.N0107.d009050 (by omega) (by omega) hσ hτ).le
  have he1 : e ≤ 1 :=
    (_root_.GD.N0107.d009051 (by omega) (by omega) hσ hτ).le
  have hbase :=
    _root_.GD.N0137.d008947 m n hm hn
      (Sigma := Sigma) he0 he1
  have hpull :=
    _root_.GD.N0107.d012741
      (P := _root_.GD.N0107.d009030 m n μ σ τ)
      (Q := _root_.GD.N0137.d008914 m n)
      (S := _root_.GD.N0107.d009025 m n μ σ τ)
      (f := _root_.GD.N0137.d008945 m n e Sigma)
      (g := fun ω =>
        (_root_.GD.N0137.d008942 m n e Sigma ω,
          (_root_.GD.N0137.d008943 m n e ω, _root_.GD.N0137.d008944 m n e ω)))
      (_root_.GD.N0107.d009027 m n μ σ τ)
      (by
        unfold _root_.GD.N0137.d008945
        exact measurable_const.mul (_root_.GD.N0137.d008936 m n e))
      (_root_.GD.N0137.d008946 m n e Sigma)
      (_root_.GD.N0107.d009031
        m n μ σ τ hσ.ne' hτ.ne')
      hbase
  have hdl :
      ((fun z =>
        (_root_.GD.N0137.d008942 m n e Sigma z,
          (_root_.GD.N0137.d008943 m n e z, _root_.GD.N0137.d008944 m n e z))) ∘
          _root_.GD.N0107.d009025 m n μ σ τ) =
        (fun ω =>
          (_root_.GD.N0137.d008942 m n e Sigma
              (_root_.GD.N0107.d009025 m n μ σ τ ω),
            (_root_.GD.N0137.d008943 m n e
                (_root_.GD.N0107.d009025 m n μ σ τ ω),
              _root_.GD.N0137.d008944 m n e
                (_root_.GD.N0107.d009025 m n μ σ τ ω)))) := by
    rfl
  rw [hdl] at hpull
  have horacle :
      _root_.GD.N0107.d012738 m n μ σ τ e Sigma =
        _root_.GD.N0107.d012732 m n μ e := by
    funext ω
    exact _root_.GD.N0107.d012740
      m n hm hn μ σ τ hσ hτ ω
  rw [← horacle]
  simpa [_root_.GD.N0107.d012738, _root_.GD.N0107.d009038,
    _root_.GD.N0107.d009039, _root_.GD.N0107.d009040, Function.comp_apply,
    e, Sigma] using hpull


theorem d012746
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (μ σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ) :
    ∫ ω, _root_.GD.N0107.d012732 m n μ
        (_root_.GD.N0107.d009046 m n σ τ) ω
      ∂_root_.GD.N0107.d009030 m n μ σ τ = 0 := by
  let e := _root_.GD.N0107.d009046 m n σ τ
  let Sigma := _root_.GD.N0107.d009045 m n σ τ
  have he0 : 0 ≤ e :=
    (_root_.GD.N0107.d009050 (by omega) (by omega) hσ hτ).le
  have he1 : e ≤ 1 :=
    (_root_.GD.N0107.d009051 (by omega) (by omega) hσ hτ).le
  have htransport :=
    _root_.GD.N0107.d012742
      (P := _root_.GD.N0107.d009030 m n μ σ τ)
      (Q := _root_.GD.N0137.d008914 m n)
      (S := _root_.GD.N0107.d009025 m n μ σ τ)
      (f := _root_.GD.N0137.d008945 m n e Sigma)
      (_root_.GD.N0107.d009027 m n μ σ τ)
      (by
        unfold _root_.GD.N0137.d008945
        exact measurable_const.mul (_root_.GD.N0137.d008936 m n e))
      (_root_.GD.N0107.d009031
        m n μ σ τ hσ.ne' hτ.ne')
  rw [_root_.GD.N0137.d008948 m n hm hn he0 he1] at htransport
  have horacle :
      _root_.GD.N0107.d012738 m n μ σ τ e Sigma =
        _root_.GD.N0107.d012732 m n μ e := by
    funext ω
    exact _root_.GD.N0107.d012740
      m n hm hn μ σ τ hσ hτ ω
  rw [← horacle]
  simpa [_root_.GD.N0107.d012738, e, Sigma] using htransport


theorem d012747
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (μ σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ) :
    MemLp
      (_root_.GD.N0107.d012732 m n μ (_root_.GD.N0107.d009046 m n σ τ))
      2 (_root_.GD.N0107.d009030 m n μ σ τ) := by
  let e := _root_.GD.N0107.d009046 m n σ τ
  let Sigma := _root_.GD.N0107.d009045 m n σ τ
  have he0 : 0 ≤ e :=
    (_root_.GD.N0107.d009050 (by omega) (by omega) hσ hτ).le
  have he1 : e ≤ 1 :=
    (_root_.GD.N0107.d009051 (by omega) (by omega) hσ hτ).le
  have hpull :=
    _root_.GD.N0107.d012743
      (P := _root_.GD.N0107.d009030 m n μ σ τ)
      (Q := _root_.GD.N0137.d008914 m n)
      (S := _root_.GD.N0107.d009025 m n μ σ τ)
      (f := _root_.GD.N0137.d008945 m n e Sigma)
      (p := 2)
      (_root_.GD.N0107.d009027 m n μ σ τ)
      (by
        unfold _root_.GD.N0137.d008945
        exact measurable_const.mul (_root_.GD.N0137.d008936 m n e))
      (_root_.GD.N0107.d009031
        m n μ σ τ hσ.ne' hτ.ne')
      (_root_.GD.N0107.d012744 m n hm hn he0 he1)
  have horacle :
      _root_.GD.N0107.d012738 m n μ σ τ e Sigma =
        _root_.GD.N0107.d012732 m n μ e := by
    funext ω
    exact _root_.GD.N0107.d012740
      m n hm hn μ σ τ hσ hτ ω
  rw [← horacle]
  simpa [_root_.GD.N0107.d012738, e, Sigma] using hpull

end

end GD.N0107
