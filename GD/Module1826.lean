import GD.Module1825

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace GD.N0236.N0745

variable {S Θ : Type*} [MeasurableSpace S]

def d030178 (μ : Θ → Measure S) (δ : Θ → ℝ) : Prop :=
  ∃ L U : ℝ × S → ℝ,
    Measurable L ∧ Measurable U ∧
    _root_.GD.N0236.N0745.d030147 (_root_.GD.N0236.N0745.d030167 L U) ∧
    (∀ a ∈ Ioo (0 : ℝ) 1, ∀ s, L (a,s) ≤ U (a,s)) ∧
    ∀ θ a, a ∈ Ioo (0 : ℝ) 1 →
      (μ θ).real {s | δ θ ∈ Icc (L (a,s)) (U (a,s))} = 1-a

def d030179 (μ : Θ → Measure S) (δ : Θ → ℝ) : Prop :=
  ∃ P : S × ℝ → ℝ, ∃ L U : ℝ × S → ℝ,
    Measurable P ∧ Measurable L ∧ Measurable U ∧
    (∀ x, P x ∈ Icc (0 : ℝ) 1) ∧
    (∀ a ∈ Ioo (0 : ℝ) 1, ∀ s, L (a,s) ≤ U (a,s)) ∧
    (∀ a ∈ Ioo (0 : ℝ) 1, ∀ s d,
      a ≤ P (s,d) ↔ d ∈ Icc (L (a,s)) (U (a,s))) ∧
    ∀ θ, (μ θ).map (fun s => P (s,δ θ)) = volume.restrict (Icc (0 : ℝ) 1)

theorem d030180
    (μ : Θ → Measure S) (δ : Θ → ℝ) [∀ θ, IsProbabilityMeasure (μ θ)]
    (h : _root_.GD.N0236.N0745.d030178 μ δ) : _root_.GD.N0236.N0745.d030179 μ δ := by
  obtain ⟨L,U,hL,hU,hnest,horder,hcal⟩ := h
  obtain ⟨P,L',U',hP,hL',hU',hrange,horder',hinv,hlaw⟩ :=
    _root_.GD.N0236.N0745.d030177 hL hU hnest horder
  refine ⟨P,L',U',hP,hL',hU',hrange,horder',hinv,?_⟩
  intro θ
  let f : S → S × ℝ := fun s => (s,δ θ)
  have hf : Measurable f := measurable_id.prodMk measurable_const
  have hprob : IsProbabilityMeasure ((μ θ).map f) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  have hcal' : ∀ a ∈ Ioo (0 : ℝ) 1,
      ((μ θ).map f).real (_root_.GD.N0236.N0745.d030167 L U a) = 1-a := by
    intro a ha
    rw [measureReal_def, Measure.map_apply hf (_root_.GD.N0236.N0745.d030172 hL hU a)]
    exact hcal θ a ha
  have hr := hlaw ((μ θ).map f) hprob hcal'
  rwa [Measure.map_map hP hf] at hr

theorem d030181 (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) :
    (volume.restrict (Icc (0 : ℝ) 1)) (Ici a) = ENNReal.ofReal (1-a) := by
  rw [Measure.restrict_apply measurableSet_Ici]
  have hs : Ici a ∩ Icc (0 : ℝ) 1 = Icc a 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    exact ⟨fun h => ⟨h.1,h.2.2⟩, fun h => ⟨h.1,ha.1.le.trans h.1,h.2⟩⟩
  rw [hs, Real.volume_Icc]

theorem d030182
    (μ : Θ → Measure S) (δ : Θ → ℝ)
    (h : _root_.GD.N0236.N0745.d030179 μ δ) : _root_.GD.N0236.N0745.d030178 μ δ := by
  obtain ⟨P,L,U,hP,hL,hU,_hrange,horder,hinv,hlaw⟩ := h
  refine ⟨L,U,hL,hU,?_,horder,?_⟩
  · intro a ha b hb hab x hx
    exact (hinv a ha x.1 x.2).mp (hab.trans ((hinv b hb x.1 x.2).mpr hx))
  · intro θ a ha
    have hf : Measurable (fun s => P (s,δ θ)) :=
      hP.comp (measurable_id.prodMk measurable_const)
    have hs : {s | δ θ ∈ Icc (L (a,s)) (U (a,s))} =
        (fun s => P (s,δ θ)) ⁻¹' Ici a := by
      ext s
      exact (hinv a ha s (δ θ)).symm
    rw [measureReal_def, hs, ← Measure.map_apply hf measurableSet_Ici,
      hlaw θ, _root_.GD.N0236.N0745.d030181 a ha, ENNReal.toReal_ofReal (by linarith [ha.2])]

theorem d030183
    (μ : Θ → Measure S) (δ : Θ → ℝ) [∀ θ, IsProbabilityMeasure (μ θ)] :
    _root_.GD.N0236.N0745.d030178 μ δ ↔ _root_.GD.N0236.N0745.d030179 μ δ :=
  ⟨_root_.GD.N0236.N0745.d030180 μ δ,
    _root_.GD.N0236.N0745.d030182 μ δ⟩

#print axioms _root_.GD.N0236.N0745.d030180
#print axioms _root_.GD.N0236.N0745.d030182
#print axioms _root_.GD.N0236.N0745.d030183

end GD.N0236.N0745
