import GD.Module0756
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Sequences
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity














set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Filter Set
open scoped Topology

namespace GD.N0213.N0497

noncomputable section

variable {K : Type*} [MetricSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

def d022004 (β : ℝ) (p : (ℝ × K)) : ℝ :=
  Real.exp (β * p.1 ^ 2)

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] in
theorem d022005 (β : ℝ) : Continuous (_root_.GD.N0213.N0497.d022004 (K := K) β) := by
  unfold _root_.GD.N0213.N0497.d022004
  fun_prop

omit [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] in
theorem d022006 (β : ℝ) (p : (ℝ × K)) :
    0 < _root_.GD.N0213.N0497.d022004 β p := Real.exp_pos _

def d022007 (ν : ℕ → ProbabilityMeasure (ℝ × K))
    (β B : ℝ) : Prop :=
  ∀ n, Integrable (_root_.GD.N0213.N0497.d022004 β) (ν n : Measure (ℝ × K)) ∧
    (∫ p, _root_.GD.N0213.N0497.d022004 β p ∂(ν n : Measure (ℝ × K))) ≤ B

omit [CompactSpace K] in
theorem d022008 {μ : ProbabilityMeasure (ℝ × K)}
    {β B : ℝ} (hβ : 0 < β)
    (hi : Integrable (_root_.GD.N0213.N0497.d022004 β) (μ : Measure (ℝ × K)))
    (hB : (∫ p, _root_.GD.N0213.N0497.d022004 β p ∂(μ : Measure (ℝ × K))) ≤ B) :
    Integrable (fun p : (ℝ × K) ↦ p.1 ^ 2) (μ : Measure (ℝ × K)) ∧
      (∫ p, p.1 ^ 2 ∂(μ : Measure (ℝ × K))) ≤ B / β := by
  have hb (p : (ℝ × K)) : p.1 ^ 2 ≤ _root_.GD.N0213.N0497.d022004 β p / β := by
    apply (le_div_iff₀ hβ).2
    have he := Real.add_one_le_exp (β * p.1 ^ 2)
    dsimp [_root_.GD.N0213.N0497.d022004]
    nlinarith
  have hisq : Integrable (fun p : (ℝ × K) ↦ p.1 ^ 2)
      (μ : Measure (ℝ × K)) :=
    (hi.div_const β).mono_nonneg (by fun_prop)
      (Eventually.of_forall fun p ↦ sq_nonneg p.1) (Eventually.of_forall hb)
  refine ⟨hisq, ?_⟩
  calc
    (∫ p, p.1 ^ 2 ∂(μ : Measure (ℝ × K)))
      ≤ ∫ p, _root_.GD.N0213.N0497.d022004 β p / β ∂(μ : Measure (ℝ × K)) :=
        integral_mono hisq (hi.div_const β) hb
    _ = (∫ p, _root_.GD.N0213.N0497.d022004 β p ∂(μ : Measure (ℝ × K))) / β :=
      integral_div β _
    _ ≤ B / β := div_le_div_of_nonneg_right hB hβ.le

omit [BorelSpace K] [SecondCountableTopology K] in


theorem d022009 (ν : ℕ → ProbabilityMeasure (ℝ × K))
    {C : ℝ} (hC : 0 ≤ C)
    (hi : ∀ n, Integrable (fun p : (ℝ × K) ↦ p.1 ^ 2)
      (ν n : Measure (ℝ × K)))
    (hb : ∀ n, (∫ p, p.1 ^ 2 ∂(ν n : Measure (ℝ × K))) ≤ C) :
    IsTightMeasureSet {μ : Measure (ℝ × K) | ∃ n, μ = (ν n : Measure (ℝ × K))} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases htop : ε = ⊤
  · exact ⟨∅, isCompact_empty, by simp [htop]⟩
  have hη : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  let R : ℝ := C / ε.toReal + 1
  have hdiv : 0 ≤ C / ε.toReal := div_nonneg hC hη.le
  have hR : 0 < R := by dsimp [R]; linarith
  have hCR : C ≤ R ^ 2 * ε.toReal := by
    apply (div_le_iff₀ hη).1
    dsimp [R]
    nlinarith [sq_nonneg (C / ε.toReal)]
  let rectangle : Set (ℝ × K) := Icc (-R) R ×ˢ univ
  refine ⟨rectangle, isCompact_Icc.prod isCompact_univ, ?_⟩
  rintro μ ⟨n, rfl⟩
  have hsub : rectangleᶜ ⊆ {p : (ℝ × K) | R ^ 2 ≤ p.1 ^ 2} := by
    intro p hp
    have hp' : p.1 < -R ∨ R < p.1 := by
      simpa only [rectangle, mem_compl_iff, mem_prod, mem_Icc, mem_univ, and_true,
        not_and_or, not_le] using hp
    change R ^ 2 ≤ p.1 ^ 2
    apply sq_le_sq.2
    rw [abs_of_pos hR]
    rcases hp' with hp' | hp'
    · exact (show R ≤ -p.1 by linarith).trans (neg_le_abs _)
    · exact hp'.le.trans (le_abs_self _)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := (ν n : Measure (ℝ × K)))
    (Eventually.of_forall fun p : (ℝ × K) ↦ sq_nonneg p.1) (hi n) (R ^ 2)
  have hm : (ν n : Measure (ℝ × K)).real rectangleᶜ ≤ ε.toReal := by
    have hmono := measureReal_mono (μ := (ν n : Measure (ℝ × K))) hsub
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hR)).1
    exact (mul_le_mul_of_nonneg_left hmono (sq_nonneg R)).trans
      (hmark.trans ((hb n).trans hCR))
  rw [← ofReal_measureReal]
  exact (ENNReal.ofReal_le_ofReal hm).trans (le_of_eq (ENNReal.ofReal_toReal htop))

theorem d022010
    (ν : ℕ → ProbabilityMeasure (ℝ × K)) {β B : ℝ}
    (hβ : 0 < β) (h : _root_.GD.N0213.N0497.d022007 ν β B) :
    IsTightMeasureSet {μ : Measure (ℝ × K) | ∃ n, μ = (ν n : Measure (ℝ × K))} := by
  have hB : 0 ≤ B := (integral_nonneg fun p ↦
    (_root_.GD.N0213.N0497.d022006 β p).le).trans (h 0).2
  apply _root_.GD.N0213.N0497.d022009 ν (div_nonneg hB hβ.le)
  · exact fun n ↦ (_root_.GD.N0213.N0497.d022008 hβ (h n).1 (h n).2).1
  · exact fun n ↦ (_root_.GD.N0213.N0497.d022008 hβ (h n).1 (h n).2).2


theorem d022011
    (ν : ℕ → ProbabilityMeasure (ℝ × K)) {β B : ℝ}
    (hβ : 0 < β) (h : _root_.GD.N0213.N0497.d022007 ν β B) :
    ∃ (μ : ProbabilityMeasure (ℝ × K)) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (ν ∘ φ) atTop (𝓝 μ) := by
  have ht := _root_.GD.N0213.N0497.d022010 ν hβ h
  have ht' : IsTightMeasureSet
      {((μ : ProbabilityMeasure (ℝ × K)) : Measure (ℝ × K)) |
        μ ∈ range ν} := by
    convert ht using 1
    ext μ
    simp only [mem_setOf_eq, mem_range]
    constructor
    · rintro ⟨μ', ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨ν n, ⟨n, rfl⟩, rfl⟩
  obtain ⟨μ, -, φ, hφ, hlim⟩ :=
    (isCompact_closure_of_isTightMeasureSet ht').tendsto_subseq
      (fun n ↦ subset_closure (mem_range_self n))
  exact ⟨μ, φ, hφ, hlim⟩

omit [CompactSpace K] in


theorem d022012
    {ν : ℕ → ProbabilityMeasure (ℝ × K)} {μ : ProbabilityMeasure (ℝ × K)}
    (hlim : Tendsto ν atTop (𝓝 μ)) {f : (ℝ × K) → ℝ}
    (hf : Continuous f) (hpos : ∀ p, 0 ≤ f p) {B : ℝ}
    (hi : ∀ n, Integrable f (ν n : Measure (ℝ × K)))
    (hb : ∀ n, (∫ p, f p ∂(ν n : Measure (ℝ × K))) ≤ B) :
    Integrable f (μ : Measure (ℝ × K)) ∧
      (∫ p, f p ∂(μ : Measure (ℝ × K))) ≤ B := by
  have hB : 0 ≤ B := (integral_nonneg hpos).trans (hb 0)
  have hport := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    hf hpos (fun _ ho ↦ ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim ho)
  have hb' : ∀ n, (∫⁻ p, ENNReal.ofReal (f p) ∂(ν n : Measure (ℝ × K)))
      ≤ ENNReal.ofReal B := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (Eventually.of_forall hpos)]
    exact ENNReal.ofReal_le_ofReal (hb n)
  have hlin : (∫⁻ p, ENNReal.ofReal (f p) ∂(μ : Measure (ℝ × K)))
      ≤ ENNReal.ofReal B := hport.trans <|
    liminf_le_of_le (by isBoundedDefault) fun b hbn ↦
      let ⟨n, hn⟩ := hbn.exists
      hn.trans (hb' n)
  have hfi : Integrable f (μ : Measure (ℝ × K)) :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable
      (Eventually.of_forall hpos)).1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin)
  refine ⟨hfi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall hpos)] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 hlin

omit [CompactSpace K] in
theorem d022013
    {ν : ℕ → ProbabilityMeasure (ℝ × K)} {μ : ProbabilityMeasure (ℝ × K)}
    (hlim : Tendsto ν atTop (𝓝 μ)) {β B : ℝ}
    (h : _root_.GD.N0213.N0497.d022007 ν β B) :
    Integrable (_root_.GD.N0213.N0497.d022004 β) (μ : Measure (ℝ × K)) ∧
      (∫ p, _root_.GD.N0213.N0497.d022004 β p ∂(μ : Measure (ℝ × K))) ≤ B :=
  _root_.GD.N0213.N0497.d022012 hlim (_root_.GD.N0213.N0497.d022005 β)
    (fun p ↦ (_root_.GD.N0213.N0497.d022006 β p).le) (fun n ↦ (h n).1) (fun n ↦ (h n).2)


omit [CompactSpace K] in

theorem d022014
    {ν : ℕ → ProbabilityMeasure (ℝ × K)} {α β B : ℝ}
    (hαβ : α ≤ β) (h : _root_.GD.N0213.N0497.d022007 ν β B) :
    _root_.GD.N0213.N0497.d022007 ν α B := by
  intro n
  have hpoint (p : ℝ × K) : _root_.GD.N0213.N0497.d022004 α p ≤ _root_.GD.N0213.N0497.d022004 β p := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hαβ (sq_nonneg p.1)
  have hi : Integrable (_root_.GD.N0213.N0497.d022004 α) (ν n : Measure (ℝ × K)) :=
    (h n).1.mono_nonneg (_root_.GD.N0213.N0497.d022005 α).aestronglyMeasurable
      (Eventually.of_forall fun p => (_root_.GD.N0213.N0497.d022006 α p).le)
      (Eventually.of_forall hpoint)
  exact ⟨hi, (integral_mono hi (h n).1 hpoint).trans (h n).2⟩



theorem d022015
    (ν : ℕ → ProbabilityMeasure (ℝ × K)) {β B : ℝ}
    (hβ : 0 < β) (h : _root_.GD.N0213.N0497.d022007 ν β B) :
    ∃ (μ : ProbabilityMeasure (ℝ × K)) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (ν ∘ φ) atTop (𝓝 μ) ∧
      ∀ α : ℝ, α ≤ β →
        Integrable (_root_.GD.N0213.N0497.d022004 α) (μ : Measure (ℝ × K)) ∧
          (∫ p, _root_.GD.N0213.N0497.d022004 α p ∂(μ : Measure (ℝ × K))) ≤ B := by
  obtain ⟨μ, φ, hφ, hlim⟩ := _root_.GD.N0213.N0497.d022011 ν hβ h
  refine ⟨μ, φ, hφ, hlim, ?_⟩
  intro α hα
  exact _root_.GD.N0213.N0497.d022013 hlim
    (_root_.GD.N0213.N0497.d022014 hα (fun n => h (φ n)))



theorem d022016
    (ν : ℕ → ProbabilityMeasure (ℝ × K))
    (h : ∀ β : ℝ, 0 < β → β < 1 / 2 →
      ∃ B : ℝ, _root_.GD.N0213.N0497.d022007 ν β B) :
    ∃ (μ : ProbabilityMeasure (ℝ × K)) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (ν ∘ φ) atTop (𝓝 μ) ∧
      ∀ β : ℝ, 0 < β → β < 1 / 2 → ∃ B : ℝ,
        _root_.GD.N0213.N0497.d022007 ν β B ∧
        Integrable (_root_.GD.N0213.N0497.d022004 β) (μ : Measure (ℝ × K)) ∧
          (∫ p, _root_.GD.N0213.N0497.d022004 β p ∂(μ : Measure (ℝ × K))) ≤ B := by
  obtain ⟨B, hB⟩ := h (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨μ, φ, hφ, hlim⟩ :=
    _root_.GD.N0213.N0497.d022011 ν (by norm_num : (0 : ℝ) < 1 / 4) hB
  refine ⟨μ, φ, hφ, hlim, ?_⟩
  intro β hβ hhalf
  obtain ⟨C, hC⟩ := h β hβ hhalf
  exact ⟨C, hC, _root_.GD.N0213.N0497.d022013 hlim (fun n => hC (φ n))⟩



theorem d022017
    (k : ℕ)
    (ν : ℕ → ProbabilityMeasure (_root_.GD.N0232.N0719.N0994.d011371 k))
    (h : ∀ β : ℝ, 0 < β → β < 1 / 2 →
      ∃ B : ℝ, _root_.GD.N0213.N0497.d022007 ν β B) :
    ∃ (μ : ProbabilityMeasure (_root_.GD.N0232.N0719.N0994.d011371 k))
      (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (ν ∘ φ) atTop (𝓝 μ) ∧
      _root_.GD.N0232.N0719.N0994.d011375
        (μ : Measure (_root_.GD.N0232.N0719.N0994.d011371 k)) ∧
      ∀ β : ℝ, 0 < β → β < 1 / 2 → ∃ B : ℝ,
        _root_.GD.N0213.N0497.d022007 ν β B ∧
        (∫ p : _root_.GD.N0232.N0719.N0994.d011371 k,
          Real.exp (β * p.1 ^ 2)
          ∂(μ : Measure (_root_.GD.N0232.N0719.N0994.d011371 k))) ≤ B := by
  obtain ⟨μ, φ, hφ, hlim, hmom⟩ := _root_.GD.N0213.N0497.d022016 ν h
  refine ⟨μ, φ, hφ, hlim, ?_, ?_⟩
  · intro β hβ hhalf
    obtain ⟨B, _, hi, _⟩ := hmom β hβ hhalf
    exact hi
  · intro β hβ hhalf
    obtain ⟨B, hB, _, hb⟩ := hmom β hβ hhalf
    exact ⟨B, hB, hb⟩

end
end GD.N0213.N0497

#print axioms _root_.GD.N0213.N0497.d022009
#print axioms _root_.GD.N0213.N0497.d022010
#print axioms _root_.GD.N0213.N0497.d022011
#print axioms _root_.GD.N0213.N0497.d022012
#print axioms _root_.GD.N0213.N0497.d022013
#print axioms _root_.GD.N0213.N0497.d022014
#print axioms _root_.GD.N0213.N0497.d022015
#print axioms _root_.GD.N0213.N0497.d022016
#print axioms _root_.GD.N0213.N0497.d022017
