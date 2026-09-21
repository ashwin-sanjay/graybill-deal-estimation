import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Sequences
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity














set_option linter.unusedSectionVars false

open MeasureTheory Filter Set
open scoped Topology

namespace GD.N0212.N0468

noncomputable section

abbrev d007644 (K : Type*) := ℝ × K

variable {K : Type*} [MetricSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

def d007645 (β : ℝ) (p : (_root_.GD.N0212.N0468.d007644 K)) : ℝ :=
  Real.exp (β * p.1 ^ 2)

theorem d007646 (β : ℝ) : Continuous (_root_.GD.N0212.N0468.d007645 (K := K) β) := by
  unfold _root_.GD.N0212.N0468.d007645
  fun_prop

theorem d007647 (β : ℝ) (p : (_root_.GD.N0212.N0468.d007644 K)) :
    0 < _root_.GD.N0212.N0468.d007645 β p := Real.exp_pos _

def d007648 (ν : ℕ → ProbabilityMeasure (_root_.GD.N0212.N0468.d007644 K))
    (β B : ℝ) : Prop :=
  ∀ n, Integrable (_root_.GD.N0212.N0468.d007645 β) (ν n : Measure (_root_.GD.N0212.N0468.d007644 K)) ∧
    (∫ p, _root_.GD.N0212.N0468.d007645 β p ∂(ν n : Measure (_root_.GD.N0212.N0468.d007644 K))) ≤ B

theorem d007649 {μ : ProbabilityMeasure (_root_.GD.N0212.N0468.d007644 K)}
    {β B : ℝ} (hβ : 0 < β)
    (hi : Integrable (_root_.GD.N0212.N0468.d007645 β) (μ : Measure (_root_.GD.N0212.N0468.d007644 K)))
    (hB : (∫ p, _root_.GD.N0212.N0468.d007645 β p ∂(μ : Measure (_root_.GD.N0212.N0468.d007644 K))) ≤ B) :
    Integrable (fun p : (_root_.GD.N0212.N0468.d007644 K) ↦ p.1 ^ 2) (μ : Measure (_root_.GD.N0212.N0468.d007644 K)) ∧
      (∫ p, p.1 ^ 2 ∂(μ : Measure (_root_.GD.N0212.N0468.d007644 K))) ≤ B / β := by
  have hb (p : (_root_.GD.N0212.N0468.d007644 K)) : p.1 ^ 2 ≤ _root_.GD.N0212.N0468.d007645 β p / β := by
    apply (le_div_iff₀ hβ).2
    have he := Real.add_one_le_exp (β * p.1 ^ 2)
    dsimp [_root_.GD.N0212.N0468.d007645]
    nlinarith
  have hisq : Integrable (fun p : (_root_.GD.N0212.N0468.d007644 K) ↦ p.1 ^ 2)
      (μ : Measure (_root_.GD.N0212.N0468.d007644 K)) :=
    (hi.div_const β).mono_nonneg (by fun_prop)
      (Eventually.of_forall fun p ↦ sq_nonneg p.1) (Eventually.of_forall hb)
  refine ⟨hisq, ?_⟩
  calc
    (∫ p, p.1 ^ 2 ∂(μ : Measure (_root_.GD.N0212.N0468.d007644 K)))
      ≤ ∫ p, _root_.GD.N0212.N0468.d007645 β p / β ∂(μ : Measure (_root_.GD.N0212.N0468.d007644 K)) :=
        integral_mono hisq (hi.div_const β) hb
    _ = (∫ p, _root_.GD.N0212.N0468.d007645 β p ∂(μ : Measure (_root_.GD.N0212.N0468.d007644 K))) / β :=
      integral_div β _
    _ ≤ B / β := div_le_div_of_nonneg_right hB hβ.le



theorem d007650 (ν : ℕ → ProbabilityMeasure (_root_.GD.N0212.N0468.d007644 K))
    {C : ℝ} (hC : 0 ≤ C)
    (hi : ∀ n, Integrable (fun p : (_root_.GD.N0212.N0468.d007644 K) ↦ p.1 ^ 2)
      (ν n : Measure (_root_.GD.N0212.N0468.d007644 K)))
    (hb : ∀ n, (∫ p, p.1 ^ 2 ∂(ν n : Measure (_root_.GD.N0212.N0468.d007644 K))) ≤ C) :
    IsTightMeasureSet {μ : Measure (_root_.GD.N0212.N0468.d007644 K) | ∃ n, μ = (ν n : Measure (_root_.GD.N0212.N0468.d007644 K))} := by
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
  let box : Set (_root_.GD.N0212.N0468.d007644 K) := Icc (-R) R ×ˢ univ
  refine ⟨box, isCompact_Icc.prod isCompact_univ, ?_⟩
  rintro μ ⟨n, rfl⟩
  have hsub : boxᶜ ⊆ {p : (_root_.GD.N0212.N0468.d007644 K) | R ^ 2 ≤ p.1 ^ 2} := by
    intro p hp
    have hp' : p.1 < -R ∨ R < p.1 := by
      simpa only [box, mem_compl_iff, mem_prod, mem_Icc, mem_univ, and_true,
        not_and_or, not_le] using hp
    change R ^ 2 ≤ p.1 ^ 2
    apply sq_le_sq.2
    rw [abs_of_pos hR]
    rcases hp' with hp' | hp'
    · exact (show R ≤ -p.1 by linarith).trans (neg_le_abs _)
    · exact hp'.le.trans (le_abs_self _)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := (ν n : Measure (_root_.GD.N0212.N0468.d007644 K)))
    (Eventually.of_forall fun p : (_root_.GD.N0212.N0468.d007644 K) ↦ sq_nonneg p.1) (hi n) (R ^ 2)
  have hm : (ν n : Measure (_root_.GD.N0212.N0468.d007644 K)).real boxᶜ ≤ ε.toReal := by
    have hmono := measureReal_mono (μ := (ν n : Measure (_root_.GD.N0212.N0468.d007644 K))) hsub
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hR)).1
    exact (mul_le_mul_of_nonneg_left hmono (sq_nonneg R)).trans
      (hmark.trans ((hb n).trans hCR))
  rw [← ofReal_measureReal]
  exact (ENNReal.ofReal_le_ofReal hm).trans (le_of_eq (ENNReal.ofReal_toReal htop))

theorem d007651
    (ν : ℕ → ProbabilityMeasure (_root_.GD.N0212.N0468.d007644 K)) {β B : ℝ}
    (hβ : 0 < β) (h : _root_.GD.N0212.N0468.d007648 ν β B) :
    IsTightMeasureSet {μ : Measure (_root_.GD.N0212.N0468.d007644 K) | ∃ n, μ = (ν n : Measure (_root_.GD.N0212.N0468.d007644 K))} := by
  have hB : 0 ≤ B := (integral_nonneg fun p ↦
    (_root_.GD.N0212.N0468.d007647 β p).le).trans (h 0).2
  apply _root_.GD.N0212.N0468.d007650 ν (div_nonneg hB hβ.le)
  · exact fun n ↦ (_root_.GD.N0212.N0468.d007649 hβ (h n).1 (h n).2).1
  · exact fun n ↦ (_root_.GD.N0212.N0468.d007649 hβ (h n).1 (h n).2).2


theorem d007652
    (ν : ℕ → ProbabilityMeasure (_root_.GD.N0212.N0468.d007644 K)) {β B : ℝ}
    (hβ : 0 < β) (h : _root_.GD.N0212.N0468.d007648 ν β B) :
    ∃ (μ : ProbabilityMeasure (_root_.GD.N0212.N0468.d007644 K)) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (ν ∘ φ) atTop (𝓝 μ) := by
  have ht := _root_.GD.N0212.N0468.d007651 ν hβ h
  have ht' : IsTightMeasureSet
      {((μ : ProbabilityMeasure (_root_.GD.N0212.N0468.d007644 K)) : Measure (_root_.GD.N0212.N0468.d007644 K)) |
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



theorem d007653
    {ν : ℕ → ProbabilityMeasure (_root_.GD.N0212.N0468.d007644 K)} {μ : ProbabilityMeasure (_root_.GD.N0212.N0468.d007644 K)}
    (hlim : Tendsto ν atTop (𝓝 μ)) {f : (_root_.GD.N0212.N0468.d007644 K) → ℝ}
    (hf : Continuous f) (hpos : ∀ p, 0 ≤ f p) {B : ℝ}
    (hi : ∀ n, Integrable f (ν n : Measure (_root_.GD.N0212.N0468.d007644 K)))
    (hb : ∀ n, (∫ p, f p ∂(ν n : Measure (_root_.GD.N0212.N0468.d007644 K))) ≤ B) :
    Integrable f (μ : Measure (_root_.GD.N0212.N0468.d007644 K)) ∧
      (∫ p, f p ∂(μ : Measure (_root_.GD.N0212.N0468.d007644 K))) ≤ B := by
  have hB : 0 ≤ B := (integral_nonneg hpos).trans (hb 0)
  have hport := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    hf hpos (fun _ ho ↦ ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim ho)
  have hb' : ∀ n, (∫⁻ p, ENNReal.ofReal (f p) ∂(ν n : Measure (_root_.GD.N0212.N0468.d007644 K)))
      ≤ ENNReal.ofReal B := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (Eventually.of_forall hpos)]
    exact ENNReal.ofReal_le_ofReal (hb n)
  have hlin : (∫⁻ p, ENNReal.ofReal (f p) ∂(μ : Measure (_root_.GD.N0212.N0468.d007644 K)))
      ≤ ENNReal.ofReal B := hport.trans <|
    liminf_le_of_le (by isBoundedDefault) fun b hbn ↦
      let ⟨n, hn⟩ := hbn.exists
      hn.trans (hb' n)
  have hfi : Integrable f (μ : Measure (_root_.GD.N0212.N0468.d007644 K)) :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable
      (Eventually.of_forall hpos)).1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin)
  refine ⟨hfi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall hpos)] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 hlin

theorem d007654
    {ν : ℕ → ProbabilityMeasure (_root_.GD.N0212.N0468.d007644 K)} {μ : ProbabilityMeasure (_root_.GD.N0212.N0468.d007644 K)}
    (hlim : Tendsto ν atTop (𝓝 μ)) {β B : ℝ}
    (h : _root_.GD.N0212.N0468.d007648 ν β B) :
    Integrable (_root_.GD.N0212.N0468.d007645 β) (μ : Measure (_root_.GD.N0212.N0468.d007644 K)) ∧
      (∫ p, _root_.GD.N0212.N0468.d007645 β p ∂(μ : Measure (_root_.GD.N0212.N0468.d007644 K))) ≤ B :=
  _root_.GD.N0212.N0468.d007653 hlim (_root_.GD.N0212.N0468.d007646 β)
    (fun p ↦ (_root_.GD.N0212.N0468.d007647 β p).le) (fun n ↦ (h n).1) (fun n ↦ (h n).2)

end
end GD.N0212.N0468

#print axioms _root_.GD.N0212.N0468.d007652
#print axioms _root_.GD.N0212.N0468.d007654
