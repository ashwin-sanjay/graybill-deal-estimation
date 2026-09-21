import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Sequences
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity













open MeasureTheory Filter Set
open scoped Topology

namespace GD.N0232.N0720.N1297

noncomputable section

abbrev d002701 := Icc (0 : ℝ) 1
abbrev d002702 := ℝ × _root_.GD.N0232.N0720.N1297.d002701

def d002703 (β : ℝ) (p : _root_.GD.N0232.N0720.N1297.d002702) : ℝ :=
  Real.exp (β * p.1 ^ 2)

theorem d002704 (β : ℝ) : Continuous (_root_.GD.N0232.N0720.N1297.d002703 β) := by
  unfold _root_.GD.N0232.N0720.N1297.d002703
  fun_prop

theorem d002705 (β : ℝ) (p : _root_.GD.N0232.N0720.N1297.d002702) :
    0 < _root_.GD.N0232.N0720.N1297.d002703 β p := Real.exp_pos _

def d002706 (ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1297.d002702)
    (β B : ℝ) : Prop :=
  ∀ n, Integrable (_root_.GD.N0232.N0720.N1297.d002703 β) (ν n : Measure _root_.GD.N0232.N0720.N1297.d002702) ∧
    (∫ p, _root_.GD.N0232.N0720.N1297.d002703 β p ∂(ν n : Measure _root_.GD.N0232.N0720.N1297.d002702)) ≤ B

theorem d002707 {μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1297.d002702}
    {β B : ℝ} (hβ : 0 < β)
    (hi : Integrable (_root_.GD.N0232.N0720.N1297.d002703 β) (μ : Measure _root_.GD.N0232.N0720.N1297.d002702))
    (hB : (∫ p, _root_.GD.N0232.N0720.N1297.d002703 β p ∂(μ : Measure _root_.GD.N0232.N0720.N1297.d002702)) ≤ B) :
    Integrable (fun p : _root_.GD.N0232.N0720.N1297.d002702 ↦ p.1 ^ 2) (μ : Measure _root_.GD.N0232.N0720.N1297.d002702) ∧
      (∫ p, p.1 ^ 2 ∂(μ : Measure _root_.GD.N0232.N0720.N1297.d002702)) ≤ B / β := by
  have hb (p : _root_.GD.N0232.N0720.N1297.d002702) : p.1 ^ 2 ≤ _root_.GD.N0232.N0720.N1297.d002703 β p / β := by
    apply (le_div_iff₀ hβ).2
    have he := Real.add_one_le_exp (β * p.1 ^ 2)
    dsimp [_root_.GD.N0232.N0720.N1297.d002703]
    nlinarith
  have hisq : Integrable (fun p : _root_.GD.N0232.N0720.N1297.d002702 ↦ p.1 ^ 2)
      (μ : Measure _root_.GD.N0232.N0720.N1297.d002702) :=
    (hi.div_const β).mono_nonneg (by fun_prop)
      (Eventually.of_forall fun p ↦ sq_nonneg p.1) (Eventually.of_forall hb)
  refine ⟨hisq, ?_⟩
  calc
    (∫ p, p.1 ^ 2 ∂(μ : Measure _root_.GD.N0232.N0720.N1297.d002702))
      ≤ ∫ p, _root_.GD.N0232.N0720.N1297.d002703 β p / β ∂(μ : Measure _root_.GD.N0232.N0720.N1297.d002702) :=
        integral_mono hisq (hi.div_const β) hb
    _ = (∫ p, _root_.GD.N0232.N0720.N1297.d002703 β p ∂(μ : Measure _root_.GD.N0232.N0720.N1297.d002702)) / β :=
      integral_div β _
    _ ≤ B / β := div_le_div_of_nonneg_right hB hβ.le



theorem d002708 (ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1297.d002702)
    {C : ℝ} (hC : 0 ≤ C)
    (hi : ∀ n, Integrable (fun p : _root_.GD.N0232.N0720.N1297.d002702 ↦ p.1 ^ 2)
      (ν n : Measure _root_.GD.N0232.N0720.N1297.d002702))
    (hb : ∀ n, (∫ p, p.1 ^ 2 ∂(ν n : Measure _root_.GD.N0232.N0720.N1297.d002702)) ≤ C) :
    IsTightMeasureSet {μ : Measure _root_.GD.N0232.N0720.N1297.d002702 | ∃ n, μ = (ν n : Measure _root_.GD.N0232.N0720.N1297.d002702)} := by
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
  let K : Set _root_.GD.N0232.N0720.N1297.d002702 := Icc (-R) R ×ˢ univ
  refine ⟨K, isCompact_Icc.prod isCompact_univ, ?_⟩
  rintro μ ⟨n, rfl⟩
  have hsub : Kᶜ ⊆ {p : _root_.GD.N0232.N0720.N1297.d002702 | R ^ 2 ≤ p.1 ^ 2} := by
    intro p hp
    have hp' : p.1 < -R ∨ R < p.1 := by
      simpa only [K, mem_compl_iff, mem_prod, mem_Icc, mem_univ, and_true,
        not_and_or, not_le] using hp
    change R ^ 2 ≤ p.1 ^ 2
    apply sq_le_sq.2
    rw [abs_of_pos hR]
    rcases hp' with hp' | hp'
    · exact (show R ≤ -p.1 by linarith).trans (neg_le_abs _)
    · exact hp'.le.trans (le_abs_self _)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := (ν n : Measure _root_.GD.N0232.N0720.N1297.d002702))
    (Eventually.of_forall fun p : _root_.GD.N0232.N0720.N1297.d002702 ↦ sq_nonneg p.1) (hi n) (R ^ 2)
  have hm : (ν n : Measure _root_.GD.N0232.N0720.N1297.d002702).real Kᶜ ≤ ε.toReal := by
    have hmono := measureReal_mono (μ := (ν n : Measure _root_.GD.N0232.N0720.N1297.d002702)) hsub
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hR)).1
    exact (mul_le_mul_of_nonneg_left hmono (sq_nonneg R)).trans
      (hmark.trans ((hb n).trans hCR))
  rw [← ofReal_measureReal]
  exact (ENNReal.ofReal_le_ofReal hm).trans (le_of_eq (ENNReal.ofReal_toReal htop))

theorem d002709
    (ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1297.d002702) {β B : ℝ}
    (hβ : 0 < β) (h : _root_.GD.N0232.N0720.N1297.d002706 ν β B) :
    IsTightMeasureSet {μ : Measure _root_.GD.N0232.N0720.N1297.d002702 | ∃ n, μ = (ν n : Measure _root_.GD.N0232.N0720.N1297.d002702)} := by
  have hB : 0 ≤ B := (integral_nonneg fun p ↦
    (_root_.GD.N0232.N0720.N1297.d002705 β p).le).trans (h 0).2
  apply _root_.GD.N0232.N0720.N1297.d002708 ν (div_nonneg hB hβ.le)
  · exact fun n ↦ (_root_.GD.N0232.N0720.N1297.d002707 hβ (h n).1 (h n).2).1
  · exact fun n ↦ (_root_.GD.N0232.N0720.N1297.d002707 hβ (h n).1 (h n).2).2


theorem d002710
    (ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1297.d002702) {β B : ℝ}
    (hβ : 0 < β) (h : _root_.GD.N0232.N0720.N1297.d002706 ν β B) :
    ∃ (μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1297.d002702) (φ : ℕ → ℕ),
      StrictMono φ ∧ Tendsto (ν ∘ φ) atTop (𝓝 μ) := by
  have ht := _root_.GD.N0232.N0720.N1297.d002709 ν hβ h
  have ht' : IsTightMeasureSet
      {((μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1297.d002702) : Measure _root_.GD.N0232.N0720.N1297.d002702) |
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



theorem d002711
    {ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1297.d002702} {μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1297.d002702}
    (hlim : Tendsto ν atTop (𝓝 μ)) {f : _root_.GD.N0232.N0720.N1297.d002702 → ℝ}
    (hf : Continuous f) (hpos : ∀ p, 0 ≤ f p) {B : ℝ}
    (hi : ∀ n, Integrable f (ν n : Measure _root_.GD.N0232.N0720.N1297.d002702))
    (hb : ∀ n, (∫ p, f p ∂(ν n : Measure _root_.GD.N0232.N0720.N1297.d002702)) ≤ B) :
    Integrable f (μ : Measure _root_.GD.N0232.N0720.N1297.d002702) ∧
      (∫ p, f p ∂(μ : Measure _root_.GD.N0232.N0720.N1297.d002702)) ≤ B := by
  have hB : 0 ≤ B := (integral_nonneg hpos).trans (hb 0)
  have hport := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    hf hpos (fun _ ho ↦ ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim ho)
  have hb' : ∀ n, (∫⁻ p, ENNReal.ofReal (f p) ∂(ν n : Measure _root_.GD.N0232.N0720.N1297.d002702))
      ≤ ENNReal.ofReal B := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (Eventually.of_forall hpos)]
    exact ENNReal.ofReal_le_ofReal (hb n)
  have hlin : (∫⁻ p, ENNReal.ofReal (f p) ∂(μ : Measure _root_.GD.N0232.N0720.N1297.d002702))
      ≤ ENNReal.ofReal B := hport.trans <|
    liminf_le_of_le (by isBoundedDefault) fun b hbn ↦
      let ⟨n, hn⟩ := hbn.exists
      hn.trans (hb' n)
  have hfi : Integrable f (μ : Measure _root_.GD.N0232.N0720.N1297.d002702) :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable
      (Eventually.of_forall hpos)).1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlin)
  refine ⟨hfi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall hpos)] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 hlin

theorem d002712
    {ν : ℕ → ProbabilityMeasure _root_.GD.N0232.N0720.N1297.d002702} {μ : ProbabilityMeasure _root_.GD.N0232.N0720.N1297.d002702}
    (hlim : Tendsto ν atTop (𝓝 μ)) {β B : ℝ}
    (h : _root_.GD.N0232.N0720.N1297.d002706 ν β B) :
    Integrable (_root_.GD.N0232.N0720.N1297.d002703 β) (μ : Measure _root_.GD.N0232.N0720.N1297.d002702) ∧
      (∫ p, _root_.GD.N0232.N0720.N1297.d002703 β p ∂(μ : Measure _root_.GD.N0232.N0720.N1297.d002702)) ≤ B :=
  _root_.GD.N0232.N0720.N1297.d002711 hlim (_root_.GD.N0232.N0720.N1297.d002704 β)
    (fun p ↦ (_root_.GD.N0232.N0720.N1297.d002705 β p).le) (fun n ↦ (h n).1) (fun n ↦ (h n).2)

end
end GD.N0232.N0720.N1297

#print axioms _root_.GD.N0232.N0720.N1297.d002710
#print axioms _root_.GD.N0232.N0720.N1297.d002712
