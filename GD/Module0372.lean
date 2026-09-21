import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic























set_option autoImplicit false
set_option warningAsError true

open Polynomial Set Metric

namespace GD.N0106.N0428.N0765.N1614




theorem d005637 {A B : ℝ[X]} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {h₀ F₀ : ℝ} (hmem : (h₀, F₀) ∈ U)
    (hvan : ∀ p ∈ U, A.eval p.1 * p.2 - B.eval p.1 = 0) :
    ∃ ε > 0, ∀ h ∈ Ioo (h₀ - ε) (h₀ + ε), A.eval h = 0 ∧ B.eval h = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU _ hmem
  refine ⟨ε, hε, fun h hh => ?_⟩
  have hd : dist h h₀ < ε := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hh.1, hh.2]
  have hin1 : (h, F₀) ∈ U := by
    apply hball
    rw [mem_ball, Prod.dist_eq, dist_self]
    exact max_lt hd hε
  have hin2 : (h, F₀ + ε / 2) ∈ U := by
    apply hball
    rw [mem_ball, Prod.dist_eq]
    apply max_lt hd
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by positivity)]
    linarith
  have e1 := hvan _ hin1
  have e2 := hvan _ hin2
  simp only at e1 e2
  have hA : A.eval h = 0 := by
    have : A.eval h * (ε / 2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact h1
    · exact absurd h1 (by positivity)
  refine ⟨hA, ?_⟩
  rw [hA] at e1
  linarith



theorem d005638 {A B : ℝ[X]} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hne : U.Nonempty) (hvan : ∀ p ∈ U, A.eval p.1 * p.2 - B.eval p.1 = 0) :
    A = 0 ∧ B = 0 := by
  obtain ⟨⟨h₀, F₀⟩, hmem⟩ := hne
  obtain ⟨ε, hε, hroots⟩ := _root_.GD.N0106.N0428.N0765.N1614.d005637 hU hmem hvan
  have hinf : (Ioo (h₀ - ε) (h₀ + ε)).Infinite := Ioo_infinite (by linarith)
  constructor
  · exact Polynomial.eq_zero_of_infinite_isRoot A
      (hinf.mono fun h hh => (hroots h hh).1)
  · exact Polynomial.eq_zero_of_infinite_isRoot B
      (hinf.mono fun h hh => (hroots h hh).2)




theorem d005639 {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : MeasureTheory.Measure X} [μ.IsOpenPosMeasure]
    {f : X → ℝ} (hf : Continuous f) (h : f =ᵐ[μ] fun _ => (0 : ℝ)) : f = fun _ => 0 :=
  (hf.ae_eq_iff_eq μ continuous_const).mp h




theorem d005640 {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : MeasureTheory.Measure X} [μ.IsOpenPosMeasure]
    {Φ : X → ℝ × ℝ} (hΦ : Continuous Φ) {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hne : U.Nonempty)
    (hsurj : U ⊆ Set.range Φ) {A B : ℝ[X]}
    (h : (fun x => A.eval (Φ x).1 * (Φ x).2 - B.eval (Φ x).1) =ᵐ[μ] fun _ => (0 : ℝ)) :
    A = 0 ∧ B = 0 := by
  have hcont : Continuous fun x => A.eval (Φ x).1 * (Φ x).2 - B.eval (Φ x).1 := by
    have h1 : Continuous fun x => (Φ x).1 := (continuous_fst.comp hΦ)
    have h2 : Continuous fun x => (Φ x).2 := (continuous_snd.comp hΦ)
    exact ((A.continuous.comp h1).mul h2).sub (B.continuous.comp h1)
  have hall := _root_.GD.N0106.N0428.N0765.N1614.d005639 hcont h
  apply _root_.GD.N0106.N0428.N0765.N1614.d005638 hU hne
  intro p hp
  obtain ⟨x, rfl⟩ := hsurj hp
  exact congrFun hall x

end GD.N0106.N0428.N0765.N1614
