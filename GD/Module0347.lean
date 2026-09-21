import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open Set

namespace GD.N0081.N0326

theorem d005148 {X : Type*} (K : Set X) (p q : X → ℝ)
    {δ η M : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hM : 0 ≤ M)
    (hp : ∀ x, p x ≤ 1) (hpK : ∀ x ∈ K, p x ≤ 1 - δ)
    (hq : ∀ x, q x ≤ 1 + M) (hqK : ∀ x ∉ K, q x ≤ 1 - η) :
    ∃ ε γ : ℝ, 0 < ε ∧ ε < 1 ∧ 0 < γ ∧
      ∀ x, (1 - ε) * p x + ε * q x ≤ 1 - γ := by
  let ε := δ / (2 * (δ + M + 1))
  have hden : 0 < 2 * (δ + M + 1) := by positivity
  have hε : 0 < ε := div_pos hδ hden
  have hε1 : ε < 1 := by
    apply (div_lt_one hden).mpr
    linarith
  have heq : ε * (2 * (δ + M + 1)) = δ := by
    exact div_mul_cancel₀ δ hden.ne'
  have hcore : ε * (δ + M) ≤ δ / 2 := by nlinarith
  refine ⟨ε, min (ε * η) (δ / 2), hε, hε1,
    lt_min (mul_pos hε hη) (half_pos hδ), ?_⟩
  intro x
  by_cases hx : x ∈ K
  · have h1 := mul_le_mul_of_nonneg_left (hpK x hx) (sub_pos.mpr hε1).le
    have h2 := mul_le_mul_of_nonneg_left (hq x) hε.le
    have hmin := min_le_right (ε * η) (δ / 2)
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_left (hp x) (sub_pos.mpr hε1).le
    have h2 := mul_le_mul_of_nonneg_left (hqK x hx) hε.le
    have hmin := min_le_left (ε * η) (δ / 2)
    nlinarith

theorem d005149 {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {p : X → ℝ}
    (hp : ContinuousOn p K) (hstrict : ∀ x ∈ K, p x < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, p x ≤ 1 - δ := by
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne hp
    exact ⟨1 - p x, sub_pos.mpr (hstrict x hx),
      fun y hy => by simpa using hmax hy⟩
  · exact ⟨1, by norm_num, fun x hx => (hne ⟨x, hx⟩).elim⟩

theorem d005150 {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (p q : X → ℝ)
    (hpcont : ContinuousOn p K) (hp : ∀ x, p x < 1)
    {η M : ℝ} (hη : 0 < η) (hM : 0 ≤ M)
    (hq : ∀ x, q x ≤ 1 + M) (hqK : ∀ x ∉ K, q x ≤ 1 - η) :
    ∃ ε γ : ℝ, 0 < ε ∧ ε < 1 ∧ 0 < γ ∧
      ∀ x, (1 - ε) * p x + ε * q x ≤ 1 - γ := by
  obtain ⟨δ, hδ, hδK⟩ := _root_.GD.N0081.N0326.d005149 hK hpcont (fun x _ => hp x)
  exact _root_.GD.N0081.N0326.d005148 K p q hδ hη hM (fun x => (hp x).le) hδK hq hqK

theorem d005151 {X : Type*} [TopologicalSpace X]
    [CompactSpace X] (B : Set X) (p q : X → ℝ)
    (hpcont : ContinuousOn p Bᶜ) (hp : ∀ x ∉ B, p x < 1)
    (hqcont : Continuous q) {r : ℝ} (hr : r < 1)
    (hqB : ∀ x ∈ B, q x < r) :
    ∃ ε γ : ℝ, 0 < ε ∧ ε < 1 ∧ 0 < γ ∧
      ∀ x ∉ B, (1 - ε) * p x + ε * q x ≤ 1 - γ := by
  let K : Set X := {x | r ≤ q x}
  have hK : IsCompact K := (isClosed_le continuous_const hqcont).isCompact
  have hKB : K ⊆ Bᶜ := by
    intro x hx hB
    exact (not_lt_of_ge hx) (hqB x hB)
  obtain ⟨δ, hδ, hδK⟩ := _root_.GD.N0081.N0326.d005149 hK (hpcont.mono hKB)
    (fun x hx => hp x (hKB hx))
  obtain ⟨M, hM⟩ := isCompact_univ.bddAbove_image hqcont.continuousOn
  let M' := max 0 M
  let Y := Bᶜ
  have hbound : ∀ x : Y, q x ≤ 1 + M' := by
    intro x
    have hx := hM (mem_image_of_mem q (mem_univ (x : X)))
    have hm : M ≤ M' := le_max_right _ _
    linarith
  obtain ⟨ε, γ, hε, hε1, hγ, hmix⟩ := _root_.GD.N0081.N0326.d005148
    {x : Y | (x : X) ∈ K} (fun x : Y => p x) (fun x : Y => q x)
    hδ (sub_pos.mpr hr) (le_max_left 0 M)
    (fun x => (hp x x.property).le)
    (fun x hx => hδK x hx) hbound
    (fun x hx => by
      have hlt : q x < r := lt_of_not_ge hx
      linarith)
  exact ⟨ε, γ, hε, hε1, hγ, fun x hx => hmix ⟨x, hx⟩⟩

theorem d005152 (p q : ℝ → ℝ)
    (hpcont : ContinuousOn p (Ioo 0 1))
    (hp : ∀ t ∈ Ioo (0 : ℝ) 1, p t < 1)
    (hqcont : ContinuousOn q (Icc 0 1))
    (hq0 : q 0 < 1) (hq1 : q 1 < 1) :
    ∃ ε γ : ℝ, 0 < ε ∧ ε < 1 ∧ 0 < γ ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, (1 - ε) * p t + ε * q t ≤ 1 - γ := by
  let X := Icc (0 : ℝ) 1
  let B : Set X := {x | (x : ℝ) = 0 ∨ (x : ℝ) = 1}
  let r := (max (q 0) (q 1) + 1) / 2
  have hmax : max (q 0) (q 1) < 1 := max_lt hq0 hq1
  have hr : r < 1 := by dsimp [r]; linarith
  have hQr : max (q 0) (q 1) < r := by dsimp [r]; linarith
  have hmem (x : X) (hx : x ∉ B) : (x : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    have hne0 : (x : ℝ) ≠ 0 := fun h => hx (Or.inl h)
    have hne1 : (x : ℝ) ≠ 1 := fun h => hx (Or.inr h)
    exact ⟨lt_of_le_of_ne x.property.1 hne0.symm,
      lt_of_le_of_ne x.property.2 hne1⟩
  have hpc : ContinuousOn (fun x : X => p x) Bᶜ :=
    hpcont.comp continuous_subtype_val.continuousOn (fun x hx => hmem x hx)
  have hqc : Continuous (fun x : X => q x) :=
    continuousOn_iff_continuous_restrict.mp hqcont
  obtain ⟨ε, γ, hε, hε1, hγ, hmix⟩ := _root_.GD.N0081.N0326.d005151 B
    (fun x : X => p x) (fun x : X => q x) hpc
    (fun x hx => hp x (hmem x hx)) hqc hr (by
      intro x hx
      rcases hx with hx | hx
      · exact hx ▸ (le_max_left (q 0) (q 1)).trans_lt hQr
      · exact hx ▸ (le_max_right (q 0) (q 1)).trans_lt hQr)
  refine ⟨ε, γ, hε, hε1, hγ, fun t ht => ?_⟩
  exact hmix ⟨t, ht.1.le, ht.2.le⟩ (by
    rintro (h | h)
    · exact ht.1.ne' h
    · exact ht.2.ne h)

end GD.N0081.N0326

#print axioms _root_.GD.N0081.N0326.d005148
#print axioms _root_.GD.N0081.N0326.d005151
#print axioms _root_.GD.N0081.N0326.d005152
