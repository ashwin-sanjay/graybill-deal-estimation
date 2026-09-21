import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0024.N0267

variable {Θ X Ω : Type*}

theorem d005153
    (L : Set Θ) (r r' : Θ → ℝ) (V h k M η : ℝ)
    (hr : ∀ θ, r θ ≤ V)
    (hslack : ∀ θ ∈ L, r θ ≤ V - h)
    (hlocal : ∀ θ ∈ L, r' θ ≤ r θ + η * M)
    (houtside : ∀ θ ∉ L, r' θ ≤ r θ - η * k)
    (hk : 0 < k) (hη : 0 < η) (hstep : η * M < h) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ θ, r' θ ≤ V - ε := by
  refine ⟨min (h - η * M) (η * k), lt_min (by linarith) (mul_pos hη hk), ?_⟩
  intro θ
  by_cases hθ : θ ∈ L
  · have hs := hslack θ hθ
    have hl := hlocal θ hθ
    have hm := min_le_left (h - η * M) (η * k)
    linarith
  · have ho := houtside θ hθ
    have hb := hr θ
    have hm := min_le_right (h - η * M) (η * k)
    linarith

theorem d005154
    (L : Set Θ) (r r' : Θ → ℝ) (V h k M η : ℝ)
    (hr : ∀ θ, r θ ≤ V)
    (hslack : ∀ θ ∈ L, r θ ≤ V - h)
    (hlocal : ∀ θ ∈ L, r' θ ≤ r θ + η * M)
    (houtside : ∀ θ ∉ L, r' θ ≤ r θ - η * k)
    (hk : 0 < k) (hη : 0 < η) (hstep : η * M < h)
    (hbarrier : ∀ ε : ℝ, 0 < ε → ∃ θ, V - ε < r' θ) : False := by
  obtain ⟨ε, hε, hbound⟩ :=
    _root_.GD.N0024.N0267.d005153 L r r' V h k M η hr hslack hlocal houtside hk hη hstep
  obtain ⟨θ, hθ⟩ := hbarrier ε hε
  exact (not_lt.mpr (hbound θ)) hθ

theorem d005155 [Nonempty Θ]
    (L : Set Θ) (r r' : Θ → ℝ) (V h k M η : ℝ)
    (hr : ∀ θ, r θ ≤ V)
    (hslack : ∀ θ ∈ L, r θ ≤ V - h)
    (hlocal : ∀ θ ∈ L, r' θ ≤ r θ + η * M)
    (houtside : ∀ θ ∉ L, r' θ ≤ r θ - η * k)
    (hk : 0 < k) (hη : 0 < η) (hstep : η * M < h)
    (hbarrier : V ≤ sSup (Set.range r')) : False := by
  obtain ⟨ε, hε, hbound⟩ :=
    _root_.GD.N0024.N0267.d005153 L r r' V h k M η hr hslack hlocal houtside hk hη hstep
  have hs : sSup (Set.range r') ≤ V - ε := by
    apply csSup_le (Set.range_nonempty r')
    rintro _ ⟨θ, rfl⟩
    exact hbound θ
  linarith

theorem d005156 (h M : ℝ) (hh : 0 < h) (hM : 0 ≤ M) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ η * M < h := by
  let q : ℝ := h / (2 * (M + 1))
  have hden : 0 < 2 * (M + 1) := by linarith
  have hq : 0 < q := div_pos hh hden
  have heq : q * (2 * (M + 1)) = h :=
    div_mul_cancel₀ h (ne_of_gt hden)
  have hqM : q * M < h := by nlinarith
  refine ⟨min 1 q, lt_min (by norm_num) hq, min_le_left _ _, ?_⟩
  exact (mul_le_mul_of_nonneg_right (min_le_right 1 q) hM).trans_lt hqM

theorem d005157
    (L : Set Θ) (r : Θ → ℝ) (perturb : ℝ → Θ → ℝ) (V h k M : ℝ)
    (hr : ∀ θ, r θ ≤ V)
    (hslack : ∀ θ ∈ L, r θ ≤ V - h)
    (hlocal : ∀ η, 0 < η → η ≤ 1 → ∀ θ ∈ L,
      perturb η θ ≤ r θ + η * M)
    (houtside : ∀ η, 0 < η → η ≤ 1 → ∀ θ ∉ L,
      perturb η θ ≤ r θ - η * k)
    (hh : 0 < h) (hk : 0 < k) (hM : 0 ≤ M) :
    ∃ η ε : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < ε ∧ ∀ θ, perturb η θ ≤ V - ε := by
  obtain ⟨η, hη, hη1, hstep⟩ := _root_.GD.N0024.N0267.d005156 h M hh hM
  obtain ⟨ε, hε, hbound⟩ := _root_.GD.N0024.N0267.d005153 L r (perturb η) V h k M η
    hr hslack (hlocal η hη hη1) (houtside η hη hη1) hk hη hstep
  exact ⟨η, ε, hη, hη1, hε, hbound⟩

theorem d005158
    (C : Set X) (risk : X → Θ → ℝ) (L : Set Θ)
    (r : Θ → ℝ) (perturb : ℝ → X) (V h k M : ℝ)
    (hr : ∀ θ, r θ ≤ V)
    (hslack : ∀ θ ∈ L, r θ ≤ V - h)
    (hadmissible : ∀ η, 0 < η → η ≤ 1 → perturb η ∈ C)
    (hlocal : ∀ η, 0 < η → η ≤ 1 → ∀ θ ∈ L,
      risk (perturb η) θ ≤ r θ + η * M)
    (houtside : ∀ η, 0 < η → η ≤ 1 → ∀ θ ∉ L,
      risk (perturb η) θ ≤ r θ - η * k)
    (hh : 0 < h) (hk : 0 < k) (hM : 0 ≤ M)
    (hminimax : ∀ x ∈ C, ∀ ε : ℝ, 0 < ε → ∃ θ, V - ε < risk x θ) : False := by
  obtain ⟨η, ε, hη, hη1, hε, hbound⟩ :=
    _root_.GD.N0024.N0267.d005157 L r (fun η => risk (perturb η)) V h k M
      hr hslack hlocal houtside hh hk hM
  obtain ⟨θ, hθ⟩ := hminimax (perturb η) (hadmissible η hη hη1) ε hε
  exact (not_lt.mpr (hbound θ)) hθ

theorem d005159
    (L : Set Θ) (r r' : Θ → ℝ) (V h k M C η : ℝ)
    (hr : ∀ θ, r θ ≤ V)
    (hslack : ∀ θ ∈ L, r θ ≤ V - h)
    (hlocal : ∀ θ ∈ L, r' θ ≤ r θ + η * M)
    (houtside : ∀ θ ∉ L, r' θ ≤ r θ - η * k + η ^ 2 * C)
    (hk : 0 < k) (hη : 0 < η) (hstep : η * M < h)
    (hquadratic : η * C ≤ k / 2) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ θ, r' θ ≤ V - ε := by
  apply _root_.GD.N0024.N0267.d005153 L r r' V h (k / 2) M η
    hr hslack hlocal _ (by linarith) hη hstep
  intro θ hθ
  have ho := houtside θ hθ
  have hc := mul_le_mul_of_nonneg_left hquadratic (le_of_lt hη)
  nlinarith

open MeasureTheory

section Integrals

variable [MeasurableSpace Ω]

theorem d005160
    (ν : Measure Ω) (g d : Ω → ℝ) (μ η : ℝ)
    (hg : Integrable (fun z => (g z - μ) ^ 2) ν)
    (hcross : Integrable (fun z => (g z - μ) * d z) ν)
    (hd : Integrable (fun z => d z ^ 2) ν) :
    (∫ z, (g z + η * d z - μ) ^ 2 ∂ν) =
      (∫ z, (g z - μ) ^ 2 ∂ν) +
        (2 * η) * (∫ z, (g z - μ) * d z ∂ν) +
        η ^ 2 * (∫ z, d z ^ 2 ∂ν) := by
  have heq : (fun z => (g z + η * d z - μ) ^ 2) =
      (fun z => (g z - μ) ^ 2 + (2 * η) * ((g z - μ) * d z) +
        η ^ 2 * d z ^ 2) := by
    funext z
    ring
  have hlinear : Integrable
      (fun z => (g z - μ) ^ 2 + (2 * η) * ((g z - μ) * d z)) ν :=
    hg.add (hcross.const_mul (2 * η))
  rw [heq, integral_add hlinear (hd.const_mul (η ^ 2)),
    integral_add hg (hcross.const_mul (2 * η)), integral_const_mul, integral_const_mul]

theorem d005161
    (ν : Measure Ω) (g d : Ω → ℝ) (μ η : ℝ)
    (hg : Integrable (fun z => (g z - μ) ^ 2) ν)
    (hcross : Integrable (fun z => (g z - μ) * d z) ν)
    (hd : Integrable (fun z => d z ^ 2) ν) :
    Integrable (fun z => (g z + η * d z - μ) ^ 2) ν := by
  have heq : (fun z => (g z + η * d z - μ) ^ 2) =
      (fun z => (g z - μ) ^ 2 + (2 * η) * ((g z - μ) * d z) +
        η ^ 2 * d z ^ 2) := by
    funext z
    ring
  rw [heq]
  exact (hg.add (hcross.const_mul (2 * η))).add (hd.const_mul (η ^ 2))

theorem d005162
    (ν : Measure Ω) [IsFiniteMeasure ν] (E : Set Ω) (hE : MeasurableSet E)
    (g : Ω → ℝ) (μ η : ℝ)
    (hg : Integrable (fun z => (g z - μ) ^ 2) ν)
    (hgE : IntegrableOn (fun z => g z - μ) E ν) :
    (∫ z, (g z + η * E.indicator (fun _ => (1 : ℝ)) z - μ) ^ 2 ∂ν) =
      (∫ z, (g z - μ) ^ 2 ∂ν) +
        (2 * η) * (∫ z in E, g z - μ ∂ν) + η ^ 2 * ν.real E := by
  classical
  have hcross : (fun z => (g z - μ) * E.indicator (fun _ => (1 : ℝ)) z) =
      E.indicator (fun z => g z - μ) := by
    funext z
    by_cases hz : z ∈ E <;> simp [hz]
  have hsquare : (fun z => (E.indicator (fun _ => (1 : ℝ)) z) ^ 2) =
      E.indicator (fun _ => (1 : ℝ)) := by
    funext z
    by_cases hz : z ∈ E <;> simp [hz]
  have hc : Integrable (fun z => (g z - μ) * E.indicator (fun _ => (1 : ℝ)) z) ν := by
    rw [hcross]
    exact hgE.integrable_indicator hE
  have hd : Integrable (fun z => (E.indicator (fun _ => (1 : ℝ)) z) ^ 2) ν := by
    rw [hsquare]
    exact (integrable_const (1 : ℝ)).indicator hE
  rw [_root_.GD.N0024.N0267.d005160 ν g (E.indicator (fun _ => (1 : ℝ))) μ η hg hc hd,
    hcross, hsquare, integral_indicator hE, integral_indicator_const (1 : ℝ) hE]
  simp only [smul_eq_mul, mul_one]

end Integrals

#print axioms _root_.GD.N0024.N0267.d005153
#print axioms _root_.GD.N0024.N0267.d005154
#print axioms _root_.GD.N0024.N0267.d005155
#print axioms _root_.GD.N0024.N0267.d005156
#print axioms _root_.GD.N0024.N0267.d005157
#print axioms _root_.GD.N0024.N0267.d005158
#print axioms _root_.GD.N0024.N0267.d005159
#print axioms _root_.GD.N0024.N0267.d005160
#print axioms _root_.GD.N0024.N0267.d005161
#print axioms _root_.GD.N0024.N0267.d005162

end GD.N0024.N0267
