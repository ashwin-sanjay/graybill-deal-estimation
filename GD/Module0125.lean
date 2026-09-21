import GD.Module0124





































open scoped RealInnerProductSpace

namespace GD
namespace N0230
namespace N0604

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Θ : Type*}


def d001484 (ψ : Θ → H) (d' d : H) : Prop :=
  ∀ θ, ‖d' - ψ θ‖ ≤ ‖d - ψ θ‖



def d001485 (ψ : Θ → H) (d' d : H) : Prop :=
  _root_.GD.N0230.N0604.d001484 ψ d' d ∧ ∃ θ, ‖d' - ψ θ‖ < ‖d - ψ θ‖



def d001486 (S : Set H) (ψ : Θ → H) (d : H) : Prop :=
  d ∈ S ∧ ∀ d' ∈ S, ¬ _root_.GD.N0230.N0604.d001485 ψ d' d




theorem d001487 [Nonempty Θ]
    {ψ : Θ → H} {d₁ d₂ : H} (hne : d₁ ≠ d₂)
    (heq : ∀ θ, ‖d₁ - ψ θ‖ = ‖d₂ - ψ θ‖) :
    _root_.GD.N0230.N0604.d001485 ψ ((1 / 2 : ℝ) • (d₁ + d₂)) d₁ := by
  have hgap : 0 < ‖d₁ - d₂‖ ^ 2 := by
    have := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    positivity
  have hsq : ∀ θ, ‖(1 / 2 : ℝ) • (d₁ + d₂) - ψ θ‖ ^ 2 =
      ‖d₁ - ψ θ‖ ^ 2 - (1 / 4) * ‖d₁ - d₂‖ ^ 2 := by
    intro θ
    have hmid_eq : (1 / 2 : ℝ) • (d₁ + d₂) - ψ θ =
        (1 / 2 : ℝ) • ((d₁ - ψ θ) + (d₂ - ψ θ)) := by
      have h1 : (d₁ - ψ θ) + (d₂ - ψ θ) =
          (d₁ + d₂) - (2 : ℝ) • ψ θ := by
        rw [two_smul]
        abel
      rw [h1, smul_sub, smul_smul,
        show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]
    have hadd := norm_add_sq_real (d₁ - ψ θ) (d₂ - ψ θ)
    have hsub := norm_sub_sq_real (d₁ - ψ θ) (d₂ - ψ θ)
    have hpar : ‖(d₁ - ψ θ) + (d₂ - ψ θ)‖ ^ 2 =
        2 * ‖d₁ - ψ θ‖ ^ 2 + 2 * ‖d₂ - ψ θ‖ ^ 2 -
          ‖(d₁ - ψ θ) - (d₂ - ψ θ)‖ ^ 2 := by
      linarith [hadd, hsub]
    have hab : (d₁ - ψ θ) - (d₂ - ψ θ) = d₁ - d₂ := by abel
    rw [hmid_eq, norm_smul, Real.norm_eq_abs,
      show |(1 / 2 : ℝ)| = 1 / 2 by norm_num, mul_pow, hpar, hab,
      ← heq θ]
    ring
  have hlt : ∀ θ, ‖(1 / 2 : ℝ) • (d₁ + d₂) - ψ θ‖ < ‖d₁ - ψ θ‖ := by
    intro θ
    have hlt_sq : ‖(1 / 2 : ℝ) • (d₁ + d₂) - ψ θ‖ ^ 2 <
        ‖d₁ - ψ θ‖ ^ 2 := by
      rw [hsq θ]
      linarith
    have h := Real.sqrt_lt_sqrt (by positivity) hlt_sq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
      at h
  exact ⟨fun θ ↦ (hlt θ).le, Classical.arbitrary Θ,
    hlt (Classical.arbitrary Θ)⟩




theorem d001488 [Nonempty Θ] {S : Set H}
    (hS : Convex ℝ S) {ψ : Θ → H} {d₁ d₂ : H}
    (h₁ : _root_.GD.N0230.N0604.d001486 S ψ d₁) (h₂ : _root_.GD.N0230.N0604.d001486 S ψ d₂)
    (hne : d₁ ≠ d₂) :
    ¬ _root_.GD.N0230.N0604.d001484 ψ d₁ d₂ ∧ ¬ _root_.GD.N0230.N0604.d001484 ψ d₂ d₁ := by
  constructor
  · intro hdom
    by_cases hstrict : ∃ θ, ‖d₁ - ψ θ‖ < ‖d₂ - ψ θ‖
    · exact h₂.2 d₁ h₁.1 ⟨hdom, hstrict⟩
    · push Not at hstrict
      have heq : ∀ θ, ‖d₁ - ψ θ‖ = ‖d₂ - ψ θ‖ := fun θ ↦
        le_antisymm (hdom θ) (hstrict θ)
      have hmidS : (1 / 2 : ℝ) • (d₁ + d₂) ∈ S := by
        have := hS h₁.1 h₂.1 (by norm_num : (0:ℝ) ≤ 1/2)
          (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
        rwa [← smul_add] at this
      exact h₁.2 _ hmidS (_root_.GD.N0230.N0604.d001487 hne heq)
  · intro hdom
    by_cases hstrict : ∃ θ, ‖d₂ - ψ θ‖ < ‖d₁ - ψ θ‖
    · exact h₁.2 d₂ h₂.1 ⟨hdom, hstrict⟩
    · push Not at hstrict
      have heq : ∀ θ, ‖d₂ - ψ θ‖ = ‖d₁ - ψ θ‖ := fun θ ↦
        le_antisymm (hdom θ) (hstrict θ)
      have hmidS : (1 / 2 : ℝ) • (d₂ + d₁) ∈ S := by
        have := hS h₂.1 h₁.1 (by norm_num : (0:ℝ) ≤ 1/2)
          (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
        rwa [← smul_add] at this
      exact h₂.2 _ hmidS (_root_.GD.N0230.N0604.d001487 hne.symm heq)




theorem d001489
    {ψ : Θ → H} {T : H → H} {lam : ℝ} (hlam : 0 < lam)
    (hsim : ∀ x y : H, ‖T x - T y‖ = lam * ‖x - y‖)
    {θ θ' : Θ} (hstep : ψ θ' = T (ψ θ))
    {d₁ d₂ : H} (hfix₁ : T d₁ = d₁) (hfix₂ : T d₂ = d₂)
    (h : ‖d₁ - ψ θ‖ ≤ ‖d₂ - ψ θ‖) :
    ‖d₁ - ψ θ'‖ ≤ ‖d₂ - ψ θ'‖ := by
  rw [hstep, ← hfix₁, ← hfix₂, hsim, hsim]
  exact mul_le_mul_of_nonneg_left h hlam.le




theorem d001490 [Nonempty Θ]
    {G : Type*} {ψ : Θ → H} {act : G → Θ → Θ} {T : G → H → H}
    {lam : G → ℝ} (hlam : ∀ g, 0 < lam g)
    (hsim : ∀ g, ∀ x y : H, ‖T g x - T g y‖ = lam g * ‖x - y‖)
    (hcompat : ∀ g θ, ψ (act g θ) = T g (ψ θ))
    (htrans : ∀ θ θ' : Θ, ∃ g, act g θ = θ')
    {d₁ d₂ : H} (hfix₁ : ∀ g, T g d₁ = d₁)
    (hfix₂ : ∀ g, T g d₂ = d₂) :
    _root_.GD.N0230.N0604.d001484 ψ d₁ d₂ ∨ _root_.GD.N0230.N0604.d001484 ψ d₂ d₁ := by
  have hkey : ∀ (a b : H), (∀ g, T g a = a) → (∀ g, T g b = b) →
      ∀ θ θ', ‖a - ψ θ‖ ≤ ‖b - ψ θ‖ → ‖a - ψ θ'‖ ≤ ‖b - ψ θ'‖ := by
    intro a b hfa hfb θ θ' h
    obtain ⟨g, hg⟩ := htrans θ θ'
    exact _root_.GD.N0230.N0604.d001489 (hlam g) (hsim g)
      (by rw [← hg, hcompat]) (hfa g) (hfb g) h
  have θ₀ : Θ := Classical.arbitrary Θ
  rcases le_total ‖d₁ - ψ θ₀‖ ‖d₂ - ψ θ₀‖ with h | h
  · exact Or.inl fun θ ↦ hkey d₁ d₂ hfix₁ hfix₂ θ₀ θ h
  · exact Or.inr fun θ ↦ hkey d₂ d₁ hfix₂ hfix₁ θ₀ θ h





theorem d001491 [Nonempty Θ]
    {S : Set H} (hS : Convex ℝ S) {ψ : Θ → H}
    {G : Type*} {act : G → Θ → Θ} {T : G → H → H} {lam : G → ℝ}
    (hlam : ∀ g, 0 < lam g)
    (hsim : ∀ g, ∀ x y : H, ‖T g x - T g y‖ = lam g * ‖x - y‖)
    (hcompat : ∀ g θ, ψ (act g θ) = T g (ψ θ))
    (htrans : ∀ θ θ' : Θ, ∃ g, act g θ = θ')
    {d₁ d₂ : H} (h₁ : _root_.GD.N0230.N0604.d001486 S ψ d₁) (h₂ : _root_.GD.N0230.N0604.d001486 S ψ d₂)
    (hfix₁ : ∀ g, T g d₁ = d₁) (hfix₂ : ∀ g, T g d₂ = d₂) :
    d₁ = d₂ := by
  by_contra hne
  obtain ⟨hnd₁, hnd₂⟩ := _root_.GD.N0230.N0604.d001488 hS h₁ h₂ hne
  rcases _root_.GD.N0230.N0604.d001490 hlam hsim hcompat
    htrans hfix₁ hfix₂ with h | h
  · exact hnd₁ h
  · exact hnd₂ h

end

end N0604
end N0230
end GD

#print axioms _root_.GD.N0230.N0604.d001487
#print axioms _root_.GD.N0230.N0604.d001488
#print axioms _root_.GD.N0230.N0604.d001489
#print axioms _root_.GD.N0230.N0604.d001490
#print axioms _root_.GD.N0230.N0604.d001491
