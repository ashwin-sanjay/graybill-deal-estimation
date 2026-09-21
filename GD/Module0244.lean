import GD.Module0243
import GD.Module0091










open Set
open scoped ENNReal BigOperators

namespace GD.N0230.N0632

noncomputable section

set_option linter.unusedSectionVars false

variable {H Θ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

def d003532 (risk : Θ → H → ℝ≥0∞) : Set H :=
  {p | ∀ θ, risk θ p ≠ ⊤}

variable (risk : Θ → H → ℝ≥0∞)
  (hcombo : ∀ θ p q a b, 0 ≤ a → 0 ≤ b → a + b = 1 →
    risk θ (a • p + b • q) ≤
      ENNReal.ofReal a * risk θ p + ENNReal.ofReal b * risk θ q)

include hcombo

theorem d003533 : Convex ℝ (_root_.GD.N0230.N0632.d003532 risk) := by
  intro p hp q hq a b ha hb hab θ
  exact ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hp θ),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq θ)⟩)
    (hcombo θ p q a b ha hb hab)

theorem d003534 (θ : Θ) :
    ConvexOn ℝ (_root_.GD.N0230.N0632.d003532 risk) (fun p ↦ (risk θ p).toReal) := by
  refine ⟨_root_.GD.N0230.N0632.d003533 risk hcombo, ?_⟩
  intro p hp q hq a b ha hb hab
  have hright : ENNReal.ofReal a * risk θ p + ENNReal.ofReal b * risk θ q ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hp θ),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq θ)⟩
  have h := ENNReal.toReal_mono hright (hcombo θ p q a b ha hb hab)
  rw [ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hp θ))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq θ)),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb] at h
  exact h

theorem d003535 (θ : Θ) (c : ℝ) :
    Convex ℝ {p | risk θ p ≤ ENNReal.ofReal c} := by
  intro p hp q hq a b ha hb hab
  refine (hcombo θ p q a b ha hb hab).trans ?_
  calc
    ENNReal.ofReal a * risk θ p + ENNReal.ofReal b * risk θ q ≤
        ENNReal.ofReal a * ENNReal.ofReal c + ENNReal.ofReal b * ENNReal.ofReal c :=
      add_le_add (mul_le_mul' le_rfl hp) (mul_le_mul' le_rfl hq)
    _ = ENNReal.ofReal c := by
      rw [← add_mul, ← ENNReal.ofReal_add ha hb, hab]
      simp


theorem d003536
    (hclosed : ∀ θ c, IsClosed {p | risk θ p ≤ ENNReal.ofReal c})
    (anchor : Θ) (hanchor : ∀ p, risk anchor p = ENNReal.ofReal (‖p‖ ^ 2))
    (hne : (_root_.GD.N0230.N0632.d003532 risk).Nonempty)
    (cap : Θ → ℝ) (hcap : ∀ θ, 0 ≤ cap θ) :
    (∃ p, ∀ θ, risk θ p ≤ ENNReal.ofReal (cap θ)) ↔
      ∀ (F : Finset Θ) (w : Θ → ℝ), (∀ θ ∈ F, 0 ≤ w θ) → ∀ a : ℝ,
        (∀ p ∈ _root_.GD.N0230.N0632.d003532 risk, a ≤ ∑ θ ∈ F, w θ * (risk θ p).toReal) →
          a ≤ ∑ θ ∈ F, w θ * cap θ := by
  classical
  let e := toWeakSpace ℝ H
  let R : Θ → WeakSpace ℝ H → ℝ≥0∞ := fun θ p ↦ risk θ (e.symm p)
  let D : Set (WeakSpace ℝ H) := {p | e.symm p ∈ _root_.GD.N0230.N0632.d003532 risk}
  have hD : Convex ℝ D := (_root_.GD.N0230.N0632.d003533 risk hcombo).linear_preimage e.symm.toLinearMap
  have hDne : D.Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨e p, by simpa [D] using hp⟩
  have hcon : ∀ θ, ConvexOn ℝ D (fun p ↦ (R θ p).toReal) := by
    intro θ
    refine ⟨hD, ?_⟩
    intro p hp q hq a b ha hb hab
    simpa [R, map_add, map_smul] using
      (_root_.GD.N0230.N0632.d003534 risk hcombo θ).2
        (x := e.symm p) (y := e.symm q) hp hq ha hb hab
  have hset (θ : Θ) (c : ℝ) :
      {p | R θ p ≤ ENNReal.ofReal c} = e '' {p | risk θ p ≤ ENNReal.ofReal c} := by
    ext p
    constructor
    · intro hp
      exact ⟨e.symm p, hp, e.apply_symm_apply p⟩
    · rintro ⟨q, hq, rfl⟩
      simpa [R] using hq
  have hcl : ∀ θ c, IsClosed {p | R θ p ≤ ENNReal.ofReal c} := by
    intro θ c
    rw [hset]
    exact _root_.GD.N0230.N0708.d001175
      (_root_.GD.N0230.N0632.d003535 risk hcombo θ c) (hclosed θ c)
  have hc : IsCompact {p | R anchor p ≤ ENNReal.ofReal (cap anchor + 1)} := by
    rw [hset]
    apply _root_.GD.N0230.N0633.d001201
      (Real.sqrt (cap anchor + 1))
      (_root_.GD.N0230.N0632.d003535 risk hcombo anchor _) (hclosed anchor _)
    intro p hp
    change risk anchor p ≤ ENNReal.ofReal (cap anchor + 1) at hp
    rw [hanchor] at hp
    have hs : ‖p‖ ^ 2 ≤ cap anchor + 1 :=
      (ENNReal.ofReal_le_ofReal_iff (by linarith [hcap anchor])).mp hp
    nlinarith [norm_nonneg p, Real.sqrt_nonneg (cap anchor + 1),
      Real.sq_sqrt (show 0 ≤ cap anchor + 1 by linarith [hcap anchor])]
  have h := _root_.GD.N0230.N0626.d003530
    R cap D hD hDne (fun _ ↦ Iff.rfl) hcon hcap anchor hc hcl
  constructor
  · rintro ⟨p, hp⟩ F w hw a ha
    apply h.mp ⟨e p, by simpa [R] using hp⟩ F w hw a
    intro q hq
    exact ha (e.symm q) hq
  · intro ht
    have hw : ∃ p, ∀ θ, R θ p ≤ ENNReal.ofReal (cap θ) := by
      apply h.mpr
      intro F w hw a ha
      apply ht F w hw a
      intro p hp
      simpa [R, D] using ha (e p) (show e p ∈ D by simpa [D] using hp)
    obtain ⟨p, hp⟩ := hw
    exact ⟨e.symm p, hp⟩

end

end GD.N0230.N0632

#print axioms _root_.GD.N0230.N0632.d003536
