import GD.Module0159
import Mathlib.Order.CompleteLattice.Basic

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0079.N0323

universe u v w x y

variable {Θ : Type u} {D : Type v} {S : Type w} {U : Type x}
variable {V : Type y} [Preorder V]

def d008225 (R : Θ → D → V) (e d : D) : Prop := ∀ θ, R θ e ≤ R θ d

def d008226 (R : Θ → D → V) (e d : D) : Prop :=
  _root_.GD.N0079.N0323.d008225 R e d ∧ ∃ θ, R θ e < R θ d

def d008227 (R : Θ → D → V) (d : D) : Prop := ¬ ∃ e, _root_.GD.N0079.N0323.d008226 R e d

def d008228 (R : Θ → D → V) (d : D) : Prop := ∀ e, _root_.GD.N0079.N0323.d008225 R e d → e = d

structure d008229 (R : Θ → D → V) (r : Θ → S → V) where
  embed : S → D
  project : D → S
  retract : ∀ s, project (embed s) = s
  preserve : ∀ θ s, R θ (embed s) = r θ s
  improve : ∀ θ d, r θ (project d) ≤ R θ d

namespace d008229

variable {R : Θ → D → V} {r : Θ → S → V} {q : Θ → U → V}
variable (F : _root_.GD.N0079.N0323.d008229 R r)

theorem d008230 : Function.Injective F.embed := by
  intro s t h
  have := congrArg F.project h
  simpa only [F.retract] using this

theorem d008231 (s t : S) : _root_.GD.N0079.N0323.d008225 R (F.embed s) (F.embed t) ↔ _root_.GD.N0079.N0323.d008225 r s t := by
  simp only [_root_.GD.N0079.N0323.d008225, F.preserve]

theorem d008232 (s t : S) : _root_.GD.N0079.N0323.d008226 R (F.embed s) (F.embed t) ↔ _root_.GD.N0079.N0323.d008226 r s t := by
  simp only [_root_.GD.N0079.N0323.d008226, F.d008231, F.preserve]

theorem d008233 {d : D} {s : S} (hd : _root_.GD.N0079.N0323.d008225 R d (F.embed s)) :
    _root_.GD.N0079.N0323.d008225 r (F.project d) s := by
  intro θ
  exact (F.improve θ d).trans ((hd θ).trans_eq (F.preserve θ s))

theorem d008234 {d : D} {s : S} (hd : _root_.GD.N0079.N0323.d008226 R d (F.embed s)) :
    _root_.GD.N0079.N0323.d008226 r (F.project d) s := by
  refine ⟨F.d008233 hd.1, ?_⟩
  obtain ⟨θ, hθ⟩ := hd.2
  exact ⟨θ, (lt_of_le_of_lt (F.improve θ d) hθ).trans_eq (F.preserve θ s)⟩

theorem d008235 (s : S) : _root_.GD.N0079.N0323.d008227 R (F.embed s) ↔ _root_.GD.N0079.N0323.d008227 r s := by
  constructor
  · intro h hs
    obtain ⟨t, ht⟩ := hs
    exact h ⟨F.embed t, (F.d008232 t s).mpr ht⟩
  · intro h hd
    obtain ⟨d, hd⟩ := hd
    exact h ⟨F.project d, F.d008234 hd⟩

theorem d008236 (s : S)
    (hrigid : ∀ d, _root_.GD.N0079.N0323.d008225 R d (F.embed s) → F.project d = s → d = F.embed s) :
    _root_.GD.N0079.N0323.d008228 R (F.embed s) ↔ _root_.GD.N0079.N0323.d008228 r s := by
  constructor
  · intro h t ht
    exact F.d008230 (h (F.embed t) ((F.d008231 t s).mpr ht))
  · intro h d hd
    exact hrigid d hd (h (F.project d) (F.d008233 hd))

theorem d008237 (s : S) :
    _root_.GD.N0079.N0323.d008228 R (F.embed s) ↔ _root_.GD.N0079.N0323.d008228 r s ∧
      (∀ d, _root_.GD.N0079.N0323.d008225 R d (F.embed s) → F.project d = s → d = F.embed s) := by
  constructor
  · intro h
    refine ⟨?_, fun d hd _ => h d hd⟩
    intro t ht
    exact F.d008230 (h (F.embed t) ((F.d008231 t s).mpr ht))
  · rintro ⟨h, hrigid⟩
    exact (F.d008236 s hrigid).mpr h

include F in
theorem d008238 (B : Θ → V) :
    (∃ d : D, ∀ θ, R θ d ≤ B θ) ↔ (∃ s : S, ∀ θ, r θ s ≤ B θ) := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨F.project d, fun θ => (F.improve θ d).trans (hd θ)⟩
  · rintro ⟨s, hs⟩
    exact ⟨F.embed s, fun θ => (F.preserve θ s).trans_le (hs θ)⟩

def d008239 (G : _root_.GD.N0079.N0323.d008229 r q) : _root_.GD.N0079.N0323.d008229 R q where
  embed := F.embed ∘ G.embed
  project := G.project ∘ F.project
  retract s := by simp only [Function.comp_apply, F.retract, G.retract]
  preserve θ s := by simp only [Function.comp_apply, F.preserve, G.preserve]
  improve θ d := (G.improve θ (F.project d)).trans (F.improve θ d)

include F in
theorem d008240 {W : Type*} [CompleteLattice W]
    (Φ : (Θ → V) → W) (hΦ : Monotone Φ) :
    (⨅ d : D, Φ (fun θ => R θ d)) = ⨅ s : S, Φ (fun θ => r θ s) := by
  apply le_antisymm
  · apply le_iInf
    intro s
    exact iInf_le_of_le (F.embed s) (by simp only [F.preserve, le_refl])
  · apply le_iInf
    intro d
    exact (iInf_le (fun s : S => Φ (fun θ => r θ s)) (F.project d)).trans
      (hΦ (fun θ => F.improve θ d))

include F in
theorem d008241 {W : Type*} [Preorder W]
    (Φ : (Θ → V) → W) (hΦ : Monotone Φ) :
    (∃ d : D, ∀ e : D, Φ (fun θ => R θ d) ≤ Φ (fun θ => R θ e)) ↔
      (∃ s : S, ∀ t : S, Φ (fun θ => r θ s) ≤ Φ (fun θ => r θ t)) := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨F.project d, fun t => ?_⟩
    have h := hd (F.embed t)
    simp only [F.preserve] at h
    exact (hΦ (fun θ => F.improve θ d)).trans h
  · rintro ⟨s, hs⟩
    refine ⟨F.embed s, fun d => ?_⟩
    simp only [F.preserve]
    exact (hs (F.project d)).trans (hΦ (fun θ => F.improve θ d))

end d008229

open scoped ENNReal

variable {R : Θ → D → ℝ≥0∞} {r : Θ → S → ℝ≥0∞}

theorem d008242 (F : _root_.GD.N0079.N0323.d008229 R r)
    (θ₀ : Θ) (τ : D → ℝ≥0∞)
    (hdecomp : ∀ d, R θ₀ d = r θ₀ (F.project d) + τ d)
    (hfaithful : ∀ d, τ d = 0 → d = F.embed (F.project d))
    (s : S) (hfinite : r θ₀ s ≠ ⊤) :
    _root_.GD.N0079.N0323.d008228 R (F.embed s) ↔ _root_.GD.N0079.N0323.d008228 r s := by
  apply F.d008236 s
  intro d hd hp
  have hsum : r θ₀ s + τ d ≤ r θ₀ s := by
    have h := hd θ₀
    rwa [hdecomp, hp, F.preserve] at h
  have hz := _root_.GD.N0232.N0719.N1001.d001795.d001797
    hfinite hsum
  simpa only [hp] using hfaithful d hz

theorem d008243 {q : Θ → U → ℝ≥0∞}
    (F : _root_.GD.N0079.N0323.d008229 R r) (G : _root_.GD.N0079.N0323.d008229 r q)
    (τ : Θ → D → ℝ≥0∞) (υ : Θ → S → ℝ≥0∞)
    (hF : ∀ θ d, R θ d = r θ (F.project d) + τ θ d)
    (hG : ∀ θ s, r θ s = q θ (G.project s) + υ θ s)
    (θ : Θ) (d : D) :
    R θ d = q θ ((F.d008239 G).project d) + (υ θ (F.project d) + τ θ d) := by
  rw [hF, hG, add_assoc]
  rfl

end GD.N0079.N0323

#print axioms _root_.GD.N0079.N0323.d008229.d008235
#print axioms _root_.GD.N0079.N0323.d008229.d008236
#print axioms _root_.GD.N0079.N0323.d008229.d008237
#print axioms _root_.GD.N0079.N0323.d008229.d008238
#print axioms _root_.GD.N0079.N0323.d008229.d008240
#print axioms _root_.GD.N0079.N0323.d008229.d008241
#print axioms _root_.GD.N0079.N0323.d008242
#print axioms _root_.GD.N0079.N0323.d008243
