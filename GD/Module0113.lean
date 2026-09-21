import Mathlib.Analysis.InnerProductSpace.Continuous
import GD.Module0112









































open scoped RealInnerProductSpace
open Filter

namespace GD
namespace N0230
namespace N0576

noncomputable section

open _root_.GD.N0230.N0669
open _root_.GD.N0230.N0574

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Θ : Type*} (ψ : Θ → H) (m : H)


def d001421 (c R : ℝ) (h₀ : H) : Set H :=
  {v : H | ‖v‖ * c ≤ R * ⟪h₀, v⟫}


theorem d001422 {c R : ℝ} {h₀ : H}
    (hc : 0 ≤ c)
    (hfloor : ∀ θ, c ≤ ⟪h₀, ψ θ - m⟫)
    (hR : ∀ θ, ‖ψ θ - m‖ ≤ R) (θ : Θ) :
    ψ θ - m ∈ _root_.GD.N0230.N0576.d001421 c R h₀ := by
  unfold _root_.GD.N0230.N0576.d001421
  rw [Set.mem_setOf_eq]
  have h1 : ‖ψ θ - m‖ * c ≤ R * c :=
    mul_le_mul_of_nonneg_right (hR θ) hc
  have hR0 : (0 : ℝ) ≤ R := le_trans (norm_nonneg _) (hR θ)
  have h2 : R * c ≤ R * ⟪h₀, ψ θ - m⟫ :=
    mul_le_mul_of_nonneg_left (hfloor θ) hR0
  linarith

theorem d001423 (c R : ℝ) (h₀ : H) :
    (0 : H) ∈ _root_.GD.N0230.N0576.d001421 c R h₀ := by
  unfold _root_.GD.N0230.N0576.d001421
  simp

theorem d001424 {c R : ℝ} {h₀ : H} (hc : 0 ≤ c)
    {v v' : H} (hv : v ∈ _root_.GD.N0230.N0576.d001421 c R h₀)
    (hv' : v' ∈ _root_.GD.N0230.N0576.d001421 c R h₀) :
    v + v' ∈ _root_.GD.N0230.N0576.d001421 c R h₀ := by
  unfold _root_.GD.N0230.N0576.d001421 at hv hv' ⊢
  rw [Set.mem_setOf_eq] at hv hv' ⊢
  have htri : ‖v + v'‖ * c ≤ ‖v‖ * c + ‖v'‖ * c := by
    have := norm_add_le v v'
    nlinarith [this, hc]
  rw [inner_add_right]
  linarith

theorem d001425 {c R : ℝ} {h₀ : H}
    {v : H} {t : ℝ} (ht : 0 ≤ t)
    (hv : v ∈ _root_.GD.N0230.N0576.d001421 c R h₀) :
    t • v ∈ _root_.GD.N0230.N0576.d001421 c R h₀ := by
  unfold _root_.GD.N0230.N0576.d001421 at hv ⊢
  rw [Set.mem_setOf_eq] at hv ⊢
  rw [norm_smul, real_inner_smul_right, Real.norm_eq_abs,
    abs_of_nonneg ht]
  nlinarith [hv, ht]



theorem d001426 {c R : ℝ} {h₀ : H}
    (hc : 0 ≤ c)
    (hfloor : ∀ θ, c ≤ ⟪h₀, ψ θ - m⟫)
    (hR : ∀ θ, ‖ψ θ - m‖ ≤ R)
    {k : ℕ} (lam : Fin k → ℝ) (θs : Fin k → Θ)
    (hlam : ∀ i, 0 ≤ lam i) :
    (∑ i, lam i • (ψ (θs i) - m)) ∈ _root_.GD.N0230.N0576.d001421 c R h₀ := by
  apply Finset.sum_induction
  · exact fun a b ha hb ↦ _root_.GD.N0230.N0576.d001424 hc ha hb
  · exact _root_.GD.N0230.N0576.d001423 c R h₀
  · intro i _
    exact _root_.GD.N0230.N0576.d001425 (hlam i)
      (_root_.GD.N0230.N0576.d001422 ψ m hc hfloor hR (θs i))


theorem d001427 {c R : ℝ} {h₀ : H}
    {v : ℕ → H} {w : H}
    (hv : ∀ n, v n ∈ _root_.GD.N0230.N0576.d001421 c R h₀)
    (hlim : Tendsto v atTop (nhds w)) :
    w ∈ _root_.GD.N0230.N0576.d001421 c R h₀ := by
  unfold _root_.GD.N0230.N0576.d001421 at hv ⊢
  rw [Set.mem_setOf_eq]
  have h1 : Tendsto (fun n ↦ ‖v n‖ * c) atTop (nhds (‖w‖ * c)) :=
    hlim.norm.mul_const c
  have h2 : Tendsto (fun n ↦ R * ⟪h₀, v n⟫) atTop
      (nhds (R * ⟪h₀, w⟫)) :=
    (Tendsto.inner tendsto_const_nhds hlim).const_mul R
  exact le_of_tendsto_of_tendsto' h1 h2 fun n ↦ hv n




theorem d001428 {c R : ℝ} {h₀ : H}
    (hc : 0 < c) (hR0 : 0 < R)
    {w : H} (hw : w ∈ _root_.GD.N0230.N0576.d001421 c R h₀) (hne : w ≠ 0) :
    c * ‖w‖ / R ≤ ⟪h₀, w⟫ ∧ 0 < ⟪h₀, w⟫ := by
  unfold _root_.GD.N0230.N0576.d001421 at hw
  rw [Set.mem_setOf_eq] at hw
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hne
  constructor
  · rw [div_le_iff₀ hR0]
    nlinarith [hw]
  · have h1 : 0 < c * ‖w‖ / R := by positivity
    have h2 : c * ‖w‖ / R ≤ ⟪h₀, w⟫ := by
      rw [div_le_iff₀ hR0]
      nlinarith [hw]
    linarith




theorem d001429 {c R : ℝ} {h₀ : H}
    (hc : 0 < c) (hR0 : 0 < R)
    {w : H} (hw : w ∈ _root_.GD.N0230.N0576.d001421 c R h₀)
    (hblind : ⟪h₀, w⟫ ≤ 0) :
    w = 0 := by
  by_contra hne
  have := (_root_.GD.N0230.N0576.d001428 hc hR0 hw hne).2
  linarith








theorem d001430
    {c R : ℝ} {h₀ w : H}
    (hc : 0 < c) (hR0 : 0 < R) (hu0 : h₀ ≠ 0)
    (hfloor : ∀ θ, c ≤ ⟪h₀, ψ θ - m⟫)
    (hR : ∀ θ, ‖ψ θ - m‖ ≤ R)
    {v : ℕ → H}
    (hcombo : ∀ n, ∃ (k : ℕ) (lam : Fin k → ℝ) (θs : Fin k → Θ),
      (∀ i, 0 ≤ lam i) ∧ v n = ∑ i, lam i • (ψ (θs i) - m))
    (hlim : Tendsto v atTop (nhds w))
    (hw : w ≠ 0) :
    (c * ‖w‖ / R ≤ ⟪h₀, w⟫ ∧ 0 < ⟪h₀, w⟫) ∧
      ∀ η : ℝ, 0 < η →
        η < 4 * ⟪h₀, w⟫ * c / ‖h₀‖ ^ 2 →
        Convex ℝ (_root_.GD.N0230.N0574.d001411 ψ m w η) ∧
          (_root_.GD.N0230.N0574.d001411 ψ m w η).Nonempty ∧
          ∃ p ∈ _root_.GD.N0230.N0574.d001411 ψ m w η,
            ∀ θ, 0 < ‖m - ψ θ‖ ^ 2 - ‖p - ψ θ‖ ^ 2 := by
  have hvK : ∀ n, v n ∈ _root_.GD.N0230.N0576.d001421 c R h₀ := by
    intro n
    obtain ⟨k, lam, θs, hlam, hvn⟩ := hcombo n
    rw [hvn]
    exact _root_.GD.N0230.N0576.d001426 ψ m hc.le hfloor hR
      lam θs hlam
  have hwK := _root_.GD.N0230.N0576.d001427 hvK hlim
  have hslope := _root_.GD.N0230.N0576.d001428 hc hR0 hwK hw
  refine ⟨hslope, fun η hη hbudget ↦ ?_⟩
  exact _root_.GD.N0230.N0574.d001414 ψ m w hu0 hfloor hc
    (le_refl _) hslope.2 hη hbudget

end

end N0576
end N0230
end GD

#print axioms _root_.GD.N0230.N0576.d001422
#print axioms _root_.GD.N0230.N0576.d001426
#print axioms _root_.GD.N0230.N0576.d001427
#print axioms _root_.GD.N0230.N0576.d001428
#print axioms _root_.GD.N0230.N0576.d001429
#print axioms _root_.GD.N0230.N0576.d001430
