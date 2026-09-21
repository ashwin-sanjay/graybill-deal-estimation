import GD.Module0089
import GD.Module0043
import Mathlib.Analysis.Normed.Operator.Banach






























open Filter Set Topology
open scoped NNReal

namespace GD
namespace N0230
namespace N0570

open _root_.GD.N0230.N0708

variable {H E F : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]






def d001186 : Prop :=
  ∀ u : ℕ → H, Bornology.IsBounded (Set.range u) →
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧
      ∃ h : H,
        _root_.GD.N0230.N0708.d001170 ℝ (fun n ↦ u (k n)) atTop h




theorem d001187
    {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [CompleteSpace G]
    {u : ℕ → G} {h : G}
    (hu : _root_.GD.N0230.N0646.d000537 u h) :
    _root_.GD.N0230.N0708.d001170 ℝ u atTop h := by
  unfold _root_.GD.N0230.N0708.d001170
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto
    (topDualPairing ℝ G).flip ?_).2
  · intro f
    let z : G := (InnerProductSpace.toDual ℝ G).symm f
    have hz := hu z
    change Tendsto (fun i ↦ f (u i)) atTop (𝓝 (f h))
    rw [← (InnerProductSpace.toDual ℝ G).apply_symm_apply f]
    simpa only [z, InnerProductSpace.toDual_apply_apply,
      real_inner_comm] using hz
  · intro x y hxy
    apply ext_inner_left ℝ
    intro z
    have hz := DFunLike.congr_fun hxy
      (InnerProductSpace.toDual ℝ G z)
    change (InnerProductSpace.toDual ℝ G z) x =
      (InnerProductSpace.toDual ℝ G z) y at hz
    simpa only [InnerProductSpace.toDual_apply_apply] using hz




theorem d001188
    {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [CompleteSpace G]
    [TopologicalSpace.SeparableSpace G] :
    _root_.GD.N0230.N0570.d001186 (H := G) := by
  intro u hu
  obtain ⟨k, hk, h, hh⟩ :=
    _root_.GD.N0230.N0646.d000550
      (E := G) u hu
  exact ⟨k, hk, h, _root_.GD.N0230.N0570.d001187 hh⟩





theorem d001189
    (left : H →L[ℝ] E) (right : H →L[ℝ] F)
    (u : ℕ → H) (K R₁ R₂ : ℝ)
    (hK : 0 ≤ K)
    (hcontrol : ∀ h : H,
      ‖h‖ ≤ K * (‖left h‖ + ‖right h‖))
    (hleft : ∀ n, ‖left (u n)‖ ≤ R₁)
    (hright : ∀ n, ‖right (u n)‖ ≤ R₂) :
    Bornology.IsBounded (Set.range u) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨K * (R₁ + R₂), ?_⟩
  intro h hh
  obtain ⟨n, rfl⟩ := hh
  calc
    ‖u n‖ ≤ K * (‖left (u n)‖ + ‖right (u n)‖) := hcontrol (u n)
    _ ≤ K * (R₁ + R₂) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add (hleft n) (hright n)) hK








theorem d001190
    (hcompact : _root_.GD.N0230.N0570.d001186 (H := H))
    (left : H →L[ℝ] E) (right : H →L[ℝ] F)
    (u : ℕ → H) {x : E} {y : F}
    (hbounded : Bornology.IsBounded (Set.range u))
    (hx : _root_.GD.N0230.N0708.d001170 ℝ (fun n ↦ left (u n)) atTop x)
    (hy : _root_.GD.N0230.N0708.d001170 ℝ (fun n ↦ right (u n)) atTop y) :
    _root_.GD.N0230.N0708.d001177 left right x y := by
  obtain ⟨k, hk, h, hh⟩ := hcompact u hbounded
  exact _root_.GD.N0230.N0708.d001180 left right hh
    (hx.comp hk) (hy.comp hk)



theorem d001191
    (hcompact : _root_.GD.N0230.N0570.d001186 (H := H))
    (left : H →L[ℝ] E) (right : H →L[ℝ] F)
    (u : ℕ → H) {x : E} {y : F}
    (K R₁ R₂ : ℝ) (hK : 0 ≤ K)
    (hcontrol : ∀ h : H,
      ‖h‖ ≤ K * (‖left h‖ + ‖right h‖))
    (hleft : ∀ n, ‖left (u n)‖ ≤ R₁)
    (hright : ∀ n, ‖right (u n)‖ ≤ R₂)
    (hx : _root_.GD.N0230.N0708.d001170 ℝ (fun n ↦ left (u n)) atTop x)
    (hy : _root_.GD.N0230.N0708.d001170 ℝ (fun n ↦ right (u n)) atTop y) :
    _root_.GD.N0230.N0708.d001177 left right x y := by
  exact _root_.GD.N0230.N0570.d001190
    hcompact left right u
    (_root_.GD.N0230.N0570.d001189
      left right u K R₁ R₂ hK hcontrol hleft hright)
    hx hy



theorem d001192
    (hcompact : _root_.GD.N0230.N0570.d001186 (H := H))
    (left : H →L[ℝ] E) (right : H →L[ℝ] F)
    (C : Set H) (u : ℕ → H) {x : E} {y : F}
    (K R₁ R₂ : ℝ) (hK : 0 ≤ K)
    (hcontrol : ∀ h : H,
      ‖h‖ ≤ K * (‖left h‖ + ‖right h‖))
    (huC : ∀ n, u n ∈ C)
    (hleftC : ∀ h ∈ C, ‖left h‖ ≤ R₁)
    (hrightC : ∀ h ∈ C, ‖right h‖ ≤ R₂)
    (hx : _root_.GD.N0230.N0708.d001170 ℝ (fun n ↦ left (u n)) atTop x)
    (hy : _root_.GD.N0230.N0708.d001170 ℝ (fun n ↦ right (u n)) atTop y) :
    _root_.GD.N0230.N0708.d001177 left right x y := by
  exact _root_.GD.N0230.N0570.d001191
    hcompact left right u K R₁ R₂ hK hcontrol
    (fun n ↦ hleftC (u n) (huC n))
    (fun n ↦ hrightC (u n) (huC n)) hx hy










theorem d001193
    (left : H →L[ℝ] E) (right : H →L[ℝ] F)
    (haverage : ∀ h : H,
      2 * ‖h‖ ^ 2 = ‖left h‖ ^ 2 + ‖right h‖ ^ 2) :
    ∀ h : H, ‖h‖ ≤ ‖(left.prod right) h‖ := by
  intro h
  have hl : ‖left h‖ ≤ ‖(left.prod right) h‖ := by
    simp only [ContinuousLinearMap.prod_apply, Prod.norm_def]
    exact le_max_left _ _
  have hr : ‖right h‖ ≤ ‖(left.prod right) h‖ := by
    simp only [ContinuousLinearMap.prod_apply, Prod.norm_def]
    exact le_max_right _ _
  have hlsq : ‖left h‖ ^ 2 ≤ ‖(left.prod right) h‖ ^ 2 := by
    nlinarith [norm_nonneg (left h), norm_nonneg ((left.prod right) h)]
  have hrsq : ‖right h‖ ^ 2 ≤ ‖(left.prod right) h‖ ^ 2 := by
    nlinarith [norm_nonneg (right h), norm_nonneg ((left.prod right) h)]
  nlinarith [haverage h, norm_nonneg h,
    norm_nonneg ((left.prod right) h)]



theorem d001194
    (left : H →L[ℝ] E) (right : H →L[ℝ] F)
    (K : ℝ≥0)
    (hcontrol : ∀ h : H,
      ‖h‖ ≤ (K : ℝ) * ‖(left.prod right) h‖) :
    AntilipschitzWith K (left.prod right) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro a b
  simpa only [dist_eq_norm, map_sub] using hcontrol (a - b)



theorem d001195
    [CompleteSpace H]
    (left : H →L[ℝ] E) (right : H →L[ℝ] F)
    (K : ℝ≥0)
    (hcontrol : ∀ h : H,
      ‖h‖ ≤ (K : ℝ) * ‖(left.prod right) h‖) :
    IsClosed (Set.range (left.prod right)) := by
  exact (_root_.GD.N0230.N0570.d001194 left right K hcontrol).isClosed_range
    (left.prod right).uniformContinuous




theorem d001196
    [CompleteSpace H]
    (left : H →L[ℝ] E) (right : H →L[ℝ] F)
    (K : ℝ≥0)
    (hcontrol : ∀ h : H,
      ‖h‖ ≤ (K : ℝ) * ‖(left.prod right) h‖)
    {I : Type*} {u : I → H} {l : Filter I} [NeBot l]
    {x : E} {y : F}
    (hx : _root_.GD.N0230.N0708.d001170 ℝ (fun i ↦ left (u i)) l x)
    (hy : _root_.GD.N0230.N0708.d001170 ℝ (fun i ↦ right (u i)) l y) :
    _root_.GD.N0230.N0708.d001177 left right x y := by
  exact _root_.GD.N0230.N0708.d001179
    left right
    (_root_.GD.N0230.N0570.d001195 left right K hcontrol)
    hx hy



theorem d001197
    [CompleteSpace H]
    (left : H →L[ℝ] E) (right : H →L[ℝ] F)
    (haverage : ∀ h : H,
      2 * ‖h‖ ^ 2 = ‖left h‖ ^ 2 + ‖right h‖ ^ 2)
    {I : Type*} {u : I → H} {l : Filter I} [NeBot l]
    {x : E} {y : F}
    (hx : _root_.GD.N0230.N0708.d001170 ℝ (fun i ↦ left (u i)) l x)
    (hy : _root_.GD.N0230.N0708.d001170 ℝ (fun i ↦ right (u i)) l y) :
    _root_.GD.N0230.N0708.d001177 left right x y := by
  exact _root_.GD.N0230.N0570.d001196 left right 1
    (by simpa using _root_.GD.N0230.N0570.d001193 left right haverage)
    hx hy

#print axioms _root_.GD.N0230.N0570.d001189
#print axioms _root_.GD.N0230.N0570.d001192
#print axioms _root_.GD.N0230.N0570.d001195
#print axioms _root_.GD.N0230.N0570.d001196
#print axioms _root_.GD.N0230.N0570.d001197

end N0570
end N0230
end GD
