import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic



















set_option autoImplicit false
set_option warningAsError true

open Finset

namespace GD.N0106.N0428.N0765.N1629
noncomputable section

variable {ι κ E : Type*} [NormedAddCommGroup E] [CompleteSpace E]


theorem d008244 {f : ι → E} {g : ι → ℝ}
    (s : Finset ι) (hg : Summable g) (hfg : ∀ i, ‖f i‖ ≤ g i) :
    ‖(∑' i, f i) - ∑ i ∈ s, f i‖ ≤ (∑' i, g i) - ∑ i ∈ s, g i := by
  have hf : Summable f := hg.of_norm_bounded hfg
  have hfc := (s.hasSum_iff_compl).mp hf.hasSum
  have hgc := (s.hasSum_iff_compl).mp hg.hasSum
  exact hfc.norm_le_of_bounded hgc (fun i => hfg i)


theorem d008245 {f : ι × κ → E} {u : ι → ℝ} {v : κ → ℝ}
    (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ j, 0 ≤ v j)
    (hu : Summable u) (hv : Summable v)
    (hdom : ∀ p, ‖f p‖ ≤ u p.1 * v p.2) : Summable f :=
  (hu.mul_of_nonneg hv hu0 hv0).of_norm_bounded hdom



theorem d008246 {u : ι → ℝ} {v : κ → ℝ}
    (s : Finset ι) (t : Finset κ)
    (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ j, 0 ≤ v j)
    (hu : Summable u) (hv : Summable v) :
    (∑' p : {p : ι × κ // p ∉ s ×ˢ t}, u p.1.1 * v p.1.2) =
      ((∑' i, u i) - ∑ i ∈ s, u i) * (∑' j, v j) +
        (∑ i ∈ s, u i) * ((∑' j, v j) - ∑ j ∈ t, v j) := by
  have hp := hu.mul_of_nonneg hv hu0 hv0
  rw [((s ×ˢ t).hasSum_iff_compl.mp hp.hasSum).tsum_eq]
  rw [← hu.tsum_mul_tsum hv hp, Finset.sum_product, ← Finset.sum_mul_sum]
  ring


theorem d008247 {f : ι × κ → E} {u : ι → ℝ} {v : κ → ℝ}
    (s : Finset ι) (t : Finset κ)
    (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ j, 0 ≤ v j)
    (hu : Summable u) (hv : Summable v)
    (hdom : ∀ p, ‖f p‖ ≤ u p.1 * v p.2) :
    ‖(∑' p, f p) - ∑ p ∈ s ×ˢ t, f p‖ ≤
      ((∑' i, u i) - ∑ i ∈ s, u i) * (∑' j, v j) +
        (∑ i ∈ s, u i) * ((∑' j, v j) - ∑ j ∈ t, v j) := by
  have hp := hu.mul_of_nonneg hv hu0 hv0
  have h := _root_.GD.N0106.N0428.N0765.N1629.d008244 (s ×ˢ t) hp hdom
  have hs : (∑ p ∈ s ×ˢ t, u p.1 * v p.2) =
      (∑ i ∈ s, u i) * (∑ j ∈ t, v j) := by
    rw [Finset.sum_product, ← Finset.sum_mul_sum]
  rw [← hu.tsum_mul_tsum hv hp, hs] at h
  convert h using 1 <;> ring



theorem d008248
    {f : ι × κ → E} {u : ι → ℝ} {v : κ → ℝ} {TA V TB : ℝ}
    (s : Finset ι) (t : Finset κ)
    (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ j, 0 ≤ v j)
    (hu : Summable u) (hv : Summable v)
    (hdom : ∀ p, ‖f p‖ ≤ u p.1 * v p.2)
    (hV : (∑' j, v j) ≤ V)
    (hTA : (∑' i, u i) - ∑ i ∈ s, u i ≤ TA)
    (hTB : (∑' j, v j) - ∑ j ∈ t, v j ≤ TB) :
    ‖(∑' p, f p) - ∑ p ∈ s ×ˢ t, f p‖ ≤
      TA * V + (∑ i ∈ s, u i) * TB := by
  have hA0 : 0 ≤ (∑' i, u i) - ∑ i ∈ s, u i :=
    sub_nonneg.mpr (Summable.sum_le_tsum s (fun i _ => hu0 i) hu)
  have hTA0 : 0 ≤ TA := hA0.trans hTA
  have hV0 : 0 ≤ ∑' j, v j := tsum_nonneg hv0
  have hSA0 : 0 ≤ ∑ i ∈ s, u i := Finset.sum_nonneg (fun i _ => hu0 i)
  refine (_root_.GD.N0106.N0428.N0765.N1629.d008247 s t hu0 hv0 hu hv hdom).trans ?_
  exact add_le_add (mul_le_mul hTA hV hV0 hTA0)
    (mul_le_mul_of_nonneg_left hTB hSA0)


theorem d008249
    {f : ι × κ → E} {u : ι → ℝ} {v : κ → ℝ} {UA TA V TB : ℝ}
    (s : Finset ι) (t : Finset κ)
    (hu0 : ∀ i, 0 ≤ u i) (hv0 : ∀ j, 0 ≤ v j)
    (hu : Summable u) (hv : Summable v)
    (hdom : ∀ p, ‖f p‖ ≤ u p.1 * v p.2)
    (hUA : (∑' i, u i) ≤ UA) (hV : (∑' j, v j) ≤ V)
    (hTA : (∑' i, u i) - ∑ i ∈ s, u i ≤ TA)
    (hTB : (∑' j, v j) - ∑ j ∈ t, v j ≤ TB) :
    ‖(∑' p, f p) - ∑ p ∈ s ×ˢ t, f p‖ ≤ TA * V + UA * TB := by
  have hSB : (∑ j ∈ t, v j) ≤ ∑' j, v j :=
    Summable.sum_le_tsum t (fun j _ => hv0 j) hv
  have hTB0 : 0 ≤ TB := (sub_nonneg.mpr hSB).trans hTB
  have hSA : (∑ i ∈ s, u i) ≤ UA :=
    (Summable.sum_le_tsum s (fun i _ => hu0 i) hu).trans hUA
  exact (_root_.GD.N0106.N0428.N0765.N1629.d008248 s t hu0 hv0 hu hv hdom hV hTA hTB).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hSA hTB0))


theorem d008250
    {f : ι × κ → E} {u : ι → ℝ} {v₁ v₂ : κ → ℝ} {c₁ c₂ : ℝ}
    (hu0 : ∀ i, 0 ≤ u i) (hv₁0 : ∀ j, 0 ≤ v₁ j) (hv₂0 : ∀ j, 0 ≤ v₂ j)
    (hu : Summable u) (hv₁ : Summable v₁) (hv₂ : Summable v₂)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hdom : ∀ p, ‖f p‖ ≤ c₁ * u p.1 * v₁ p.2 + c₂ * u p.1 * v₂ p.2) :
    Summable f := by
  apply _root_.GD.N0106.N0428.N0765.N1629.d008245 hu0
    (fun j => add_nonneg (mul_nonneg hc₁ (hv₁0 j)) (mul_nonneg hc₂ (hv₂0 j)))
    hu ((hv₁.mul_left c₁).add (hv₂.mul_left c₂))
  intro p
  convert hdom p using 1 <;> ring




theorem d008251
    {f : ι × κ → E} {u : ι → ℝ} {v₁ v₂ : κ → ℝ}
    {c₁ c₂ UA V₁ V₂ TA TB₁ TB₂ : ℝ}
    (s : Finset ι) (t : Finset κ)
    (hu0 : ∀ i, 0 ≤ u i) (hv₁0 : ∀ j, 0 ≤ v₁ j) (hv₂0 : ∀ j, 0 ≤ v₂ j)
    (hu : Summable u) (hv₁ : Summable v₁) (hv₂ : Summable v₂)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hdom : ∀ p, ‖f p‖ ≤ c₁ * u p.1 * v₁ p.2 + c₂ * u p.1 * v₂ p.2)
    (hUA : (∑' i, u i) ≤ UA) (hV₁ : (∑' j, v₁ j) ≤ V₁)
    (hV₂ : (∑' j, v₂ j) ≤ V₂)
    (hTA : (∑' i, u i) - ∑ i ∈ s, u i ≤ TA)
    (hTB₁ : (∑' j, v₁ j) - ∑ j ∈ t, v₁ j ≤ TB₁)
    (hTB₂ : (∑' j, v₂ j) - ∑ j ∈ t, v₂ j ≤ TB₂) :
    ‖(∑' p, f p) - ∑ p ∈ s ×ˢ t, f p‖ ≤
      c₁ * (TA * V₁ + UA * TB₁) + c₂ * (TA * V₂ + UA * TB₂) := by
  let v : κ → ℝ := fun j => c₁ * v₁ j + c₂ * v₂ j
  have hv0 : ∀ j, 0 ≤ v j := fun j =>
    add_nonneg (mul_nonneg hc₁ (hv₁0 j)) (mul_nonneg hc₂ (hv₂0 j))
  have hv : Summable v := (hv₁.mul_left c₁).add (hv₂.mul_left c₂)
  have hdom' : ∀ p, ‖f p‖ ≤ u p.1 * v p.2 := by
    intro p
    dsimp [v]
    convert hdom p using 1 <;> ring
  have hV : (∑' j, v j) ≤ c₁ * V₁ + c₂ * V₂ := by
    dsimp [v]
    rw [(hv₁.mul_left c₁).tsum_add (hv₂.mul_left c₂), tsum_mul_left, tsum_mul_left]
    exact add_le_add (mul_le_mul_of_nonneg_left hV₁ hc₁)
      (mul_le_mul_of_nonneg_left hV₂ hc₂)
  have hTB : (∑' j, v j) - ∑ j ∈ t, v j ≤ c₁ * TB₁ + c₂ * TB₂ := by
    dsimp [v]
    rw [(hv₁.mul_left c₁).tsum_add (hv₂.mul_left c₂), tsum_mul_left, tsum_mul_left,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      _ = c₁ * ((∑' j, v₁ j) - ∑ j ∈ t, v₁ j) +
          c₂ * ((∑' j, v₂ j) - ∑ j ∈ t, v₂ j) := by ring
      _ ≤ c₁ * TB₁ + c₂ * TB₂ :=
        add_le_add (mul_le_mul_of_nonneg_left hTB₁ hc₁)
          (mul_le_mul_of_nonneg_left hTB₂ hc₂)
  have h := _root_.GD.N0106.N0428.N0765.N1629.d008249 s t hu0 hv0 hu hv hdom'
    hUA hV hTA hTB
  convert h using 1 <;> ring

end
end GD.N0106.N0428.N0765.N1629

#print axioms _root_.GD.N0106.N0428.N0765.N1629.d008244
#print axioms _root_.GD.N0106.N0428.N0765.N1629.d008245
#print axioms _root_.GD.N0106.N0428.N0765.N1629.d008246
#print axioms _root_.GD.N0106.N0428.N0765.N1629.d008247
#print axioms _root_.GD.N0106.N0428.N0765.N1629.d008248
#print axioms _root_.GD.N0106.N0428.N0765.N1629.d008249
#print axioms _root_.GD.N0106.N0428.N0765.N1629.d008250
#print axioms _root_.GD.N0106.N0428.N0765.N1629.d008251
