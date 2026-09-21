import Mathlib.MeasureTheory.Integral.Bochner.Set
import GD.Module0087



































open MeasureTheory Filter

namespace GD
namespace N0230
namespace N0717

noncomputable section

variable {Θ : Type*} [MeasurableSpace Θ]





theorem d001324
    {μ : Measure Θ} {φ : Θ → ℝ} {A B : Set Θ}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hφA : IntegrableOn φ A μ) (hφB : IntegrableOn φ B μ) :
    (∫ θ in A, φ θ ∂μ) - ∫ θ in B, φ θ ∂μ =
      (∫ θ in A \ B, φ θ ∂μ) - ∫ θ in B \ A, φ θ ∂μ := by
  have hdisjA : Disjoint (A ∩ B) (A \ B) :=
    Set.disjoint_left.mpr fun _x hx hx' ↦ hx'.2 hx.2
  have hdisjB : Disjoint (B ∩ A) (B \ A) :=
    Set.disjoint_left.mpr fun _x hx hx' ↦ hx'.2 hx.2
  have hAsplit : (∫ θ in A, φ θ ∂μ) =
      (∫ θ in A ∩ B, φ θ ∂μ) + ∫ θ in A \ B, φ θ ∂μ := by
    rw [← setIntegral_union hdisjA (hA.diff hB)
      (hφA.mono_set Set.inter_subset_left)
      (hφA.mono_set Set.diff_subset), Set.inter_union_diff]
  have hBsplit : (∫ θ in B, φ θ ∂μ) =
      (∫ θ in B ∩ A, φ θ ∂μ) + ∫ θ in B \ A, φ θ ∂μ := by
    rw [← setIntegral_union hdisjB (hB.diff hA)
      (hφB.mono_set Set.inter_subset_left)
      (hφB.mono_set Set.diff_subset), Set.inter_union_diff]
  rw [hAsplit, hBsplit, Set.inter_comm B A]
  ring



theorem d001325
    {μ : Measure Θ} {φ : Θ → ℝ} {A B : Set Θ} {M : ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hφA : IntegrableOn φ A μ) (hφB : IntegrableOn φ B μ)
    (hAB : μ (A \ B) < ⊤) (hBA : μ (B \ A) < ⊤)
    (hM : ∀ θ, |φ θ| ≤ M) :
    |(∫ θ in A, φ θ ∂μ) - ∫ θ in B, φ θ ∂μ| ≤
      M * ((μ (A \ B)).toReal + (μ (B \ A)).toReal) := by
  rw [_root_.GD.N0230.N0717.d001324 hA hB hφA hφB]
  have h1 : |∫ θ in A \ B, φ θ ∂μ| ≤ M * (μ (A \ B)).toReal := by
    have := norm_setIntegral_le_of_norm_le_const (μ := μ)
      (f := φ) (s := A \ B) hAB
      (fun θ _ ↦ by simpa [Real.norm_eq_abs] using hM θ)
    simpa [Real.norm_eq_abs, measureReal_def] using this
  have h2 : |∫ θ in B \ A, φ θ ∂μ| ≤ M * (μ (B \ A)).toReal := by
    have := norm_setIntegral_le_of_norm_le_const (μ := μ)
      (f := φ) (s := B \ A) hBA
      (fun θ _ ↦ by simpa [Real.norm_eq_abs] using hM θ)
    simpa [Real.norm_eq_abs, measureReal_def] using this
  calc
    |(∫ θ in A \ B, φ θ ∂μ) - ∫ θ in B \ A, φ θ ∂μ| =
        |(∫ θ in A \ B, φ θ ∂μ) + -(∫ θ in B \ A, φ θ ∂μ)| := by
      rw [sub_eq_add_neg]
    _ ≤ |∫ θ in A \ B, φ θ ∂μ| + |-(∫ θ in B \ A, φ θ ∂μ)| :=
      abs_add_le _ _
    _ = |∫ θ in A \ B, φ θ ∂μ| + |∫ θ in B \ A, φ θ ∂μ| := by
      rw [abs_neg]
    _ ≤ M * (μ (A \ B)).toReal + M * (μ (B \ A)).toReal :=
      add_le_add h1 h2
    _ = M * ((μ (A \ B)).toReal + (μ (B \ A)).toReal) := by ring






theorem d001326
    {μ : Measure Θ} {τ : Θ → Θ}
    (hpres : MeasurePreserving τ μ μ) (hemb : MeasurableEmbedding τ)
    {φ φ' : Θ → ℝ} {c : ℝ}
    (hequi : ∀ θ, φ' (τ θ) = c * φ θ) (K : Set Θ) :
    (∫ θ in K, φ' θ ∂μ) = c * ∫ θ in τ ⁻¹' K, φ θ ∂μ := by
  rw [← hpres.setIntegral_preimage_emb hemb φ' K]
  simp only [hequi]
  exact integral_const_mul c φ





theorem d001327
    {μ : Measure Θ} {τ : Θ → Θ}
    (hpres : MeasurePreserving τ μ μ) (hemb : MeasurableEmbedding τ)
    {φ φ' : Θ → ℝ} {c : ℝ}
    (hequi : ∀ θ, φ' (τ θ) = c * φ θ)
    {K : Set Θ} (hK : MeasurableSet K)
    (hφK : IntegrableOn φ K μ)
    (hφτK : IntegrableOn φ (τ ⁻¹' K) μ) :
    (∫ θ in K, φ' θ ∂μ) - c * ∫ θ in K, φ θ ∂μ =
      c * ((∫ θ in (τ ⁻¹' K) \ K, φ θ ∂μ) -
        ∫ θ in K \ (τ ⁻¹' K), φ θ ∂μ) := by
  rw [_root_.GD.N0230.N0717.d001326 hpres hemb hequi K, ← mul_sub]
  congr 1
  exact _root_.GD.N0230.N0717.d001324
    (hemb.measurable hK) hK hφτK hφK


theorem d001328
    {μ : Measure Θ} {τ : Θ → Θ}
    (hpres : MeasurePreserving τ μ μ) (hemb : MeasurableEmbedding τ)
    {φ φ' : Θ → ℝ} {c M : ℝ}
    (hequi : ∀ θ, φ' (τ θ) = c * φ θ)
    {K : Set Θ} (hK : MeasurableSet K)
    (hφK : IntegrableOn φ K μ)
    (hφτK : IntegrableOn φ (τ ⁻¹' K) μ)
    (hM : ∀ θ, |φ θ| ≤ M) (hc : 0 ≤ c)
    (hfin1 : μ ((τ ⁻¹' K) \ K) < ⊤)
    (hfin2 : μ (K \ (τ ⁻¹' K)) < ⊤) :
    |(∫ θ in K, φ' θ ∂μ) - c * ∫ θ in K, φ θ ∂μ| ≤
      c * (M * ((μ ((τ ⁻¹' K) \ K)).toReal +
        (μ (K \ (τ ⁻¹' K))).toReal)) := by
  rw [_root_.GD.N0230.N0717.d001326 hpres hemb hequi K, ← mul_sub,
    abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left
    (_root_.GD.N0230.N0717.d001325
      (hemb.measurable hK) hK hφτK hφK hfin1 hfin2 hM) hc



variable {H : Type*} {G : Type*} [Monoid G] [MulAction G H]


def d001329 (μ : Measure Θ) (K : ℕ → Set Θ) (a : ℕ → ℝ)
    (φ : H → Θ → ℝ) (n : ℕ) (d : H) : ℝ :=
  a n * ∫ θ in K n, φ d θ ∂μ





theorem d001330
    {μ : Measure Θ} {K : ℕ → Set Θ} {a : ℕ → ℝ} {φ : H → Θ → ℝ}
    {τ : Θ → Θ} {c : ℝ} {g : G} {d : H} {M : ℝ}
    (hpres : MeasurePreserving τ μ μ) (hemb : MeasurableEmbedding τ)
    (hequi : ∀ θ, φ (g • d) (τ θ) = c * φ d θ)
    (hK : ∀ n, MeasurableSet (K n))
    (hφK : ∀ n, IntegrableOn (φ d) (K n) μ)
    (hφτK : ∀ n, IntegrableOn (φ d) (τ ⁻¹' K n) μ)
    (hM : ∀ θ, |φ d θ| ≤ M) (hc : 0 ≤ c) (ha : ∀ n, 0 ≤ a n)
    (hfin : ∀ n, μ ((τ ⁻¹' K n) \ K n) < ⊤ ∧
      μ (K n \ (τ ⁻¹' K n)) < ⊤)
    (hfolner : Tendsto (fun n ↦ a n *
      ((μ ((τ ⁻¹' K n) \ K n)).toReal +
        (μ (K n \ (τ ⁻¹' K n))).toReal)) atTop (nhds 0)) :
    Tendsto (fun n ↦ _root_.GD.N0230.N0717.d001329 μ K a φ n (g • d) -
      c * _root_.GD.N0230.N0717.d001329 μ K a φ n d) atTop (nhds 0) := by
  have hbound : ∀ n,
      ‖_root_.GD.N0230.N0717.d001329 μ K a φ n (g • d) -
        c * _root_.GD.N0230.N0717.d001329 μ K a φ n d‖ ≤
      c * M * (a n * ((μ ((τ ⁻¹' K n) \ K n)).toReal +
        (μ (K n \ (τ ⁻¹' K n))).toReal)) := by
    intro n
    have hdef := _root_.GD.N0230.N0717.d001328 hpres hemb hequi
      (hK n) (hφK n) (hφτK n) hM hc (hfin n).1 (hfin n).2
    calc
      ‖_root_.GD.N0230.N0717.d001329 μ K a φ n (g • d) -
          c * _root_.GD.N0230.N0717.d001329 μ K a φ n d‖ =
          |a n * ((∫ θ in K n, φ (g • d) θ ∂μ) -
            c * ∫ θ in K n, φ d θ ∂μ)| := by
        rw [Real.norm_eq_abs]
        congr 1
        unfold _root_.GD.N0230.N0717.d001329
        ring
      _ = a n * |(∫ θ in K n, φ (g • d) θ ∂μ) -
            c * ∫ θ in K n, φ d θ ∂μ| := by
        rw [abs_mul, abs_of_nonneg (ha n)]
      _ ≤ a n * (c * (M * ((μ ((τ ⁻¹' K n) \ K n)).toReal +
            (μ (K n \ (τ ⁻¹' K n))).toReal))) :=
        mul_le_mul_of_nonneg_left hdef (ha n)
      _ = c * M * (a n * ((μ ((τ ⁻¹' K n) \ K n)).toReal +
            (μ (K n \ (τ ⁻¹' K n))).toReal)) := by ring
  have hlim0 : Tendsto (fun n ↦ c * M * (a n *
      ((μ ((τ ⁻¹' K n) \ K n)).toReal +
        (μ (K n \ (τ ⁻¹' K n))).toReal))) atTop (nhds 0) := by
    simpa using hfolner.const_mul (c * M)
  exact squeeze_zero_norm hbound hlim0










theorem d001331
    {μ : Measure Θ} {K : ℕ → Set Θ} {a : ℕ → ℝ}
    {φ : H → Θ → ℝ} {charge : H → ℝ} {character : G → ℝ}
    {τ : G → Θ → Θ} {M : H → ℝ}
    (hpres : ∀ g, MeasurePreserving (τ g) μ μ)
    (hemb : ∀ g, MeasurableEmbedding (τ g))
    (hequi : ∀ g d θ, φ (g • d) (τ g θ) = character g * φ d θ)
    (hK : ∀ n, MeasurableSet (K n))
    (hint : ∀ d n, IntegrableOn (φ d) (K n) μ)
    (hint' : ∀ g d n, IntegrableOn (φ d) ((τ g) ⁻¹' K n) μ)
    (hM : ∀ d θ, |φ d θ| ≤ M d)
    (hchar0 : ∀ g : G, 0 ≤ character g)
    (ha : ∀ n, 0 ≤ a n)
    (hfin : ∀ (g : G) (n : ℕ),
      μ (((τ g) ⁻¹' K n) \ K n) < ⊤ ∧
        μ (K n \ ((τ g) ⁻¹' K n)) < ⊤)
    (hfolner : ∀ g : G, Tendsto (fun n ↦ a n *
      ((μ (((τ g) ⁻¹' K n) \ K n)).toReal +
        (μ (K n \ ((τ g) ⁻¹' K n))).toReal)) atTop (nhds 0))
    (hlimit : ∀ d, Tendsto (fun n ↦ _root_.GD.N0230.N0717.d001329 μ K a φ n d)
      atTop (nhds (charge d))) :
    ∀ (g : G) (d : H), charge (g • d) = character g * charge d := by
  apply
    _root_.GD.N0230.N0704.d001164
      (fun n d ↦ _root_.GD.N0230.N0717.d001329 μ K a φ n d) charge character hlimit
  intro g d
  exact _root_.GD.N0230.N0717.d001330 (hpres g) (hemb g)
    (fun θ ↦ hequi g d θ) hK (hint d) (hint' g d) (hM d)
    (hchar0 g) ha (hfin g) (hfolner g)

end

end N0717
end N0230
end GD

#print axioms _root_.GD.N0230.N0717.d001324
#print axioms _root_.GD.N0230.N0717.d001326
#print axioms _root_.GD.N0230.N0717.d001327
#print axioms _root_.GD.N0230.N0717.d001330
#print axioms _root_.GD.N0230.N0717.d001331
