import GD.Module0576
















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1638
noncomputable section

open MeasureTheory Set Metric Complex Filter
open _root_.GD.N0106.N0428.N0765.N1532
open scoped Topology BigOperators

def d008452 (a b δ : ℝ) (n : ℤ × ℤ) : Set (ℝ × ℝ) :=
  _root_.GD.N0106.N0428.N0765.N1532.d007575 a δ n.1 ×ˢ _root_.GD.N0106.N0428.N0765.N1532.d007575 b δ n.2

def d008453 (A : ℝ × ℝ → ℝ) (a b δ : ℝ) (n : ℤ × ℤ) : ℝ :=
  (∫ t in _root_.GD.N0106.N0428.N0765.N1638.d008452 a b δ n, A t ∂(volume.prod volume)) / δ ^ 2

theorem d008454 {δ : ℝ} (hsep : 2 * δ < 1) (a b : ℝ) :
    Pairwise (fun i j : ℤ × ℤ => Disjoint (_root_.GD.N0106.N0428.N0765.N1638.d008452 a b δ i) (_root_.GD.N0106.N0428.N0765.N1638.d008452 a b δ j)) := by
  intro i j hij
  apply Set.disjoint_prod.mpr
  by_cases hfirst : i.1 = j.1
  · have hsecond : i.2 ≠ j.2 := by
      intro hsecond
      exact hij (Prod.ext hfirst hsecond)
    exact Or.inr (_root_.GD.N0106.N0428.N0765.N1532.d007578 hsep b hsecond)
  · exact Or.inl (_root_.GD.N0106.N0428.N0765.N1532.d007578 hsep a hfirst)


theorem d008455 {g : ℝ × ℝ → ℂ} {A : ℝ × ℝ → ℝ}
    {δ a b : ℝ} {x : ℝ × ℝ} {n : ℤ × ℤ}
    (hδ : 0 < δ) (hA : Integrable A (volume.prod volume))
    (hlocal : ∀ x : ℝ × ℝ, ∀ᵐ t : ℝ × ℝ ∂(volume.prod volume),
      |x.1 - t.1| ≤ 2 * δ → |x.2 - t.2| ≤ 2 * δ → ‖g x‖ ≤ 4 * A t)
    (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1638.d008452 a b δ n) :
    ‖g x‖ ≤ _root_.GD.N0106.N0428.N0765.N1638.d008453 A a b δ n := by
  have ha : a + (n.1 : ℝ) - δ ≤ a + (n.1 : ℝ) + δ := by linarith
  have hb : b + (n.2 : ℝ) - δ ≤ b + (n.2 : ℝ) + δ := by linarith
  have harea : (volume.prod volume).real (_root_.GD.N0106.N0428.N0765.N1638.d008452 a b δ n) = 4 * δ ^ 2 := by
    rw [_root_.GD.N0106.N0428.N0765.N1638.d008452, measureReal_prod_prod]
    simp only [_root_.GD.N0106.N0428.N0765.N1532.d007575, Real.volume_real_Icc_of_le ha, Real.volume_real_Icc_of_le hb]
    ring
  have hcompare :
      (∫ _t in _root_.GD.N0106.N0428.N0765.N1638.d008452 a b δ n, ‖g x‖ ∂(volume.prod volume)) ≤
        ∫ t in _root_.GD.N0106.N0428.N0765.N1638.d008452 a b δ n, 4 * A t ∂(volume.prod volume) := by
    apply setIntegral_mono_on_ae
      (integrableOn_const (isCompact_Icc.prod isCompact_Icc).measure_ne_top)
      (hA.integrableOn.const_mul 4) (measurableSet_Icc.prod measurableSet_Icc)
    filter_upwards [hlocal x] with t ht
    intro htc
    apply ht
    · apply abs_le.mpr
      have hx1 := hx.1
      have ht1 := htc.1
      change a + (n.1 : ℝ) - δ ≤ x.1 ∧ x.1 ≤ a + (n.1 : ℝ) + δ at hx1
      change a + (n.1 : ℝ) - δ ≤ t.1 ∧ t.1 ≤ a + (n.1 : ℝ) + δ at ht1
      constructor <;> linarith [hx1.1, hx1.2, ht1.1, ht1.2]
    · apply abs_le.mpr
      have hx2 := hx.2
      have ht2 := htc.2
      change b + (n.2 : ℝ) - δ ≤ x.2 ∧ x.2 ≤ b + (n.2 : ℝ) + δ at hx2
      change b + (n.2 : ℝ) - δ ≤ t.2 ∧ t.2 ≤ b + (n.2 : ℝ) + δ at ht2
      constructor <;> linarith [hx2.1, hx2.2, ht2.1, ht2.2]
  rw [setIntegral_const, integral_const_mul, harea, smul_eq_mul] at hcompare
  apply (le_div_iff₀ (sq_pos_of_pos hδ)).2
  change ‖g x‖ * δ ^ 2 ≤ ∫ t in _root_.GD.N0106.N0428.N0765.N1638.d008452 a b δ n, A t ∂(volume.prod volume)
  nlinarith

theorem d008456 {A : ℝ × ℝ → ℝ} {δ : ℝ}
    (hsep : 2 * δ < 1) (hA : Integrable A (volume.prod volume))
    (hA0 : ∀ t : ℝ × ℝ, 0 ≤ A t) (a b : ℝ) :
    Summable (_root_.GD.N0106.N0428.N0765.N1638.d008453 A a b δ) := by
  apply summable_of_sum_le
    (fun n => div_nonneg (integral_nonneg hA0) (sq_nonneg δ))
  intro s
  have hsum : (∑ n ∈ s, ∫ t in _root_.GD.N0106.N0428.N0765.N1638.d008452 a b δ n, A t ∂(volume.prod volume)) ≤
      ∫ t : ℝ × ℝ, A t ∂(volume.prod volume) := by
    rw [← integral_biUnion_finset (s := _root_.GD.N0106.N0428.N0765.N1638.d008452 a b δ) s
      (fun _ _ => measurableSet_Icc.prod measurableSet_Icc)
      (fun i _ j _ hij => _root_.GD.N0106.N0428.N0765.N1638.d008454 hsep a b hij)
      (fun _ _ => hA.integrableOn)]
    exact integral_mono_measure Measure.restrict_le_self (ae_of_all _ hA0) hA
  change (∑ n ∈ s, (∫ t in _root_.GD.N0106.N0428.N0765.N1638.d008452 a b δ n, A t ∂(volume.prod volume)) / δ ^ 2) ≤ _
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right hsum (sq_nonneg δ)

theorem d008457 {g : ℝ × ℝ → ℂ} {A : ℝ × ℝ → ℝ}
    {δ : ℝ} (hδ : 0 < δ) (hsep : 2 * δ < 1)
    (hA : Integrable A (volume.prod volume)) (hA0 : ∀ t : ℝ × ℝ, 0 ≤ A t)
    (hlocal : ∀ x : ℝ × ℝ, ∀ᵐ t : ℝ × ℝ ∂(volume.prod volume),
      |x.1 - t.1| ≤ 2 * δ → |x.2 - t.2| ≤ 2 * δ → ‖g x‖ ≤ 4 * A t)
    (a b : ℝ) : Summable (fun n : ℤ × ℤ => g (a + (n.1 : ℝ), b + (n.2 : ℝ))) := by
  apply Summable.of_norm_bounded (_root_.GD.N0106.N0428.N0765.N1638.d008456 hsep hA hA0 a b)
  intro n
  apply _root_.GD.N0106.N0428.N0765.N1638.d008455 hδ hA hlocal
  constructor
  · change a + (n.1 : ℝ) - δ ≤ a + (n.1 : ℝ) ∧
      a + (n.1 : ℝ) ≤ a + (n.1 : ℝ) + δ
    constructor <;> linarith
  · change b + (n.2 : ℝ) - δ ≤ b + (n.2 : ℝ) ∧
      b + (n.2 : ℝ) ≤ b + (n.2 : ℝ) + δ
    constructor <;> linarith

end
end GD.N0106.N0428.N0765.N1638

#print axioms _root_.GD.N0106.N0428.N0765.N1638.d008455
#print axioms _root_.GD.N0106.N0428.N0765.N1638.d008457
