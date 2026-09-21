import GD.Module0494
import GD.Module0382





















set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

namespace GD.N0106.N0428.N0765.N1637
noncomputable section

open MeasureTheory Set Metric Complex Filter TopologicalSpace
open _root_.GD.N0106.N0428.N0765.N1532 _root_.GD.N0106.N0428.N0765.N1652
open scoped Topology BigOperators

def d008442 (A : ℝ → ℝ) (a δ : ℝ) (n : ℤ) : ℝ :=
  (∫ t in _root_.GD.N0106.N0428.N0765.N1532.d007575 a δ n, A t) / δ


theorem d008443 {g : ℝ → ℂ} {A : ℝ → ℝ} {δ a x : ℝ} {n : ℤ}
    (hδ : 0 < δ) (hA : Integrable A)
    (hlocal : ∀ x : ℝ, ∀ᵐ t : ℝ, |x - t| ≤ 2 * δ → ‖g x‖ ≤ 2 * A t)
    (hx : x ∈ _root_.GD.N0106.N0428.N0765.N1532.d007575 a δ n) :
    ‖g x‖ ≤ _root_.GD.N0106.N0428.N0765.N1637.d008442 A a δ n := by
  have hab : a + (n : ℝ) - δ ≤ a + (n : ℝ) + δ := by linarith
  have hcompare :
      (∫ _t in _root_.GD.N0106.N0428.N0765.N1532.d007575 a δ n, ‖g x‖) ≤
        ∫ t in _root_.GD.N0106.N0428.N0765.N1532.d007575 a δ n, 2 * A t := by
    apply setIntegral_mono_on_ae (integrableOn_const isCompact_Icc.measure_ne_top)
      (hA.integrableOn.const_mul 2) measurableSet_Icc
    filter_upwards [hlocal x] with t ht
    intro htc
    apply ht
    apply abs_le.mpr
    change _ ≤ x ∧ x ≤ _ at hx
    change _ ≤ t ∧ t ≤ _ at htc
    constructor <;> linarith [hx.1, hx.2, htc.1, htc.2]
  rw [setIntegral_const, integral_const_mul] at hcompare
  simp only [_root_.GD.N0106.N0428.N0765.N1532.d007575, Real.volume_real_Icc_of_le hab, smul_eq_mul] at hcompare
  apply (le_div_iff₀ hδ).2
  change ‖g x‖ * δ ≤ ∫ t in Icc (a + (n : ℝ) - δ) (a + (n : ℝ) + δ), A t
  nlinarith

theorem d008444 {A : ℝ → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hA0 : ∀ t : ℝ, 0 ≤ A t) (a : ℝ) (n : ℤ) :
    0 ≤ _root_.GD.N0106.N0428.N0765.N1637.d008442 A a δ n := div_nonneg (integral_nonneg hA0) hδ

theorem d008445 {A : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hsep : 2 * δ < 1) (hA : Integrable A)
    (hA0 : ∀ t : ℝ, 0 ≤ A t) (a : ℝ) (s : Finset ℤ) :
    ∑ n ∈ s, _root_.GD.N0106.N0428.N0765.N1637.d008442 A a δ n ≤ (∫ t : ℝ, A t) / δ := by
  have hsum : (∑ n ∈ s, ∫ t in _root_.GD.N0106.N0428.N0765.N1532.d007575 a δ n, A t) ≤ ∫ t : ℝ, A t := by
    rw [← integral_biUnion_finset (s := _root_.GD.N0106.N0428.N0765.N1532.d007575 a δ) s
      (fun _ _ => measurableSet_Icc)
      (fun i _ j _ hij => _root_.GD.N0106.N0428.N0765.N1532.d007578 hsep a hij)
      (fun _ _ => hA.integrableOn)]
    exact integral_mono_measure Measure.restrict_le_self (ae_of_all _ hA0) hA
  simp only [_root_.GD.N0106.N0428.N0765.N1637.d008442]
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right hsum hδ

theorem d008446 {A : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hsep : 2 * δ < 1) (hA : Integrable A)
    (hA0 : ∀ t : ℝ, 0 ≤ A t) (a : ℝ) : Summable (_root_.GD.N0106.N0428.N0765.N1637.d008442 A a δ) := by
  apply summable_of_sum_le (_root_.GD.N0106.N0428.N0765.N1637.d008444 hδ hA0 a)
  exact _root_.GD.N0106.N0428.N0765.N1637.d008445 hδ hsep hA hA0 a

theorem d008447 {g : C(ℝ, ℂ)} {A : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hA : Integrable A) (hA0 : ∀ t : ℝ, 0 ≤ A t)
    (hlocal : ∀ x : ℝ, ∀ᵐ t : ℝ, |x - t| ≤ 2 * δ → ‖g x‖ ≤ 2 * A t)
    (a : ℝ) (n : ℤ) : _root_.GD.N0106.N0428.N0765.N1532.d007577 g a δ n ≤ _root_.GD.N0106.N0428.N0765.N1637.d008442 A a δ n := by
  apply (ContinuousMap.norm_le _ (_root_.GD.N0106.N0428.N0765.N1637.d008444 hδ.le hA0 a n)).2
  intro x
  change ‖g ((x : ℝ) + (n : ℝ))‖ ≤ _
  apply _root_.GD.N0106.N0428.N0765.N1637.d008443 hδ hA hlocal
  have hx := x.property
  change a - δ ≤ (x : ℝ) ∧ (x : ℝ) ≤ a + δ at hx
  change a + (n : ℝ) - δ ≤ (x : ℝ) + (n : ℝ) ∧
    (x : ℝ) + (n : ℝ) ≤ a + (n : ℝ) + δ
  constructor <;> linarith [hx.1, hx.2]

theorem d008448 {g : C(ℝ, ℂ)} {A : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hsep : 2 * δ < 1) (hA : Integrable A)
    (hA0 : ∀ t : ℝ, 0 ≤ A t)
    (hlocal : ∀ x : ℝ, ∀ᵐ t : ℝ, |x - t| ≤ 2 * δ → ‖g x‖ ≤ 2 * A t)
    (a : ℝ) (s : Finset ℤ) :
    ∑ n ∈ s, _root_.GD.N0106.N0428.N0765.N1532.d007577 g a δ n ≤ (∫ t : ℝ, A t) / δ := by
  exact (Finset.sum_le_sum (fun n _ => _root_.GD.N0106.N0428.N0765.N1637.d008447 hδ hA hA0 hlocal a n)).trans
    (_root_.GD.N0106.N0428.N0765.N1637.d008445 hδ.le hsep hA hA0 a s)




theorem d008449 {g : C(ℝ, ℂ)} {A : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hsep : 2 * δ < 1) (hA : Integrable A)
    (hA0 : ∀ t : ℝ, 0 ≤ A t)
    (hlocal : ∀ x : ℝ, ∀ᵐ t : ℝ, |x - t| ≤ 2 * δ → ‖g x‖ ≤ 2 * A t)
    (K : Compacts ℝ) :
    Summable (fun n : ℤ => ‖(g.comp (ContinuousMap.addRight (n : ℝ))).restrict K‖) := by
  classical
  obtain ⟨s, hs⟩ := K.isCompact.elim_finite_subcover (fun a : ℝ => ball a δ)
    (fun _ => isOpen_ball) (by
      intro x _hx
      exact mem_iUnion.mpr ⟨x, mem_ball_self hδ⟩)
  have hmajor (n : ℤ) :
      ‖(g.comp (ContinuousMap.addRight (n : ℝ))).restrict K‖ ≤
        ∑ a ∈ s, _root_.GD.N0106.N0428.N0765.N1532.d007577 g a δ n := by
    apply (ContinuousMap.norm_le _ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).2
    intro x
    obtain ⟨a, has, hax⟩ := mem_iUnion₂.mp (hs x.property)
    have hxc : (x : ℝ) ∈ _root_.GD.N0106.N0428.N0765.N1532.d007576 a δ := by
      have hxabs : |(x : ℝ) - a| < δ := by simpa only [mem_ball, Real.dist_eq] using hax
      change a - δ ≤ (x : ℝ) ∧ (x : ℝ) ≤ a + δ
      constructor <;> linarith [(abs_lt.mp hxabs).1, (abs_lt.mp hxabs).2]
    have hxnorm := ((g.comp (ContinuousMap.addRight (n : ℝ))).restrict
      (_root_.GD.N0106.N0428.N0765.N1532.d007576 a δ)).norm_coe_le_norm ⟨(x : ℝ), hxc⟩
    change ‖g ((x : ℝ) + (n : ℝ))‖ ≤ _
    exact hxnorm.trans (Finset.single_le_sum (f := fun a => _root_.GD.N0106.N0428.N0765.N1532.d007577 g a δ n)
      (fun _ _ => norm_nonneg _) has)
  apply summable_of_sum_le (fun _ => norm_nonneg _)
  intro u
  calc
    _ ≤ ∑ n ∈ u, ∑ a ∈ s, _root_.GD.N0106.N0428.N0765.N1532.d007577 g a δ n := Finset.sum_le_sum (fun n _ => hmajor n)
    _ = ∑ a ∈ s, ∑ n ∈ u, _root_.GD.N0106.N0428.N0765.N1532.d007577 g a δ n := Finset.sum_comm
    _ ≤ ∑ _a ∈ s, (∫ t : ℝ, A t) / δ :=
      Finset.sum_le_sum (fun a _ => _root_.GD.N0106.N0428.N0765.N1637.d008448 hδ hsep hA hA0 hlocal a u)

theorem d008450 {g : ℝ → ℂ} {A : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hsep : 2 * δ < 1) (hA : Integrable A)
    (hA0 : ∀ t : ℝ, 0 ≤ A t)
    (hlocal : ∀ x : ℝ, ∀ᵐ t : ℝ, |x - t| ≤ 2 * δ → ‖g x‖ ≤ 2 * A t)
    (a : ℝ) : Summable (fun n : ℤ => g (a + (n : ℝ))) := by
  apply Summable.of_norm_bounded (_root_.GD.N0106.N0428.N0765.N1637.d008446 hδ.le hsep hA hA0 a)
  intro n
  apply _root_.GD.N0106.N0428.N0765.N1637.d008443 hδ hA hlocal
  change a + (n : ℝ) - δ ≤ a + (n : ℝ) ∧ a + (n : ℝ) ≤ a + (n : ℝ) + δ
  constructor <;> linarith



theorem d008451 {g : ℝ → ℤ → ℂ} {A : ℝ → ℝ} {δ k : ℝ}
    (hδ : 0 < δ) (hsep : 2 * δ < 1) (hA : Integrable A)
    (hA0 : ∀ t : ℝ, 0 ≤ A t) (hk : 0 < k)
    (hlocal : ∀ n : ℤ, ∀ x : ℝ, ∀ᵐ t : ℝ, |x - t| ≤ 2 * δ →
      ‖g x n‖ ≤ 2 * (Real.exp (-k * |(n : ℝ)|) * A t))
    (a : ℝ) : Summable (fun p : ℤ × ℤ => g (a + (p.1 : ℝ)) p.2) := by
  have hfreq : Summable (fun n : ℤ => Real.exp (-k * |(n : ℝ)|)) := by
    have hs := _root_.GD.N0106.N0428.N0765.N1613.d005630
      (s := fun n : ℤ => ((Real.exp (-k * |(n : ℝ)|) : ℝ) : ℂ)) (C := 1) hk (by
        intro n
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          one_mul, le_refl])
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hs.norm
  apply _root_.GD.N0106.N0428.N0765.N1652.d005819
    (_root_.GD.N0106.N0428.N0765.N1637.d008446 hδ.le hsep hA hA0 a)
    hfreq
    (_root_.GD.N0106.N0428.N0765.N1637.d008444 hδ.le hA0 a) (fun n => (Real.exp_pos _).le)
  intro p
  have hpoint : a + (p.1 : ℝ) ∈ _root_.GD.N0106.N0428.N0765.N1532.d007575 a δ p.1 := by
    change a + (p.1 : ℝ) - δ ≤ a + (p.1 : ℝ) ∧
      a + (p.1 : ℝ) ≤ a + (p.1 : ℝ) + δ
    constructor <;> linarith
  have hb := _root_.GD.N0106.N0428.N0765.N1637.d008443 hδ
    (hA.const_mul (Real.exp (-k * |(p.2 : ℝ)|))) (hlocal p.2) hpoint
  have heq : _root_.GD.N0106.N0428.N0765.N1637.d008442 (fun t : ℝ => Real.exp (-k * |(p.2 : ℝ)|) * A t) a δ p.1 =
      _root_.GD.N0106.N0428.N0765.N1637.d008442 A a δ p.1 * Real.exp (-k * |(p.2 : ℝ)|) := by
    unfold _root_.GD.N0106.N0428.N0765.N1637.d008442
    rw [integral_const_mul]
    ring
  exact hb.trans_eq heq

end
end GD.N0106.N0428.N0765.N1637

#print axioms _root_.GD.N0106.N0428.N0765.N1637.d008443
#print axioms _root_.GD.N0106.N0428.N0765.N1637.d008449
#print axioms _root_.GD.N0106.N0428.N0765.N1637.d008450
#print axioms _root_.GD.N0106.N0428.N0765.N1637.d008451
