import GD.Module0523










set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory

namespace GD.N0106.N0428.N0766
noncomputable section

open _root_.GD.N0106.N0428.N0766.N1692.N1763





theorem d007877
    {alpha beta e C : ℝ} (ha : 0 < alpha) (hb : 0 < beta)
    (he : e ∈ Icc (0 : ℝ) 1)
    (q : ℝ × ℝ → ℝ) (hq : Measurable q) (hC : ∀ x, |q x| ≤ C)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hsupport : Function.support q ⊆ K) (hOmega : K ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844) :
    Integrable (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta (e, x) * q x) (volume.prod volume) ∧
      Integrable (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) * q x ^ 2)
        (volume.prod volume) := by
  have hpair : Continuous (fun x : ℝ × ℝ => (e, x)) :=
    continuous_const.prodMk continuous_id
  have hmaps : MapsTo (fun x : ℝ × ℝ => (e, x)) K _root_.GD.N0106.N0428.N0766.N1692.N1763.d007845 :=
    fun _ hx => ⟨he, hOmega hx⟩
  have htrace : IntegrableOn (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta (e, x)) K
      (volume.prod volume) :=
    ((_root_.GD.N0106.N0428.N0766.N1692.N1763.d007866 ha hb).comp' hpair.continuousOn hmaps).integrableOn_compact hK
  have henergy : IntegrableOn (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x)) K
      (volume.prod volume) :=
    ((_root_.GD.N0106.N0428.N0766.N1692.N1763.d007865 ha hb).comp' hpair.continuousOn hmaps).integrableOn_compact hK
  have hqBound : ∀ᵐ x ∂((volume.prod volume).restrict K), ‖q x‖ ≤ C :=
    Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hC x
  have hqSqBound : ∀ᵐ x ∂((volume.prod volume).restrict K), ‖q x ^ 2‖ ≤ C ^ 2 :=
    Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_sq]
      calc
        q x ^ 2 = |q x| ^ 2 := (sq_abs _).symm
        _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hC x) 2
  have htraceLocal : IntegrableOn
      (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta (e, x) * q x) K (volume.prod volume) :=
    htrace.mul_bdd hq.aestronglyMeasurable hqBound
  have henergyLocal : IntegrableOn
      (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) * q x ^ 2) K (volume.prod volume) :=
    henergy.mul_bdd (hq.pow_const 2).aestronglyMeasurable hqSqBound
  have htraceSupport : Function.support
      (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta (e, x) * q x) ⊆ K :=
    (Function.support_mul_subset_right _ _).trans hsupport
  have henergySupport : Function.support
      (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) * q x ^ 2) ⊆ K := by
    intro x hx
    apply hsupport
    change q x ≠ 0
    intro hzero
    change _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) * q x ^ 2 ≠ 0 at hx
    exact hx (by simp [hzero])
  exact ⟨(integrableOn_iff_integrable_of_support_subset htraceSupport).mp htraceLocal,
    (integrableOn_iff_integrable_of_support_subset henergySupport).mp henergyLocal⟩

end
end GD.N0106.N0428.N0766

#print axioms _root_.GD.N0106.N0428.N0766.d007877
