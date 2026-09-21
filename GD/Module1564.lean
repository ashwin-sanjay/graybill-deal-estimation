import GD.Module1562
import GD.Module0598










set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped BigOperators

namespace GD.N0106.N0428.N0766
noncomputable section

open _root_.GD.N0118 _root_.GD.N0106.N0428.N0766.N1691 _root_.GD.N0106.N0428.N0766.N1690 _root_.GD.N0106.N0428.N0766.N1692.N1763




theorem d024115 {alpha beta w : ℝ} {N : ℕ}
    (ha : 0 < alpha) (hb : 0 < beta) (hN : 1 ≤ N)
    (hw : 0 < w) (hwsmall : w ≤ _root_.GD.N0106.N0428.N0766.N1690.d006015 alpha beta N) :
    ∃ K > 0, ∀ e ∈ Icc (0 : ℝ) 1,
      Integrable
        (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) * _root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w x ^ 2)
        (volume.prod volume) ∧
      (∫ x, _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) * _root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w x ^ 2
        ∂(volume.prod volume)) ≤
        4 * K / (9 * w ^ 2) *
          ∑ i, (_root_.GD.N0106.N0428.N0766.N1690.d006014 alpha beta N i /
            _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i)) ^ 2 := by
  let center : Fin 8 → ℝ × ℝ := _root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N
  let coeff : Fin 8 → ℝ := fun i => _root_.GD.N0106.N0428.N0766.N1690.d006014 alpha beta N i /
    _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta (center i)
  let boxes : Set (ℝ × ℝ) := ⋃ i : Fin 8, _root_.GD.N0106.N0428.N0766.N1690.d006007 (center i) w
  obtain ⟨hrect, hdisjoint⟩ :=
    (_root_.GD.N0106.N0428.N0766.N1690.d006017 ha hb hN).2 w hw hwsmall
  have hboxesCompact : IsCompact boxes :=
    isCompact_iUnion fun i => _root_.GD.N0106.N0428.N0766.N1690.d006008 (center i) w
  have hboxesDomain : boxes ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844 := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact (hrect i).2 hi
  have hparameter : Icc (0 : ℝ) 1 ×ˢ boxes ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007845 :=
    fun _ hx => ⟨hx.1, hboxesDomain hx.2⟩
  obtain ⟨K, hK, hkernel⟩ := _root_.GD.N0106.N0428.N0766.N1692.N1763.d007871 ha hb
    (isCompact_Icc.prod hboxesCompact) hparameter
  refine ⟨K, hK, ?_⟩
  intro e he
  have hdisj : Pairwise fun i j =>
      Disjoint (_root_.GD.N0106.N0428.N0766.N1691.d024083 (center i) w) (_root_.GD.N0106.N0428.N0766.N1691.d024083 (center j) w) := hdisjoint
  have hInt (i : Fin 8) : Integrable
      (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) *
        (coeff i * _root_.GD.N0118.d008583 (center i).1 (center i).2 w x) ^ 2)
      (volume.prod volume) := by
    have hsupport : Function.support
        (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) *
          (coeff i * _root_.GD.N0118.d008583 (center i).1 (center i).2 w x) ^ 2) ⊆
        _root_.GD.N0106.N0428.N0766.N1690.d006007 (center i) w := by
      intro x hx
      change _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) *
        (coeff i * _root_.GD.N0118.d008583 (center i).1 (center i).2 w x) ^ 2 ≠ 0 at hx
      by_contra hout
      have ht : _root_.GD.N0118.d008583 (center i).1 (center i).2 w x = 0 := by
        by_contra ht
        exact hout (_root_.GD.N0106.N0428.N0766.N1691.d024086 hw.le ht)
      exact hx (by simp [ht])
    have henergy : ContinuousOn (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x))
        (_root_.GD.N0106.N0428.N0766.N1690.d006007 (center i) w) :=
      (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007865 ha hb).comp'
        (continuous_const.prodMk continuous_id).continuousOn
        (by intro x hx; exact ⟨he, (hrect i).2 hx⟩)
    have hcont : ContinuousOn
        (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) *
          (coeff i * _root_.GD.N0118.d008583 (center i).1 (center i).2 w x) ^ 2)
        (_root_.GD.N0106.N0428.N0766.N1690.d006007 (center i) w) :=
      henergy.mul
        (((_root_.GD.N0106.N0428.N0766.N1691.d024069 (center i).1 (center i).2 w hw).const_mul (coeff i)).pow 2).continuousOn
    exact (integrableOn_iff_integrable_of_support_subset hsupport).mp
      (hcont.integrableOn_compact (_root_.GD.N0106.N0428.N0766.N1690.d006008 (center i) w))
  have hsum :
      (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) * _root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w x ^ 2) =
      fun x => ∑ i, _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) *
        (coeff i * _root_.GD.N0118.d008583 (center i).1 (center i).2 w x) ^ 2 := by
    funext x
    change _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) * _root_.GD.N0106.N0428.N0766.N1691.d024082 center coeff w x ^ 2 = _
    rw [_root_.GD.N0106.N0428.N0766.N1691.d024092 center coeff hw.le hdisj, Finset.mul_sum]
  have hwhole : Integrable
      (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) * _root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w x ^ 2)
      (volume.prod volume) := by
    rw [hsum]
    exact integrable_finsetSum _ fun i _ => hInt i
  have hbound := _root_.GD.N0147.d008612
    Finset.univ (fun i => (center i).1) (fun i => (center i).2) coeff (fun _ => K)
    w (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x)) hw
    (fun _ _ => hK.le)
    (fun _ _ _ _ hij x => _root_.GD.N0106.N0428.N0766.N1691.d024091 center coeff hw.le hdisj hij x)
    (fun i _ => hInt i)
    (fun i _ x hx => by
      have hxbox : x ∈ boxes := mem_iUnion.mpr
        ⟨i, _root_.GD.N0106.N0428.N0766.N1691.d024086 hw.le hx⟩
      have h := hkernel (e, x) ⟨he, hxbox⟩
      exact ⟨h.1.le, h.2.1⟩)
  have hfactor : (∑ i : Fin 8, 4 / (9 * w ^ 2) * coeff i ^ 2 * K) =
      4 * K / (9 * w ^ 2) * ∑ i : Fin 8, coeff i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  refine ⟨hwhole, ?_⟩
  change (∫ x, _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) * _root_.GD.N0106.N0428.N0766.N1691.d024082 center coeff w x ^ 2
    ∂(volume.prod volume)) ≤ 4 * K / (9 * w ^ 2) * ∑ i, coeff i ^ 2
  exact hbound.trans_eq hfactor

end
end GD.N0106.N0428.N0766

#print axioms _root_.GD.N0106.N0428.N0766.d024115
