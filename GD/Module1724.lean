import GD.Module1562
import GD.Module0519
import GD.Module1723





set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace GD.N0106.N0428.N0766
noncomputable section

open Set MeasureTheory
open scoped BigOperators
open _root_.GD.N0232.N0720.N1254
open _root_.GD.N0106.N0428.N0766.N1690 _root_.GD.N0106.N0428.N0766.N1691 _root_.GD.N0106.N0428.N0766.N1692 _root_.GD.N0106.N0428.N0766.N1692.N1763 _root_.GD.N0106.N0428.N0766.N1692.N1762
open _root_.GD.N0118

def d028738 (alpha beta : ℝ) (q : ℝ × ℝ → ℝ) (e : ℝ) : ℝ :=
  ∫ x, q x * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta (e, x) ∂(volume.prod volume)

def d028739 (alpha beta : ℝ) (q : ℝ × ℝ → ℝ) (e : ℝ) : ℝ :=
  ∫ x, _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) * q x ^ 2 ∂(volume.prod volume)

def d028740 (alpha beta : ℝ) (N : ℕ) (w e : ℝ) (i : Fin 8) : ℝ :=
  ∫ x, _root_.GD.N0118.d008583 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i).1
    (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i).2 w x *
    _root_.GD.N0106.N0428.N0766.N1692.N1763.d007850 alpha beta (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i) (e, x)
    ∂(volume.prod volume)



theorem d028741 {alpha beta : ℝ} {N : ℕ}
    (ha : 0 < alpha) (hb : 0 < beta) (hN : 1 ≤ N) (e : ℝ) :
    (∑ i, _root_.GD.N0106.N0428.N0766.N1690.d006014 alpha beta N i *
      _root_.GD.N0106.N0428.N0766.N1692.N1763.d007850 alpha beta (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i)
        (e, _root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i)) = _root_.GD.N0106.N0428.N0766.N1692.N1762.d007780 alpha beta N e := by
  have hc (i : Fin 8) : _root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i ∈ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844 := by
    have h := _root_.GD.N0106.N0428.N0766.N1690.d006016 ha hb hN i
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  simp_rw [_root_.GD.N0106.N0428.N0766.N1692.N1763.d007858 ha hb e (hc _)]
  rw [_root_.GD.N0106.N0428.N0766.N1690.d006014, _root_.GD.N0106.N0428.N0766.N1690.d006002 _ _ _ _
    (_root_.GD.N0232.N0720.N1254.d002528 ha hb (by omega)).ne' (_root_.GD.N0232.N0720.N1254.d002529 ha hb (by omega)).ne']
  unfold _root_.GD.N0106.N0428.N0766.N1692.N1762.d007780
  congr 1
  simp [_root_.GD.N0106.N0428.N0766.N1690.d006001, _root_.GD.N0106.N0428.N0766.N1690.d006013, _root_.GD.N0106.N0428.N0766.N1690.d005999, _root_.GD.N0106.N0428.N0766.N1692.N1762.d007779,
    sub_eq_add_neg, add_assoc, add_comm, add_left_comm]




theorem d028742 (alpha beta : ℝ) (N : ℕ) (w e : ℝ)
    (hi : ∀ i : Fin 8, Integrable
      (fun x => _root_.GD.N0118.d008583 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i).1
        (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i).2 w x *
        _root_.GD.N0106.N0428.N0766.N1692.N1763.d007850 alpha beta (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i) (e, x))
      (volume.prod volume)) :
    _root_.GD.N0106.N0428.N0766.d028738 alpha beta (_root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w) e =
      ∑ i, _root_.GD.N0106.N0428.N0766.N1690.d006014 alpha beta N i * _root_.GD.N0106.N0428.N0766.d028740 alpha beta N w e i := by
  have hfun : (fun x => _root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w x * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta (e, x)) =
      fun x => ∑ i, _root_.GD.N0106.N0428.N0766.N1690.d006014 alpha beta N i *
        (_root_.GD.N0118.d008583 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i).1
          (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i).2 w x *
          _root_.GD.N0106.N0428.N0766.N1692.N1763.d007850 alpha beta (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i) (e, x)) := by
    funext x
    unfold _root_.GD.N0106.N0428.N0766.N1691.d024093 _root_.GD.N0106.N0428.N0766.N1691.d024082
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    unfold _root_.GD.N0106.N0428.N0766.N1692.N1763.d007850
    ring
  unfold _root_.GD.N0106.N0428.N0766.d028738
  rw [hfun, integral_finset_sum _ (fun i _ => (hi i).const_mul _)]
  simp only [integral_const_mul, _root_.GD.N0106.N0428.N0766.d028740]



theorem d028743 {alpha beta : ℝ} {N : ℕ} {w e E : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (hN : 1 ≤ N)
    (hi : ∀ i : Fin 8, Integrable
      (fun x => _root_.GD.N0118.d008583 (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i).1
        (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i).2 w x *
        _root_.GD.N0106.N0428.N0766.N1692.N1763.d007850 alpha beta (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i) (e, x))
      (volume.prod volume))
    (herr : ∀ i : Fin 8,
      |_root_.GD.N0106.N0428.N0766.d028740 alpha beta N w e i -
        _root_.GD.N0106.N0428.N0766.N1692.N1763.d007850 alpha beta (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i)
          (e, _root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i)| ≤ E) :
    |_root_.GD.N0106.N0428.N0766.d028738 alpha beta (_root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w) e - _root_.GD.N0106.N0428.N0766.N1692.N1762.d007780 alpha beta N e| ≤
      (∑ i, |_root_.GD.N0106.N0428.N0766.N1690.d006014 alpha beta N i|) * E := by
  rw [_root_.GD.N0106.N0428.N0766.d028742 alpha beta N w e hi,
    ← _root_.GD.N0106.N0428.N0766.d028741 ha hb hN e, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ i, |_root_.GD.N0106.N0428.N0766.N1690.d006014 alpha beta N i *
        (_root_.GD.N0106.N0428.N0766.d028740 alpha beta N w e i -
          _root_.GD.N0106.N0428.N0766.N1692.N1763.d007850 alpha beta (_root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i)
            (e, _root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |_root_.GD.N0106.N0428.N0766.N1690.d006014 alpha beta N i| * E := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (herr i) (abs_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm



theorem d028744 {alpha beta J : ℝ} {N : ℕ}
    (ha : 0 < alpha) (hb : 0 < beta) (hN : 1 ≤ N) (hJ : 0 < J)
    (hatomic : ∀ e ∈ Icc (0 : ℝ) 1, _root_.GD.N0106.N0428.N0766.N1692.N1762.d007780 alpha beta N e ≤ -3 * J / 4) :
    ∃ width > 0, width ≤ _root_.GD.N0106.N0428.N0766.N1690.d006015 alpha beta N ∧
      ∀ w, 0 < w → w ≤ width → ∀ e ∈ Icc (0 : ℝ) 1,
        _root_.GD.N0106.N0428.N0766.d028738 alpha beta (_root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w) e ≤ -5 * J / 8 := by
  classical
  let centers := _root_.GD.N0106.N0428.N0766.N1690.d006013 alpha beta N
  let radius := _root_.GD.N0106.N0428.N0766.N1690.d006015 alpha beta N
  let weights := _root_.GD.N0106.N0428.N0766.N1690.d006014 alpha beta N
  let W := ∑ i, |weights i|
  let tolerance := J / (8 * (1 + W))
  have hW : 0 ≤ W := Finset.sum_nonneg fun i _ => abs_nonneg _
  have htolerance : 0 < tolerance := by dsimp [tolerance]; positivity
  obtain ⟨hradius, hgeometry⟩ := _root_.GD.N0106.N0428.N0766.N1690.d006017 ha hb hN
  have hbox := (hgeometry radius hradius le_rfl).1
  have hex (i : Fin 8) : ∃ wi > 0, wi ≤ radius ∧
      ∀ w, 0 < w → w ≤ wi → ∀ e ∈ Icc (0 : ℝ) 1,
        Integrable (fun p => _root_.GD.N0118.d008583 (centers i).1 (centers i).2 w p *
          _root_.GD.N0106.N0428.N0766.N1692.N1763.d007850 alpha beta (centers i) (e, p)) (volume.prod volume) ∧
        |_root_.GD.N0106.N0428.N0766.d028740 alpha beta N w e i -
          _root_.GD.N0106.N0428.N0766.N1692.N1763.d007850 alpha beta (centers i) (e, centers i)| ≤ tolerance := by
    apply _root_.GD.N0106.N0428.N0766.N1693.d028737 (centers i).1 (centers i).2
      radius hradius (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007850 alpha beta (centers i)) ?_ tolerance htolerance
    apply (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007867 ha hb (centers i)).mono
    intro x hx
    exact ⟨hx.1, (hbox i).2 hx.2⟩
  choose wi hwi hwiRadius hwiWorks using hex
  let width := Finset.univ.inf' Finset.univ_nonempty wi
  have hwidth : 0 < width := by
    apply (Finset.lt_inf'_iff _).mpr
    intro i _
    exact hwi i
  have hwidthi (i : Fin 8) : width ≤ wi i := Finset.inf'_le wi (Finset.mem_univ i)
  refine ⟨width, hwidth, (hwidthi 0).trans (hwiRadius 0), ?_⟩
  intro w hw hww e he
  have hterms (i : Fin 8) := hwiWorks i w hw (hww.trans (hwidthi i)) e he
  have herr := _root_.GD.N0106.N0428.N0766.d028743 ha hb hN (fun i => (hterms i).1)
    (fun i => (hterms i).2)
  have htNonneg : 0 ≤ tolerance := htolerance.le
  have htotal : W * tolerance ≤ J / 8 := by
    calc
      W * tolerance ≤ (1 + W) * tolerance :=
        mul_le_mul_of_nonneg_right (by linarith) htNonneg
      _ = J / 8 := by
        dsimp [tolerance]
        have hn : 1 + W ≠ 0 := by positivity
        field_simp
        <;> ring
  have hupper := le_abs_self
    (_root_.GD.N0106.N0428.N0766.d028738 alpha beta (_root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w) e - _root_.GD.N0106.N0428.N0766.N1692.N1762.d007780 alpha beta N e)
  have hat := hatomic e he
  change |_root_.GD.N0106.N0428.N0766.d028738 alpha beta (_root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w) e -
    _root_.GD.N0106.N0428.N0766.N1692.N1762.d007780 alpha beta N e| ≤ W * tolerance at herr
  linarith



theorem d028745 (f : ℝ × ℝ → ℝ)
    (hf : Integrable f (volume.prod volume)) (hs : Function.support f ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844) :
    (∫ x, f x ∂(volume.prod volume)) =
      ∫ L in Ioo (0 : ℝ) 1, ∫ F in Ioi (0 : ℝ), f (L, F) := by
  calc
    _ = ∫ x in _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844, f x ∂(volume.prod volume) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      by_contra hn
      exact hx (hs hn)
    _ = _ := setIntegral_prod f hf.integrableOn



theorem d028746 (alpha beta e : ℝ) (q : ℝ × ℝ → ℝ)
    (hq : tsupport q ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844)
    (hint : Integrable (fun x => q x * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta (e, x)) (volume.prod volume)) :
    _root_.GD.N0106.N0428.N0766.d028738 alpha beta q e =
      ∫ L in Ioo (0 : ℝ) 1, ∫ F in Ioi (0 : ℝ),
        (L - e) * q (L, F) * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta (L, F) *
          _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847 alpha beta e (L, F) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta) := by
  rw [_root_.GD.N0106.N0428.N0766.d028738, _root_.GD.N0106.N0428.N0766.d028745 _ hint
    ((Function.support_mul_subset_left _ _).trans ((subset_tsupport q).trans hq))]
  congr 1
  funext L
  congr 1
  funext F
  unfold _root_.GD.N0106.N0428.N0766.N1692.N1763.d007849
  ring



theorem d028747 (alpha beta e : ℝ) (q : ℝ × ℝ → ℝ)
    (hq : tsupport q ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844)
    (hint : Integrable (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) * q x ^ 2)
      (volume.prod volume)) :
    _root_.GD.N0106.N0428.N0766.d028739 alpha beta q e =
      ∫ L in Ioo (0 : ℝ) 1, ∫ F in Ioi (0 : ℝ),
        q (L, F)^2 * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta (L, F) *
          _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847 alpha beta e (L, F) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta) := by
  have hs : Function.support (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta (e, x) * q x ^ 2) ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844 := by
    intro x hx
    have hqx : q x ≠ 0 := by
      intro hz
      apply hx
      simp [hz]
    exact hq (subset_tsupport _ hqx)
  rw [_root_.GD.N0106.N0428.N0766.d028739, _root_.GD.N0106.N0428.N0766.d028745 _ hint hs]
  congr 1
  funext L
  congr 1
  funext F
  unfold _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848
  ring



theorem d028748 {alpha beta w : ℝ} {N : ℕ}
    (ha : 0 < alpha) (hb : 0 < beta) (hN : 1 ≤ N) (hw : 0 < w)
    (hwsmall : w ≤ _root_.GD.N0106.N0428.N0766.N1690.d006015 alpha beta N) :
    Continuous (_root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w) ∧
      HasCompactSupport (_root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w) ∧
      tsupport (_root_.GD.N0106.N0428.N0766.N1691.d024093 alpha beta N w) ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844 := by
  refine ⟨_root_.GD.N0106.N0428.N0766.N1691.d024085 _ _ hw, _root_.GD.N0106.N0428.N0766.N1691.d024088 _ _ hw.le, ?_⟩
  apply (_root_.GD.N0106.N0428.N0766.N1691.d024087 _ _ hw.le).trans
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact (((_root_.GD.N0106.N0428.N0766.N1690.d006017 ha hb hN).2 w hw hwsmall).1 i).2 hi



theorem d028749 {alpha beta e : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (he : e ∈ Icc (0 : ℝ) 1)
    {q : ℝ × ℝ → ℝ} (hc : Continuous q) (hk : HasCompactSupport q)
    (hs : tsupport q ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844) :
    Integrable (fun x => q x * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta (e, x)) (volume.prod volume) := by
  have hkernel : ContinuousOn (fun x => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta (e, x)) (tsupport q) := by
    intro x hx
    exact ((_root_.GD.N0106.N0428.N0766.N1692.N1763.d007864 ha hb ⟨he, hs hx⟩).comp
      (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_left _ _).trans (subset_tsupport q))).mp
  exact (hc.continuousOn.mul hkernel).integrableOn_compact hk

end
end GD.N0106.N0428.N0766

#print axioms _root_.GD.N0106.N0428.N0766.d028741
#print axioms _root_.GD.N0106.N0428.N0766.d028742
#print axioms _root_.GD.N0106.N0428.N0766.d028743

#print axioms _root_.GD.N0106.N0428.N0766.d028744
