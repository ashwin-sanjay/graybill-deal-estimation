import GD.Module1725
import GD.Module0524









set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory

namespace GD.N0106.N0428.N0766
noncomputable section

open _root_.GD.N0232.N0720.N1254
open _root_.GD.N0106.N0428.N0766.N1692 _root_.GD.N0106.N0428.N0766.N1691 _root_.GD.N0106.N0428.N0766.N1692.N1763



structure d028763 (f : ℝ × ℝ → ℝ) : Prop where
  product_integrable : IntegrableOn f _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844 (volume.prod volume)
  inner_ae : ∀ᵐ L ∂(volume.restrict (Ioo (0 : ℝ) 1)),
    IntegrableOn (fun F => f (L, F)) (Ioi (0 : ℝ)) volume
  outer_integrable : IntegrableOn
    (fun L => ∫ F in Ioi (0 : ℝ), f (L, F)) (Ioo (0 : ℝ) 1) volume
  absolute_outer_integrable : IntegrableOn
    (fun L => ∫ F in Ioi (0 : ℝ), |f (L, F)|) (Ioo (0 : ℝ) 1) volume

private theorem d028764 {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844 (volume.prod volume)) : _root_.GD.N0106.N0428.N0766.d028763 f := by
  have hprod : Integrable f
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    simpa only [Measure.prod_restrict, _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844, IntegrableOn] using hf
  refine ⟨hf, hprod.prod_right_ae, hprod.integral_prod_left, ?_⟩
  simpa only [IntegrableOn, Real.norm_eq_abs] using hprod.integral_norm_prod_left




theorem d028765
    {alpha beta e C : ℝ} (ha : 0 < alpha) (hb : 0 < beta)
    (he : e ∈ Icc (0 : ℝ) 1)
    (q : ℝ × ℝ → ℝ) (hq : Measurable q) (hC : ∀ x, |q x| ≤ C)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hsupport : Function.support q ⊆ K) (hOmega : K ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844) :
    _root_.GD.N0106.N0428.N0766.d028763
      (fun x => (x.1 - e) * q x * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta x *
        _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847 alpha beta e x ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta)) ∧
      _root_.GD.N0106.N0428.N0766.d028763
        (fun x => q x ^ 2 * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta x *
          _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847 alpha beta e x ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta)) := by
  obtain ⟨htrace, henergy⟩ :=
    _root_.GD.N0106.N0428.N0766.d007877 ha hb he q hq hC
      hK hsupport hOmega
  have htracePaper : Integrable
      (fun x => (x.1 - e) * q x * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta x *
        _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847 alpha beta e x ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta))
      (volume.prod volume) := by
    convert htrace using 1
    funext x
    unfold _root_.GD.N0106.N0428.N0766.N1692.N1763.d007849
    ring
  have henergyPaper : Integrable
      (fun x => q x ^ 2 * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta x *
        _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847 alpha beta e x ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta))
      (volume.prod volume) := by
    convert henergy using 1
    funext x
    unfold _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848
    ring
  exact ⟨_root_.GD.N0106.N0428.N0766.d028764 htracePaper.integrableOn,
    _root_.GD.N0106.N0428.N0766.d028764 henergyPaper.integrableOn⟩




theorem d028766
    {alpha beta e C : ℝ} (ha : 0 < alpha) (hb : 0 < beta)
    (he : e ∈ Icc (0 : ℝ) 1)
    (q : ℝ × ℝ → ℝ) (hq : Measurable q) (hC : ∀ x, |q x| ≤ C)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hsupport : Function.support q ⊆ K) (hOmega : K ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844) :
    (_root_.GD.N0106.N0428.N0766.d028738 alpha beta q e =
      ∫ L in Ioo (0 : ℝ) 1, ∫ F in Ioi (0 : ℝ),
        (L - e) * q (L, F) * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta (L, F) *
          _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847 alpha beta e (L, F) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta)) ∧
    (_root_.GD.N0106.N0428.N0766.d028739 alpha beta q e =
      ∫ L in Ioo (0 : ℝ) 1, ∫ F in Ioi (0 : ℝ),
        q (L, F) ^ 2 * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta (L, F) *
          _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847 alpha beta e (L, F) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta)) := by
  obtain ⟨htrace, henergy⟩ :=
    _root_.GD.N0106.N0428.N0766.d007877 ha hb he q hq hC
      hK hsupport hOmega
  have htop : tsupport q ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844 :=
    (closure_minimal hsupport hK.isClosed).trans hOmega
  have htrace' : Integrable (fun x => q x * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta (e, x))
      (volume.prod volume) := by
    simpa only [mul_comm] using htrace
  exact ⟨_root_.GD.N0106.N0428.N0766.d028746 alpha beta e q htop htrace',
    _root_.GD.N0106.N0428.N0766.d028747 alpha beta e q htop henergy⟩




theorem d028767 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794)
    (e : ℝ) (he : e ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0766.d028763
      (fun x => (x.1 - e) *
        _root_.GD.N0106.N0428.N0766.N1691.d024093 a.val b.val (_root_.GD.N0106.N0428.N0766.N1692.d007798 a b) (_root_.GD.N0106.N0428.N0766.d028757 a b) x *
        _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 a.val b.val x * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847 a.val b.val e x ^ (-_root_.GD.N0232.N0720.N1254.d002513 a.val b.val)) ∧
    _root_.GD.N0106.N0428.N0766.d028763
      (fun x => _root_.GD.N0106.N0428.N0766.N1691.d024093 a.val b.val (_root_.GD.N0106.N0428.N0766.N1692.d007798 a b) (_root_.GD.N0106.N0428.N0766.d028757 a b) x ^ 2 *
        _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 a.val b.val x * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847 a.val b.val e x ^ (-_root_.GD.N0232.N0720.N1254.d002513 a.val b.val)) := by
  have hprop := _root_.GD.N0106.N0428.N0766.d028760 a b
  obtain ⟨C, _, hC⟩ := hprop.bounded
  exact _root_.GD.N0106.N0428.N0766.d028765 a.property b.property he
    _ hprop.continuous.measurable hC hprop.compact (subset_tsupport _) hprop.inside




theorem d028768 (a b : _root_.GD.N0106.N0428.N0766.N1692.d007794) :
    ∃ epsilon > 0, ∀ e ∈ Icc (0 : ℝ) 1,
      2 * epsilon *
        (∫ L in Ioo (0 : ℝ) 1, ∫ F in Ioi (0 : ℝ),
          (L - e) *
            _root_.GD.N0106.N0428.N0766.N1691.d024093 a.val b.val (_root_.GD.N0106.N0428.N0766.N1692.d007798 a b) (_root_.GD.N0106.N0428.N0766.d028757 a b) (L, F) *
            _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 a.val b.val (L, F) *
            _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847 a.val b.val e (L, F) ^ (-_root_.GD.N0232.N0720.N1254.d002513 a.val b.val)) +
        epsilon ^ 2 *
          (∫ L in Ioo (0 : ℝ) 1, ∫ F in Ioi (0 : ℝ),
            _root_.GD.N0106.N0428.N0766.N1691.d024093 a.val b.val (_root_.GD.N0106.N0428.N0766.N1692.d007798 a b) (_root_.GD.N0106.N0428.N0766.d028757 a b) (L, F) ^ 2 *
              _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 a.val b.val (L, F) *
              _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847 a.val b.val e (L, F) ^ (-_root_.GD.N0232.N0720.N1254.d002513 a.val b.val)) < 0 := by
  have hprop := _root_.GD.N0106.N0428.N0766.d028760 a b
  obtain ⟨epsilon, hepsilon, himproves⟩ := hprop.improves
  refine ⟨epsilon, hepsilon, ?_⟩
  intro e he
  have htrace := _root_.GD.N0106.N0428.N0766.d028746 a.val b.val e
    (_root_.GD.N0106.N0428.N0766.N1691.d024093 a.val b.val (_root_.GD.N0106.N0428.N0766.N1692.d007798 a b) (_root_.GD.N0106.N0428.N0766.d028757 a b))
    hprop.inside (hprop.trace_integrable e he)
  have henergy := _root_.GD.N0106.N0428.N0766.d028747 a.val b.val e
    (_root_.GD.N0106.N0428.N0766.N1691.d024093 a.val b.val (_root_.GD.N0106.N0428.N0766.N1692.d007798 a b) (_root_.GD.N0106.N0428.N0766.d028757 a b))
    hprop.inside (hprop.energy_integrable e he)
  simpa only [htrace, henergy] using himproves e he

end
end GD.N0106.N0428.N0766

#print axioms _root_.GD.N0106.N0428.N0766.d028765
#print axioms _root_.GD.N0106.N0428.N0766.d028766
#print axioms _root_.GD.N0106.N0428.N0766.d028767
#print axioms _root_.GD.N0106.N0428.N0766.d028768
