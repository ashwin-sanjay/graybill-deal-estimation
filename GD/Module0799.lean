import GD.Module0777
import GD.Module0744

set_option autoImplicit false
set_option warningAsError true












open MeasureTheory Set Topology
open scoped ENNReal

namespace GD.N0232.N0719.N0961

noncomputable section

open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0842 _root_.GD.N0232.N0719.N0805
open _root_.GD.N0232.N0719.N0946 _root_.GD.N0232.N0719.N0946.d009229
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0691 _root_.GD.N0230.N0708
open _root_.GD.N0230.N0582

variable (k : ℕ) (sizes : Fin k → ℕ)

local instance d012133 :
    IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  unfold _root_.GD.N0232.N0719.N0859.d010813
    _root_.GD.N0232.N0719.d009182 _root_.GD.N0232.N0719.d009176
  infer_instance

local instance d012134 (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
  unfold _root_.GD.N0232.N0719.N0859.d010812 _root_.GD.N0232.N0719.d009176
  infer_instance



theorem d012135
    (p : _root_.GD.N0232.N0719.N0805.d011787 k sizes) (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    MemLp (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
  have hstrong : AEStronglyMeasurable
      (fun omega ↦ _root_.GD.N0232.N0719.N0896.d011088 k sizes p omega - theta.location)
      (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) :=
    ((_root_.GD.N0232.N0719.N0896.d011089 k sizes p).sub measurable_const).aestronglyMeasurable
  have herr : MemLp (fun omega ↦ _root_.GD.N0232.N0719.N0896.d011088 k sizes p omega - theta.location)
      2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
    apply (memLp_two_iff_integrable_sq hstrong).2
    have hlin : (∫⁻ omega,
        ENNReal.ofReal ((_root_.GD.N0232.N0719.N0896.d011088 k sizes p omega - theta.location) ^ 2)
        ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) ≠ ⊤ := by
      change _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
        (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) ≠ ⊤
      rw [_root_.GD.N0232.N0719.N0896.d011093]
      exact hp theta
    have hint := integrable_toReal_of_lintegral_ne_top
      ((hstrong.aemeasurable.pow_const 2).ennreal_ofReal) hlin
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hint
  have hadd := herr.add (memLp_const theta.location :
    MemLp (fun _ : _root_.GD.N0232.N0719.d009173 k sizes ↦ theta.location) 2
      (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta))
  convert hadd using 1
  funext omega
  simp



def d012136 (g : _root_.GD.N0232.N0719.N0946.d009229) (p : _root_.GD.N0232.N0719.N0805.d011787 k sizes)
    (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p) :
    Lp ℝ 2 (_root_.GD.N0232.N0719.N0805.d011790 k sizes g.shift g.d009239) :=
  MemLp.toLp (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) (by
    rw [_root_.GD.N0232.N0719.N0805.d011792 k sizes g.shift g.d009239 g.d009240]
    exact _root_.GD.N0232.N0719.N0961.d012135 k sizes p hp
      (_root_.GD.N0232.N0719.N0805.d011791 k g.shift g.d009239 g.d009240))



theorem d012137 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p : _root_.GD.N0232.N0719.N0805.d011787 k sizes) (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p) :
    _root_.GD.N0232.N0719.N0896.d011109 k sizes g p hp =
      _root_.GD.N0232.N0719.N0805.d011797 k sizes g.shift g.d009239 g.d009240 (_root_.GD.N0232.N0719.N0961.d012136 k sizes g p hp) := by
  apply Lp.ext
  have hout := (_root_.GD.N0232.N0719.N0896.d011108 k sizes g p hp).coeFn_toLp
  have hpullMem : MemLp (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) 2
      (_root_.GD.N0232.N0719.N0805.d011790 k sizes g.shift g.d009239) := by
    rw [_root_.GD.N0232.N0719.N0805.d011792 k sizes g.shift g.d009239 g.d009240]
    exact _root_.GD.N0232.N0719.N0961.d012135 k sizes p hp
      (_root_.GD.N0232.N0719.N0805.d011791 k g.shift g.d009239 g.d009240)
  have hpull : (fun omega ↦ _root_.GD.N0232.N0719.N0961.d012136 k sizes g p hp omega) =ᵐ[
      _root_.GD.N0232.N0719.N0805.d011790 k sizes g.shift g.d009239] _root_.GD.N0232.N0719.N0896.d011088 k sizes p :=
    hpullMem.coeFn_toLp
  have hpullComp := (_root_.GD.N0232.N0719.N0805.d011793
    k sizes g.shift g.d009239).quasiMeasurePreserving.ae_eq_comp hpull
  have hencode := Lp.coeFn_compMeasurePreserving (_root_.GD.N0232.N0719.N0961.d012136 k sizes g p hp)
    (_root_.GD.N0232.N0719.N0805.d011793 k sizes g.shift g.d009239)
  let c : _root_.GD.N0232.N0719.N0805.d011787 k sizes := _root_.GD.N0232.N0719.N0805.d011799 k sizes g.shift
  let z : _root_.GD.N0232.N0719.N0805.d011787 k sizes :=
    _root_.GD.N0232.N0719.N0805.d011795 k sizes g.shift g.d009239 (_root_.GD.N0232.N0719.N0961.d012136 k sizes g p hp)
  have hc := (memLp_const g.shift : MemLp
    (fun _ : _root_.GD.N0232.N0719.d009173 k sizes ↦ g.shift) 2
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)).coeFn_toLp
  have hs := Lp.coeFn_smul g.d009239 z
  have ha := Lp.coeFn_add c (g.d009239 • z)
  filter_upwards [hout, hpullComp, hencode, hc, hs, ha] with omega ho hpull he hc hs ha
  change _root_.GD.N0232.N0719.N0896.d011109 k sizes g p hp omega = (c + g.d009239 • z) omega
  rw [ha]
  change _root_.GD.N0232.N0719.N0896.d011109 k sizes g p hp omega = c omega + (g.d009239 • z) omega
  rw [hs]
  change _root_.GD.N0232.N0719.N0896.d011109 k sizes g p hp omega = c omega + g.d009239 * z omega
  have hc' : c omega = g.shift := hc
  have he' : z omega = _root_.GD.N0232.N0719.N0961.d012136 k sizes g p hp
      (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.shift g.d009239 omega) := he
  have hpull' : _root_.GD.N0232.N0719.N0961.d012136 k sizes g p hp
      (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.shift g.d009239 omega) =
      _root_.GD.N0232.N0719.N0896.d011088 k sizes p
        (_root_.GD.N0232.N0719.N0842.d010907 k sizes g.shift g.d009239 omega) := hpull
  rw [hc', he', hpull']
  exact ho



theorem d012138 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p : _root_.GD.N0232.N0719.N0805.d011787 k sizes) (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p) :
    _root_.GD.N0230.N0708.d001177
      (_root_.GD.N0230.N0691.d001209 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0805.d011790 k sizes g.shift g.d009239))
      (_root_.GD.N0230.N0691.d001210 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0805.d011790 k sizes g.shift g.d009239))
      p (_root_.GD.N0232.N0719.N0961.d012136 k sizes g p hp) := by
  let hmu := _root_.GD.N0232.N0719.N0896.d011091 k sizes p
  let hnu : MemLp (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) 2
      (_root_.GD.N0232.N0719.N0805.d011790 k sizes g.shift g.d009239) := by
    rw [_root_.GD.N0232.N0719.N0805.d011792 k sizes g.shift g.d009239 g.d009240]
    exact _root_.GD.N0232.N0719.N0961.d012135 k sizes p hp
      (_root_.GD.N0232.N0719.N0805.d011791 k g.shift g.d009239 g.d009240)
  let u := _root_.GD.N0230.N0691.d001218 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
    (_root_.GD.N0232.N0719.N0805.d011790 k sizes g.shift g.d009239) (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) hmu hnu
  refine ⟨u, ?_, ?_⟩
  · rw [show _root_.GD.N0230.N0691.d001209 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0805.d011790 k sizes g.shift g.d009239) u =
        hmu.toLp (_root_.GD.N0232.N0719.N0896.d011088 k sizes p) from _root_.GD.N0230.N0691.d001219 _ _ _ hmu hnu]
    exact _root_.GD.N0232.N0719.N0896.d011092 k sizes p
  · exact _root_.GD.N0230.N0691.d001220 _ _ _ hmu hnu



theorem d012139 (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p q : _root_.GD.N0232.N0719.N0805.d011787 k sizes) (hp : _root_.GD.N0232.N0719.N0896.d011103 k sizes p) :
    _root_.GD.N0230.N0708.d001177
      (_root_.GD.N0230.N0691.d001209 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0805.d011790 k sizes g.shift g.d009239))
      (_root_.GD.N0230.N0691.d001210 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0805.d011790 k sizes g.shift g.d009239))
      p (_root_.GD.N0232.N0719.N0805.d011798 k sizes g.shift g.d009239 g.d009240 q) ↔
      q = _root_.GD.N0232.N0719.N0896.d011109 k sizes g p hp := by
  constructor
  · intro hb
    have he := _root_.GD.N0232.N0719.N0805.d011814
      (_root_.GD.N0230.N0691.d001209 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0805.d011790 k sizes g.shift g.d009239))
      (_root_.GD.N0230.N0691.d001210 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0805.d011790 k sizes g.shift g.d009239))
      (_root_.GD.N0232.N0719.N0805.d011813 _ _
        (_root_.GD.N0232.N0719.N0805.d011812 k sizes g.shift g.d009239 g.d009240))
      hb (_root_.GD.N0232.N0719.N0961.d012138 k sizes g p hp)
    calc
      q = _root_.GD.N0232.N0719.N0805.d011797 k sizes g.shift g.d009239 g.d009240
          (_root_.GD.N0232.N0719.N0805.d011798 k sizes g.shift g.d009239 g.d009240 q) :=
        (_root_.GD.N0232.N0719.N0805.d011806 k sizes g.shift g.d009239 g.d009240 q).symm
      _ = _root_.GD.N0232.N0719.N0805.d011797 k sizes g.shift g.d009239 g.d009240 (_root_.GD.N0232.N0719.N0961.d012136 k sizes g p hp) :=
        by rw [he]
      _ = _root_.GD.N0232.N0719.N0896.d011109 k sizes g p hp := (_root_.GD.N0232.N0719.N0961.d012137 k sizes g p hp).symm
  · intro he
    rw [he, _root_.GD.N0232.N0719.N0961.d012137, _root_.GD.N0232.N0719.N0805.d011805]
    exact _root_.GD.N0232.N0719.N0961.d012138 k sizes g p hp



theorem d012140
    (C : Set (WeakSpace ℝ (_root_.GD.N0232.N0719.N0805.d011787 k sizes))) (hC : IsCompact C)
    (hfinite : ∀ p ∈ C, _root_.GD.N0232.N0719.N0896.d011103 k sizes ((toWeakSpace ℝ _).symm p))
    (g : _root_.GD.N0232.N0719.N0946.d009229) (f : C → C)
    (hf : ∀ p : C, (f p).1 = toWeakSpace ℝ _
      (_root_.GD.N0232.N0719.N0896.d011109 k sizes g ((toWeakSpace ℝ _).symm p.1)
        (hfinite p.1 p.2))) :
    Continuous f := by
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  apply _root_.GD.N0230.N0582.d000063
  have hgraph : _root_.GD.N0230.N0582.d000059 f =
      (fun p : C × C ↦ (p.1.1, p.2.1)) ⁻¹'
        _root_.GD.N0232.N0719.N0805.d011810 k sizes g.shift g.d009239 g.d009240 := by
    ext p
    change p.2 = f p.1 ↔ _root_.GD.N0230.N0708.d001177
      (_root_.GD.N0230.N0691.d001209 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0805.d011790 k sizes g.shift g.d009239))
      (_root_.GD.N0230.N0691.d001210 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0805.d011790 k sizes g.shift g.d009239))
      ((toWeakSpace ℝ _).symm p.1.1)
      (_root_.GD.N0232.N0719.N0805.d011798 k sizes g.shift g.d009239 g.d009240 ((toWeakSpace ℝ _).symm p.2.1))
    rw [_root_.GD.N0232.N0719.N0961.d012139 k sizes g _ _ (hfinite p.1.1 p.1.2)]
    constructor
    · intro he
      rw [he, hf]
      rfl
    · intro he
      apply Subtype.ext
      rw [hf]
      exact (toWeakSpace ℝ _).symm.injective he
  rw [hgraph]
  exact (_root_.GD.N0232.N0719.N0805.d011811 k sizes g.shift g.d009239 g.d009240).preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

end

end GD.N0232.N0719.N0961

#print axioms _root_.GD.N0232.N0719.N0961.d012137
#print axioms _root_.GD.N0232.N0719.N0961.d012139
#print axioms _root_.GD.N0232.N0719.N0961.d012140
