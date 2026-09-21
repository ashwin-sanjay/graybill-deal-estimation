import GD.Module0948
import GD.Module0932










set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Topology
open scoped ENNReal

namespace GD.N0232.N0720.N1255

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1483
open _root_.GD.N0232.N0720.N1025 _root_.GD.N0232.N0720.N1065
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0691 _root_.GD.N0230.N0708
open _root_.GD.N0230.N0582

variable (m n : ℕ)

local instance d014918 : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance

local instance d014919 (theta : _root_.GD.N0232.N0720.N1080.d014168) : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  unfold _root_.GD.N0232.N0720.N1080.d014171
  infer_instance



theorem d014920
    (p : _root_.GD.N0232.N0720.N1483.d014869 m n) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    MemLp (_root_.GD.N0232.N0720.N1214.d014265 m n p) 2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  have hstrong : AEStronglyMeasurable
      (fun omega => _root_.GD.N0232.N0720.N1214.d014265 m n p omega - theta.location) (_root_.GD.N0232.N0720.N1080.d014171 m n theta) :=
    ((_root_.GD.N0232.N0720.N1214.d014266 m n p).sub measurable_const).aestronglyMeasurable
  have herr : MemLp (fun omega => _root_.GD.N0232.N0720.N1214.d014265 m n p omega - theta.location)
      2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    apply (memLp_two_iff_integrable_sq hstrong).2
    have hlin : (∫⁻ omega,
        ENNReal.ofReal ((_root_.GD.N0232.N0720.N1214.d014265 m n p omega - theta.location) ^ 2)
        ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) ≠ ⊤ := by
      change _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1214.d014265 m n p) ≠ ⊤
      rw [_root_.GD.N0232.N0720.N1215.d014286]
      exact hp theta
    have hint := integrable_toReal_of_lintegral_ne_top
      ((hstrong.aemeasurable.pow_const 2).ennreal_ofReal) hlin
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hint
  have hadd := herr.add (memLp_const theta.location :
    MemLp (fun _ : _root_.GD.N0232.N0720.N1080.d014170 m n => theta.location) 2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta))
  convert hadd using 1
  funext omega
  simp

def d014921 (g : _root_.GD.N0232.N0720.N1025.d014301) (p : _root_.GD.N0232.N0720.N1483.d014869 m n)
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) : Lp ℝ 2 (_root_.GD.N0232.N0720.N1483.d014872 m n g) :=
  MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014265 m n p) (by
    rw [_root_.GD.N0232.N0720.N1483.d014874]
    exact _root_.GD.N0232.N0720.N1255.d014920 m n p hp (_root_.GD.N0232.N0720.N1483.d014873 g))

theorem d014922 (g : _root_.GD.N0232.N0720.N1025.d014301)
    (p : _root_.GD.N0232.N0720.N1483.d014869 m n) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g p hp = _root_.GD.N0232.N0720.N1483.d014881 m n g (_root_.GD.N0232.N0720.N1255.d014921 m n g p hp) := by
  apply Lp.ext
  have hout := (_root_.GD.N0232.N0720.N1159.d014641 m n g p hp).coeFn_toLp
  have hpullMem : MemLp (_root_.GD.N0232.N0720.N1214.d014265 m n p) 2 (_root_.GD.N0232.N0720.N1483.d014872 m n g) := by
    rw [_root_.GD.N0232.N0720.N1483.d014874]
    exact _root_.GD.N0232.N0720.N1255.d014920 m n p hp (_root_.GD.N0232.N0720.N1483.d014873 g)
  have hpull : (fun omega => _root_.GD.N0232.N0720.N1255.d014921 m n g p hp omega) =ᵐ[_root_.GD.N0232.N0720.N1483.d014872 m n g]
      _root_.GD.N0232.N0720.N1214.d014265 m n p := hpullMem.coeFn_toLp
  have hpullComp := (_root_.GD.N0232.N0720.N1483.d014875 m n g).quasiMeasurePreserving.ae_eq_comp hpull
  have hencode := Lp.coeFn_compMeasurePreserving (_root_.GD.N0232.N0720.N1255.d014921 m n g p hp)
    (_root_.GD.N0232.N0720.N1483.d014875 m n g)
  let c : _root_.GD.N0232.N0720.N1483.d014869 m n := _root_.GD.N0232.N0720.N1483.d014879 m n g.shift
  let z : _root_.GD.N0232.N0720.N1483.d014869 m n := _root_.GD.N0232.N0720.N1483.d014877 m n g (_root_.GD.N0232.N0720.N1255.d014921 m n g p hp)
  have hc := (memLp_const g.shift : MemLp
    (fun _ : _root_.GD.N0232.N0720.N1080.d014170 m n => g.shift) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n)).coeFn_toLp
  have hs := Lp.coeFn_smul g.d009239 z
  have ha := Lp.coeFn_add c (g.d009239 • z)
  filter_upwards [hout, hpullComp, hencode, hc, hs, ha] with omega ho hpull he hc hs ha
  change _root_.GD.N0232.N0720.N1159.d014642 m n g p hp omega = (c + g.d009239 • z) omega
  rw [ha]
  change _root_.GD.N0232.N0720.N1159.d014642 m n g p hp omega = c omega + (g.d009239 • z) omega
  rw [hs]
  change _root_.GD.N0232.N0720.N1159.d014642 m n g p hp omega = c omega + g.d009239 * z omega
  have hc' : c omega = g.shift := hc
  have he' : z omega = _root_.GD.N0232.N0720.N1255.d014921 m n g p hp (g⁻¹ • omega) := he
  change _root_.GD.N0232.N0720.N1255.d014921 m n g p hp (g⁻¹ • omega) = _root_.GD.N0232.N0720.N1214.d014265 m n p (g⁻¹ • omega) at hpull
  rw [hc', he', hpull]
  exact ho

theorem d014923 (g : _root_.GD.N0232.N0720.N1025.d014301)
    (p : _root_.GD.N0232.N0720.N1483.d014869 m n) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0230.N0708.d001177 (_root_.GD.N0230.N0691.d001209 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g))
      (_root_.GD.N0230.N0691.d001210 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g))
      p (_root_.GD.N0232.N0720.N1255.d014921 m n g p hp) := by
  let hmu := _root_.GD.N0232.N0720.N1214.d014268 m n p
  let hnu : MemLp (_root_.GD.N0232.N0720.N1214.d014265 m n p) 2 (_root_.GD.N0232.N0720.N1483.d014872 m n g) := by
    rw [_root_.GD.N0232.N0720.N1483.d014874]
    exact _root_.GD.N0232.N0720.N1255.d014920 m n p hp (_root_.GD.N0232.N0720.N1483.d014873 g)
  let u := _root_.GD.N0230.N0691.d001218 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g)
    (_root_.GD.N0232.N0720.N1214.d014265 m n p) hmu hnu
  refine ⟨u, ?_, ?_⟩
  · rw [show _root_.GD.N0230.N0691.d001209 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g) u =
        hmu.toLp (_root_.GD.N0232.N0720.N1214.d014265 m n p) from _root_.GD.N0230.N0691.d001219 _ _ _ hmu hnu]
    exact _root_.GD.N0232.N0720.N1214.d014269 m n p
  · exact _root_.GD.N0230.N0691.d001220 _ _ _ hmu hnu

theorem d014924 (g : _root_.GD.N0232.N0720.N1025.d014301)
    (p q : _root_.GD.N0232.N0720.N1483.d014869 m n) (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) :
    _root_.GD.N0230.N0708.d001177 (_root_.GD.N0230.N0691.d001209 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g))
      (_root_.GD.N0230.N0691.d001210 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g)) p (_root_.GD.N0232.N0720.N1483.d014882 m n g q) ↔
      q = _root_.GD.N0232.N0720.N1159.d014642 m n g p hp := by
  constructor
  · intro hb
    have he := _root_.GD.N0232.N0720.N1483.d014896
      (_root_.GD.N0230.N0691.d001209 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g))
      (_root_.GD.N0230.N0691.d001210 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g))
      (_root_.GD.N0232.N0720.N1483.d014895 _ _
        (_root_.GD.N0232.N0720.N1483.d014894 m n g))
      hb (_root_.GD.N0232.N0720.N1255.d014923 m n g p hp)
    calc q = _root_.GD.N0232.N0720.N1483.d014881 m n g (_root_.GD.N0232.N0720.N1483.d014882 m n g q) := (_root_.GD.N0232.N0720.N1483.d014888 m n g q).symm
      _ = _root_.GD.N0232.N0720.N1483.d014881 m n g (_root_.GD.N0232.N0720.N1255.d014921 m n g p hp) := by rw [he]
      _ = _root_.GD.N0232.N0720.N1159.d014642 m n g p hp := (_root_.GD.N0232.N0720.N1255.d014922 m n g p hp).symm
  · intro he
    rw [he, _root_.GD.N0232.N0720.N1255.d014922, _root_.GD.N0232.N0720.N1483.d014887]
    exact _root_.GD.N0232.N0720.N1255.d014923 m n g p hp



theorem d014925
    (C : Set (WeakSpace ℝ (_root_.GD.N0232.N0720.N1483.d014869 m n))) (hC : IsCompact C)
    (hfinite : ∀ p ∈ C, _root_.GD.N0232.N0720.N1159.d014637 m n ((toWeakSpace ℝ _).symm p))
    (g : _root_.GD.N0232.N0720.N1025.d014301) (f : C → C)
    (hf : ∀ p : C, (f p).1 = toWeakSpace ℝ _
      (_root_.GD.N0232.N0720.N1159.d014642 m n g ((toWeakSpace ℝ _).symm p.1) (hfinite p.1 p.2))) :
    Continuous f := by
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  apply _root_.GD.N0230.N0582.d000063
  have hgraph : _root_.GD.N0230.N0582.d000059 f =
      (fun p : C × C => (p.1.1, p.2.1)) ⁻¹' _root_.GD.N0232.N0720.N1483.d014892 m n g := by
    ext p
    change p.2 = f p.1 ↔ _root_.GD.N0230.N0708.d001177
      (_root_.GD.N0230.N0691.d001209 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g))
      (_root_.GD.N0230.N0691.d001210 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g))
      ((toWeakSpace ℝ _).symm p.1.1) (_root_.GD.N0232.N0720.N1483.d014882 m n g ((toWeakSpace ℝ _).symm p.2.1))
    rw [_root_.GD.N0232.N0720.N1255.d014924 m n g _ _ (hfinite p.1.1 p.1.2)]
    constructor
    · intro he
      rw [he, hf]
      rfl
    · intro he
      apply Subtype.ext
      rw [hf]
      exact (toWeakSpace ℝ _).symm.injective he
  rw [hgraph]
  exact (_root_.GD.N0232.N0720.N1483.d014893 m n g).preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

end
end GD.N0232.N0720.N1255

#print axioms _root_.GD.N0232.N0720.N1255.d014925
