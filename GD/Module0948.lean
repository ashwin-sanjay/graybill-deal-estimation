import GD.Module0007
import GD.Module0093
import GD.Module0099
import GD.Module0930














open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1483

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1065
open _root_.GD.N0107
open _root_.GD.N0230.N0582
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0691
open _root_.GD.N0230.N0708
open _root_.GD.N0230.N0715
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

abbrev d014869 := _root_.GD.N0232.N0720.N1025.d014302 m n

noncomputable local instance d014870 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance

noncomputable local instance d014871 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  unfold _root_.GD.N0232.N0720.N1080.d014171
  infer_instance




def d014872 (g : _root_.GD.N0232.N0720.N1025.d014301) :
    Measure (_root_.GD.N0232.N0720.N1080.d014170 m n) :=
  (_root_.GD.N0232.N0720.N1080.d014172 m n).map (fun omega ↦ g⁻¹ • omega)


def d014873 (g : _root_.GD.N0232.N0720.N1025.d014301) : _root_.GD.N0232.N0720.N1080.d014168 :=
  _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ _root_.GD.N0232.N0720.N1080.d014169

theorem d014874 (g : _root_.GD.N0232.N0720.N1025.d014301) :
    _root_.GD.N0232.N0720.N1483.d014872 m n g = _root_.GD.N0232.N0720.N1080.d014171 m n (_root_.GD.N0232.N0720.N1483.d014873 g) := by
  simpa [_root_.GD.N0232.N0720.N1483.d014872, _root_.GD.N0232.N0720.N1483.d014873, _root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1214.d014259] using
    (_root_.GD.N0232.N0720.N1215.d014282 m n g⁻¹ _root_.GD.N0232.N0720.N1080.d014169)



theorem d014875 (g : _root_.GD.N0232.N0720.N1025.d014301) :
    MeasurePreserving (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g⁻¹ • omega)
      (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g) := by
  refine ⟨?_, rfl⟩
  simpa only [_root_.GD.N0232.N0720.N1214.d014259] using
    (_root_.GD.N0107.d009026
      m n g⁻¹.shift g⁻¹.d009239 g⁻¹.d009239)


theorem d014876 (g : _root_.GD.N0232.N0720.N1025.d014301) :
    MeasurePreserving (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g • omega)
      (_root_.GD.N0232.N0720.N1483.d014872 m n g) (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  refine ⟨?_, ?_⟩
  · simpa only [_root_.GD.N0232.N0720.N1214.d014259] using
      (_root_.GD.N0107.d009026
        m n g.shift g.d009239 g.d009239)
  · unfold _root_.GD.N0232.N0720.N1483.d014872
    rw [Measure.map_map]
    · convert Measure.map_id
      funext omega
      exact smul_inv_smul g omega
    · simpa only [_root_.GD.N0232.N0720.N1214.d014259] using
        (_root_.GD.N0107.d009026
          m n g.shift g.d009239 g.d009239)
    · simpa only [_root_.GD.N0232.N0720.N1214.d014259] using
        (_root_.GD.N0107.d009026
          m n g⁻¹.shift g⁻¹.d009239 g⁻¹.d009239)



def d014877 (g : _root_.GD.N0232.N0720.N1025.d014301) :
    Lp ℝ 2 (_root_.GD.N0232.N0720.N1483.d014872 m n g) →L[ℝ] _root_.GD.N0232.N0720.N1483.d014869 m n :=
  (Lp.compMeasurePreservingₗᵢ ℝ
    (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g⁻¹ • omega)
    (_root_.GD.N0232.N0720.N1483.d014875 m n g)).toContinuousLinearMap


def d014878 (g : _root_.GD.N0232.N0720.N1025.d014301) :
    _root_.GD.N0232.N0720.N1483.d014869 m n →L[ℝ] Lp ℝ 2 (_root_.GD.N0232.N0720.N1483.d014872 m n g) :=
  (Lp.compMeasurePreservingₗᵢ ℝ
    (fun omega : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g • omega)
    (_root_.GD.N0232.N0720.N1483.d014876 m n g)).toContinuousLinearMap


def d014879 (c : ℝ) : _root_.GD.N0232.N0720.N1483.d014869 m n :=
  MemLp.toLp (fun _ : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ c) (memLp_const c)


def d014880 (g : _root_.GD.N0232.N0720.N1025.d014301) (c : ℝ) :
    Lp ℝ 2 (_root_.GD.N0232.N0720.N1483.d014872 m n g) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1483.d014872 m n g) := by
    rw [_root_.GD.N0232.N0720.N1483.d014874 m n g]
    infer_instance
  exact MemLp.toLp (fun _ : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ c) (memLp_const c)


def d014881 (g : _root_.GD.N0232.N0720.N1025.d014301)
    (d : Lp ℝ 2 (_root_.GD.N0232.N0720.N1483.d014872 m n g)) : _root_.GD.N0232.N0720.N1483.d014869 m n :=
  _root_.GD.N0232.N0720.N1483.d014879 m n g.shift + g.d009239 • _root_.GD.N0232.N0720.N1483.d014877 m n g d


def d014882 (g : _root_.GD.N0232.N0720.N1025.d014301) (d : _root_.GD.N0232.N0720.N1483.d014869 m n) :
    Lp ℝ 2 (_root_.GD.N0232.N0720.N1483.d014872 m n g) :=
  g.d009239⁻¹ •
    (_root_.GD.N0232.N0720.N1483.d014878 m n g d - _root_.GD.N0232.N0720.N1483.d014880 m n g g.shift)

theorem d014883
    (g : _root_.GD.N0232.N0720.N1025.d014301)
    (d : Lp ℝ 2 (_root_.GD.N0232.N0720.N1483.d014872 m n g)) :
    _root_.GD.N0232.N0720.N1483.d014878 m n g (_root_.GD.N0232.N0720.N1483.d014877 m n g d) = d := by
  apply Lp.ext
  have houter := Lp.coeFn_compMeasurePreserving
    (_root_.GD.N0232.N0720.N1483.d014877 m n g d) (_root_.GD.N0232.N0720.N1483.d014876 m n g)
  have hinner := Lp.coeFn_compMeasurePreserving d
    (_root_.GD.N0232.N0720.N1483.d014875 m n g)
  have hinnerComp :=
    (_root_.GD.N0232.N0720.N1483.d014876 m n g).quasiMeasurePreserving.ae_eq_comp
      hinner
  filter_upwards [houter, hinnerComp] with omega houterOmega hinnerOmega
  calc
    _root_.GD.N0232.N0720.N1483.d014878 m n g (_root_.GD.N0232.N0720.N1483.d014877 m n g d) omega =
        _root_.GD.N0232.N0720.N1483.d014877 m n g d (g • omega) := houterOmega
    _ = d (g⁻¹ • (g • omega)) := hinnerOmega
    _ = d omega := congrArg (fun x ↦ d x) (inv_smul_smul g omega)

theorem d014884
    (g : _root_.GD.N0232.N0720.N1025.d014301) (d : _root_.GD.N0232.N0720.N1483.d014869 m n) :
    _root_.GD.N0232.N0720.N1483.d014877 m n g (_root_.GD.N0232.N0720.N1483.d014878 m n g d) = d := by
  apply Lp.ext
  have houter := Lp.coeFn_compMeasurePreserving
    (_root_.GD.N0232.N0720.N1483.d014878 m n g d) (_root_.GD.N0232.N0720.N1483.d014875 m n g)
  have hinner := Lp.coeFn_compMeasurePreserving d
    (_root_.GD.N0232.N0720.N1483.d014876 m n g)
  have hinnerComp :=
    (_root_.GD.N0232.N0720.N1483.d014875 m n g).quasiMeasurePreserving.ae_eq_comp
      hinner
  filter_upwards [houter, hinnerComp] with omega houterOmega hinnerOmega
  calc
    _root_.GD.N0232.N0720.N1483.d014877 m n g (_root_.GD.N0232.N0720.N1483.d014878 m n g d) omega =
        _root_.GD.N0232.N0720.N1483.d014878 m n g d (g⁻¹ • omega) := houterOmega
    _ = d (g • (g⁻¹ • omega)) := hinnerOmega
    _ = d omega := congrArg (fun x ↦ d x) (smul_inv_smul g omega)

theorem d014885
    (g : _root_.GD.N0232.N0720.N1025.d014301) (c : ℝ) :
    _root_.GD.N0232.N0720.N1483.d014878 m n g (_root_.GD.N0232.N0720.N1483.d014879 m n c) =
      _root_.GD.N0232.N0720.N1483.d014880 m n g c := by
  apply Lp.ext
  have hcomp := Lp.coeFn_compMeasurePreserving
    (_root_.GD.N0232.N0720.N1483.d014879 m n c) (_root_.GD.N0232.N0720.N1483.d014876 m n g)
  have href := (memLp_const c : MemLp
    (fun _ : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ c) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n)).coeFn_toLp
  have hrefComp :=
    (_root_.GD.N0232.N0720.N1483.d014876 m n g).quasiMeasurePreserving.ae_eq_comp
      href
  have hpull :
      (fun omega ↦ _root_.GD.N0232.N0720.N1483.d014880 m n g c omega) =ᵐ[_root_.GD.N0232.N0720.N1483.d014872 m n g]
        fun _ ↦ c := by
    simpa only [_root_.GD.N0232.N0720.N1483.d014880] using
      (show MemLp (fun _ : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ c) 2
          (_root_.GD.N0232.N0720.N1483.d014872 m n g) from by
        letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1483.d014872 m n g) := by
          rw [_root_.GD.N0232.N0720.N1483.d014874 m n g]
          infer_instance
        exact memLp_const c).coeFn_toLp
  filter_upwards [hcomp, hrefComp, hpull] with omega hcompOmega hrefOmega hpullOmega
  calc
    _root_.GD.N0232.N0720.N1483.d014878 m n g (_root_.GD.N0232.N0720.N1483.d014879 m n c) omega =
        _root_.GD.N0232.N0720.N1483.d014879 m n c (g • omega) := hcompOmega
    _ = c := hrefOmega
    _ = _root_.GD.N0232.N0720.N1483.d014880 m n g c omega := hpullOmega.symm

theorem d014886
    (g : _root_.GD.N0232.N0720.N1025.d014301) (c : ℝ) :
    _root_.GD.N0232.N0720.N1483.d014877 m n g (_root_.GD.N0232.N0720.N1483.d014880 m n g c) =
      _root_.GD.N0232.N0720.N1483.d014879 m n c := by
  rw [← _root_.GD.N0232.N0720.N1483.d014884 m n g (_root_.GD.N0232.N0720.N1483.d014879 m n c)]
  rw [_root_.GD.N0232.N0720.N1483.d014885 m n g c]

theorem d014887
    (g : _root_.GD.N0232.N0720.N1025.d014301)
    (d : Lp ℝ 2 (_root_.GD.N0232.N0720.N1483.d014872 m n g)) :
    _root_.GD.N0232.N0720.N1483.d014882 m n g (_root_.GD.N0232.N0720.N1483.d014881 m n g d) = d := by
  unfold _root_.GD.N0232.N0720.N1483.d014882 _root_.GD.N0232.N0720.N1483.d014881
  rw [map_add, map_smul, _root_.GD.N0232.N0720.N1483.d014885,
    _root_.GD.N0232.N0720.N1483.d014883]
  have hcancel : _root_.GD.N0232.N0720.N1483.d014880 m n g g.shift +
      g.d009239 • d - _root_.GD.N0232.N0720.N1483.d014880 m n g g.shift =
      g.d009239 • d := by module
  rw [hcancel, inv_smul_smul₀ g.d009241]

theorem d014888
    (g : _root_.GD.N0232.N0720.N1025.d014301) (d : _root_.GD.N0232.N0720.N1483.d014869 m n) :
    _root_.GD.N0232.N0720.N1483.d014881 m n g (_root_.GD.N0232.N0720.N1483.d014882 m n g d) = d := by
  unfold _root_.GD.N0232.N0720.N1483.d014882 _root_.GD.N0232.N0720.N1483.d014881
  rw [map_smul, map_sub, _root_.GD.N0232.N0720.N1483.d014884,
    _root_.GD.N0232.N0720.N1483.d014886]
  rw [smul_inv_smul₀ g.d009241]
  module




def d014889 (g : _root_.GD.N0232.N0720.N1025.d014301) :
    WeakSpace ℝ (_root_.GD.N0232.N0720.N1483.d014869 m n) →
      WeakSpace ℝ (Lp ℝ 2 (_root_.GD.N0232.N0720.N1483.d014872 m n g)) :=
  fun d ↦ g.d009239⁻¹ •
    (WeakSpace.map (_root_.GD.N0232.N0720.N1483.d014878 m n g) d -
      toWeakSpace ℝ _ (_root_.GD.N0232.N0720.N1483.d014880 m n g g.shift))

theorem d014890 (g : _root_.GD.N0232.N0720.N1025.d014301) :
    Continuous (_root_.GD.N0232.N0720.N1483.d014889 m n g) := by
  exact ((WeakSpace.map (_root_.GD.N0232.N0720.N1483.d014878 m n g)).continuous.sub
    continuous_const).const_smul _

@[simp] theorem d014891
    (g : _root_.GD.N0232.N0720.N1025.d014301) (d : _root_.GD.N0232.N0720.N1483.d014869 m n) :
    _root_.GD.N0232.N0720.N1483.d014889 m n g (toWeakSpace ℝ _ d) =
      toWeakSpace ℝ _ (_root_.GD.N0232.N0720.N1483.d014882 m n g d) := by
  apply (toWeakSpace ℝ (Lp ℝ 2 (_root_.GD.N0232.N0720.N1483.d014872 m n g))).injective
  rfl



def d014892 (g : _root_.GD.N0232.N0720.N1025.d014301) :
    Set (WeakSpace ℝ (_root_.GD.N0232.N0720.N1483.d014869 m n) ×
      WeakSpace ℝ (_root_.GD.N0232.N0720.N1483.d014869 m n)) :=
  {p | (p.1, _root_.GD.N0232.N0720.N1483.d014889 m n g p.2) ∈
    _root_.GD.N0230.N0715.d001272
      (_root_.GD.N0230.N0691.d001209 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g))
      (_root_.GD.N0230.N0691.d001210 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g))}

theorem d014893 (g : _root_.GD.N0232.N0720.N1025.d014301) :
    IsClosed (_root_.GD.N0232.N0720.N1483.d014892 m n g) := by
  apply (_root_.GD.N0230.N0715.d001274
    (_root_.GD.N0230.N0691.d001209 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g))
    (_root_.GD.N0230.N0691.d001210 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g))
    (_root_.GD.N0230.N0691.d001216
      (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g))).preimage
  exact continuous_fst.prodMk
    ((_root_.GD.N0232.N0720.N1483.d014890 m n g).comp continuous_snd)

theorem d014894
    (g : _root_.GD.N0232.N0720.N1025.d014301) :
    _root_.GD.N0232.N0720.N1483.d014872 m n g ≪ _root_.GD.N0232.N0720.N1080.d014172 m n := by
  rw [_root_.GD.N0232.N0720.N1483.d014874 m n g]
  exact _root_.GD.N0232.N0720.N1080.d014173 m n (_root_.GD.N0232.N0720.N1483.d014873 g)

theorem d014895
    {Omega : Type*} [MeasurableSpace Omega]
    (mu nu : Measure Omega) (hnu : nu ≪ mu) :
    Function.Injective (_root_.GD.N0230.N0691.d001209 mu nu) := by
  intro f h hfh
  apply Lp.ext
  have hf := _root_.GD.N0230.N0691.d001211 mu nu f
  have hh := _root_.GD.N0230.N0691.d001211 mu nu h
  have hmu : (fun omega ↦ f omega) =ᵐ[mu] fun omega ↦ h omega := by
    filter_upwards [hf, hh] with omega hfOmega hhOmega
    calc
      f omega = _root_.GD.N0230.N0691.d001209 mu nu f omega := hfOmega.symm
      _ = _root_.GD.N0230.N0691.d001209 mu nu h omega := by rw [hfh]
      _ = h omega := hhOmega
  exact (ae_add_measure_iff).2 ⟨hmu, hnu.ae_eq hmu⟩

theorem d014896
    {H E F : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (left : H →L[ℝ] E) (right : H →L[ℝ] F)
    (hleft : Function.Injective left)
    {x : E} {y z : F}
    (hy : _root_.GD.N0230.N0708.d001177 left right x y)
    (hz : _root_.GD.N0230.N0708.d001177 left right x z) : y = z := by
  obtain ⟨a, haLeft, haRight⟩ := hy
  obtain ⟨b, hbLeft, hbRight⟩ := hz
  have hab : a = b := hleft (haLeft.trans hbLeft.symm)
  calc
    y = right a := haRight.symm
    _ = right b := by rw [hab]
    _ = z := hbRight





theorem d014897
    (theta : _root_.GD.N0232.N0720.N1080.d014168) (d : _root_.GD.N0232.N0720.N1483.d014869 m n)
    (hd : d ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    MemLp (_root_.GD.N0232.N0720.N1214.d014265 m n d) 2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  have hmeas : Measurable (_root_.GD.N0232.N0720.N1214.d014265 m n d) :=
    _root_.GD.N0232.N0720.N1214.d014266 m n d
  have hrisk : _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1214.d014265 m n d) ≠ ⊤ := by
    rw [_root_.GD.N0232.N0720.N1215.d014286 m n theta d]
    apply ne_top_of_le_ne_top _ (hd theta)
    rw [_root_.GD.N0232.N0720.N1080.d014185 m n hm hn theta]
    exact ENNReal.ofReal_ne_top
  have herr : MemLp
      (fun omega ↦ _root_.GD.N0232.N0720.N1214.d014265 m n d omega - theta.location)
      2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    have hstrong : AEStronglyMeasurable
        (fun omega ↦ _root_.GD.N0232.N0720.N1214.d014265 m n d omega - theta.location)
        (_root_.GD.N0232.N0720.N1080.d014171 m n theta) :=
      (hmeas.sub measurable_const).aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq hstrong).2
    have hlin :
        (∫⁻ omega,
          ENNReal.ofReal
            ((_root_.GD.N0232.N0720.N1214.d014265 m n d omega - theta.location) ^ 2)
          ∂_root_.GD.N0232.N0720.N1080.d014171 m n theta) ≠ ⊤ := by
      simpa [_root_.GD.N0232.N0720.N1080.d014197] using hrisk
    have hint := integrable_toReal_of_lintegral_ne_top
      ((hstrong.aemeasurable.pow_const 2).ennreal_ofReal) hlin
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hint
  have hconst : MemLp (fun _ : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ theta.location)
      2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := memLp_const theta.location
  have hadd := herr.add hconst
  convert hadd using 1
  funext omega
  simp


def d014898
    (g : _root_.GD.N0232.N0720.N1025.d014301) (d : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    Lp ℝ 2 (_root_.GD.N0232.N0720.N1483.d014872 m n g) :=
  MemLp.toLp (_root_.GD.N0232.N0720.N1214.d014265 m n d.1) <| by
    rw [_root_.GD.N0232.N0720.N1483.d014874 m n g]
    exact _root_.GD.N0232.N0720.N1483.d014897
      m n hm hn (_root_.GD.N0232.N0720.N1483.d014873 g) d.1 d.2





theorem d014899
    (g : _root_.GD.N0232.N0720.N1025.d014301) (d : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g d.1 d.2 =
      _root_.GD.N0232.N0720.N1483.d014881 m n g (_root_.GD.N0232.N0720.N1483.d014898 m n hm hn g d) := by
  apply Lp.ext
  let hraw : MemLp
      (_root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n d.1)) 2
      (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014288 m n hm hn g d.1 d.2
  have hout := hraw.coeFn_toLp
  let hpullMem : MemLp (_root_.GD.N0232.N0720.N1214.d014265 m n d.1) 2
      (_root_.GD.N0232.N0720.N1483.d014872 m n g) := by
    rw [_root_.GD.N0232.N0720.N1483.d014874 m n g]
    exact _root_.GD.N0232.N0720.N1483.d014897
      m n hm hn (_root_.GD.N0232.N0720.N1483.d014873 g) d.1 d.2
  have hpull :
      (fun omega ↦ _root_.GD.N0232.N0720.N1483.d014898 m n hm hn g d omega) =ᵐ[
          _root_.GD.N0232.N0720.N1483.d014872 m n g] _root_.GD.N0232.N0720.N1214.d014265 m n d.1 := by
    simpa only [_root_.GD.N0232.N0720.N1483.d014898] using hpullMem.coeFn_toLp
  have hpullComp :=
    (_root_.GD.N0232.N0720.N1483.d014875 m n g).quasiMeasurePreserving.ae_eq_comp
      hpull
  have hencode := Lp.coeFn_compMeasurePreserving
    (_root_.GD.N0232.N0720.N1483.d014898 m n hm hn g d)
    (_root_.GD.N0232.N0720.N1483.d014875 m n g)
  let c : _root_.GD.N0232.N0720.N1483.d014869 m n := _root_.GD.N0232.N0720.N1483.d014879 m n g.shift
  let z : _root_.GD.N0232.N0720.N1483.d014869 m n :=
    _root_.GD.N0232.N0720.N1483.d014877 m n g (_root_.GD.N0232.N0720.N1483.d014898 m n hm hn g d)
  have hc := (memLp_const g.shift : MemLp
    (fun _ : _root_.GD.N0232.N0720.N1080.d014170 m n ↦ g.shift) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n)).coeFn_toLp
  have hs := Lp.coeFn_smul g.d009239 z
  have ha := Lp.coeFn_add c (g.d009239 • z)
  filter_upwards [hout, hpullComp, hencode, hc, hs, ha] with omega
      houtOmega hpullOmega hencodeOmega hcOmega hsOmega haOmega
  calc
    _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g d.1 d.2 omega =
        _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n d.1) omega := by
      simpa only [_root_.GD.N0232.N0720.N1215.d014289] using houtOmega
    _ = g.shift + g.d009239 * _root_.GD.N0232.N0720.N1214.d014265 m n d.1 (g⁻¹ • omega) := rfl
    _ = g.shift + g.d009239 *
        _root_.GD.N0232.N0720.N1483.d014898 m n hm hn g d (g⁻¹ • omega) := by
      exact congrArg (fun x : ℝ ↦ g.shift + g.d009239 * x)
        hpullOmega.symm
    _ = g.shift + g.d009239 * z omega := by
      exact congrArg (fun x : ℝ ↦ g.shift + g.d009239 * x)
        hencodeOmega.symm
    _ = c omega + (g.d009239 • z) omega := by
      rw [show c omega = g.shift by simpa only [c, _root_.GD.N0232.N0720.N1483.d014879] using hcOmega]
      rw [show (g.d009239 • z) omega = g.d009239 * z omega by
        simpa only [Pi.smul_apply, smul_eq_mul] using hsOmega]
    _ = (c + g.d009239 • z) omega := haOmega.symm
    _ = _root_.GD.N0232.N0720.N1483.d014881 m n g (_root_.GD.N0232.N0720.N1483.d014898 m n hm hn g d) omega := rfl



theorem d014900
    (g : _root_.GD.N0232.N0720.N1025.d014301) (d : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    _root_.GD.N0230.N0708.d001177
      (_root_.GD.N0230.N0691.d001209 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g))
      (_root_.GD.N0230.N0691.d001210 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g))
      d.1 (_root_.GD.N0232.N0720.N1483.d014898 m n hm hn g d) := by
  let hmu := _root_.GD.N0232.N0720.N1214.d014268 m n d.1
  let hnu : MemLp (_root_.GD.N0232.N0720.N1214.d014265 m n d.1) 2 (_root_.GD.N0232.N0720.N1483.d014872 m n g) := by
    rw [_root_.GD.N0232.N0720.N1483.d014874 m n g]
    exact _root_.GD.N0232.N0720.N1483.d014897
      m n hm hn (_root_.GD.N0232.N0720.N1483.d014873 g) d.1 d.2
  let u := _root_.GD.N0230.N0691.d001218 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g)
    (_root_.GD.N0232.N0720.N1214.d014265 m n d.1) hmu hnu
  refine ⟨u, ?_, ?_⟩
  · rw [show _root_.GD.N0230.N0691.d001209 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g) u =
        hmu.toLp (_root_.GD.N0232.N0720.N1214.d014265 m n d.1) from
      _root_.GD.N0230.N0691.d001219 _ _ _ hmu hnu]
    apply Lp.ext
    exact hmu.coeFn_toLp.trans
      (_root_.GD.N0232.N0720.N1214.d014267 m n d.1)
  · rw [show _root_.GD.N0230.N0691.d001210 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g) u =
        hnu.toLp (_root_.GD.N0232.N0720.N1214.d014265 m n d.1) from
      _root_.GD.N0230.N0691.d001220 _ _ _ hmu hnu]
    rfl



theorem d014901
    (g : _root_.GD.N0232.N0720.N1025.d014301)
    (d e : _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    _root_.GD.N0230.N0708.d001177
        (_root_.GD.N0230.N0691.d001209 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g))
        (_root_.GD.N0230.N0691.d001210 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g))
        d.1 (_root_.GD.N0232.N0720.N1483.d014882 m n g e.1) ↔
      e.1 = _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g d.1 d.2 := by
  let left := _root_.GD.N0230.N0691.d001209 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g)
  let right := _root_.GD.N0230.N0691.d001210 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g)
  constructor
  · intro hbridge
    have hcanonical := _root_.GD.N0232.N0720.N1483.d014900 m n hm hn g d
    have hright : _root_.GD.N0232.N0720.N1483.d014882 m n g e.1 =
        _root_.GD.N0232.N0720.N1483.d014898 m n hm hn g d :=
      _root_.GD.N0232.N0720.N1483.d014896 left right
        (_root_.GD.N0232.N0720.N1483.d014895 _ _
          (_root_.GD.N0232.N0720.N1483.d014894 m n g))
        hbridge hcanonical
    calc
      e.1 = _root_.GD.N0232.N0720.N1483.d014881 m n g (_root_.GD.N0232.N0720.N1483.d014882 m n g e.1) :=
        (_root_.GD.N0232.N0720.N1483.d014888 m n g e.1).symm
      _ = _root_.GD.N0232.N0720.N1483.d014881 m n g (_root_.GD.N0232.N0720.N1483.d014898 m n hm hn g d) := by rw [hright]
      _ = _root_.GD.N0232.N0720.N1215.d014289 m n hm hn g d.1 d.2 :=
        (_root_.GD.N0232.N0720.N1483.d014899
          m n hm hn g d).symm
  · intro he
    rw [he, _root_.GD.N0232.N0720.N1483.d014899]
    rw [_root_.GD.N0232.N0720.N1483.d014887]
    exact _root_.GD.N0232.N0720.N1483.d014900 m n hm hn g d





theorem d014902
    (g : _root_.GD.N0232.N0720.N1025.d014301)
    (d e : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    (d.1, e.1) ∈ _root_.GD.N0232.N0720.N1483.d014892 m n g ↔
      e = _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g d := by
  change _root_.GD.N0230.N0708.d001177
      (_root_.GD.N0230.N0691.d001209 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g))
      (_root_.GD.N0230.N0691.d001210 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1483.d014872 m n g))
      ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm d).1
      (_root_.GD.N0232.N0720.N1483.d014882 m n g ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm e).1) ↔ _
  rw [_root_.GD.N0232.N0720.N1483.d014901
    m n hm hn g
    ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm d)
    ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm e)]
  constructor
  · intro heq
    have hstrong :
        (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm e =
          _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
            ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm d) :=
      Subtype.ext heq
    have hweak := congrArg (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn) hstrong
    simpa only [Equiv.apply_symm_apply, _root_.GD.N0232.N0720.N1025.d014317] using hweak
  · intro heq
    have hstrong := congrArg (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm heq
    have hstrong' :
        (_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm e =
          _root_.GD.N0232.N0720.N1215.d014298 m n hm hn g
            ((_root_.GD.N0232.N0720.N1025.d014307 m n hm hn).symm d) := by
      simpa only [_root_.GD.N0232.N0720.N1025.d014317, Equiv.symm_apply_apply] using hstrong
    exact congrArg Subtype.val hstrong'


theorem d014903 (g : _root_.GD.N0232.N0720.N1025.d014301) :
    IsClosed (_root_.GD.N0230.N0582.d000059 (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g)) := by
  have hpre : _root_.GD.N0230.N0582.d000059 (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g) =
      (fun p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn × _root_.GD.N0232.N0720.N1025.d014304 m n hm hn ↦
        (p.1.1, p.2.1)) ⁻¹' _root_.GD.N0232.N0720.N1483.d014892 m n g := by
    ext p
    exact (_root_.GD.N0232.N0720.N1483.d014902
      m n hm hn g p.1 p.2).symm
  rw [hpre]
  exact (_root_.GD.N0232.N0720.N1483.d014893 m n g).preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))






theorem d014904 (g : _root_.GD.N0232.N0720.N1025.d014301) :
    Continuous (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g) := by
  letI : CompactSpace (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :=
    isCompact_iff_compactSpace.mp (_root_.GD.N0232.N0720.N1025.d014311 m n hm hn)
  exact _root_.GD.N0230.N0582.d000063 _
    (_root_.GD.N0232.N0720.N1483.d014903 m n hm hn g)



theorem d014905
    (g : _root_.GD.N0232.N0720.N1025.d014301) :
    ContinuousOn (_root_.GD.N0232.N0720.N1065.d014576 m n hm hn g)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) := by
  rw [continuousOn_iff_continuous_restrict]
  have hcontinuous : Continuous
      (fun p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn ↦
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1) :=
    continuous_subtype_val.comp
      (_root_.GD.N0232.N0720.N1483.d014904 m n hm hn g)
  convert hcontinuous using 1
  funext p
  exact _root_.GD.N0232.N0720.N1065.d014577 m n hm hn g p.2





theorem d014906 :
    ∃ p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn,
      p.1 ∈ _root_.GD.N0232.N0720.N1065.d014568 m n hm hn ∧
      ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
        _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p := by
  apply _root_.GD.N0232.N0720.N1065.d014613 m n hm hn
  intro g
  exact (_root_.GD.N0232.N0720.N1483.d014905 m n hm hn g).mono
    (_root_.GD.N0232.N0720.N1065.d014600 m n hm hn)

end

end N1483
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1483.d014899
#print axioms _root_.GD.N0232.N0720.N1483.d014893
#print axioms _root_.GD.N0232.N0720.N1483.d014903
#print axioms _root_.GD.N0232.N0720.N1483.d014904
#print axioms _root_.GD.N0232.N0720.N1483.d014906
