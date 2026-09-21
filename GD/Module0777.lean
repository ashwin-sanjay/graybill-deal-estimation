import GD.Module0007
import GD.Module0093
import GD.Module0099
import GD.Module0731
import GD.Module0742
import GD.Module0776























open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0805

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0842
open _root_.GD.N0232.N0719.N0828
open _root_.GD.N0232.N0719.N0849
open _root_.GD.N0232.N0719.N0816
open _root_.GD.N0232.N0719.N0845
open _root_.GD.N0107
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0691
open _root_.GD.N0230.N0708
open _root_.GD.N0230.N0582
open _root_.GD.N0230.N0715

variable
  (k : ℕ) (sizes : Fin k → ℕ)
  (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)

abbrev d011787 :=
  _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)

noncomputable local instance d011788 :
    IsProbabilityMeasure
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  unfold _root_.GD.N0232.N0719.N0859.d010813
    _root_.GD.N0232.N0719.d009182 _root_.GD.N0232.N0719.d009176
  infer_instance

noncomputable local instance d011789
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
  unfold _root_.GD.N0232.N0719.N0859.d010812 _root_.GD.N0232.N0719.d009176
  infer_instance


def d011790 (shift dilation : ℝ) :
    Measure (_root_.GD.N0232.N0719.d009173 k sizes) :=
  (_root_.GD.N0232.N0719.N0859.d010813 k sizes).map
    (_root_.GD.N0232.N0719.N0842.d010907 k sizes shift dilation)


def d011791 (shift dilation : ℝ) (hdilation : 0 < dilation) :
    _root_.GD.N0232.N0719.N0859.d010809 k :=
  _root_.GD.N0232.N0719.N0845.d010881 (_root_.GD.N0232.N0719.N0842.d010906 shift dilation) dilation⁻¹
    (inv_pos.mpr hdilation) (_root_.GD.N0232.N0719.N0859.d010810 k)



theorem d011792
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    _root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation =
      _root_.GD.N0232.N0719.N0859.d010812 k sizes (_root_.GD.N0232.N0719.N0805.d011791 k shift dilation hdilation) := by
  simpa [_root_.GD.N0232.N0719.N0805.d011790, _root_.GD.N0232.N0719.N0805.d011791,
    _root_.GD.N0232.N0719.N0859.d010813,
    _root_.GD.N0232.N0719.N0859.d010812,
    _root_.GD.N0232.N0719.d009182,
    _root_.GD.N0232.N0719.N0842.d010907, _root_.GD.N0232.N0719.N0859.d010810,
    _root_.GD.N0232.N0719.N0845.d010881] using
      (_root_.GD.N0232.N0719.d009188
        k sizes (_root_.GD.N0232.N0719.N0842.d010906 shift dilation) dilation⁻¹
        0 (fun _ : Fin k ↦ (1 : ℝ)))



theorem d011793
    (shift dilation : ℝ) :
    MeasurePreserving
      (_root_.GD.N0232.N0719.N0842.d010907 k sizes shift dilation)
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation) := by
  exact ⟨_root_.GD.N0232.N0719.N0842.d010908 k sizes shift dilation, rfl⟩


theorem d011794
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    MeasurePreserving
      (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation)
      (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation)
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := by
  refine ⟨_root_.GD.N0232.N0719.N0900.d009112 k sizes shift dilation, ?_⟩
  unfold _root_.GD.N0232.N0719.N0805.d011790
  rw [Measure.map_map]
  · convert Measure.map_id
    funext omega
    exact _root_.GD.N0232.N0719.N0842.d010910
      k sizes shift dilation hdilation.ne' omega
  · exact _root_.GD.N0232.N0719.N0900.d009112 k sizes shift dilation
  · exact _root_.GD.N0232.N0719.N0842.d010908 k sizes shift dilation



def d011795
    (shift dilation : ℝ) :
    Lp ℝ 2 (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation) →L[ℝ]
      _root_.GD.N0232.N0719.N0805.d011787 k sizes :=
  (Lp.compMeasurePreservingₗᵢ ℝ
    (_root_.GD.N0232.N0719.N0842.d010907 k sizes shift dilation)
    (_root_.GD.N0232.N0719.N0805.d011793 k sizes shift dilation)).toContinuousLinearMap



def d011796
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    _root_.GD.N0232.N0719.N0805.d011787 k sizes →L[ℝ]
      Lp ℝ 2 (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation) :=
  (Lp.compMeasurePreservingₗᵢ ℝ
    (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation)
    (_root_.GD.N0232.N0719.N0805.d011794
      k sizes shift dilation hdilation)).toContinuousLinearMap


def d011797
    (shift dilation : ℝ) (_hdilation : 0 < dilation)
    (d : Lp ℝ 2 (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation)) :
    _root_.GD.N0232.N0719.N0805.d011787 k sizes :=
  (MemLp.toLp (fun _ : _root_.GD.N0232.N0719.d009173 k sizes ↦ shift)
      (memLp_const shift)) + dilation • _root_.GD.N0232.N0719.N0805.d011795 k sizes shift dilation d



def d011798
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (d : _root_.GD.N0232.N0719.N0805.d011787 k sizes) :
    Lp ℝ 2 (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation) := by
    rw [_root_.GD.N0232.N0719.N0805.d011792 k sizes shift dilation hdilation]
    unfold _root_.GD.N0232.N0719.N0859.d010812 _root_.GD.N0232.N0719.d009176
    infer_instance
  exact dilation⁻¹ •
    (_root_.GD.N0232.N0719.N0805.d011796 k sizes shift dilation hdilation d -
      MemLp.toLp (fun _ : _root_.GD.N0232.N0719.d009173 k sizes ↦ shift)
        (memLp_const shift))


def d011799 (c : ℝ) : _root_.GD.N0232.N0719.N0805.d011787 k sizes :=
  MemLp.toLp (fun _ : _root_.GD.N0232.N0719.d009173 k sizes ↦ c) (memLp_const c)


def d011800
    (shift dilation : ℝ) (hdilation : 0 < dilation) (c : ℝ) :
    Lp ℝ 2 (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation) := by
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation) := by
    rw [_root_.GD.N0232.N0719.N0805.d011792 k sizes shift dilation hdilation]
    unfold _root_.GD.N0232.N0719.N0859.d010812 _root_.GD.N0232.N0719.d009176
    infer_instance
  exact MemLp.toLp (fun _ : _root_.GD.N0232.N0719.d009173 k sizes ↦ c) (memLp_const c)



theorem d011801
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (d : Lp ℝ 2 (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation)) :
    _root_.GD.N0232.N0719.N0805.d011796 k sizes shift dilation hdilation
        (_root_.GD.N0232.N0719.N0805.d011795 k sizes shift dilation d) = d := by
  apply Lp.ext
  have houter := Lp.coeFn_compMeasurePreserving
    (_root_.GD.N0232.N0719.N0805.d011795 k sizes shift dilation d)
    (_root_.GD.N0232.N0719.N0805.d011794
      k sizes shift dilation hdilation)
  have hinner := Lp.coeFn_compMeasurePreserving d
    (_root_.GD.N0232.N0719.N0805.d011793 k sizes shift dilation)
  have hinnerComp :=
    (_root_.GD.N0232.N0719.N0805.d011794
      k sizes shift dilation hdilation).quasiMeasurePreserving.ae_eq_comp hinner
  filter_upwards [houter, hinnerComp] with omega houterOmega hinnerOmega
  calc
    _root_.GD.N0232.N0719.N0805.d011796 k sizes shift dilation hdilation
        (_root_.GD.N0232.N0719.N0805.d011795 k sizes shift dilation d) omega =
        _root_.GD.N0232.N0719.N0805.d011795 k sizes shift dilation d
          (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega) := by
            change ((Lp.compMeasurePreserving
              (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation)
              (_root_.GD.N0232.N0719.N0805.d011794
                k sizes shift dilation hdilation))
                (_root_.GD.N0232.N0719.N0805.d011795 k sizes shift dilation d)) omega = _
            exact houterOmega
    _ = d (_root_.GD.N0232.N0719.N0842.d010907 k sizes shift dilation
          (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega)) := by
            change ((Lp.compMeasurePreserving
              (_root_.GD.N0232.N0719.N0842.d010907 k sizes shift dilation)
              (_root_.GD.N0232.N0719.N0805.d011793
                k sizes shift dilation)) d)
                (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega) = _
            exact hinnerOmega
    _ = d omega := by
      rw [_root_.GD.N0232.N0719.N0842.d010909
        k sizes shift dilation hdilation.ne' omega]



theorem d011802
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (d : _root_.GD.N0232.N0719.N0805.d011787 k sizes) :
    _root_.GD.N0232.N0719.N0805.d011795 k sizes shift dilation
        (_root_.GD.N0232.N0719.N0805.d011796 k sizes shift dilation hdilation d) = d := by
  apply Lp.ext
  have houter := Lp.coeFn_compMeasurePreserving
    (_root_.GD.N0232.N0719.N0805.d011796 k sizes shift dilation hdilation d)
    (_root_.GD.N0232.N0719.N0805.d011793 k sizes shift dilation)
  have hinner := Lp.coeFn_compMeasurePreserving d
    (_root_.GD.N0232.N0719.N0805.d011794
      k sizes shift dilation hdilation)
  have hinnerComp :=
    (_root_.GD.N0232.N0719.N0805.d011793
      k sizes shift dilation).quasiMeasurePreserving.ae_eq_comp hinner
  filter_upwards [houter, hinnerComp] with omega houterOmega hinnerOmega
  calc
    _root_.GD.N0232.N0719.N0805.d011795 k sizes shift dilation
        (_root_.GD.N0232.N0719.N0805.d011796 k sizes shift dilation hdilation d) omega =
        _root_.GD.N0232.N0719.N0805.d011796 k sizes shift dilation hdilation d
          (_root_.GD.N0232.N0719.N0842.d010907 k sizes shift dilation omega) := by
            change ((Lp.compMeasurePreserving
              (_root_.GD.N0232.N0719.N0842.d010907 k sizes shift dilation)
              (_root_.GD.N0232.N0719.N0805.d011793
                k sizes shift dilation))
                (_root_.GD.N0232.N0719.N0805.d011796 k sizes shift dilation hdilation d)) omega = _
            exact houterOmega
    _ = d (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation
          (_root_.GD.N0232.N0719.N0842.d010907 k sizes shift dilation omega)) := by
            change ((Lp.compMeasurePreserving
              (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation)
              (_root_.GD.N0232.N0719.N0805.d011794
                k sizes shift dilation hdilation)) d)
                (_root_.GD.N0232.N0719.N0842.d010907 k sizes shift dilation omega) = _
            exact hinnerOmega
    _ = d omega := by
      rw [_root_.GD.N0232.N0719.N0842.d010910
        k sizes shift dilation hdilation.ne' omega]



theorem d011803
    (shift dilation : ℝ) (hdilation : 0 < dilation) (c : ℝ) :
    _root_.GD.N0232.N0719.N0805.d011796 k sizes shift dilation hdilation (_root_.GD.N0232.N0719.N0805.d011799 k sizes c) =
      _root_.GD.N0232.N0719.N0805.d011800 k sizes shift dilation hdilation c := by
  apply Lp.ext
  have hcomp := Lp.coeFn_compMeasurePreserving
    (_root_.GD.N0232.N0719.N0805.d011799 k sizes c)
    (_root_.GD.N0232.N0719.N0805.d011794
      k sizes shift dilation hdilation)
  have href := (memLp_const c : MemLp
    (fun _ : _root_.GD.N0232.N0719.d009173 k sizes ↦ c) 2
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)).coeFn_toLp
  have hrefComp :=
    (_root_.GD.N0232.N0719.N0805.d011794
      k sizes shift dilation hdilation).quasiMeasurePreserving.ae_eq_comp href
  have hpull :
      (fun omega => _root_.GD.N0232.N0719.N0805.d011800 k sizes shift dilation hdilation c omega) =ᵐ[
        _root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation] fun _ ↦ c := by
    simpa only [_root_.GD.N0232.N0719.N0805.d011800] using
      (show MemLp (fun _ : _root_.GD.N0232.N0719.d009173 k sizes ↦ c) 2
          (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation) from by
        letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation) := by
          rw [_root_.GD.N0232.N0719.N0805.d011792 k sizes shift dilation hdilation]
          unfold _root_.GD.N0232.N0719.N0859.d010812 _root_.GD.N0232.N0719.d009176
          infer_instance
        exact memLp_const c).coeFn_toLp
  filter_upwards [hcomp, hrefComp, hpull] with omega hcompOmega hrefOmega hpullOmega
  calc
    _root_.GD.N0232.N0719.N0805.d011796 k sizes shift dilation hdilation
        (_root_.GD.N0232.N0719.N0805.d011799 k sizes c) omega =
        _root_.GD.N0232.N0719.N0805.d011799 k sizes c
          (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega) := by
            change ((Lp.compMeasurePreserving
              (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation)
              (_root_.GD.N0232.N0719.N0805.d011794
                k sizes shift dilation hdilation))
                (_root_.GD.N0232.N0719.N0805.d011799 k sizes c)) omega = _
            exact hcompOmega
    _ = c := hrefOmega
    _ = _root_.GD.N0232.N0719.N0805.d011800 k sizes shift dilation hdilation c omega := hpullOmega.symm



theorem d011804
    (shift dilation : ℝ) (hdilation : 0 < dilation) (c : ℝ) :
    _root_.GD.N0232.N0719.N0805.d011795 k sizes shift dilation
        (_root_.GD.N0232.N0719.N0805.d011800 k sizes shift dilation hdilation c) =
      _root_.GD.N0232.N0719.N0805.d011799 k sizes c := by
  rw [← _root_.GD.N0232.N0719.N0805.d011802 k sizes shift dilation hdilation
    (_root_.GD.N0232.N0719.N0805.d011799 k sizes c)]
  rw [_root_.GD.N0232.N0719.N0805.d011803 k sizes shift dilation hdilation c]


theorem d011805
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (d : Lp ℝ 2 (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation)) :
    _root_.GD.N0232.N0719.N0805.d011798 k sizes shift dilation hdilation
        (_root_.GD.N0232.N0719.N0805.d011797 k sizes shift dilation hdilation d) = d := by
  unfold _root_.GD.N0232.N0719.N0805.d011798 _root_.GD.N0232.N0719.N0805.d011797
  change dilation⁻¹ •
      (_root_.GD.N0232.N0719.N0805.d011796 k sizes shift dilation hdilation
          (_root_.GD.N0232.N0719.N0805.d011799 k sizes shift +
            dilation • _root_.GD.N0232.N0719.N0805.d011795 k sizes shift dilation d) -
        _root_.GD.N0232.N0719.N0805.d011800 k sizes shift dilation hdilation shift) = d
  rw [map_add, map_smul,
    _root_.GD.N0232.N0719.N0805.d011803 k sizes shift dilation hdilation shift,
    _root_.GD.N0232.N0719.N0805.d011801 k sizes shift dilation hdilation d]
  have hcancel : _root_.GD.N0232.N0719.N0805.d011800 k sizes shift dilation hdilation shift +
      dilation • d - _root_.GD.N0232.N0719.N0805.d011800 k sizes shift dilation hdilation shift =
      dilation • d := by module
  rw [hcancel, inv_smul_smul₀ hdilation.ne']


theorem d011806
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (d : _root_.GD.N0232.N0719.N0805.d011787 k sizes) :
    _root_.GD.N0232.N0719.N0805.d011797 k sizes shift dilation hdilation
        (_root_.GD.N0232.N0719.N0805.d011798 k sizes shift dilation hdilation d) = d := by
  unfold _root_.GD.N0232.N0719.N0805.d011798 _root_.GD.N0232.N0719.N0805.d011797
  change _root_.GD.N0232.N0719.N0805.d011799 k sizes shift + dilation •
      _root_.GD.N0232.N0719.N0805.d011795 k sizes shift dilation
        (dilation⁻¹ •
          (_root_.GD.N0232.N0719.N0805.d011796 k sizes shift dilation hdilation d -
            _root_.GD.N0232.N0719.N0805.d011800 k sizes shift dilation hdilation shift)) = d
  rw [map_smul, map_sub,
    _root_.GD.N0232.N0719.N0805.d011802 k sizes shift dilation hdilation d,
    _root_.GD.N0232.N0719.N0805.d011804 k sizes shift dilation hdilation shift]
  rw [smul_inv_smul₀ hdilation.ne']
  module


def d011807
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    WeakSpace ℝ (_root_.GD.N0232.N0719.N0805.d011787 k sizes) →
      WeakSpace ℝ (Lp ℝ 2 (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation)) :=
  fun d ↦ dilation⁻¹ •
    (WeakSpace.map (_root_.GD.N0232.N0719.N0805.d011796 k sizes shift dilation hdilation) d -
      toWeakSpace ℝ _ (_root_.GD.N0232.N0719.N0805.d011800 k sizes shift dilation hdilation shift))

theorem d011808
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    Continuous (_root_.GD.N0232.N0719.N0805.d011807 k sizes shift dilation hdilation) := by
  exact ((WeakSpace.map
    (_root_.GD.N0232.N0719.N0805.d011796 k sizes shift dilation hdilation)).continuous.sub
      continuous_const).const_smul _

@[simp] theorem d011809
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (d : _root_.GD.N0232.N0719.N0805.d011787 k sizes) :
    _root_.GD.N0232.N0719.N0805.d011807 k sizes shift dilation hdilation (toWeakSpace ℝ _ d) =
      toWeakSpace ℝ _ (_root_.GD.N0232.N0719.N0805.d011798 k sizes shift dilation hdilation d) := by
  apply (toWeakSpace ℝ
    (Lp ℝ 2 (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation))).injective
  rfl




def d011810
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    Set (WeakSpace ℝ (_root_.GD.N0232.N0719.N0805.d011787 k sizes) ×
      WeakSpace ℝ (_root_.GD.N0232.N0719.N0805.d011787 k sizes)) :=
  {p | (p.1, _root_.GD.N0232.N0719.N0805.d011807 k sizes shift dilation hdilation p.2) ∈
    _root_.GD.N0230.N0715.d001272
      (_root_.GD.N0230.N0691.d001209
        (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation))
      (_root_.GD.N0230.N0691.d001210
        (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation))}



theorem d011811
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    IsClosed (_root_.GD.N0232.N0719.N0805.d011810 k sizes shift dilation hdilation) := by
  apply (_root_.GD.N0230.N0715.d001274
    (_root_.GD.N0230.N0691.d001209
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation))
    (_root_.GD.N0230.N0691.d001210
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation))
    (_root_.GD.N0230.N0691.d001216
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation))).preimage
  exact continuous_fst.prodMk
    ((_root_.GD.N0232.N0719.N0805.d011808 k sizes shift dilation hdilation).comp continuous_snd)



theorem d011812
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    _root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation ≪
      _root_.GD.N0232.N0719.N0859.d010813 k sizes := by
  rw [_root_.GD.N0232.N0719.N0805.d011792 k sizes shift dilation hdilation]
  exact _root_.GD.N0232.N0719.N0859.d010814
    k sizes (_root_.GD.N0232.N0719.N0805.d011791 k shift dilation hdilation)




theorem d011813
    {Omega : Type*} [MeasurableSpace Omega]
    (mu nu : Measure Omega) (hnu : nu ≪ mu) :
    Function.Injective (_root_.GD.N0230.N0691.d001209 mu nu) := by
  intro f g hfg
  apply Lp.ext
  have hf := _root_.GD.N0230.N0691.d001211 mu nu f
  have hg := _root_.GD.N0230.N0691.d001211 mu nu g
  have hmu : (fun omega ↦ f omega) =ᵐ[mu] fun omega ↦ g omega := by
    filter_upwards [hf, hg] with omega hfOmega hgOmega
    calc
      f omega = _root_.GD.N0230.N0691.d001209 mu nu f omega := hfOmega.symm
      _ = _root_.GD.N0230.N0691.d001209 mu nu g omega := by rw [hfg]
      _ = g omega := hgOmega
  exact (ae_add_measure_iff).2 ⟨hmu, hnu.ae_eq hmu⟩



theorem d011814
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



theorem d011815
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (d : _root_.GD.N0232.N0719.N0805.d011787 k sizes)
    (hd : d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes) :
    MemLp (_root_.GD.N0232.N0719.N0849.d011768 k sizes d) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
  have hmeas : Measurable (_root_.GD.N0232.N0719.N0849.d011768 k sizes d) :=
    _root_.GD.N0232.N0719.N0849.d011769 k sizes d
  have hrisk : _root_.GD.N0232.N0719.N0859.d010840 k sizes theta
      (_root_.GD.N0232.N0719.N0849.d011768 k sizes d) ≠ ⊤ := by
    rw [_root_.GD.N0232.N0719.N0849.d011773 k sizes theta
      (_root_.GD.N0232.N0719.N0849.d011768 k sizes d)
      (_root_.GD.N0232.N0719.N0849.d011771 k sizes d)]
    rw [_root_.GD.N0232.N0719.N0849.d011772 k sizes d]
    apply (lt_top_iff_ne_top).mp
    exact (hd theta).trans_lt (by simp [_root_.GD.N0232.N0719.N0858.d010852])
  have herr : MemLp
      (fun omega ↦ _root_.GD.N0232.N0719.N0849.d011768 k sizes d omega - theta.location)
      2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
    have hstrong : AEStronglyMeasurable
        (fun omega ↦ _root_.GD.N0232.N0719.N0849.d011768 k sizes d omega - theta.location)
        (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) :=
      (hmeas.sub measurable_const).aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq hstrong).2
    have hlin :
        (∫⁻ omega,
          ENNReal.ofReal
            ((_root_.GD.N0232.N0719.N0849.d011768 k sizes d omega - theta.location) ^ 2)
          ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) ≠ ⊤ := by
      simpa [_root_.GD.N0232.N0719.N0859.d010840] using hrisk
    have hint := integrable_toReal_of_lintegral_ne_top
      ((hstrong.aemeasurable.pow_const 2).ennreal_ofReal) hlin
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using hint
  have hconst : MemLp (fun _ : _root_.GD.N0232.N0719.d009173 k sizes ↦ theta.location)
      2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := memLp_const theta.location
  have hadd := herr.add hconst
  convert hadd using 1
  funext omega
  simp


def d011816
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (d : {d : _root_.GD.N0232.N0719.N0805.d011787 k sizes // d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes}) :
    Lp ℝ 2 (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation) :=
  MemLp.toLp (_root_.GD.N0232.N0719.N0849.d011768 k sizes d.1) <| by
    rw [_root_.GD.N0232.N0719.N0805.d011792 k sizes shift dilation hdilation]
    exact _root_.GD.N0232.N0719.N0805.d011815
      k sizes hk hsizes
      (_root_.GD.N0232.N0719.N0805.d011791 k shift dilation hdilation) d.1 d.2


def d011817
    (shift dilation : ℝ)
    (d : {d : _root_.GD.N0232.N0719.N0805.d011787 k sizes // d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes}) :
    _root_.GD.N0232.N0719.d009173 k sizes → ℝ :=
  _root_.GD.N0232.N0719.N0842.d010911 k sizes shift dilation (_root_.GD.N0232.N0719.N0849.d011768 k sizes d.1)

theorem d011818
    (shift dilation : ℝ)
    (d : {d : _root_.GD.N0232.N0719.N0805.d011787 k sizes // d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes}) :
    Measurable (_root_.GD.N0232.N0719.N0805.d011817 k sizes hk hsizes shift dilation d) :=
  _root_.GD.N0232.N0719.N0842.d010912 k sizes shift dilation _
    (_root_.GD.N0232.N0719.N0849.d011769 k sizes d.1)

theorem d011819
    (d : {d : _root_.GD.N0232.N0719.N0805.d011787 k sizes // d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes}) :
    _root_.GD.N0232.N0719.N0842.d010921 k sizes hk hsizes
      (_root_.GD.N0232.N0719.N0849.d011768 k sizes d.1) := by
  intro theta
  rw [_root_.GD.N0232.N0719.N0849.d011773 k sizes theta
    (_root_.GD.N0232.N0719.N0849.d011768 k sizes d.1)
    (_root_.GD.N0232.N0719.N0849.d011771 k sizes d.1)]
  rw [_root_.GD.N0232.N0719.N0849.d011772 k sizes d.1]
  exact d.2 theta

theorem d011820
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (d : {d : _root_.GD.N0232.N0719.N0805.d011787 k sizes // d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes}) :
    _root_.GD.N0232.N0719.N0842.d010921 k sizes hk hsizes
      (_root_.GD.N0232.N0719.N0805.d011817 k sizes hk hsizes shift dilation d) :=
  _root_.GD.N0232.N0719.N0842.d010922 k sizes hk hsizes
    shift dilation hdilation _
    (_root_.GD.N0232.N0719.N0849.d011769 k sizes d.1)
    (_root_.GD.N0232.N0719.N0805.d011819 k sizes hk hsizes d)


def d011821
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    {d : _root_.GD.N0232.N0719.N0805.d011787 k sizes // d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes} →
      {d : _root_.GD.N0232.N0719.N0805.d011787 k sizes // d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes} :=
  fun d ↦
    ⟨MemLp.toLp (_root_.GD.N0232.N0719.N0805.d011817 k sizes hk hsizes shift dilation d)
        (_root_.GD.N0232.N0719.N0849.d011774 k sizes hk hsizes _
          (_root_.GD.N0232.N0719.N0805.d011818 k sizes hk hsizes shift dilation d)
          (_root_.GD.N0232.N0719.N0805.d011820 k sizes hk hsizes
            shift dilation hdilation d)),
      _root_.GD.N0232.N0719.N0849.d011775 k sizes hk hsizes _
        (_root_.GD.N0232.N0719.N0805.d011818 k sizes hk hsizes shift dilation d)
        (_root_.GD.N0232.N0719.N0805.d011820 k sizes hk hsizes
          shift dilation hdilation d)⟩



theorem d011822
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (d : {d : _root_.GD.N0232.N0719.N0805.d011787 k sizes // d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes}) :
    (_root_.GD.N0232.N0719.N0805.d011821 k sizes hk hsizes shift dilation hdilation d).1 =
      _root_.GD.N0232.N0719.N0805.d011797 k sizes shift dilation hdilation
        (_root_.GD.N0232.N0719.N0805.d011816 k sizes hk hsizes shift dilation hdilation d) := by
  apply Lp.ext
  let hraw : MemLp
      (_root_.GD.N0232.N0719.N0805.d011817 k sizes hk hsizes shift dilation d) 2
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
    _root_.GD.N0232.N0719.N0849.d011774 k sizes hk hsizes _
      (_root_.GD.N0232.N0719.N0805.d011818 k sizes hk hsizes shift dilation d)
      (_root_.GD.N0232.N0719.N0805.d011820 k sizes hk hsizes
        shift dilation hdilation d)
  have hout := hraw.coeFn_toLp
  let hpullMem : MemLp (_root_.GD.N0232.N0719.N0849.d011768 k sizes d.1) 2
      (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation) := by
    rw [_root_.GD.N0232.N0719.N0805.d011792 k sizes shift dilation hdilation]
    exact _root_.GD.N0232.N0719.N0805.d011815
      k sizes hk hsizes
      (_root_.GD.N0232.N0719.N0805.d011791 k shift dilation hdilation) d.1 d.2
  have hpull :
      (fun omega =>
        _root_.GD.N0232.N0719.N0805.d011816 k sizes hk hsizes shift dilation hdilation d omega) =ᵐ[
          _root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation]
        _root_.GD.N0232.N0719.N0849.d011768 k sizes d.1 := by
    simpa only [_root_.GD.N0232.N0719.N0805.d011816] using hpullMem.coeFn_toLp
  have hpullComp :=
    (_root_.GD.N0232.N0719.N0805.d011793 k sizes shift dilation).quasiMeasurePreserving.ae_eq_comp
      hpull
  have hencode := Lp.coeFn_compMeasurePreserving
    (_root_.GD.N0232.N0719.N0805.d011816 k sizes hk hsizes shift dilation hdilation d)
    (_root_.GD.N0232.N0719.N0805.d011793 k sizes shift dilation)
  let c : _root_.GD.N0232.N0719.N0805.d011787 k sizes :=
    MemLp.toLp (fun _ : _root_.GD.N0232.N0719.d009173 k sizes ↦ shift) (memLp_const shift)
  let z : _root_.GD.N0232.N0719.N0805.d011787 k sizes :=
    _root_.GD.N0232.N0719.N0805.d011795 k sizes shift dilation
      (_root_.GD.N0232.N0719.N0805.d011816 k sizes hk hsizes shift dilation hdilation d)
  have hc := (memLp_const shift : MemLp
    (fun _ : _root_.GD.N0232.N0719.d009173 k sizes ↦ shift) 2
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)).coeFn_toLp
  have hs := Lp.coeFn_smul dilation z
  have ha := Lp.coeFn_add c (dilation • z)
  filter_upwards [hout, hpullComp, hencode, hc, hs, ha] with omega
      houtOmega hpullOmega hencodeOmega hcOmega hsOmega haOmega
  calc
    (_root_.GD.N0232.N0719.N0805.d011821 k sizes hk hsizes shift dilation hdilation d).1 omega =
        _root_.GD.N0232.N0719.N0805.d011817 k sizes hk hsizes shift dilation d omega := by
          simpa only [_root_.GD.N0232.N0719.N0805.d011821] using houtOmega
    _ = shift + dilation *
        _root_.GD.N0232.N0719.N0849.d011768 k sizes d.1
          (_root_.GD.N0232.N0719.N0842.d010907 k sizes shift dilation omega) := rfl
    _ = shift + dilation *
        (_root_.GD.N0232.N0719.N0805.d011816 k sizes hk hsizes shift dilation hdilation d)
          (_root_.GD.N0232.N0719.N0842.d010907 k sizes shift dilation omega) := by
          exact congrArg (fun x : ℝ ↦ shift + dilation * x) hpullOmega.symm
    _ = shift + dilation * z omega := by
          exact congrArg (fun x : ℝ ↦ shift + dilation * x) hencodeOmega.symm
    _ = c omega + (dilation • z) omega := by
          rw [show c omega = shift by simpa only [c] using hcOmega]
          rw [show (dilation • z) omega = dilation * z omega by
            simpa only [Pi.smul_apply, smul_eq_mul] using hsOmega]
    _ = (c + dilation • z) omega := haOmega.symm
    _ = (_root_.GD.N0232.N0719.N0805.d011797 k sizes shift dilation hdilation
        (_root_.GD.N0232.N0719.N0805.d011816 k sizes hk hsizes shift dilation hdilation d)) omega := rfl



theorem d011823
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (d : {d : _root_.GD.N0232.N0719.N0805.d011787 k sizes // d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes}) :
    _root_.GD.N0230.N0708.d001177
      (_root_.GD.N0230.N0691.d001209
        (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation))
      (_root_.GD.N0230.N0691.d001210
        (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation))
      d.1 (_root_.GD.N0232.N0719.N0805.d011816 k sizes hk hsizes shift dilation hdilation d) := by
  let hmu := _root_.GD.N0232.N0719.N0849.d011771 k sizes d.1
  let hnu : MemLp (_root_.GD.N0232.N0719.N0849.d011768 k sizes d.1) 2
      (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation) := by
    rw [_root_.GD.N0232.N0719.N0805.d011792 k sizes shift dilation hdilation]
    exact _root_.GD.N0232.N0719.N0805.d011815
      k sizes hk hsizes
      (_root_.GD.N0232.N0719.N0805.d011791 k shift dilation hdilation) d.1 d.2
  let u := _root_.GD.N0230.N0691.d001218
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
    (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation)
    (_root_.GD.N0232.N0719.N0849.d011768 k sizes d.1) hmu hnu
  refine ⟨u, ?_, ?_⟩
  · rw [show _root_.GD.N0230.N0691.d001209
        (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation) u =
        hmu.toLp (_root_.GD.N0232.N0719.N0849.d011768 k sizes d.1) from
      _root_.GD.N0230.N0691.d001219 _ _ _ hmu hnu]
    apply Lp.ext
    exact hmu.coeFn_toLp.trans
      (_root_.GD.N0232.N0719.N0849.d011770 k sizes d.1)
  · rw [show _root_.GD.N0230.N0691.d001210
        (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation) u =
        hnu.toLp (_root_.GD.N0232.N0719.N0849.d011768 k sizes d.1) from
      _root_.GD.N0230.N0691.d001220 _ _ _ hmu hnu]
    rfl



theorem d011824
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (d e : {d : _root_.GD.N0232.N0719.N0805.d011787 k sizes // d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes}) :
    _root_.GD.N0230.N0708.d001177
        (_root_.GD.N0230.N0691.d001209
          (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
          (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation))
        (_root_.GD.N0230.N0691.d001210
          (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
          (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation))
        d.1 (_root_.GD.N0232.N0719.N0805.d011798 k sizes shift dilation hdilation e.1) ↔
      e.1 = (_root_.GD.N0232.N0719.N0805.d011821 k sizes hk hsizes
        shift dilation hdilation d).1 := by
  let left := _root_.GD.N0230.N0691.d001209
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
    (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation)
  let right := _root_.GD.N0230.N0691.d001210
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
    (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation)
  constructor
  · intro hbridge
    have hcanonical := _root_.GD.N0232.N0719.N0805.d011823
      k sizes hk hsizes shift dilation hdilation d
    have hright : _root_.GD.N0232.N0719.N0805.d011798 k sizes shift dilation hdilation e.1 =
        _root_.GD.N0232.N0719.N0805.d011816 k sizes hk hsizes shift dilation hdilation d :=
      _root_.GD.N0232.N0719.N0805.d011814 left right
        (_root_.GD.N0232.N0719.N0805.d011813 _ _
          (_root_.GD.N0232.N0719.N0805.d011812
            k sizes shift dilation hdilation)) hbridge hcanonical
    calc
      e.1 = _root_.GD.N0232.N0719.N0805.d011797 k sizes shift dilation hdilation
          (_root_.GD.N0232.N0719.N0805.d011798 k sizes shift dilation hdilation e.1) :=
        (_root_.GD.N0232.N0719.N0805.d011806 k sizes shift dilation hdilation e.1).symm
      _ = _root_.GD.N0232.N0719.N0805.d011797 k sizes shift dilation hdilation
          (_root_.GD.N0232.N0719.N0805.d011816 k sizes hk hsizes shift dilation hdilation d) := by
            rw [hright]
      _ = (_root_.GD.N0232.N0719.N0805.d011821 k sizes hk hsizes
          shift dilation hdilation d).1 :=
        (_root_.GD.N0232.N0719.N0805.d011822
          k sizes hk hsizes shift dilation hdilation d).symm
  · intro he
    rw [he]
    rw [_root_.GD.N0232.N0719.N0805.d011822
      k sizes hk hsizes shift dilation hdilation d]
    rw [_root_.GD.N0232.N0719.N0805.d011805 k sizes shift dilation hdilation]
    exact _root_.GD.N0232.N0719.N0805.d011823
      k sizes hk hsizes shift dilation hdilation d




abbrev d011825 :=
  {w : WeakSpace ℝ (_root_.GD.N0232.N0719.N0805.d011787 k sizes) //
    w ∈ _root_.GD.N0232.N0719.N0850.d011063
      k sizes hk hsizes}


def d011826 (d : _root_.GD.N0232.N0719.N0805.d011825 k sizes hk hsizes) :
    {d : _root_.GD.N0232.N0719.N0805.d011787 k sizes // d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes} := by
  refine ⟨(toWeakSpace ℝ (_root_.GD.N0232.N0719.N0805.d011787 k sizes)).symm d.1, ?_⟩
  have hmem : (toWeakSpace ℝ (_root_.GD.N0232.N0719.N0805.d011787 k sizes)).symm d.1 ∈
      (toWeakSpace ℝ (_root_.GD.N0232.N0719.N0805.d011787 k sizes)).symm ''
        _root_.GD.N0232.N0719.N0850.d011063
          k sizes hk hsizes := ⟨d.1, d.2, rfl⟩
  rw [← _root_.GD.N0232.N0719.N0850.d011064]
  exact hmem


def d011827
    (d : {d : _root_.GD.N0232.N0719.N0805.d011787 k sizes // d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes}) :
    _root_.GD.N0232.N0719.N0805.d011825 k sizes hk hsizes :=
  ⟨toWeakSpace ℝ (_root_.GD.N0232.N0719.N0805.d011787 k sizes) d.1, ⟨d.1, d.2, rfl⟩⟩

@[simp] theorem d011828
    (d : {d : _root_.GD.N0232.N0719.N0805.d011787 k sizes // d ∈ _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes}) :
    _root_.GD.N0232.N0719.N0805.d011826 k sizes hk hsizes (_root_.GD.N0232.N0719.N0805.d011827 k sizes hk hsizes d) = d := by
  apply Subtype.ext
  rfl

@[simp] theorem d011829
    (d : _root_.GD.N0232.N0719.N0805.d011825 k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0805.d011827 k sizes hk hsizes (_root_.GD.N0232.N0719.N0805.d011826 k sizes hk hsizes d) = d := by
  apply Subtype.ext
  exact (toWeakSpace ℝ (_root_.GD.N0232.N0719.N0805.d011787 k sizes)).apply_symm_apply d.1



def d011830
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    _root_.GD.N0232.N0719.N0805.d011825 k sizes hk hsizes → _root_.GD.N0232.N0719.N0805.d011825 k sizes hk hsizes :=
  fun d ↦ _root_.GD.N0232.N0719.N0805.d011827 k sizes hk hsizes
    (_root_.GD.N0232.N0719.N0805.d011821 k sizes hk hsizes shift dilation hdilation
      (_root_.GD.N0232.N0719.N0805.d011826 k sizes hk hsizes d))



theorem d011831
    (shift dilation : ℝ) (hdilation : 0 < dilation)
    (d e : _root_.GD.N0232.N0719.N0805.d011825 k sizes hk hsizes) :
    (d.1, e.1) ∈ _root_.GD.N0232.N0719.N0805.d011810 k sizes
        shift dilation hdilation ↔
      e = _root_.GD.N0232.N0719.N0805.d011830 k sizes hk hsizes
        shift dilation hdilation d := by
  change _root_.GD.N0230.N0708.d001177
      (_root_.GD.N0230.N0691.d001209
        (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation))
      (_root_.GD.N0230.N0691.d001210
        (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
        (_root_.GD.N0232.N0719.N0805.d011790 k sizes shift dilation))
      (_root_.GD.N0232.N0719.N0805.d011826 k sizes hk hsizes d).1
      (_root_.GD.N0232.N0719.N0805.d011798 k sizes shift dilation hdilation
        (_root_.GD.N0232.N0719.N0805.d011826 k sizes hk hsizes e).1) ↔ _
  rw [_root_.GD.N0232.N0719.N0805.d011824
    k sizes hk hsizes shift dilation hdilation
    (_root_.GD.N0232.N0719.N0805.d011826 k sizes hk hsizes d)
    (_root_.GD.N0232.N0719.N0805.d011826 k sizes hk hsizes e)]
  constructor
  · intro heq
    apply Subtype.ext
    have hweak := congrArg (toWeakSpace ℝ (_root_.GD.N0232.N0719.N0805.d011787 k sizes)) heq
    simpa only [_root_.GD.N0232.N0719.N0805.d011826, _root_.GD.N0232.N0719.N0805.d011830, _root_.GD.N0232.N0719.N0805.d011827,
      LinearEquiv.apply_symm_apply] using hweak
  · intro heq
    have hval := congrArg
      (fun w : _root_.GD.N0232.N0719.N0805.d011825 k sizes hk hsizes ↦
        (toWeakSpace ℝ (_root_.GD.N0232.N0719.N0805.d011787 k sizes)).symm w.1) heq
    simpa only [_root_.GD.N0232.N0719.N0805.d011826, _root_.GD.N0232.N0719.N0805.d011830, _root_.GD.N0232.N0719.N0805.d011827,
      LinearEquiv.symm_apply_apply] using hval


theorem d011832
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    IsClosed (_root_.GD.N0230.N0582.d000059 (_root_.GD.N0232.N0719.N0805.d011830 k sizes hk hsizes
      shift dilation hdilation)) := by
  have hpre : _root_.GD.N0230.N0582.d000059 (_root_.GD.N0232.N0719.N0805.d011830 k sizes hk hsizes
        shift dilation hdilation) =
      (fun p : _root_.GD.N0232.N0719.N0805.d011825 k sizes hk hsizes × _root_.GD.N0232.N0719.N0805.d011825 k sizes hk hsizes ↦
        (p.1.1, p.2.1)) ⁻¹'
        _root_.GD.N0232.N0719.N0805.d011810 k sizes shift dilation hdilation := by
    ext p
    exact (_root_.GD.N0232.N0719.N0805.d011831
      k sizes hk hsizes shift dilation hdilation p.1 p.2).symm
  rw [hpre]
  exact (_root_.GD.N0232.N0719.N0805.d011811
    k sizes shift dilation hdilation).preimage
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))






theorem d011833
    (shift dilation : ℝ) (hdilation : 0 < dilation) :
    Continuous (_root_.GD.N0232.N0719.N0805.d011830 k sizes hk hsizes
      shift dilation hdilation) := by
  letI : CompactSpace (_root_.GD.N0232.N0719.N0805.d011825 k sizes hk hsizes) :=
    isCompact_iff_compactSpace.mp
      (_root_.GD.N0232.N0719.N0850.d011067
        k sizes hk hsizes)
  exact _root_.GD.N0230.N0582.d000063 _
    (_root_.GD.N0232.N0719.N0805.d011832
      k sizes hk hsizes shift dilation hdilation)

end

end N0805
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0805.d011822
#print axioms _root_.GD.N0232.N0719.N0805.d011811
#print axioms _root_.GD.N0232.N0719.N0805.d011824
#print axioms _root_.GD.N0232.N0719.N0805.d011832
#print axioms _root_.GD.N0232.N0719.N0805.d011833
