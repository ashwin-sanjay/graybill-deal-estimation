import GD.Module1090
import GD.Module0917





























open Filter MeasureTheory Set Topology
open scoped ENNReal Topology

namespace GD
namespace N0232
namespace N0720
namespace N1185

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1036
open _root_.GD.N0232.N0720.N1111
open _root_.GD.N0232.N0720.N1112
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1169
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1177
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0230.N0589
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608

abbrev d017510 :=
  _root_.GD.N0232.N0720.N1173.d015933

abbrev d017511 :=
  _root_.GD.N0232.N0720.N1173.d015936




def d017512
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1185.d017511 → ℝ)
    (weight : _root_.GD.N0232.N0720.N1185.d017510 → ℝ) (x : _root_.GD.N0232.N0720.N1185.d017511) : ℝ :=
  ∫ theta,
    (_root_.GD.N0232.N0720.N1173.d015938 theta - candidate x) * _root_.GD.N0232.N0720.N1173.d015939 weight theta x
      ∂_root_.GD.N0232.N0720.N1173.d015934 rho


def d017513
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1185.d017511 → ℝ)
    (weight : _root_.GD.N0232.N0720.N1185.d017510 → ℝ) (x : _root_.GD.N0232.N0720.N1185.d017511) : ℝ :=
  _root_.GD.N0232.N0720.N1185.d017512 rho candidate weight x ^ 2 /
    _root_.GD.N0232.N0720.N1173.d015940 rho weight x


def d017514
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1185.d017511 → ℝ)
    (weight : _root_.GD.N0232.N0720.N1185.d017510 → ℝ) : ℝ :=
  ∫ x, _root_.GD.N0232.N0720.N1185.d017513 rho candidate weight x
    ∂_root_.GD.N0232.N0720.N1080.d014172 2 2


def d017515
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1185.d017511 → ℝ)
    (weight : _root_.GD.N0232.N0720.N1185.d017510 → ℝ) : ℝ :=
  _root_.GD.N0230.N0589.d000084
      (_root_.GD.N0232.N0720.N1173.d015934 rho) (_root_.GD.N0232.N0720.N1080.d014172 2 2)
        (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938 candidate -
    _root_.GD.N0230.N0589.d000084
      (_root_.GD.N0232.N0720.N1173.d015934 rho) (_root_.GD.N0232.N0720.N1080.d014172 2 2)
        (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938 (_root_.GD.N0232.N0720.N1173.d015943 rho weight)


theorem d017516
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1185.d017511 → ℝ)
    (weight : _root_.GD.N0232.N0720.N1185.d017510 → ℝ) (x : _root_.GD.N0232.N0720.N1185.d017511)
    (hw : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015939 weight theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (htw : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015938 theta * _root_.GD.N0232.N0720.N1173.d015939 weight theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho)) :
    _root_.GD.N0232.N0720.N1185.d017512 rho candidate weight x =
      _root_.GD.N0232.N0720.N1173.d015942 rho weight x -
        candidate x * _root_.GD.N0232.N0720.N1173.d015940 rho weight x := by
  unfold _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1173.d015942 _root_.GD.N0232.N0720.N1173.d015940
    _root_.GD.N0230.N0589.d000088
  let W := fun theta : _root_.GD.N0232.N0720.N1185.d017510 ↦ _root_.GD.N0232.N0720.N1173.d015939 weight theta x
  have hconst : Integrable
      (fun theta ↦ candidate x * W theta)
      (_root_.GD.N0232.N0720.N1173.d015934 rho) := hw.const_mul _
  have hpoint :
      (fun theta ↦ (_root_.GD.N0232.N0720.N1173.d015938 theta - candidate x) * W theta) =
        (fun theta ↦
          _root_.GD.N0232.N0720.N1173.d015938 theta * W theta - candidate x * W theta) := by
    funext theta
    ring
  rw [hpoint, integral_sub htw hconst, integral_const_mul]


theorem d017517
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1185.d017511 → ℝ)
    (weight : _root_.GD.N0232.N0720.N1185.d017510 → ℝ) (x : _root_.GD.N0232.N0720.N1185.d017511)
    (hw : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015939 weight theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (htw : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015938 theta * _root_.GD.N0232.N0720.N1173.d015939 weight theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hmass : _root_.GD.N0232.N0720.N1173.d015940 rho weight x ≠ 0) :
    _root_.GD.N0232.N0720.N1173.d015943 rho weight x - candidate x =
      _root_.GD.N0232.N0720.N1185.d017512 rho candidate weight x /
        _root_.GD.N0232.N0720.N1173.d015940 rho weight x := by
  rw [_root_.GD.N0232.N0720.N1185.d017516 rho candidate weight x hw htw]
  unfold _root_.GD.N0232.N0720.N1173.d015943
  field_simp [hmass]



theorem d017518
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1185.d017511 → ℝ)
    (weight : _root_.GD.N0232.N0720.N1185.d017510 → ℝ) (x : _root_.GD.N0232.N0720.N1185.d017511)
    (hw : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015939 weight theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (htw : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015938 theta * _root_.GD.N0232.N0720.N1173.d015939 weight theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hmass : _root_.GD.N0232.N0720.N1173.d015940 rho weight x ≠ 0) :
    _root_.GD.N0230.N0589.d000089
        (_root_.GD.N0232.N0720.N1173.d015934 rho) (_root_.GD.N0232.N0720.N1173.d015939 weight)
          candidate (_root_.GD.N0232.N0720.N1173.d015943 rho weight) x =
      _root_.GD.N0232.N0720.N1185.d017513 rho candidate weight x := by
  unfold _root_.GD.N0230.N0589.d000089 _root_.GD.N0232.N0720.N1185.d017513
  change _root_.GD.N0232.N0720.N1173.d015940 rho weight x *
      (candidate x - _root_.GD.N0232.N0720.N1173.d015943 rho weight x) ^ 2 = _
  have hshift :=
    _root_.GD.N0232.N0720.N1185.d017517 rho candidate weight x hw htw hmass
  rw [show candidate x - _root_.GD.N0232.N0720.N1173.d015943 rho weight x =
      -(_root_.GD.N0232.N0720.N1173.d015943 rho weight x - candidate x) by ring, hshift]
  field_simp [hmass]








theorem d017519
    (rho : Measure (Set.Ioo (0 : ℝ) 1)) [SigmaFinite rho]
    (candidate : _root_.GD.N0232.N0720.N1185.d017511 → ℝ)
    (weight : _root_.GD.N0232.N0720.N1185.d017510 → ℝ)
    (hcandidateJoint : Integrable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938 candidate).uncurry
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (hcutJoint : Integrable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938
          (_root_.GD.N0232.N0720.N1173.d015943 rho weight)).uncurry
      ((_root_.GD.N0232.N0720.N1173.d015934 rho).prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (htax : Integrable
      (_root_.GD.N0230.N0589.d000089
        (_root_.GD.N0232.N0720.N1173.d015934 rho) (_root_.GD.N0232.N0720.N1173.d015939 weight)
          candidate (_root_.GD.N0232.N0720.N1173.d015943 rho weight))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hmoments : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable
          (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015939 weight theta x)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      Integrable
          (fun theta ↦
            _root_.GD.N0232.N0720.N1173.d015938 theta * _root_.GD.N0232.N0720.N1173.d015939 weight theta x)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      Integrable
          (fun theta ↦
            _root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 * _root_.GD.N0232.N0720.N1173.d015939 weight theta x)
          (_root_.GD.N0232.N0720.N1173.d015934 rho) ∧
      _root_.GD.N0232.N0720.N1173.d015940 rho weight x ≠ 0) :
    _root_.GD.N0232.N0720.N1185.d017515 rho candidate weight =
      _root_.GD.N0232.N0720.N1185.d017514 rho candidate weight := by
  letI : SigmaFinite (_root_.GD.N0232.N0720.N1173.d015934 rho) := by
    unfold _root_.GD.N0232.N0720.N1173.d015934
    infer_instance
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  letI : SFinite (_root_.GD.N0232.N0720.N1080.d014172 2 2) := inferInstance
  have hpointwise : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      _root_.GD.N0230.N0589.d000087
          (_root_.GD.N0232.N0720.N1173.d015934 rho) (_root_.GD.N0232.N0720.N1173.d015939 weight)
            _root_.GD.N0232.N0720.N1173.d015938 x (candidate x) =
        _root_.GD.N0230.N0589.d000087
            (_root_.GD.N0232.N0720.N1173.d015934 rho) (_root_.GD.N0232.N0720.N1173.d015939 weight)
              _root_.GD.N0232.N0720.N1173.d015938 x (_root_.GD.N0232.N0720.N1173.d015943 rho weight x) +
          _root_.GD.N0230.N0589.d000089
            (_root_.GD.N0232.N0720.N1173.d015934 rho) (_root_.GD.N0232.N0720.N1173.d015939 weight)
              candidate (_root_.GD.N0232.N0720.N1173.d015943 rho weight) x := by
    filter_upwards [hmoments] with x hx
    rcases hx with ⟨hw, htw, ht2w, hmass⟩
    simpa [_root_.GD.N0230.N0589.d000089, _root_.GD.N0232.N0720.N1173.d015940, _root_.GD.N0230.N0589.d000088] using
      _root_.GD.N0232.N0720.N1173.d015951
        rho weight x (candidate x) hw htw ht2w hmass
  unfold _root_.GD.N0232.N0720.N1185.d017515
  rw [_root_.GD.N0230.N0589.d000093
    (_root_.GD.N0232.N0720.N1173.d015934 rho) (_root_.GD.N0232.N0720.N1080.d014172 2 2)
    (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938 candidate
    (_root_.GD.N0232.N0720.N1173.d015943 rho weight)
    hcandidateJoint hcutJoint htax hpointwise]
  unfold _root_.GD.N0232.N0720.N1185.d017514
  apply integral_congr_ae
  filter_upwards [hmoments] with x hx
  exact _root_.GD.N0232.N0720.N1185.d017518
    rho candidate weight x hx.1 hx.2.1 hx.2.2.2




theorem d017520
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1185.d017511 → ℝ)
    (base reservoir : _root_.GD.N0232.N0720.N1185.d017510 → ℝ) (x : _root_.GD.N0232.N0720.N1185.d017511)
    (hbase : Integrable
      (fun theta ↦
        (_root_.GD.N0232.N0720.N1173.d015938 theta - candidate x) * _root_.GD.N0232.N0720.N1173.d015939 base theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho))
    (hreservoir : Integrable
      (fun theta ↦
        (_root_.GD.N0232.N0720.N1173.d015938 theta - candidate x) *
          _root_.GD.N0232.N0720.N1173.d015939 reservoir theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 rho)) :
    _root_.GD.N0232.N0720.N1185.d017512 rho candidate
        (fun theta ↦ base theta + reservoir theta) x =
      _root_.GD.N0232.N0720.N1185.d017512 rho candidate base x +
        _root_.GD.N0232.N0720.N1185.d017512 rho candidate reservoir x := by
  unfold _root_.GD.N0232.N0720.N1185.d017512 _root_.GD.N0232.N0720.N1173.d015939 at *
  rw [← integral_add hbase hreservoir]
  apply integral_congr_ae
  filter_upwards [] with theta
  ring



def d017521
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1185.d017511 → ℝ)
    (base reservoir : _root_.GD.N0232.N0720.N1185.d017510 → ℝ) : ℝ :=
  ∫ x,
    (_root_.GD.N0232.N0720.N1185.d017512 rho candidate base x +
        _root_.GD.N0232.N0720.N1185.d017512 rho candidate reservoir x) ^ 2 /
      _root_.GD.N0232.N0720.N1173.d015940 rho base x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2




theorem d017522
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1185.d017511 → ℝ)
    (base reservoir : _root_.GD.N0232.N0720.N1185.d017510 → ℝ) (x : _root_.GD.N0232.N0720.N1185.d017511)
    (hbaseEvidence : 0 < _root_.GD.N0232.N0720.N1173.d015940 rho base x)
    (hreservoirEvidence : 0 ≤ _root_.GD.N0232.N0720.N1173.d015940 rho reservoir x)
    (hevidenceAdd :
      _root_.GD.N0232.N0720.N1173.d015940 rho (fun theta ↦ base theta + reservoir theta) x =
        _root_.GD.N0232.N0720.N1173.d015940 rho base x + _root_.GD.N0232.N0720.N1173.d015940 rho reservoir x)
    (hcurrentAdd :
      _root_.GD.N0232.N0720.N1185.d017512 rho candidate
          (fun theta ↦ base theta + reservoir theta) x =
        _root_.GD.N0232.N0720.N1185.d017512 rho candidate base x +
          _root_.GD.N0232.N0720.N1185.d017512 rho candidate reservoir x) :
    _root_.GD.N0232.N0720.N1185.d017513 rho candidate
        (fun theta ↦ base theta + reservoir theta) x ≤
      (_root_.GD.N0232.N0720.N1185.d017512 rho candidate base x +
          _root_.GD.N0232.N0720.N1185.d017512 rho candidate reservoir x) ^ 2 /
        _root_.GD.N0232.N0720.N1173.d015940 rho base x := by
  unfold _root_.GD.N0232.N0720.N1185.d017513
  rw [hevidenceAdd, hcurrentAdd]
  exact _root_.GD.N0232.N0720.N1169.d017496 _ _ _ _
    hbaseEvidence hreservoirEvidence


theorem d017523
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1185.d017511 → ℝ)
    (base reservoir : _root_.GD.N0232.N0720.N1185.d017510 → ℝ)
    (htotalIntegrable : Integrable
      (_root_.GD.N0232.N0720.N1185.d017513 rho candidate
        (fun theta ↦ base theta + reservoir theta))
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hresidualIntegrable : Integrable
      (fun x ↦
        (_root_.GD.N0232.N0720.N1185.d017512 rho candidate base x +
            _root_.GD.N0232.N0720.N1185.d017512 rho candidate reservoir x) ^ 2 /
          _root_.GD.N0232.N0720.N1173.d015940 rho base x)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hbaseEvidence : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1173.d015940 rho base x)
    (hreservoirEvidence : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 ≤ _root_.GD.N0232.N0720.N1173.d015940 rho reservoir x)
    (hevidenceAdd : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      _root_.GD.N0232.N0720.N1173.d015940 rho (fun theta ↦ base theta + reservoir theta) x =
        _root_.GD.N0232.N0720.N1173.d015940 rho base x + _root_.GD.N0232.N0720.N1173.d015940 rho reservoir x)
    (hcurrentAdd : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      _root_.GD.N0232.N0720.N1185.d017512 rho candidate
          (fun theta ↦ base theta + reservoir theta) x =
        _root_.GD.N0232.N0720.N1185.d017512 rho candidate base x +
          _root_.GD.N0232.N0720.N1185.d017512 rho candidate reservoir x) :
    _root_.GD.N0232.N0720.N1185.d017514 rho candidate
        (fun theta ↦ base theta + reservoir theta) ≤
      _root_.GD.N0232.N0720.N1185.d017521 rho candidate base reservoir := by
  unfold _root_.GD.N0232.N0720.N1185.d017514
    _root_.GD.N0232.N0720.N1185.d017521
  apply integral_mono_ae htotalIntegrable hresidualIntegrable
  filter_upwards [hbaseEvidence, hreservoirEvidence,
    hevidenceAdd, hcurrentAdd] with x hb hr he hc
  exact _root_.GD.N0232.N0720.N1185.d017522
    rho candidate base reservoir x hb hr he hc


theorem d017524
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1185.d017511 → ℝ)
    (weight : _root_.GD.N0232.N0720.N1185.d017510 → ℝ)
    (hevidence : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1173.d015940 rho weight x) :
    0 ≤ _root_.GD.N0232.N0720.N1185.d017514 rho candidate weight := by
  unfold _root_.GD.N0232.N0720.N1185.d017514
    _root_.GD.N0232.N0720.N1185.d017513
  apply integral_nonneg_of_ae
  filter_upwards [hevidence] with x hx
  exact div_nonneg (sq_nonneg _) hx.le



theorem d017525
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (candidate : _root_.GD.N0232.N0720.N1185.d017511 → ℝ)
    (base reservoir : ℕ → _root_.GD.N0232.N0720.N1185.d017510 → ℝ)
    (hcombinedEvidence : ∀ k, ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1173.d015940 rho
        (fun theta ↦ base k theta + reservoir k theta) x)
    (hupper : ∀ k,
      _root_.GD.N0232.N0720.N1185.d017514 rho candidate
          (fun theta ↦ base k theta + reservoir k theta) ≤
        _root_.GD.N0232.N0720.N1185.d017521 rho candidate
          (base k) (reservoir k))
    (hresidualZero : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1185.d017521 rho candidate
        (base k) (reservoir k)) atTop (nhds 0)) :
    Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1185.d017514 rho candidate
        (fun theta ↦ base k theta + reservoir k theta))
      atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hresidualZero
    (Filter.Eventually.of_forall fun k ↦
      _root_.GD.N0232.N0720.N1185.d017524 rho candidate _
        (hcombinedEvidence k))
    (Filter.Eventually.of_forall hupper)




def d017526 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2) :=
  _root_.GD.N0232.N0720.N1080.d014181 2 2 (by norm_num) (by norm_num)


def d017527 : _root_.GD.N0232.N0720.N1185.d017511 → ℝ := fun x ↦ _root_.GD.N0232.N0720.N1185.d017526 x

theorem d017528 :
    _root_.GD.N0232.N0720.N1159.d014637 2 2 _root_.GD.N0232.N0720.N1185.d017526 := by
  apply _root_.GD.N0232.N0720.N1159.d014640 2 2
    _root_.GD.N0232.N0720.N1185.d017526 (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by norm_num) (by norm_num))
  simpa only [_root_.GD.N0232.N0720.N1185.d017526] using
    (_root_.GD.N0232.N0720.N1080.d014186
      2 2 (by norm_num) (by norm_num))

theorem d017529 :
    _root_.GD.N0232.N0720.N1159.d014638 2 2 _root_.GD.N0232.N0720.N1185.d017526 := by
  intro g theta
  simpa only [_root_.GD.N0232.N0720.N1185.d017526] using
    (_root_.GD.N0232.N0720.N1215.d014296 2 2 (by norm_num) (by norm_num) g theta)



def d017530 : _root_.GD.N0232.N0720.N1159.d014639 2 2 where
  value := _root_.GD.N0232.N0720.N1185.d017526
  finiteRisk := _root_.GD.N0232.N0720.N1185.d017528
  riskCharacter := _root_.GD.N0232.N0720.N1185.d017529

@[simp] theorem d017531 :
    _root_.GD.N0232.N0720.N1185.d017530.value = _root_.GD.N0232.N0720.N1185.d017526 := rfl

theorem d017532 :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2) _root_.GD.N0232.N0720.N1185.d017526
      (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by norm_num) (by norm_num)) := by
  simpa only [_root_.GD.N0232.N0720.N1185.d017526] using
    (_root_.GD.N0232.N0720.N1080.d014186
      2 2 (by norm_num) (by norm_num))









theorem d017533
    (prior : ℕ → Measure _root_.GD.N0232.N0720.N1185.d017510)
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (hretain : _root_.GD.N0232.N0720.N1111.d016605 prior)
    (bayes : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hbayes : _root_.GD.N0232.N0720.N1111.d016612
      2 2 _root_.GD.N0232.N0720.N1173.d015935 prior bayes)
    (hcandidateIntegrable : ∀ k, Integrable
      (fun theta ↦
        (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) _root_.GD.N0232.N0720.N1185.d017526).toReal)
      (prior k))
    (base reservoir : ℕ → _root_.GD.N0232.N0720.N1185.d017510 → ℝ)
    (hcombinedEvidence : ∀ k, ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
        (fun theta ↦ base k theta + reservoir k theta) x)
    (hupper : ∀ k,
      _root_.GD.N0232.N0720.N1185.d017514 _root_.GD.N0232.N0720.N1493.d016104
          _root_.GD.N0232.N0720.N1185.d017527 (fun theta ↦ base k theta + reservoir k theta) ≤
        _root_.GD.N0232.N0720.N1185.d017521 _root_.GD.N0232.N0720.N1493.d016104
          _root_.GD.N0232.N0720.N1185.d017527 (base k) (reservoir k))
    (hresidualZero : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1185.d017521
        _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1185.d017527
          (base k) (reservoir k)) atTop (nhds 0))
    (hdeficitEq : ∀ k,
      _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k _root_.GD.N0232.N0720.N1185.d017526 -
        _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k (bayes k) =
          _root_.GD.N0232.N0720.N1185.d017514
            _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1185.d017527
              (fun theta ↦ base k theta + reservoir k theta)) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  apply _root_.GD.N0232.N0720.N1111.d016615
    2 2 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1173.d015935
      (prior := prior) (s := _root_.GD.N0232.N0720.N1185.d017530) (bayes := bayes)
  · unfold _root_.GD.N0232.N0720.N1173.d015935
    exact _root_.GD.N0232.N0720.N1486.d015877 2 2 _ _
  · unfold _root_.GD.N0232.N0720.N1173.d015935
    exact _root_.GD.N0232.N0720.N1486.d015893 2 2 _ _
  · exact hpriorFinite
  · exact hretain
  · simpa only [_root_.GD.N0232.N0720.N1185.d017531] using
      _root_.GD.N0232.N0720.N1185.d017532
  · exact hbayes
  · exact hcandidateIntegrable
  · rw [_root_.GD.N0232.N0720.N1112.d016616]
    simp only [_root_.GD.N0232.N0720.N1185.d017531]
    have hfunctions :
        (fun k ↦
          _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k _root_.GD.N0232.N0720.N1185.d017526 -
            _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k
              (bayes k)) =
          (fun k ↦ _root_.GD.N0232.N0720.N1185.d017514
            _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1185.d017527
              (fun theta ↦ base k theta + reservoir k theta)) := by
      funext k
      exact hdeficitEq k
    rw [hfunctions]
    exact _root_.GD.N0232.N0720.N1185.d017525
      _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1185.d017527 base reservoir
        hcombinedEvidence hupper hresidualZero

end

end N1185
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1185.d017519
#print axioms _root_.GD.N0232.N0720.N1185.d017523
#print axioms _root_.GD.N0232.N0720.N1185.d017532
#print axioms _root_.GD.N0232.N0720.N1185.d017533
