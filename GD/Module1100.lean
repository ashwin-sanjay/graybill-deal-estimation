import GD.Module1092
import GD.Module0963



















open Filter MeasureTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1193

noncomputable section

open _root_.GD.N0232.N0720.N1036
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1111
open _root_.GD.N0232.N0720.N1112
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1177
open _root_.GD.N0232.N0720.N1185
open _root_.GD.N0232.N0720.N1190
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0606
open _root_.GD.N0230.N0608

abbrev d017642 :=
  _root_.GD.N0232.N0720.N1173.d015933



theorem d017643
    (hterminal : _root_.GD.N0232.N0720.N1036.d014669 2 2 _root_.GD.N0232.N0720.N1185.d017526) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := 2) (n := 2) _root_.GD.N0232.N0720.N1185.d017530 = 0 := by
  apply (_root_.GD.N0232.N0720.N1482.d015171
    (m := 2) (n := 2) _root_.GD.N0232.N0720.N1185.d017530).2
  exact _root_.GD.N0232.N0720.N1036.d014671
    2 2 _root_.GD.N0232.N0720.N1185.d017530 hterminal





theorem d017644
    (hpos : 0 <
      _root_.GD.N0232.N0720.N1482.d015169 (m := 2) (n := 2) _root_.GD.N0232.N0720.N1185.d017530) :
    ¬ _root_.GD.N0232.N0720.N1036.d014669 2 2 _root_.GD.N0232.N0720.N1185.d017526 := by
  intro hterminal
  rw [_root_.GD.N0232.N0720.N1193.d017643 hterminal]
    at hpos
  exact (lt_self_iff_false 0).mp hpos



theorem d017645
    (prior : ℕ → Measure _root_.GD.N0232.N0720.N1193.d017642)
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (hretain : _root_.GD.N0232.N0720.N1111.d016605 prior)
    (bayes : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hbayes : _root_.GD.N0232.N0720.N1111.d016612
      2 2 _root_.GD.N0232.N0720.N1173.d015935 prior bayes)
    (hcandidateIntegrable : ∀ k, Integrable
      (fun theta ↦
        (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) _root_.GD.N0232.N0720.N1185.d017526).toReal)
      (prior k))
    (hdeficitZero : _root_.GD.N0230.N0606.d000961 (fun k ↦
      _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k _root_.GD.N0232.N0720.N1185.d017526 -
        _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k (bayes k))) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := 2) (n := 2) _root_.GD.N0232.N0720.N1185.d017530 = 0 := by
  apply _root_.GD.N0232.N0720.N1193.d017643
  apply _root_.GD.N0232.N0720.N1111.d016614
    2 2 _root_.GD.N0232.N0720.N1173.d015935
  · unfold _root_.GD.N0232.N0720.N1173.d015935
    exact _root_.GD.N0232.N0720.N1486.d015877 2 2 _ _
  · unfold _root_.GD.N0232.N0720.N1173.d015935
    exact _root_.GD.N0232.N0720.N1486.d015893 2 2 _ _
  · exact hpriorFinite
  · exact hretain
  · exact _root_.GD.N0232.N0720.N1185.d017528
  · exact hbayes
  · exact hcandidateIntegrable
  · exact hdeficitZero










theorem d017646
    (prior : ℕ → Measure _root_.GD.N0232.N0720.N1193.d017642)
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (hretain : _root_.GD.N0232.N0720.N1111.d016605 prior)
    (bayes : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hbayes : _root_.GD.N0232.N0720.N1111.d016612
      2 2 _root_.GD.N0232.N0720.N1173.d015935 prior bayes)
    (hcandidateIntegrable : ∀ k, Integrable
      (fun theta ↦
        (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) _root_.GD.N0232.N0720.N1185.d017526).toReal)
      (prior k))
    (base reservoir : ℕ → _root_.GD.N0232.N0720.N1193.d017642 → ℝ)
    (hcombinedEvidence : ∀ k, ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
        (fun theta ↦ base k theta + reservoir k theta) x)
    (hupperRaw : ∀ k,
      _root_.GD.N0232.N0720.N1185.d017514 _root_.GD.N0232.N0720.N1493.d016104
          _root_.GD.N0232.N0720.N1190.d017536
          (fun theta ↦ base k theta + reservoir k theta) ≤
        _root_.GD.N0232.N0720.N1185.d017521 _root_.GD.N0232.N0720.N1493.d016104
          _root_.GD.N0232.N0720.N1190.d017536 (base k) (reservoir k))
    (hresidualZeroRaw : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1185.d017521
        _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1190.d017536
          (base k) (reservoir k)) atTop (nhds 0))
    (hdeficitEqRaw : ∀ k,
      _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k _root_.GD.N0232.N0720.N1185.d017526 -
        _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k (bayes k) =
          _root_.GD.N0232.N0720.N1185.d017514
            _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1190.d017536
              (fun theta ↦ base k theta + reservoir k theta)) :
    _root_.GD.N0232.N0720.N1482.d015169 (m := 2) (n := 2) _root_.GD.N0232.N0720.N1185.d017530 = 0 := by
  apply _root_.GD.N0232.N0720.N1193.d017645
    prior hpriorFinite hretain bayes hbayes hcandidateIntegrable
  rw [_root_.GD.N0232.N0720.N1112.d016616]
  have hfunctions :
      (fun k ↦
        _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k _root_.GD.N0232.N0720.N1185.d017526 -
          _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k (bayes k)) =
      (fun k ↦ _root_.GD.N0232.N0720.N1185.d017514
        _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1190.d017536
          (fun theta ↦ base k theta + reservoir k theta)) := by
    funext k
    exact hdeficitEqRaw k
  rw [hfunctions]
  exact _root_.GD.N0232.N0720.N1185.d017525
    _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1190.d017536 base reservoir
      hcombinedEvidence hupperRaw hresidualZeroRaw






theorem d017647
    (prior : ℕ → Measure _root_.GD.N0232.N0720.N1193.d017642)
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (hretain : _root_.GD.N0232.N0720.N1111.d016605 prior)
    (bayes : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hbayes : _root_.GD.N0232.N0720.N1111.d016612
      2 2 _root_.GD.N0232.N0720.N1173.d015935 prior bayes)
    (hcandidateIntegrable : ∀ k, Integrable
      (fun theta ↦
        (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) _root_.GD.N0232.N0720.N1185.d017526).toReal)
      (prior k))
    (base reservoir : ℕ → _root_.GD.N0232.N0720.N1193.d017642 → ℝ)
    (hcombinedEvidence : ∀ k, ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
        (fun theta ↦ base k theta + reservoir k theta) x)
    (hupperRaw : ∀ k,
      _root_.GD.N0232.N0720.N1185.d017514 _root_.GD.N0232.N0720.N1493.d016104
          _root_.GD.N0232.N0720.N1190.d017536
          (fun theta ↦ base k theta + reservoir k theta) ≤
        _root_.GD.N0232.N0720.N1185.d017521 _root_.GD.N0232.N0720.N1493.d016104
          _root_.GD.N0232.N0720.N1190.d017536 (base k) (reservoir k))
    (hresidualZeroRaw : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1185.d017521
        _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1190.d017536
          (base k) (reservoir k)) atTop (nhds 0))
    (hdeficitEqRaw : ∀ k,
      _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k _root_.GD.N0232.N0720.N1185.d017526 -
        _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k (bayes k) =
          _root_.GD.N0232.N0720.N1185.d017514
            _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1190.d017536
              (fun theta ↦ base k theta + reservoir k theta)) :
    ∃ s : _root_.GD.N0232.N0720.N1159.d014639 2 2,
      _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2) s.value
        (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by norm_num) (by norm_num)) ∧
      _root_.GD.N0232.N0720.N1482.d015169 (m := 2) (n := 2) s = 0 := by
  refine ⟨_root_.GD.N0232.N0720.N1185.d017530, ?_, ?_⟩
  · simpa only [_root_.GD.N0232.N0720.N1185.d017531] using
      _root_.GD.N0232.N0720.N1185.d017532
  · exact _root_.GD.N0232.N0720.N1193.d017646
      prior hpriorFinite hretain bayes hbayes hcandidateIntegrable
        base reservoir hcombinedEvidence hupperRaw hresidualZeroRaw
          hdeficitEqRaw

end

end N1193
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1193.d017643
#print axioms _root_.GD.N0232.N0720.N1193.d017644
#print axioms _root_.GD.N0232.N0720.N1193.d017645
#print axioms _root_.GD.N0232.N0720.N1193.d017646
#print axioms _root_.GD.N0232.N0720.N1193.d017647
