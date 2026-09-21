import GD.Module1091




















open Filter MeasureTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1190

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1036
open _root_.GD.N0232.N0720.N1111
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1185
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608

abbrev d017534 :=
  _root_.GD.N0232.N0720.N1173.d015933

abbrev d017535 :=
  _root_.GD.N0232.N0720.N1173.d015936



def d017536 : _root_.GD.N0232.N0720.N1190.d017535 → ℝ :=
  _root_.GD.N0232.N0720.N1080.d014176 2 2 (by norm_num) (by norm_num)



theorem d017537 :
    MemLp _root_.GD.N0232.N0720.N1190.d017536 2 (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  unfold _root_.GD.N0232.N0720.N1190.d017536
  simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
    (_root_.GD.N0232.N0720.N1080.d014179 2 2 (by norm_num) (by norm_num)
      _root_.GD.N0232.N0720.N1080.d014169)



theorem d017538 :
    _root_.GD.N0232.N0720.N1185.d017527 =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2] _root_.GD.N0232.N0720.N1190.d017536 := by
  have hdecision :
      _root_.GD.N0232.N0720.N1185.d017526 = MemLp.toLp _root_.GD.N0232.N0720.N1190.d017536 _root_.GD.N0232.N0720.N1190.d017537 := by
    unfold _root_.GD.N0232.N0720.N1185.d017526 _root_.GD.N0232.N0720.N1190.d017536 _root_.GD.N0232.N0720.N1080.d014181
    congr
  filter_upwards [_root_.GD.N0232.N0720.N1190.d017537.coeFn_toLp] with x hx
  change _root_.GD.N0232.N0720.N1185.d017526 x = _root_.GD.N0232.N0720.N1190.d017536 x
  rw [hdecision]
  exact hx



theorem d017539
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    {candidate candidate' : _root_.GD.N0232.N0720.N1190.d017535 → ℝ}
    (weight : _root_.GD.N0232.N0720.N1190.d017534 → ℝ) (x : _root_.GD.N0232.N0720.N1190.d017535)
    (hx : candidate x = candidate' x) :
    _root_.GD.N0232.N0720.N1185.d017512 rho candidate weight x =
      _root_.GD.N0232.N0720.N1185.d017512 rho candidate' weight x := by
  unfold _root_.GD.N0232.N0720.N1185.d017512
  rw [hx]



theorem d017540
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    {candidate candidate' : _root_.GD.N0232.N0720.N1190.d017535 → ℝ}
    (weight : _root_.GD.N0232.N0720.N1190.d017534 → ℝ) (x : _root_.GD.N0232.N0720.N1190.d017535)
    (hx : candidate x = candidate' x) :
    _root_.GD.N0232.N0720.N1185.d017513 rho candidate weight x =
      _root_.GD.N0232.N0720.N1185.d017513 rho candidate' weight x := by
  unfold _root_.GD.N0232.N0720.N1185.d017513
  rw [_root_.GD.N0232.N0720.N1190.d017539 rho weight x hx]



theorem d017541
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    {candidate candidate' : _root_.GD.N0232.N0720.N1190.d017535 → ℝ}
    (weight : _root_.GD.N0232.N0720.N1190.d017534 → ℝ)
    (hcandidate : candidate =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2] candidate') :
    _root_.GD.N0232.N0720.N1185.d017514 rho candidate weight =
      _root_.GD.N0232.N0720.N1185.d017514 rho candidate' weight := by
  unfold _root_.GD.N0232.N0720.N1185.d017514
  apply integral_congr_ae
  filter_upwards [hcandidate] with x hx
  exact _root_.GD.N0232.N0720.N1190.d017540 rho weight x hx



theorem d017542
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    {candidate candidate' : _root_.GD.N0232.N0720.N1190.d017535 → ℝ}
    (base reservoir : _root_.GD.N0232.N0720.N1190.d017534 → ℝ)
    (hcandidate : candidate =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2] candidate') :
    _root_.GD.N0232.N0720.N1185.d017521 rho candidate base reservoir =
      _root_.GD.N0232.N0720.N1185.d017521 rho candidate' base reservoir := by
  unfold _root_.GD.N0232.N0720.N1185.d017521
  apply integral_congr_ae
  filter_upwards [hcandidate] with x hx
  rw [_root_.GD.N0232.N0720.N1190.d017539 rho base x hx,
    _root_.GD.N0232.N0720.N1190.d017539 rho reservoir x hx]



theorem d017543
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (weight : _root_.GD.N0232.N0720.N1190.d017534 → ℝ) :
    _root_.GD.N0232.N0720.N1185.d017514 rho _root_.GD.N0232.N0720.N1185.d017527 weight =
      _root_.GD.N0232.N0720.N1185.d017514 rho _root_.GD.N0232.N0720.N1190.d017536 weight := by
  exact _root_.GD.N0232.N0720.N1190.d017541 rho weight
    _root_.GD.N0232.N0720.N1190.d017538



theorem d017544
    (rho : Measure (Set.Ioo (0 : ℝ) 1))
    (base reservoir : _root_.GD.N0232.N0720.N1190.d017534 → ℝ) :
    _root_.GD.N0232.N0720.N1185.d017521 rho _root_.GD.N0232.N0720.N1185.d017527 base reservoir =
      _root_.GD.N0232.N0720.N1185.d017521 rho _root_.GD.N0232.N0720.N1190.d017536 base reservoir := by
  exact _root_.GD.N0232.N0720.N1190.d017542 rho base reservoir
    _root_.GD.N0232.N0720.N1190.d017538











theorem d017545
    (s : _root_.GD.N0232.N0720.N1159.d014639 2 2)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by norm_num) (by norm_num)))
    (raw : _root_.GD.N0232.N0720.N1190.d017535 → ℝ)
    (hraw : (fun x ↦ s.value x) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2] raw)
    (prior : ℕ → Measure _root_.GD.N0232.N0720.N1190.d017534)
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (hretain : _root_.GD.N0232.N0720.N1111.d016605 prior)
    (bayes : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hbayes : _root_.GD.N0232.N0720.N1111.d016612
      2 2 _root_.GD.N0232.N0720.N1173.d015935 prior bayes)
    (hcandidateIntegrable : ∀ k, Integrable
      (fun theta ↦
        (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) s.value).toReal)
      (prior k))
    (base reservoir : ℕ → _root_.GD.N0232.N0720.N1190.d017534 → ℝ)
    (hcombinedEvidence : ∀ k, ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
        (fun theta ↦ base k theta + reservoir k theta) x)
    (hupperRaw : ∀ k,
      _root_.GD.N0232.N0720.N1185.d017514 _root_.GD.N0232.N0720.N1493.d016104
          raw (fun theta ↦ base k theta + reservoir k theta) ≤
        _root_.GD.N0232.N0720.N1185.d017521 _root_.GD.N0232.N0720.N1493.d016104
          raw (base k) (reservoir k))
    (hresidualZeroRaw : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1185.d017521
        _root_.GD.N0232.N0720.N1493.d016104 raw
          (base k) (reservoir k)) atTop (nhds 0))
    (hdeficitEqRaw : ∀ k,
      _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k s.value -
        _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k (bayes k) =
          _root_.GD.N0232.N0720.N1185.d017514
            _root_.GD.N0232.N0720.N1493.d016104 raw
              (fun theta ↦ base k theta + reservoir k theta)) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  let canonical : _root_.GD.N0232.N0720.N1190.d017535 → ℝ := fun x ↦ s.value x
  have hglobal (weight : _root_.GD.N0232.N0720.N1190.d017534 → ℝ) :
      _root_.GD.N0232.N0720.N1185.d017514 _root_.GD.N0232.N0720.N1493.d016104
          canonical weight =
        _root_.GD.N0232.N0720.N1185.d017514 _root_.GD.N0232.N0720.N1493.d016104
          raw weight :=
    _root_.GD.N0232.N0720.N1190.d017541
      _root_.GD.N0232.N0720.N1493.d016104 weight hraw
  have hresidual (base' reservoir' : _root_.GD.N0232.N0720.N1190.d017534 → ℝ) :
      _root_.GD.N0232.N0720.N1185.d017521 _root_.GD.N0232.N0720.N1493.d016104
          canonical base' reservoir' =
        _root_.GD.N0232.N0720.N1185.d017521 _root_.GD.N0232.N0720.N1493.d016104
          raw base' reservoir' :=
    _root_.GD.N0232.N0720.N1190.d017542
      _root_.GD.N0232.N0720.N1493.d016104 base' reservoir' hraw
  have hupper : ∀ k,
      _root_.GD.N0232.N0720.N1185.d017514 _root_.GD.N0232.N0720.N1493.d016104
          canonical (fun theta ↦ base k theta + reservoir k theta) ≤
        _root_.GD.N0232.N0720.N1185.d017521 _root_.GD.N0232.N0720.N1493.d016104
          canonical (base k) (reservoir k) := by
    intro k
    rw [hglobal, hresidual]
    exact hupperRaw k
  have hresidualZero : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1185.d017521
        _root_.GD.N0232.N0720.N1493.d016104 canonical
          (base k) (reservoir k)) atTop (nhds 0) := by
    have hfunctions :
        (fun k ↦ _root_.GD.N0232.N0720.N1185.d017521
          _root_.GD.N0232.N0720.N1493.d016104 canonical
            (base k) (reservoir k)) =
          (fun k ↦ _root_.GD.N0232.N0720.N1185.d017521
            _root_.GD.N0232.N0720.N1493.d016104 raw
              (base k) (reservoir k)) := by
      funext k
      exact hresidual (base k) (reservoir k)
    rw [hfunctions]
    exact hresidualZeroRaw
  have hcurrentZero :=
    _root_.GD.N0232.N0720.N1185.d017525
      _root_.GD.N0232.N0720.N1493.d016104 canonical base reservoir
        hcombinedEvidence hupper hresidualZero
  apply _root_.GD.N0232.N0720.N1111.d016615
    2 2 (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1173.d015935
      (prior := prior) (s := s) (bayes := bayes)
  · unfold _root_.GD.N0232.N0720.N1173.d015935
    exact _root_.GD.N0232.N0720.N1486.d015877 2 2 _ _
  · unfold _root_.GD.N0232.N0720.N1173.d015935
    exact _root_.GD.N0232.N0720.N1486.d015893 2 2 _ _
  · exact hpriorFinite
  · exact hretain
  · exact hstrict
  · exact hbayes
  · exact hcandidateIntegrable
  · rw [_root_.GD.N0232.N0720.N1112.d016616]
    have hfunctions :
        (fun k ↦
          _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k s.value -
            _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k
              (bayes k)) =
          (fun k ↦ _root_.GD.N0232.N0720.N1185.d017514
            _root_.GD.N0232.N0720.N1493.d016104 canonical
              (fun theta ↦ base k theta + reservoir k theta)) := by
      funext k
      calc
        _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k s.value -
              _root_.GD.N0232.N0720.N1111.d016604 2 2 _root_.GD.N0232.N0720.N1173.d015935 prior k
                (bayes k) =
            _root_.GD.N0232.N0720.N1185.d017514
              _root_.GD.N0232.N0720.N1493.d016104 raw
                (fun theta ↦ base k theta + reservoir k theta) :=
          hdeficitEqRaw k
        _ = _root_.GD.N0232.N0720.N1185.d017514
              _root_.GD.N0232.N0720.N1493.d016104 canonical
                (fun theta ↦ base k theta + reservoir k theta) :=
          (hglobal _).symm
    rw [hfunctions]
    exact hcurrentZero










theorem d017546
    (prior : ℕ → Measure _root_.GD.N0232.N0720.N1190.d017534)
    (hpriorFinite : ∀ k, IsFiniteMeasure (prior k))
    (hretain : _root_.GD.N0232.N0720.N1111.d016605 prior)
    (bayes : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hbayes : _root_.GD.N0232.N0720.N1111.d016612
      2 2 _root_.GD.N0232.N0720.N1173.d015935 prior bayes)
    (hcandidateIntegrable : ∀ k, Integrable
      (fun theta ↦
        (_root_.GD.N0232.N0720.N1080.d014182 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) _root_.GD.N0232.N0720.N1185.d017526).toReal)
      (prior k))
    (base reservoir : ℕ → _root_.GD.N0232.N0720.N1190.d017534 → ℝ)
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
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  apply _root_.GD.N0232.N0720.N1185.d017533
    prior hpriorFinite hretain bayes hbayes hcandidateIntegrable
      base reservoir hcombinedEvidence
  · intro k
    rw [_root_.GD.N0232.N0720.N1190.d017543,
      _root_.GD.N0232.N0720.N1190.d017544]
    exact hupperRaw k
  · have hfunctions :
        (fun k ↦ _root_.GD.N0232.N0720.N1185.d017521
          _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1185.d017527
            (base k) (reservoir k)) =
        (fun k ↦ _root_.GD.N0232.N0720.N1185.d017521
          _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1190.d017536
            (base k) (reservoir k)) := by
      funext k
      exact _root_.GD.N0232.N0720.N1190.d017544
        _root_.GD.N0232.N0720.N1493.d016104 (base k) (reservoir k)
    rw [hfunctions]
    exact hresidualZeroRaw
  · intro k
    rw [_root_.GD.N0232.N0720.N1190.d017543]
    exact hdeficitEqRaw k

end

end N1190
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1190.d017538
#print axioms _root_.GD.N0232.N0720.N1190.d017541
#print axioms _root_.GD.N0232.N0720.N1190.d017542
#print axioms _root_.GD.N0232.N0720.N1190.d017544
#print axioms _root_.GD.N0232.N0720.N1190.d017545
#print axioms _root_.GD.N0232.N0720.N1190.d017546
