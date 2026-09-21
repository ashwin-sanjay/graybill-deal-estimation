import GD.Module1088
import GD.Module1085
















open Filter MeasureTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1167

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0232.N0720.N1491
open _root_.GD.N0232.N0720.N1493
open _root_.GD.N0232.N0720.N1166
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1175
open _root_.GD.N0232.N0720.N1176
open _root_.GD.N0230.N0589
open _root_.GD.N0232.N0720.N1467

private noncomputable local instance d017485 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance

private abbrev d017486 : Measure _root_.GD.N0232.N0720.N1173.d015933 :=
  _root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104

private abbrev d017487 (k : ℕ) : _root_.GD.N0232.N0720.N1173.d015933 → ℝ :=
  _root_.GD.N0232.N0720.N1166.d017432 k

private theorem d017488 (k : ℕ) (theta : _root_.GD.N0232.N0720.N1173.d015933) :
    0 ≤ _root_.GD.N0232.N0720.N1167.d017487 k theta :=
  _root_.GD.N0232.N0720.N1166.d017437 k theta



private theorem d017489
    (k : ℕ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1167.d017487 k) theta x)
      _root_.GD.N0232.N0720.N1167.d017486 :=
  _root_.GD.N0232.N0720.N1166.d017456 k x ht

private theorem d017490
    (k : ℕ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    Integrable
      (fun theta ↦
        _root_.GD.N0232.N0720.N1173.d015938 theta * _root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1167.d017487 k) theta x)
      _root_.GD.N0232.N0720.N1167.d017486 :=
  _root_.GD.N0232.N0720.N1166.d017457 k x ht

private theorem d017491
    (k : ℕ) (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    Integrable
      (fun theta ↦
        _root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 * _root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1167.d017487 k) theta x)
      _root_.GD.N0232.N0720.N1167.d017486 :=
  _root_.GD.N0232.N0720.N1166.d017458 k x ht







private theorem d017492
    (weight : _root_.GD.N0232.N0720.N1173.d015933 → ℝ)
    (hweight_nonneg : ∀ theta, 0 ≤ weight theta)
    (hlikelihood : Measurable (Function.uncurry (_root_.GD.N0232.N0720.N1173.d015939 weight)))
    (haction : Measurable
      (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104 weight))
    (hfullJoint : Integrable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938
          (_root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104)).uncurry
      (_root_.GD.N0232.N0720.N1167.d017486.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)))
    (hmoments : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable
          (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015939 weight theta x) _root_.GD.N0232.N0720.N1167.d017486 ∧
      Integrable
          (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015938 theta * _root_.GD.N0232.N0720.N1173.d015939 weight theta x)
          _root_.GD.N0232.N0720.N1167.d017486 ∧
      Integrable
          (fun theta ↦
            _root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 * _root_.GD.N0232.N0720.N1173.d015939 weight theta x)
          _root_.GD.N0232.N0720.N1167.d017486 ∧
      _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104 weight x ≠ 0) :
    Integrable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938
          (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104 weight)).uncurry
      (_root_.GD.N0232.N0720.N1167.d017486.prod (_root_.GD.N0232.N0720.N1080.d014172 2 2)) := by
  letI : SigmaFinite _root_.GD.N0232.N0720.N1167.d017486 := by
    unfold _root_.GD.N0232.N0720.N1167.d017486 _root_.GD.N0232.N0720.N1173.d015934
    infer_instance
  have htarget : Measurable _root_.GD.N0232.N0720.N1173.d015938 := by
    unfold _root_.GD.N0232.N0720.N1173.d015938
    fun_prop
  have hcutMeas : Measurable
      (_root_.GD.N0230.N0589.d000071
        (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938
          (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104 weight)).uncurry :=
    _root_.GD.N0230.N0589.d000073 hlikelihood htarget haction
  apply (integrable_prod_iff' hcutMeas.aestronglyMeasurable).2
  constructor
  · filter_upwards [hmoments] with x hx
    rcases hx with ⟨hw, htw, ht2w, hmass⟩
    let a := _root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104 weight x
    have hconstant : Integrable
        (fun theta ↦ a ^ 2 * _root_.GD.N0232.N0720.N1173.d015939 weight theta x) _root_.GD.N0232.N0720.N1167.d017486 :=
      hw.const_mul _
    have hcross : Integrable
        (fun theta ↦
          (2 * a) * (_root_.GD.N0232.N0720.N1173.d015938 theta * _root_.GD.N0232.N0720.N1173.d015939 weight theta x))
        _root_.GD.N0232.N0720.N1167.d017486 :=
      htw.const_mul _
    have hpoly : Integrable
        (fun theta ↦
          a ^ 2 * _root_.GD.N0232.N0720.N1173.d015939 weight theta x -
            (2 * a) *
              (_root_.GD.N0232.N0720.N1173.d015938 theta * _root_.GD.N0232.N0720.N1173.d015939 weight theta x) +
            _root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 * _root_.GD.N0232.N0720.N1173.d015939 weight theta x)
        _root_.GD.N0232.N0720.N1167.d017486 :=
      (hconstant.sub hcross).add ht2w
    refine hpoly.congr (ae_of_all _root_.GD.N0232.N0720.N1167.d017486 fun theta ↦ ?_)
    unfold _root_.GD.N0230.N0589.d000071
    dsimp only [Function.uncurry_apply_pair, a]
    ring
  · have hfullOuter : Integrable
        (fun x ↦ ∫ theta,
          ‖_root_.GD.N0230.N0589.d000071
            (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938
              (_root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104) theta x‖
            ∂_root_.GD.N0232.N0720.N1167.d017486)
        (_root_.GD.N0232.N0720.N1080.d014172 2 2) :=
      hfullJoint.integral_norm_prod_right
    refine hfullOuter.mono'
      (hcutMeas.stronglyMeasurable.norm.integral_prod_left').aestronglyMeasurable
      ?_
    filter_upwards [hmoments] with x hx
    rcases hx with ⟨hw, htw, ht2w, hmass⟩
    have hcompletion := _root_.GD.N0232.N0720.N1173.d015951
      _root_.GD.N0232.N0720.N1493.d016104 weight x
      (_root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104 x)
      hw htw ht2w hmass
    have hlikelihood_nonneg :
        ∀ theta x, 0 ≤ _root_.GD.N0232.N0720.N1173.d015939 weight theta x := by
      intro theta x
      exact mul_nonneg
        (_root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) x)
        (hweight_nonneg theta)
    have hmass_nonneg :
        0 ≤ _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104 weight x := by
      simpa [_root_.GD.N0232.N0720.N1173.d015940] using
        _root_.GD.N0230.N0589.d000090 _root_.GD.N0232.N0720.N1167.d017486 (_root_.GD.N0232.N0720.N1173.d015939 weight)
          hlikelihood_nonneg x
    have hobjective_le :
        _root_.GD.N0230.N0589.d000087 _root_.GD.N0232.N0720.N1167.d017486 (_root_.GD.N0232.N0720.N1173.d015939 weight)
            _root_.GD.N0232.N0720.N1173.d015938 x
              (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104 weight x) ≤
          _root_.GD.N0230.N0589.d000087 _root_.GD.N0232.N0720.N1167.d017486 (_root_.GD.N0232.N0720.N1173.d015939 weight)
            _root_.GD.N0232.N0720.N1173.d015938 x (_root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104 x) := by
      calc
        _root_.GD.N0230.N0589.d000087 _root_.GD.N0232.N0720.N1167.d017486 (_root_.GD.N0232.N0720.N1173.d015939 weight)
              _root_.GD.N0232.N0720.N1173.d015938 x
                (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104 weight x) ≤
            _root_.GD.N0230.N0589.d000087 _root_.GD.N0232.N0720.N1167.d017486 (_root_.GD.N0232.N0720.N1173.d015939 weight)
                _root_.GD.N0232.N0720.N1173.d015938 x
                  (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104 weight x) +
              _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104 weight x *
                (_root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104 x -
                  _root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104 weight x) ^ 2 :=
          le_add_of_nonneg_right
            (mul_nonneg hmass_nonneg (sq_nonneg _))
        _ = _root_.GD.N0230.N0589.d000087 _root_.GD.N0232.N0720.N1167.d017486 (_root_.GD.N0232.N0720.N1173.d015939 weight)
              _root_.GD.N0232.N0720.N1173.d015938 x (_root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104 x) :=
          hcompletion.symm
    have hcutNorm :
        (∫ theta,
          ‖_root_.GD.N0230.N0589.d000071
            (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938
              (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104 weight) theta x‖
            ∂_root_.GD.N0232.N0720.N1167.d017486) =
          _root_.GD.N0230.N0589.d000087 _root_.GD.N0232.N0720.N1167.d017486 (_root_.GD.N0232.N0720.N1173.d015939 weight)
            _root_.GD.N0232.N0720.N1173.d015938 x
              (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104 weight x) := by
      unfold _root_.GD.N0230.N0589.d000087
      apply integral_congr_ae
      filter_upwards with theta
      exact Real.norm_of_nonneg
        (_root_.GD.N0230.N0589.d000075 hlikelihood_nonneg theta x)
    have hfullNorm :
        (∫ theta,
          ‖_root_.GD.N0230.N0589.d000071
            (_root_.GD.N0232.N0720.N1173.d015939 weight) _root_.GD.N0232.N0720.N1173.d015938
              (_root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104) theta x‖
            ∂_root_.GD.N0232.N0720.N1167.d017486) =
          _root_.GD.N0230.N0589.d000087 _root_.GD.N0232.N0720.N1167.d017486 (_root_.GD.N0232.N0720.N1173.d015939 weight)
            _root_.GD.N0232.N0720.N1173.d015938 x (_root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104 x) := by
      unfold _root_.GD.N0230.N0589.d000087
      apply integral_congr_ae
      filter_upwards with theta
      exact Real.norm_of_nonneg
        (_root_.GD.N0230.N0589.d000075 hlikelihood_nonneg theta x)
    simp only [Function.uncurry_apply_pair]
    rw [Real.norm_of_nonneg (integral_nonneg_of_ae
      (ae_of_all _root_.GD.N0232.N0720.N1167.d017486 fun theta ↦ norm_nonneg _))]
    rw [hcutNorm, hfullNorm]
    exact hobjective_le





theorem d017493 (k : ℕ) :
    ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable
          (fun theta ↦
            _root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k) theta x) _root_.GD.N0232.N0720.N1167.d017486 ∧
      Integrable
          (fun theta ↦
            _root_.GD.N0232.N0720.N1173.d015938 theta *
              _root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k) theta x)
          _root_.GD.N0232.N0720.N1167.d017486 ∧
      Integrable
          (fun theta ↦
            _root_.GD.N0232.N0720.N1173.d015938 theta ^ 2 *
              _root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k) theta x)
          _root_.GD.N0232.N0720.N1167.d017486 ∧
      _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
        (_root_.GD.N0232.N0720.N1166.d017432 k) x ≠ 0 := by
  filter_upwards [_root_.GD.N0232.N0720.N1491.d017394] with x ht
  exact ⟨
    _root_.GD.N0232.N0720.N1167.d017489 k x ht,
    _root_.GD.N0232.N0720.N1167.d017490
      k x ht,
    _root_.GD.N0232.N0720.N1167.d017491
      k x ht,
    (_root_.GD.N0232.N0720.N1166.d017464 k x ht).ne'⟩



theorem d017494 (k : ℕ) :
    _root_.GD.N0232.N0720.N1175.d016005 _root_.GD.N0232.N0720.N1493.d016104
      (_root_.GD.N0232.N0720.N1166.d017432 k) := by
  letI : SigmaFinite _root_.GD.N0232.N0720.N1167.d017486 := by
    unfold _root_.GD.N0232.N0720.N1167.d017486 _root_.GD.N0232.N0720.N1173.d015934
    infer_instance
  have hfullJoint :=
    _root_.GD.N0232.N0720.N1166.d017474 k
  have hmoments := _root_.GD.N0232.N0720.N1167.d017493 k
  have hcutJoint := _root_.GD.N0232.N0720.N1167.d017492
    (_root_.GD.N0232.N0720.N1166.d017432 k) (_root_.GD.N0232.N0720.N1167.d017488 k)
    (_root_.GD.N0232.N0720.N1166.d017448 k)
    (_root_.GD.N0232.N0720.N1166.d017451 k)
    hfullJoint hmoments
  have hpointwise : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      _root_.GD.N0230.N0589.d000087 _root_.GD.N0232.N0720.N1167.d017486
          (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k)) _root_.GD.N0232.N0720.N1173.d015938 x
            (_root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104 x) =
        _root_.GD.N0230.N0589.d000087 _root_.GD.N0232.N0720.N1167.d017486
            (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k)) _root_.GD.N0232.N0720.N1173.d015938 x
              (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104
                (_root_.GD.N0232.N0720.N1166.d017432 k) x) +
          _root_.GD.N0230.N0589.d000089 _root_.GD.N0232.N0720.N1167.d017486
            (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k))
            (_root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104)
            (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104
              (_root_.GD.N0232.N0720.N1166.d017432 k)) x := by
    filter_upwards [hmoments] with x hx
    rcases hx with ⟨hw, htw, ht2w, hmass⟩
    simpa [_root_.GD.N0230.N0589.d000089, _root_.GD.N0232.N0720.N1173.d015940, _root_.GD.N0230.N0589.d000088] using
      _root_.GD.N0232.N0720.N1173.d015951
        _root_.GD.N0232.N0720.N1493.d016104 (_root_.GD.N0232.N0720.N1166.d017432 k) x
        (_root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104 x)
        hw htw ht2w hmass
  have htax := _root_.GD.N0230.N0589.d000101
    _root_.GD.N0232.N0720.N1167.d017486 (_root_.GD.N0232.N0720.N1080.d014172 2 2)
    (_root_.GD.N0232.N0720.N1173.d015939 (_root_.GD.N0232.N0720.N1166.d017432 k)) _root_.GD.N0232.N0720.N1173.d015938
    (_root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104)
    (_root_.GD.N0232.N0720.N1173.d015943 _root_.GD.N0232.N0720.N1493.d016104 (_root_.GD.N0232.N0720.N1166.d017432 k))
    hfullJoint hcutJoint hpointwise
  exact ⟨hfullJoint, hcutJoint, htax, hmoments⟩







theorem d017495
    (hui : UnifIntegrable
      (fun k x ↦ _root_.GD.N0232.N0720.N1175.d016001
        _root_.GD.N0232.N0720.N1493.d016104 (_root_.GD.N0232.N0720.N1166.d017432 k) x)
      1 (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :
    Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1173.d015956 _root_.GD.N0232.N0720.N1493.d016104
        (_root_.GD.N0232.N0720.N1166.d017432 k))
      atTop (nhds 0) := by
  apply _root_.GD.N0232.N0720.N1176.d017399
    _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1166.d017432
    _root_.GD.N0232.N0720.N1167.d017494 hui
  filter_upwards [_root_.GD.N0232.N0720.N1491.d017395] with x hx
  exact hx.2.2.2.comp (tendsto_add_atTop_nat 1)

end

end N1167
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1167.d017494
#print axioms _root_.GD.N0232.N0720.N1167.d017495
