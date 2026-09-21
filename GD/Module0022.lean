import Mathlib


























open Filter

namespace GD
namespace N0230
namespace N0629

noncomputable section



def d000226 (t S : ℝ) : ℝ :=
  1 + t * S


def d000227 (t S M : ℝ) : ℝ :=
  t * M / _root_.GD.N0230.N0629.d000226 t S


def d000228 (S M : ℝ) : ℝ :=
  M / S



theorem d000229
    {t S : ℝ} (ht : 0 ≤ t) (hS : 0 < S) :
    0 < _root_.GD.N0230.N0629.d000226 t S := by
  unfold _root_.GD.N0230.N0629.d000226
  positivity


theorem d000230
    {t S M : ℝ} (hS : S ≠ 0) (hmass : _root_.GD.N0230.N0629.d000226 t S ≠ 0) :
    _root_.GD.N0230.N0629.d000227 t S M - _root_.GD.N0230.N0629.d000228 S M =
      -M / (S * _root_.GD.N0230.N0629.d000226 t S) := by
  have hmass' : 1 + t * S ≠ 0 := by
    simpa only [_root_.GD.N0230.N0629.d000226] using hmass
  unfold _root_.GD.N0230.N0629.d000227 _root_.GD.N0230.N0629.d000228 _root_.GD.N0230.N0629.d000226
  field_simp [hS, hmass']
  ring


theorem d000231
    {t S M : ℝ} (ht : 0 ≤ t) (hS : 0 < S) :
    |_root_.GD.N0230.N0629.d000227 t S M - _root_.GD.N0230.N0629.d000228 S M| =
      |M| / (S * _root_.GD.N0230.N0629.d000226 t S) := by
  rw [_root_.GD.N0230.N0629.d000230 hS.ne'
    (_root_.GD.N0230.N0629.d000229 ht hS).ne']
  rw [abs_div, abs_neg, abs_mul, abs_of_pos hS,
    abs_of_pos (_root_.GD.N0230.N0629.d000229 ht hS)]



theorem d000232
    {S M : ℝ} (hS : 0 < S) :
    Tendsto (fun t : ℝ ↦ _root_.GD.N0230.N0629.d000227 t S M)
      atTop (nhds (_root_.GD.N0230.N0629.d000228 S M)) := by
  have htS : Tendsto (fun t : ℝ ↦ t * S) atTop atTop :=
    by
      convert tendsto_id.const_mul_atTop hS using 1
      ext t
      simp [mul_comm]
  have hmass : Tendsto (fun t : ℝ ↦ _root_.GD.N0230.N0629.d000226 t S) atTop atTop := by
    simpa only [_root_.GD.N0230.N0629.d000226] using tendsto_const_nhds.add_atTop htS
  have hden : Tendsto
      (fun t : ℝ ↦ S * _root_.GD.N0230.N0629.d000226 t S) atTop atTop :=
    hmass.const_mul_atTop hS
  have herror : Tendsto
      (fun t : ℝ ↦ -M / (S * _root_.GD.N0230.N0629.d000226 t S))
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have heventual : ∀ᶠ t : ℝ in atTop,
      _root_.GD.N0230.N0629.d000227 t S M - _root_.GD.N0230.N0629.d000228 S M =
        -M / (S * _root_.GD.N0230.N0629.d000226 t S) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact _root_.GD.N0230.N0629.d000230 hS.ne'
      (_root_.GD.N0230.N0629.d000229 ht hS).ne'
  have hsub : Tendsto
      (fun t : ℝ ↦
        _root_.GD.N0230.N0629.d000227 t S M - _root_.GD.N0230.N0629.d000228 S M)
      atTop (nhds 0) :=
    herror.congr' (heventual.mono fun _ ht ↦ ht.symm)
  have hadd := hsub.add_const (_root_.GD.N0230.N0629.d000228 S M)
  simpa only [sub_add_cancel, zero_add] using hadd






def d000233
    (t S M c shift dilation : ℝ) : ℝ :=
  c * t * (shift * S + dilation * M) / (1 + c * t * S)


def d000234
    (t S M shift dilation : ℝ) : ℝ :=
  shift + dilation * _root_.GD.N0230.N0629.d000227 t S M


def d000235
    (t S M c shift dilation : ℝ) : ℝ :=
  (t * (dilation * M * (c - 1) - shift * S) - shift) /
    ((1 + c * t * S) * _root_.GD.N0230.N0629.d000226 t S)


theorem d000236
    {t S M c shift dilation : ℝ}
    (horiginal : _root_.GD.N0230.N0629.d000226 t S ≠ 0)
    (htransformed : 1 + c * t * S ≠ 0) :
    _root_.GD.N0230.N0629.d000233 t S M c shift dilation -
        _root_.GD.N0230.N0629.d000234 t S M shift dilation =
      _root_.GD.N0230.N0629.d000235 t S M c shift dilation := by
  have horiginal' : 1 + t * S ≠ 0 := by
    simpa only [_root_.GD.N0230.N0629.d000226] using horiginal
  unfold _root_.GD.N0230.N0629.d000233
    _root_.GD.N0230.N0629.d000234 _root_.GD.N0230.N0629.d000227
    _root_.GD.N0230.N0629.d000235 _root_.GD.N0230.N0629.d000226
  field_simp [horiginal', htransformed]
  ring



theorem d000237
    {t S M c shift dilation : ℝ}
    (ht : t ≠ 0) :
    _root_.GD.N0230.N0629.d000235 t S M c shift dilation =
      (((dilation * M * (c - 1) - shift * S) * t⁻¹) -
          shift * (t⁻¹) ^ 2) /
        ((t⁻¹ + c * S) * (t⁻¹ + S)) := by
  unfold _root_.GD.N0230.N0629.d000235 _root_.GD.N0230.N0629.d000226
  field_simp [ht]



theorem d000238
    {S M c shift dilation : ℝ} (hS : 0 < S) (hc : 0 < c) :
    Tendsto
      (fun t : ℝ ↦ _root_.GD.N0230.N0629.d000235 t S M c shift dilation)
      atTop (nhds 0) := by
  have hinv : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hinvSq : Tendsto (fun t : ℝ ↦ (t⁻¹) ^ 2) atTop (nhds 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hinv.pow 2
  have hnum : Tendsto
      (fun t : ℝ ↦
        ((dilation * M * (c - 1) - shift * S) * t⁻¹) -
          shift * (t⁻¹) ^ 2) atTop (nhds 0) := by
    have hfirst := hinv.const_mul (dilation * M * (c - 1) - shift * S)
    have hsecond := hinvSq.const_mul shift
    simpa only [mul_zero, zero_sub, neg_zero] using hfirst.sub hsecond
  have hden : Tendsto
      (fun t : ℝ ↦ (t⁻¹ + c * S) * (t⁻¹ + S))
      atTop (nhds ((c * S) * S)) := by
    simpa only [zero_add] using
      (hinv.add_const (c * S)).mul (hinv.add_const S)
  have hlimit : (c * S) * S ≠ 0 := by positivity
  have hnormalized : Tendsto
      (fun t : ℝ ↦
        (((dilation * M * (c - 1) - shift * S) * t⁻¹) -
            shift * (t⁻¹) ^ 2) /
          ((t⁻¹ + c * S) * (t⁻¹ + S)))
      atTop (nhds 0) := by
    change Tendsto
      ((fun t : ℝ ↦
          (dilation * M * (c - 1) - shift * S) * t⁻¹ -
            shift * (t⁻¹) ^ 2) /
        (fun t : ℝ ↦ (t⁻¹ + c * S) * (t⁻¹ + S)))
      atTop (nhds 0)
    simpa only [zero_div] using hnum.div hden hlimit
  apply hnormalized.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (_root_.GD.N0230.N0629.d000237 ht.ne').symm



theorem d000239
    {S M c shift dilation : ℝ} (hS : 0 < S) (hc : 0 < c) :
    Tendsto
      (fun t : ℝ ↦
        _root_.GD.N0230.N0629.d000233 t S M c shift dilation -
          _root_.GD.N0230.N0629.d000234 t S M shift dilation)
      atTop (nhds 0) := by
  apply (_root_.GD.N0230.N0629.d000238 hS hc).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have horiginal : _root_.GD.N0230.N0629.d000226 t S ≠ 0 :=
    (_root_.GD.N0230.N0629.d000229 ht hS).ne'
  have htransformed : 1 + c * t * S ≠ 0 := by
    have : 0 < 1 + c * t * S := by positivity
    exact this.ne'
  exact (_root_.GD.N0230.N0629.d000236
    horiginal htransformed).symm

end

end N0629
end N0230
end GD

#print axioms _root_.GD.N0230.N0629.d000230
#print axioms _root_.GD.N0230.N0629.d000232
#print axioms _root_.GD.N0230.N0629.d000236
#print axioms _root_.GD.N0230.N0629.d000238
#print axioms _root_.GD.N0230.N0629.d000239
