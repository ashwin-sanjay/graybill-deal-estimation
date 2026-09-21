import GD.Module0904
import GD.Module1358

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Set
open scoped ENNReal

namespace GD.N0028
noncomputable section
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0045



theorem d021929
    (q r : ℝ) (hq : 2 ≤ q) (hr : 2*q ≤ r) (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ z, |g z| ≤ B) :
    _root_.GD.N0028.d014058*q/(8*r^2) ≤
      (∫ z, (g z - (_root_.GD.N0028.d014048 q r hq hr : ℝ)) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 2 5 (_root_.GD.N0028.d014048 q r hq hr)) +
        (q*r^2) * (∫ z, (g z - (_root_.GD.N0028.d014049 q r hq hr : ℝ)) ^ 2
          ∂_root_.GD.N0232.N0720.N1441.d013678 2 5 (_root_.GD.N0028.d014049 q r hq hr)) := by
  let t := _root_.GD.N0028.d014048 q r hq hr
  let s := _root_.GD.N0028.d014049 q r hq hr
  let F := fun z => _root_.GD.N0232.N0720.N1436.d013273 2 5 t z * (g z - (t : ℝ)) ^ 2 +
    (q*r^2) * (_root_.GD.N0232.N0720.N1436.d013273 2 5 s z * (g z - (s : ℝ)) ^ 2)
  have hIt := _root_.GD.N0045.d021928 2 5 (by norm_num) (by norm_num) t g hg hB (t : ℝ)
  have hIs := _root_.GD.N0045.d021928 2 5 (by norm_num) (by norm_num) s g hg hB (s : ℝ)
  have hI : Integrable F _root_.GD.N0232.N0720.N1436.d013288 := hIt.add (hIs.const_mul ((q*r^2)))
  have hb := _root_.GD.N0028.d014047 q r hq hr
  have hq0 := hb.1
  have hr0 := hb.2.1
  have htB : 0<1/r^2 ∧ 1/r^2≤1/4 := ⟨hb.2.2.2.1,hb.2.2.2.2.1⟩
  have hsB : 0<q^2/r^4 ∧ q^2/r^4≤1/4 := ⟨hb.2.2.2.2.2.2.2.1,hb.2.2.2.2.2.2.2.2⟩
  have hgap : (1 / 2 : ℝ) ≤ (s : ℝ) - (t : ℝ) := by
    change (1 / 2 : ℝ) ≤ (1-q^2/r^4)-1/r^2
    linarith [htB.2, hsB.2]
  have hpoint : ∀ z ∈ _root_.GD.N0028.d014050 q r, _root_.GD.N0028.d014058/(8*q*r^2) ≤ F z := by
    intro z hz
    have ht := _root_.GD.N0028.d014069 q r hq hr z hz
    have hs : _root_.GD.N0028.d014058/(q*r^2) ≤ (q*r^2) * _root_.GD.N0232.N0720.N1436.d013273 2 5 s z := by
      calc
        _ = (q*r^2) * (_root_.GD.N0028.d014058/(q^2*r^4)) := by field_simp [hq0.ne',hr0.ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left (_root_.GD.N0028.d014070 q r hq hr z hz) (by positivity : 0≤q*r^2)
    have hsq : (1 / 8 : ℝ) ≤ (g z - (t : ℝ)) ^ 2 + (g z - (s : ℝ)) ^ 2 := by
      nlinarith only [hgap, sq_nonneg (g z - ((s : ℝ) + (t : ℝ)) / 2),
        sq_nonneg ((s : ℝ) - (t : ℝ) - 1 / 2)]
    have hmul := mul_le_mul_of_nonneg_left hsq
      (div_nonneg _root_.GD.N0028.d014062.le (by positivity : 0≤q*r^2))
    have hfirst := mul_le_mul_of_nonneg_right ht (sq_nonneg (g z - (t : ℝ)))
    have hsecond := mul_le_mul_of_nonneg_right hs (sq_nonneg (g z - (s : ℝ)))
    calc
      _ = (_root_.GD.N0028.d014058/(q*r^2)) * (1 / 8) := by ring
      _ ≤ _ := hmul
      _ ≤ F z := by dsimp only [F]; nlinarith only [hfirst, hsecond]
  have hnonneg : 0 ≤ᵐ[_root_.GD.N0232.N0720.N1436.d013288] F := by
    filter_upwards [_root_.GD.N0045.d021922 2 5 (by norm_num) (by norm_num) t,
      _root_.GD.N0045.d021922 2 5 (by norm_num) (by norm_num) s] with z ht hs
    exact add_nonneg (mul_nonneg ht.le (sq_nonneg _))
      (mul_nonneg (by positivity : 0≤q*r^2) (mul_nonneg hs.le (sq_nonneg _)))
  have hS : MeasurableSet (_root_.GD.N0028.d014050 q r) := measurableSet_Icc.prod measurableSet_Icc
  have hfinite : _root_.GD.N0232.N0720.N1436.d013288 (_root_.GD.N0028.d014050 q r) ≠ ⊤ := by
    rw [_root_.GD.N0028.d014052 q r hq hr]
    exact ENNReal.ofReal_ne_top
  have hbound := setIntegral_mono_on
    (integrableOn_const hfinite : IntegrableOn
      (fun _ : _root_.GD.N0232.N0720.N1436.d013217 => _root_.GD.N0028.d014058/(8*q*r^2))
        (_root_.GD.N0028.d014050 q r) _root_.GD.N0232.N0720.N1436.d013288)
    hI.integrableOn hS hpoint
  have hconst : (∫ _ in _root_.GD.N0028.d014050 q r, _root_.GD.N0028.d014058/(8*q*r^2)
      ∂_root_.GD.N0232.N0720.N1436.d013288) = _root_.GD.N0028.d014058*q/(8*r^2) := by
    rw [integral_const]
    simp only [measureReal_def, Measure.restrict_apply_univ, _root_.GD.N0028.d014052 q r hq hr,
      ENNReal.toReal_ofReal (pow_nonneg hq0.le 2), smul_eq_mul]
    field_simp [hq0.ne',hr0.ne']
  rw [hconst] at hbound
  have htotal := hbound.trans (setIntegral_le_integral hI hnonneg)
  rw [_root_.GD.N0045.d021923 2 5 (by norm_num) (by norm_num),
    _root_.GD.N0045.d021923 2 5 (by norm_num) (by norm_num)]
  simpa only [F, integral_add hIt (hIs.const_mul ((q*r^2))), integral_const_mul, t, s] using htotal



theorem d021930
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ z, |g z|≤B) (C : ℝ)
    (hcap : ∀ t : _root_.GD.N0232.N0720.N1441.d013676,
      (∫ z, (g z-(t:ℝ))^2 ∂_root_.GD.N0232.N0720.N1441.d013678 2 5 t)≤C*(t:ℝ)*(1-(t:ℝ))) :
    ∃ η : ℝ, 0<η ∧ ∀ δ : ℝ, 0<δ → ∃ t : _root_.GD.N0232.N0720.N1441.d013676,
      1-δ<(t:ℝ) ∧ η*(1-(t:ℝ)) < ∫ z, (g z-(t:ℝ))^2 ∂_root_.GD.N0232.N0720.N1441.d013678 2 5 t := by
  let q := 16*(|C|+1)/_root_.GD.N0028.d014058+2
  have hq : 2≤q := by
    have hnon := div_nonneg (by positivity : 0≤16*(|C|+1)) _root_.GD.N0028.d014062.le
    dsimp [q]
    linarith
  have hq0 : 0<q := by linarith
  have hbig : 16*|C|<_root_.GD.N0028.d014058*q := by
    have hcancel := div_mul_cancel₀ (16*(|C|+1)) _root_.GD.N0028.d014062.ne'
    dsimp [q]
    nlinarith [_root_.GD.N0028.d014062]
  let η := _root_.GD.N0028.d014058/(16*q^2)
  have hη : 0<η := div_pos _root_.GD.N0028.d014062 (by positivity)
  refine ⟨η,hη,?_⟩
  intro δ hδ
  let r := 2*q+q^2/δ+2
  have hdiv : 0≤q^2/δ := by positivity
  have hr : 2*q≤r := by dsimp [r]; linarith
  have hr0 : 0<r := by linarith
  have hr1 : 1≤r := by linarith
  have hδr : q^2<δ*r := by
    have hcancel := div_mul_cancel₀ (q^2) hδ.ne'
    dsimp [r]
    nlinarith [mul_pos hδ hq0]
  have hr4 : r≤r^4 := by
    calc
      r=r^1 := by ring
      _≤r^4 := pow_le_pow_right₀ hr1 (by omega)
  have hsmall : q^2/r^4<δ := (div_lt_iff₀ (pow_pos hr0 4)).mpr
    (hδr.trans_le (mul_le_mul_of_nonneg_left hr4 hδ.le))
  let t := _root_.GD.N0028.d014048 q r hq hr
  let s := _root_.GD.N0028.d014049 q r hq hr
  refine ⟨s,by change 1-δ<1-q^2/r^4; linarith,?_⟩
  by_contra hnot
  have hs : (∫ z,(g z-(s:ℝ))^2 ∂_root_.GD.N0232.N0720.N1441.d013678 2 5 s)≤η*(q^2/r^4) := by
    have h := le_of_not_gt hnot
    simpa [s,_root_.GD.N0028.d014049] using h
  have ht := hcap t
  have htupper : (∫ z,(g z-(t:ℝ))^2 ∂_root_.GD.N0232.N0720.N1441.d013678 2 5 t)≤|C|/r^2 := by
    have ht0 := t.property.1
    have ht1 := t.property.2
    calc
      _≤C*(t:ℝ)*(1-(t:ℝ)) := ht
      _≤|C| *(t:ℝ)*(1-(t:ℝ)) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self C) ht0.le) (sub_pos.mpr ht1).le
      _≤|C| *(t:ℝ) := mul_le_of_le_one_right (mul_nonneg (abs_nonneg C) ht0.le)
        (by linarith)
      _=|C|/r^2 := by change |C| *(1/r^2)=|C|/r^2; ring
  have hpair := _root_.GD.N0028.d021929 q r hq hr g hg hB
  have hmul := mul_le_mul_of_nonneg_left hs (by positivity : 0≤q*r^2)
  have hfinal : _root_.GD.N0028.d014058*q/(8*r^2)≤|C|/r^2+(q*r^2)*(η*(q^2/r^4)) :=
    hpair.trans (add_le_add htupper hmul)
  have heq : |C|/r^2+(q*r^2)*(η*(q^2/r^4))=(|C|+_root_.GD.N0028.d014058*q/16)/r^2 := by
    dsimp [η]
    field_simp
  rw [heq] at hfinal
  have hscaled := (div_le_div_iff₀ (by positivity : 0<8*r^2) (sq_pos_of_pos hr0)).mp hfinal
  nlinarith [mul_pos (sq_pos_of_pos hr0) (sub_pos.mpr hbig)]

end
end GD.N0028

#print axioms _root_.GD.N0028.d021929
#print axioms _root_.GD.N0028.d021930
