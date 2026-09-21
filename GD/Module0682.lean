import GD.Module0681
import GD.Module0679
import GD.Module0156












open MeasureTheory Set

namespace GD.N0232.N0719.N0922

noncomputable section

open _root_.GD.N0232.N0719.N0928
open _root_.GD.N0232.N0719.N0929
open _root_.GD.N0232.N0719.N0940



theorem d009956
    {ε x : ℝ} (hε : 0 < ε) (hx : 0 ≤ x) :
    x ^ 3 / (ε + x) ^ 4 ≤ 1 / (ε + x) := by
  have hd : 0 < ε + x := by linarith
  have hp : x ^ 3 ≤ (ε + x) ^ 3 :=
    pow_le_pow_left₀ hx (by linarith) 3
  rw [div_le_div_iff₀ (pow_pos hd 4) hd]
  have hm := mul_le_mul_of_nonneg_right hp hd.le
  nlinarith [hm]



theorem d009957
    {ε x z : ℝ} (hε : 0 < ε) (hx : 0 ≤ x) (hz : 0 ≤ z) :
    x ^ 3 * z ^ 3 / (ε + x + z) ^ 8 ≤
      (1 / (ε + x)) * (1 / (ε + z)) := by
  have hxε : 0 < ε + x := by linarith
  have hzε : 0 < ε + z := by linarith
  have hr : 0 < ε + x + z := by linarith
  have hxr : ε + x ≤ ε + x + z := by linarith
  have hzr : ε + z ≤ ε + x + z := by linarith
  have hx4 : (ε + x) ^ 4 ≤ (ε + x + z) ^ 4 :=
    pow_le_pow_left₀ hxε.le hxr 4
  have hz4 : (ε + z) ^ 4 ≤ (ε + x + z) ^ 4 :=
    pow_le_pow_left₀ hzε.le hzr 4
  have hden : (ε + x) ^ 4 * (ε + z) ^ 4 ≤
      (ε + x + z) ^ 8 := by
    calc
      (ε + x) ^ 4 * (ε + z) ^ 4 ≤
          (ε + x + z) ^ 4 * (ε + x + z) ^ 4 :=
        mul_le_mul hx4 hz4 (pow_nonneg hzε.le 4)
          (pow_nonneg hr.le 4)
      _ = (ε + x + z) ^ 8 := by ring
  have hx3 : x ^ 3 ≤ (ε + x) ^ 3 :=
    pow_le_pow_left₀ hx (by linarith) 3
  have hz3 : z ^ 3 ≤ (ε + z) ^ 3 :=
    pow_le_pow_left₀ hz (by linarith) 3
  have hnum : x ^ 3 * z ^ 3 ≤
      (ε + x) ^ 3 * (ε + z) ^ 3 :=
    mul_le_mul hx3 hz3 (pow_nonneg hz 3) (pow_nonneg hxε.le 3)
  have hcross :
      x ^ 3 * z ^ 3 * ((ε + x) * (ε + z)) ≤
        (ε + x) ^ 4 * (ε + z) ^ 4 := by
    calc
      x ^ 3 * z ^ 3 * ((ε + x) * (ε + z)) =
          (x ^ 3 * (ε + x)) * (z ^ 3 * (ε + z)) := by ring
      _ ≤ ((ε + x) ^ 3 * (ε + x)) *
          ((ε + z) ^ 3 * (ε + z)) := by
        gcongr
      _ = (ε + x) ^ 4 * (ε + z) ^ 4 := by ring
  have htotal :
      x ^ 3 * z ^ 3 * ((ε + x) * (ε + z)) ≤
        (ε + x + z) ^ 8 := hcross.trans hden
  have htarget :
      x ^ 3 * z ^ 3 / (ε + x + z) ^ 8 ≤
        1 / ((ε + x) * (ε + z)) := by
    rw [div_le_div_iff₀ (pow_pos hr 8) (mul_pos hxε hzε)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using htotal
  calc
    x ^ 3 * z ^ 3 / (ε + x + z) ^ 8 ≤
        1 / ((ε + x) * (ε + z)) := htarget
    _ = (1 / (ε + x)) * (1 / (ε + z)) := by
      field_simp [hxε.ne', hzε.ne']


theorem d009958
    {ε : ℝ} {y t : Fin 3 → ℝ} (hE : _root_.GD.N0232.N0719.N0922.d009928 ε y t)
    {xz : ℝ × ℝ} (hxz : xz ∈ _root_.GD.N0232.N0719.N0922.d009926) :
    _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t (5 / 2) ≤
      256 * _root_.GD.N0232.N0719.N0922.d009948 *
        ((1 / (ε + xz.1)) * (1 / (ε + xz.2))) := by
  have hε : 0 < ε := hE.1
  have hx : 0 ≤ xz.1 := hxz.1.le
  have hz : 0 ≤ xz.2 := hxz.2.1.le
  have hr : 0 < ε + xz.1 + xz.2 := by linarith
  have hs := (_root_.GD.N0232.N0719.N0922.d009951 hE hxz).2
  have hmono : 0 ≤ (1 - xz.1 - xz.2) := by linarith [hxz.2.2]
  have hfront : 0 ≤ _root_.GD.N0232.N0719.N0922.d009948 := _root_.GD.N0232.N0719.N0922.d009949.le
  have hcritical := _root_.GD.N0232.N0719.N0922.d009957 hε hx hz
  have hrpow :
      ((1 / 2 : ℝ) * (ε + (xz.1 + xz.2))) ^ (-(8 : ℝ)) =
        256 / (ε + xz.1 + xz.2) ^ 8 := by
    have hb : 0 < (1 / 2 : ℝ) * (ε + (xz.1 + xz.2)) := by
      positivity
    rw [show (-(8 : ℝ)) = ((-8 : ℤ) : ℝ) by norm_num,
      Real.rpow_intCast]
    norm_num [zpow_neg, hb.ne', hr.ne']
    field_simp [hr.ne']
    ring
  rw [hrpow] at hs
  have hnumerator :
      (1 - xz.1 - xz.2) * xz.1 ^ 3 * xz.2 ^ 3 ≤
        xz.1 ^ 3 * xz.2 ^ 3 := by
    have hprod : 0 ≤ xz.1 ^ 3 * xz.2 ^ 3 :=
      mul_nonneg (pow_nonneg hx 3) (pow_nonneg hz 3)
    calc
      (1 - xz.1 - xz.2) * xz.1 ^ 3 * xz.2 ^ 3 =
          (1 - xz.1 - xz.2) * (xz.1 ^ 3 * xz.2 ^ 3) := by ring
      _ ≤ 1 * (xz.1 ^ 3 * xz.2 ^ 3) :=
        mul_le_mul_of_nonneg_right (by linarith) hprod
      _ = xz.1 ^ 3 * xz.2 ^ 3 := by ring
  have hfraction :
      ((1 - xz.1 - xz.2) * xz.1 ^ 3 * xz.2 ^ 3) /
          (ε + xz.1 + xz.2) ^ 8 ≤
        (xz.1 ^ 3 * xz.2 ^ 3) /
          (ε + xz.1 + xz.2) ^ 8 :=
    (div_le_div_iff_of_pos_right (pow_pos hr 8)).2 hnumerator
  calc
    _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t (5 / 2) ≤
        _root_.GD.N0232.N0719.N0922.d009948 *
          ((1 - xz.1 - xz.2) * xz.1 ^ 3 * xz.2 ^ 3) *
          (256 / (ε + xz.1 + xz.2) ^ 8) := hs
    _ = 256 * _root_.GD.N0232.N0719.N0922.d009948 *
          (((1 - xz.1 - xz.2) * xz.1 ^ 3 * xz.2 ^ 3) /
            (ε + xz.1 + xz.2) ^ 8) := by ring
    _ ≤ 256 * _root_.GD.N0232.N0719.N0922.d009948 *
          (xz.1 ^ 3 * xz.2 ^ 3 / (ε + xz.1 + xz.2) ^ 8) :=
      mul_le_mul_of_nonneg_left hfraction
        (mul_nonneg (by norm_num) hfront)
    _ ≤ 256 * _root_.GD.N0232.N0719.N0922.d009948 *
          ((1 / (ε + xz.1)) * (1 / (ε + xz.2))) := by
      exact mul_le_mul_of_nonneg_left hcritical
        (mul_nonneg (by norm_num) hfront)


theorem d009959 :
    _root_.GD.N0232.N0719.N0922.d009926 ⊆ Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1 := by
  rintro xz hxz
  exact ⟨⟨hxz.1, by linarith [hxz.2.1, hxz.2.2]⟩,
    ⟨hxz.2.1, by linarith [hxz.1, hxz.2.2]⟩⟩


theorem d009960
    {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn
      (fun xz : ℝ × ℝ ↦
        (1 / (ε + xz.1)) * (1 / (ε + xz.2)))
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1) := by
  have hcont : ContinuousOn (fun x : ℝ ↦ 1 / (ε + x)) (Set.Icc 0 1) := by
    apply ContinuousOn.div continuousOn_const
      (continuousOn_const.add continuousOn_id)
    intro x hx
    change ε + x ≠ 0
    exact ne_of_gt (by linarith [hx.1])
  have hsingle : IntegrableOn (fun x : ℝ ↦ 1 / (ε + x)) (Set.Ioc 0 1) :=
    hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  rw [IntegrableOn]
  change Integrable _
    (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1))
  rw [← Measure.prod_restrict]
  exact hsingle.mul_prod hsingle


theorem d009961
    {ε : ℝ} (hε : 0 < ε) :
    (∫ xz in Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1,
        (1 / (ε + xz.1)) * (1 / (ε + xz.2))) =
      Real.log ((ε + 1) / ε) ^ 2 := by
  change (∫ xz in Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1,
      (1 / (ε + xz.1)) * (1 / (ε + xz.2))
        ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) = _
  rw [show
      (∫ xz in Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1,
          (1 / (ε + xz.1)) * (1 / (ε + xz.2))
            ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) =
        (∫ x in Set.Ioc (0 : ℝ) 1, 1 / (ε + x)) *
          (∫ z in Set.Ioc (0 : ℝ) 1, 1 / (ε + z)) by
      exact setIntegral_prod_mul
        (fun x : ℝ ↦ 1 / (ε + x))
        (fun z : ℝ ↦ 1 / (ε + z))
        (Set.Ioc 0 1) (Set.Ioc 0 1)]
  have hsingle :
      (∫ x in Set.Ioc (0 : ℝ) 1, 1 / (ε + x)) =
        Real.log ((ε + 1) / ε) := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact _root_.GD.N0232.N0719.N0940.d001777 hε
  rw [hsingle]
  ring


theorem d009962
    {ε : ℝ} {y t : Fin 3 → ℝ} (hE : _root_.GD.N0232.N0719.N0922.d009928 ε y t) :
    IntegrableOn
      (fun xz ↦ _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915
        (_root_.GD.N0232.N0719.N0922.d009922 xz) y t (5 / 2)) _root_.GD.N0232.N0719.N0922.d009926 := by
  let S := _root_.GD.N0232.N0719.N0955.d009607 3
  let evidence : _root_.GD.N0232.N0719.N0857.d009377 3 → ℝ :=
    fun q ↦ _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915
      (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num) q) y t (5 / 2)
  have hshape : ∀ i, 0 < _root_.GD.N0232.N0719.N0922.d009915 i := by
    intro i
    fin_cases i <;> simp
  have ht : ∀ i, 0 < t i := by
    rcases hE with
      ⟨hε, hε1, ht0l, ht0u, ht1l, ht1u, ht2l, ht2u,
        hy1l, hy1u, hy2l, hy2u⟩
    intro i
    fin_cases i
    · simpa using (lt_of_lt_of_le hε ht0l)
    · simpa using (show (0 : ℝ) < t 1 by linarith)
    · simpa using (show (0 : ℝ) < t 2 by linarith)
  have hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 _root_.GD.N0232.N0719.N0922.d009915 (5 / 2) := by simp
  have hevidence : IntegrableOn evidence S := by
    simpa [evidence, S] using
      _root_.GD.N0232.N0719.N0929.d009645
        (by norm_num : 0 < 3) _root_.GD.N0232.N0719.N0922.d009915 y t (5 / 2) hshape ht hpower
  have htransport :=
    (_root_.GD.N0232.N0719.N0922.d009936.integrableOn_comp_preimage
      _root_.GD.N0232.N0719.N0922.d009939
      (f := evidence) (s := S)).2 hevidence
  have hpreimage : _root_.GD.N0232.N0719.N0922.d009920 ⁻¹' S = _root_.GD.N0232.N0719.N0922.d009926 := by
    ext xz
    exact _root_.GD.N0232.N0719.N0922.d009927 xz
  rw [hpreimage] at htransport
  change IntegrableOn
    (fun xz ↦ _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915
      (_root_.GD.N0232.N0719.N0922.d009922 xz) y t (5 / 2)) _root_.GD.N0232.N0719.N0922.d009926
      ((volume : Measure ℝ).prod (volume : Measure ℝ))
  simpa [evidence, Function.comp_def, _root_.GD.N0232.N0719.N0922.d009922] using htransport



theorem d009963
    {ε : ℝ} {y t : Fin 3 → ℝ} (hE : _root_.GD.N0232.N0719.N0922.d009928 ε y t) :
    (∫ xz in _root_.GD.N0232.N0719.N0922.d009926,
        _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t (5 / 2)) ≤
      256 * _root_.GD.N0232.N0719.N0922.d009948 * Real.log ((ε + 1) / ε) ^ 2 := by
  let f : ℝ × ℝ → ℝ := fun xz ↦
    _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t (5 / 2)
  let g : ℝ × ℝ → ℝ := fun xz ↦
    256 * _root_.GD.N0232.N0719.N0922.d009948 *
      ((1 / (ε + xz.1)) * (1 / (ε + xz.2)))
  have hf : IntegrableOn f _root_.GD.N0232.N0719.N0922.d009926 := by
    simpa [f] using _root_.GD.N0232.N0719.N0922.d009962 hE
  have hgSquare : IntegrableOn g
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1) := by
    exact (_root_.GD.N0232.N0719.N0922.d009960 hE.1).const_mul
      (256 * _root_.GD.N0232.N0719.N0922.d009948)
  have hg : IntegrableOn g _root_.GD.N0232.N0719.N0922.d009926 :=
    hgSquare.mono_set _root_.GD.N0232.N0719.N0922.d009959
  have hpoint : ∀ xz ∈ _root_.GD.N0232.N0719.N0922.d009926, f xz ≤ g xz := by
    intro xz hxz
    exact _root_.GD.N0232.N0719.N0922.d009958 hE hxz
  have htriangle : MeasurableSet _root_.GD.N0232.N0719.N0922.d009926 := by
    unfold _root_.GD.N0232.N0719.N0922.d009926
    have hfst : Measurable (fun xz : ℝ × ℝ ↦ xz.1) := measurable_fst
    have hsnd : Measurable (fun xz : ℝ × ℝ ↦ xz.2) := measurable_snd
    have hsum : Measurable (fun xz : ℝ × ℝ ↦ xz.1 + xz.2) :=
      hfst.add hsnd
    have hzero : Measurable (fun _ : ℝ × ℝ ↦ (0 : ℝ)) := measurable_const
    have hone : Measurable (fun _ : ℝ × ℝ ↦ (1 : ℝ)) := measurable_const
    simpa only [Set.inter_def, Set.mem_setOf_eq, and_assoc] using
      (((measurableSet_lt hzero hfst).inter
        (measurableSet_lt hzero hsnd)).inter
        (measurableSet_lt hsum hone))
  have hfirst :
      (∫ xz in _root_.GD.N0232.N0719.N0922.d009926, f xz) ≤
        ∫ xz in _root_.GD.N0232.N0719.N0922.d009926, g xz := by
    exact setIntegral_mono_on hf hg htriangle hpoint
  have hsquare : MeasurableSet
      (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1) :=
    measurableSet_Ioc.prod measurableSet_Ioc
  have hgnonneg : 0 ≤ᵐ[
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
        (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1)] g := by
    apply (ae_restrict_iff' hsquare).2
    filter_upwards with xz hxz
    unfold g
    have hx : 0 < ε + xz.1 := by linarith [hE.1, hxz.1.1]
    have hz : 0 < ε + xz.2 := by linarith [hE.1, hxz.2.1]
    exact mul_nonneg
      (mul_nonneg (by norm_num) _root_.GD.N0232.N0719.N0922.d009949.le)
      (mul_nonneg (one_div_nonneg.mpr hx.le) (one_div_nonneg.mpr hz.le))
  have hsecond :
      (∫ xz in _root_.GD.N0232.N0719.N0922.d009926, g xz) ≤
        ∫ xz in Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1, g xz := by
    exact setIntegral_mono_set hgSquare hgnonneg
      (Filter.Eventually.of_forall _root_.GD.N0232.N0719.N0922.d009959)
  calc
    (∫ xz in _root_.GD.N0232.N0719.N0922.d009926,
        _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t (5 / 2)) =
        ∫ xz in _root_.GD.N0232.N0719.N0922.d009926, f xz := by rfl
    _ ≤ ∫ xz in _root_.GD.N0232.N0719.N0922.d009926, g xz := hfirst
    _ ≤ ∫ xz in Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1, g xz := hsecond
    _ = 256 * _root_.GD.N0232.N0719.N0922.d009948 * Real.log ((ε + 1) / ε) ^ 2 := by
      change (∫ xz,
          (256 * _root_.GD.N0232.N0719.N0922.d009948) *
            ((1 / (ε + xz.1)) * (1 / (ε + xz.2)))
          ∂(volume.restrict
            (Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioc (0 : ℝ) 1))) = _
      rw [integral_const_mul]
      rw [_root_.GD.N0232.N0719.N0922.d009961 hE.1]

end

end GD.N0232.N0719.N0922

#print axioms _root_.GD.N0232.N0719.N0922.d009962
#print axioms _root_.GD.N0232.N0719.N0922.d009963
