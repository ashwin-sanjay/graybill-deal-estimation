import GD.Module0679
import GD.Module0681









open MeasureTheory Set

namespace GD.N0232.N0719.N0922

noncomputable section

open _root_.GD.N0232.N0719.N0928 _root_.GD.N0232.N0719.N0929



def d009964 (y t : Fin 3 → ℝ) (xz : ℝ × ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t (5 / 2) *
    (_root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0719.N0922.d009922 xz) y - y 0)


def d009965 : ℝ :=
  _root_.GD.N0232.N0719.N0922.d009948 * ((1 / 3 : ℝ) * (1 / 4 : ℝ) ^ 6) *
    (12 : ℝ) ^ (-(8 : ℝ)) * (1 / 2 : ℝ)

theorem d009966 : 0 < _root_.GD.N0232.N0719.N0922.d009965 := by
  unfold _root_.GD.N0232.N0719.N0922.d009965
  exact mul_pos
    (mul_pos
      (mul_pos _root_.GD.N0232.N0719.N0922.d009949 (by positivity))
      (Real.rpow_pos_of_pos (by norm_num) _))
    (by norm_num)


theorem d009967 :
    ((volume : Measure ℝ).prod (volume : Measure ℝ)).real _root_.GD.N0232.N0719.N0922.d009952 =
      (1 / 144 : ℝ) := by
  have hrect : _root_.GD.N0232.N0719.N0922.d009952 =
      Set.Icc (1 / 4 : ℝ) (1 / 3) ×ˢ Set.Icc (1 / 4 : ℝ) (1 / 3) := by
    ext xz
    simp [_root_.GD.N0232.N0719.N0922.d009952]
  rw [hrect, Measure.real, Measure.prod_prod]
  simp_rw [Real.volume_Icc]
  norm_num




theorem d009968
    {ε : ℝ} {y t : Fin 3 → ℝ} (hE : _root_.GD.N0232.N0719.N0922.d009928 ε y t) :
    IntegrableOn (_root_.GD.N0232.N0719.N0922.d009964 y t) _root_.GD.N0232.N0719.N0922.d009926 := by
  let S := _root_.GD.N0232.N0719.N0955.d009607 3
  let evidence : _root_.GD.N0232.N0719.N0857.d009377 3 → ℝ :=
    fun q => _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915
      (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num) q) y t (5 / 2)
  let mean : _root_.GD.N0232.N0719.N0857.d009377 3 → ℝ :=
    fun q => _root_.GD.N0232.N0719.N0928.d009405
      (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num) q) y
  let response : _root_.GD.N0232.N0719.N0857.d009377 3 → ℝ :=
    fun q => evidence q * (mean q - y 0)
  have hshape : ∀ i, 0 < _root_.GD.N0232.N0719.N0922.d009915 i := by
    intro i
    fin_cases i <;> simp
  have ht : ∀ i, 0 < t i := by
    intro i
    rcases hE with
      ⟨hε, hε1, ht0l, ht0u, ht1l, ht1u, ht2l, ht2u,
        hy1l, hy1u, hy2l, hy2u⟩
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl <;> linarith
  have hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 _root_.GD.N0232.N0719.N0922.d009915 (5 / 2) := by simp
  have hevidence : IntegrableOn evidence S := by
    simpa [evidence, S] using
      _root_.GD.N0232.N0719.N0929.d009645
        (by norm_num : 0 < 3) _root_.GD.N0232.N0719.N0922.d009915 y t (5 / 2) hshape ht hpower
  have hevidenceMean : IntegrableOn (fun q => evidence q * mean q) S := by
    simpa [evidence, mean, S] using
      _root_.GD.N0232.N0719.N0929.d009651
        (by norm_num : 0 < 3) _root_.GD.N0232.N0719.N0922.d009915 y t (5 / 2) hshape ht hpower
  have hresponse : IntegrableOn response S := by
    have hconst : IntegrableOn (fun q => y 0 * evidence q) S :=
      hevidence.const_mul (y 0)
    have hsub := hevidenceMean.sub hconst
    dsimp [response]
    apply hsub.congr
    filter_upwards [] with q
    simp only [Pi.sub_apply]
    ring
  let g : _root_.GD.N0232.N0719.N0857.d009377 3 → ℝ :=
    S.indicator response
  have hg : Integrable g := by
    exact (integrable_indicator_iff
      (_root_.GD.N0232.N0719.N0955.d009608 3)).2 hresponse
  have hcompInt : Integrable (g ∘ _root_.GD.N0232.N0719.N0922.d009920) :=
    (_root_.GD.N0232.N0719.N0922.d009936.integrable_comp_emb
      _root_.GD.N0232.N0719.N0922.d009939).2 hg
  have hcomp : g ∘ _root_.GD.N0232.N0719.N0922.d009920 =
      _root_.GD.N0232.N0719.N0922.d009926.indicator (_root_.GD.N0232.N0719.N0922.d009964 y t) := by
    funext xz
    by_cases hx : xz ∈ _root_.GD.N0232.N0719.N0922.d009926
    · have hs : _root_.GD.N0232.N0719.N0922.d009920 xz ∈ S :=
        (_root_.GD.N0232.N0719.N0922.d009927 xz).2 hx
      simp [g, Function.comp_apply, Set.indicator, hx, hs,
        response, evidence, mean, _root_.GD.N0232.N0719.N0922.d009964, _root_.GD.N0232.N0719.N0922.d009922]
    · have hs : _root_.GD.N0232.N0719.N0922.d009920 xz ∉ S := by
        intro hs
        exact hx ((_root_.GD.N0232.N0719.N0922.d009927 xz).1 hs)
      simp [g, Function.comp_apply, Set.indicator, hx, hs]
  rw [hcomp] at hcompInt
  have hT : MeasurableSet _root_.GD.N0232.N0719.N0922.d009926 := by
    have hfst : Measurable (fun xz : ℝ × ℝ ↦ xz.1) := measurable_fst
    have hsnd : Measurable (fun xz : ℝ × ℝ ↦ xz.2) := measurable_snd
    exact (measurableSet_lt measurable_const hfst).inter
      ((measurableSet_lt measurable_const hsnd).inter
        (measurableSet_lt (hfst.add hsnd) measurable_const))
  exact (integrable_indicator_iff hT).1 hcompInt


theorem d009969
    {ε : ℝ} {y t : Fin 3 → ℝ} (hE : _root_.GD.N0232.N0719.N0922.d009928 ε y t)
    {xz : ℝ × ℝ} (hxz : xz ∈ _root_.GD.N0232.N0719.N0922.d009926) :
    0 ≤ _root_.GD.N0232.N0719.N0922.d009964 y t xz := by
  have hbase : 0 < (1 / 2 : ℝ) * (ε + (xz.1 + xz.2)) := by
    have hε := hE.1
    have hx := hxz.1
    have hz := hxz.2.1
    positivity
  have henergy : 0 < _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t :=
    lt_of_lt_of_le hbase (_root_.GD.N0232.N0719.N0922.d009931 hE hxz)
  have hkernel : 0 < _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915
      (_root_.GD.N0232.N0719.N0922.d009922 xz) y t (5 / 2) := by
    apply _root_.GD.N0232.N0719.N0928.d009440
    · exact _root_.GD.N0232.N0719.N0929.d009631 (by norm_num)
        ((_root_.GD.N0232.N0719.N0922.d009927 xz).2 hxz)
    · exact henergy
    · simpa using (show (0 : ℝ) < 8 by norm_num)
  have hmean : 0 ≤ _root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0719.N0922.d009922 xz) y - y 0 := by
    exact le_trans (by linarith [hxz.1, hxz.2.1] : 0 ≤ xz.1 + xz.2)
      (_root_.GD.N0232.N0719.N0922.d009934 hE hxz)
  exact mul_nonneg hkernel.le hmean



theorem d009970
    {ε : ℝ} {y t : Fin 3 → ℝ} (hE : _root_.GD.N0232.N0719.N0922.d009928 ε y t) :
    _root_.GD.N0232.N0719.N0922.d009965 / 144 ≤
      ∫ xz in _root_.GD.N0232.N0719.N0922.d009926, _root_.GD.N0232.N0719.N0922.d009964 y t xz := by
  have hf := _root_.GD.N0232.N0719.N0922.d009968 hE
  have hnonneg : 0 ≤ᵐ[
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict _root_.GD.N0232.N0719.N0922.d009926]
      _root_.GD.N0232.N0719.N0922.d009964 y t := by
    have hfst : Measurable (fun xz : ℝ × ℝ ↦ xz.1) := measurable_fst
    have hsnd : Measurable (fun xz : ℝ × ℝ ↦ xz.2) := measurable_snd
    have hT : MeasurableSet _root_.GD.N0232.N0719.N0922.d009926 :=
      (measurableSet_lt measurable_const hfst).inter
        ((measurableSet_lt measurable_const hsnd).inter
          (measurableSet_lt (hfst.add hsnd) measurable_const))
    apply (ae_restrict_iff' hT).2
    filter_upwards [] with xz hxz
    exact _root_.GD.N0232.N0719.N0922.d009969 hE hxz
  have hrectSub : _root_.GD.N0232.N0719.N0922.d009952 ≤ᵐ[
      (volume : Measure ℝ).prod (volume : Measure ℝ)] _root_.GD.N0232.N0719.N0922.d009926 :=
    Filter.Eventually.of_forall _root_.GD.N0232.N0719.N0922.d009953
  have hmonoSet :
      (∫ xz in _root_.GD.N0232.N0719.N0922.d009952, _root_.GD.N0232.N0719.N0922.d009964 y t xz) ≤
        ∫ xz in _root_.GD.N0232.N0719.N0922.d009926, _root_.GD.N0232.N0719.N0922.d009964 y t xz :=
    setIntegral_mono_set hf hnonneg hrectSub
  have hconstInt : IntegrableOn (fun _ : ℝ × ℝ => _root_.GD.N0232.N0719.N0922.d009965)
      _root_.GD.N0232.N0719.N0922.d009952 := by
    have hfinite : ((volume : Measure ℝ).prod (volume : Measure ℝ))
        _root_.GD.N0232.N0719.N0922.d009952 < ⊤ := by
      rw [show _root_.GD.N0232.N0719.N0922.d009952 =
          Set.Icc (1 / 4 : ℝ) (1 / 3) ×ˢ Set.Icc (1 / 4 : ℝ) (1 / 3) by
        ext xz; simp [_root_.GD.N0232.N0719.N0922.d009952]]
      rw [Measure.prod_prod]
      simp_rw [Real.volume_Icc]
      apply ENNReal.mul_lt_top <;> simp
    exact integrableOn_const hfinite.ne
  have hfRect : IntegrableOn (_root_.GD.N0232.N0719.N0922.d009964 y t) _root_.GD.N0232.N0719.N0922.d009952 :=
    hf.mono_set _root_.GD.N0232.N0719.N0922.d009953
  have hpoint : ∀ xz ∈ _root_.GD.N0232.N0719.N0922.d009952,
      _root_.GD.N0232.N0719.N0922.d009965 ≤ _root_.GD.N0232.N0719.N0922.d009964 y t xz := by
    intro xz hxz
    simpa [_root_.GD.N0232.N0719.N0922.d009965, _root_.GD.N0232.N0719.N0922.d009964] using
      _root_.GD.N0232.N0719.N0922.d009955 hE hxz
  have hmonoFun :
      (∫ _xz in _root_.GD.N0232.N0719.N0922.d009952, _root_.GD.N0232.N0719.N0922.d009965) ≤
        ∫ xz in _root_.GD.N0232.N0719.N0922.d009952, _root_.GD.N0232.N0719.N0922.d009964 y t xz := by
    apply integral_mono_ae hconstInt hfRect
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [] with xz hxz
    exact hpoint xz hxz
  calc
    _root_.GD.N0232.N0719.N0922.d009965 / 144 =
        ((volume : Measure ℝ).prod (volume : Measure ℝ)).real
          _root_.GD.N0232.N0719.N0922.d009952 * _root_.GD.N0232.N0719.N0922.d009965 := by
      rw [_root_.GD.N0232.N0719.N0922.d009967]
      ring
    _ = ∫ _xz in _root_.GD.N0232.N0719.N0922.d009952, _root_.GD.N0232.N0719.N0922.d009965 := by
      rw [setIntegral_const]
      rfl
    _ ≤ ∫ xz in _root_.GD.N0232.N0719.N0922.d009952, _root_.GD.N0232.N0719.N0922.d009964 y t xz := hmonoFun
    _ ≤ ∫ xz in _root_.GD.N0232.N0719.N0922.d009926, _root_.GD.N0232.N0719.N0922.d009964 y t xz := hmonoSet

end

end GD.N0232.N0719.N0922


#print axioms _root_.GD.N0232.N0719.N0922.d009966
#print axioms _root_.GD.N0232.N0719.N0922.d009970
