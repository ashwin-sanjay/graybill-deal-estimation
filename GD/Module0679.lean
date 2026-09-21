import GD.Module0678

















open MeasureTheory Set

namespace GD.N0232.N0719.N0922

noncomputable section


theorem d009937 : Continuous _root_.GD.N0232.N0719.N0922.d009920 := by
  unfold _root_.GD.N0232.N0719.N0922.d009920
  fun_prop


theorem d009938 : Function.Injective _root_.GD.N0232.N0719.N0922.d009920 := by
  intro xz uv h
  have h0 := congrFun h (0 : Fin 2)
  have h1 := congrFun h (1 : Fin 2)
  have hx : xz.1 = uv.1 := by
    simpa [_root_.GD.N0232.N0719.N0922.d009920] using h1
  have hz : xz.2 = uv.2 := by
    simp only [_root_.GD.N0232.N0719.N0922.d009920, Matrix.cons_val_zero] at h0
    rw [hx] at h0
    linarith
  exact Prod.ext hx hz




theorem d009939 :
    MeasurableEmbedding _root_.GD.N0232.N0719.N0922.d009920 :=
  _root_.GD.N0232.N0719.N0922.d009937.measurableEmbedding _root_.GD.N0232.N0719.N0922.d009938





theorem d009940 (f :
    _root_.GD.N0232.N0719.N0857.d009377 3 → ℝ) :
    (∫ q in _root_.GD.N0232.N0719.N0955.d009607 3, f q) =
      ∫ xz in _root_.GD.N0232.N0719.N0922.d009926, f (_root_.GD.N0232.N0719.N0922.d009920 xz) := by
  let S := _root_.GD.N0232.N0719.N0955.d009607 3
  let T := _root_.GD.N0232.N0719.N0922.d009926
  let g : _root_.GD.N0232.N0719.N0857.d009377 3 → ℝ :=
    S.indicator f
  have htransport := _root_.GD.N0232.N0719.N0922.d009936.integral_comp
    _root_.GD.N0232.N0719.N0922.d009939 g
  have hpreimage : _root_.GD.N0232.N0719.N0922.d009920 ⁻¹' S = T := by
    ext xz
    exact _root_.GD.N0232.N0719.N0922.d009927 xz
  have hcomp : g ∘ _root_.GD.N0232.N0719.N0922.d009920 = T.indicator (f ∘ _root_.GD.N0232.N0719.N0922.d009920) := by
    funext xz
    by_cases hx : xz ∈ T
    · have hs : _root_.GD.N0232.N0719.N0922.d009920 xz ∈ S := by
        exact (_root_.GD.N0232.N0719.N0922.d009927 xz).2 hx
      simp [g, Function.comp_apply, Set.indicator_of_mem hx,
        Set.indicator_of_mem hs]
    · have hs : _root_.GD.N0232.N0719.N0922.d009920 xz ∉ S := by
        intro hs
        exact hx ((_root_.GD.N0232.N0719.N0922.d009927 xz).1 hs)
      simp [g, Function.comp_apply, Set.indicator_of_notMem hx,
        Set.indicator_of_notMem hs]
  have hS : MeasurableSet S :=
    _root_.GD.N0232.N0719.N0955.d009608 3
  have hT : MeasurableSet T := by
    unfold T _root_.GD.N0232.N0719.N0922.d009926
    have hfst : Measurable (fun xz : ℝ × ℝ ↦ xz.1) := measurable_fst
    have hsnd : Measurable (fun xz : ℝ × ℝ ↦ xz.2) := measurable_snd
    have hzero : Measurable (fun _xz : ℝ × ℝ ↦ (0 : ℝ)) := measurable_const
    have hone : Measurable (fun _xz : ℝ × ℝ ↦ (1 : ℝ)) := measurable_const
    exact (measurableSet_lt hzero hfst).inter
      ((measurableSet_lt hzero hsnd).inter
        (measurableSet_lt (hfst.add hsnd) hone))
  have hleft :
      (∫ xz, g (_root_.GD.N0232.N0719.N0922.d009920 xz)) =
        ∫ xz in T, f (_root_.GD.N0232.N0719.N0922.d009920 xz) := by
    rw [show (fun xz ↦ g (_root_.GD.N0232.N0719.N0922.d009920 xz)) =
        T.indicator (f ∘ _root_.GD.N0232.N0719.N0922.d009920) by simpa [Function.comp_def] using hcomp]
    exact integral_indicator hT
  have hright :
      (∫ q, g q) = ∫ q in S, f q := by
    simpa [g] using (integral_indicator (f := f) hS)
  calc
    (∫ q in _root_.GD.N0232.N0719.N0955.d009607 3, f q) =
        ∫ q, g q := by simpa [S] using hright.symm
    _ = ∫ xz, g (_root_.GD.N0232.N0719.N0922.d009920 xz) := htransport.symm
    _ = ∫ xz in _root_.GD.N0232.N0719.N0922.d009926, f (_root_.GD.N0232.N0719.N0922.d009920 xz) := by
      simpa [T] using hleft


theorem d009941
    (y t : Fin 3 → ℝ) :
    _root_.GD.N0232.N0719.N0929.d009647 (by norm_num)
        _root_.GD.N0232.N0719.N0922.d009915 y t (5 / 2) =
      ∫ xz in _root_.GD.N0232.N0719.N0922.d009926,
        _root_.GD.N0232.N0719.N0928.d009437
          _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t (5 / 2) := by
  unfold _root_.GD.N0232.N0719.N0929.d009647
  simpa [_root_.GD.N0232.N0719.N0922.d009922] using
    _root_.GD.N0232.N0719.N0922.d009940
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 3 ↦
        _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915
          (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num) q)
          y t (5 / 2))


theorem d009942
    (y t : Fin 3 → ℝ) :
    _root_.GD.N0232.N0719.N0929.d009652 (by norm_num)
        _root_.GD.N0232.N0719.N0922.d009915 y t (5 / 2) =
      ∫ xz in _root_.GD.N0232.N0719.N0922.d009926,
        _root_.GD.N0232.N0719.N0928.d009437
            _root_.GD.N0232.N0719.N0922.d009915 (_root_.GD.N0232.N0719.N0922.d009922 xz) y t (5 / 2) *
          _root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0719.N0922.d009922 xz) y := by
  unfold _root_.GD.N0232.N0719.N0929.d009652
  simpa [_root_.GD.N0232.N0719.N0922.d009922] using
    _root_.GD.N0232.N0719.N0922.d009940
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 3 ↦
        _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0922.d009915
            (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num) q)
            y t (5 / 2) *
          _root_.GD.N0232.N0719.N0928.d009405
            (_root_.GD.N0232.N0719.N0853.d009567 (by norm_num) q) y)

end

end GD.N0232.N0719.N0922
