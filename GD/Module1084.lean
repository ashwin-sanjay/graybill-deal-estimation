import GD.Module0791
import GD.Module1006
import GD.Module1083
import GD.Module1026






















open Filter MeasureTheory Set

namespace GD
namespace N0232
namespace N0720
namespace N1491

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0137 _root_.GD.N0107
open _root_.GD.N0232.N0719.N0832
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0720.N1467
open _root_.GD.N0232.N0720.N1486
open _root_.GD.N0232.N0720.N1485
open _root_.GD.N0232.N0720.N1493
open _root_.GD.N0232.N0720.N1490
open _root_.GD.N0232.N0720.N1499
open _root_.GD.N0232.N0720.N1501
open _root_.GD.N0232.N0720.N1173
open _root_.GD.N0232.N0720.N1175
open _root_.GD.N0230.N0589






def d017379 (k : ℕ) : _root_.GD.N0232.N0720.N1173.d015933 → ℝ :=
  (_root_.GD.N0232.N0720.N1485.d017359 k).indicator (fun _ ↦ 1)

theorem d017380 (k : ℕ) :
    Measurable (_root_.GD.N0232.N0720.N1491.d017379 k) := by
  exact measurable_const.indicator (_root_.GD.N0232.N0720.N1485.d017360 k)

theorem d017381 (k : ℕ) (theta : _root_.GD.N0232.N0720.N1173.d015933) :
    0 ≤ _root_.GD.N0232.N0720.N1491.d017379 k theta := by
  by_cases htheta : theta ∈ _root_.GD.N0232.N0720.N1485.d017359 k
  · simp [_root_.GD.N0232.N0720.N1491.d017379, htheta]
  · simp [_root_.GD.N0232.N0720.N1491.d017379, htheta]

theorem d017382 (k : ℕ) (theta : _root_.GD.N0232.N0720.N1173.d015933) :
    _root_.GD.N0232.N0720.N1491.d017379 k theta ≤ 1 := by
  by_cases htheta : theta ∈ _root_.GD.N0232.N0720.N1485.d017359 k
  · simp [_root_.GD.N0232.N0720.N1491.d017379, htheta]
  · simp [_root_.GD.N0232.N0720.N1491.d017379, htheta]



theorem d017383 (theta : _root_.GD.N0232.N0720.N1173.d015933) :
    ∀ᶠ k : ℕ in atTop, theta ∈ _root_.GD.N0232.N0720.N1485.d017359 k := by
  have hcover : theta ∈ ⋃ k : ℕ, _root_.GD.N0232.N0720.N1485.d017359 k := by
    rw [_root_.GD.N0232.N0720.N1485.d017362]
    exact Set.mem_univ theta
  rw [Set.mem_iUnion] at hcover
  rcases hcover with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop N] with k hk
  exact _root_.GD.N0232.N0720.N1485.d017361 hk hN

theorem d017384 (theta : _root_.GD.N0232.N0720.N1173.d015933) :
    ∀ᶠ k : ℕ in atTop, _root_.GD.N0232.N0720.N1491.d017379 k theta = 1 := by
  filter_upwards [_root_.GD.N0232.N0720.N1491.d017383 theta] with k hk
  simp [_root_.GD.N0232.N0720.N1491.d017379, hk]

theorem d017385 (theta : _root_.GD.N0232.N0720.N1173.d015933) :
    Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1491.d017379 k theta) atTop (nhds 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [_root_.GD.N0232.N0720.N1491.d017384 theta] with k hk
  exact hk.symm



private theorem d017386
    (theta : _root_.GD.N0232.N0720.N1173.d015933) (x : _root_.GD.N0232.N0720.N1173.d015936) :
    0 ≤ _root_.GD.N0232.N0720.N1173.d015937 theta x := by
  exact _root_.GD.N0232.N0720.N1499.d015003 2 2 (_root_.GD.N0232.N0720.N1173.d015935 theta) x




def d017387
    (x : _root_.GD.N0232.N0720.N1173.d015936) (theta : _root_.GD.N0232.N0720.N1173.d015933) : ℝ :=
  ‖(_root_.GD.N0232.N0720.N1173.d015938 theta -
      _root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104 x) *
        _root_.GD.N0232.N0720.N1173.d015937 theta x‖

theorem d017388
    (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    Integrable (_root_.GD.N0232.N0720.N1491.d017387 x)
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) := by
  have hfull := _root_.GD.N0232.N0720.N1490.d016352 x ht
  have hmoment :=
    _root_.GD.N0232.N0720.N1490.d016354 x ht
  have hcenter : Integrable
      (fun theta : _root_.GD.N0232.N0720.N1173.d015933 ↦
        _root_.GD.N0232.N0720.N1173.d015938 theta * _root_.GD.N0232.N0720.N1173.d015937 theta x -
          _root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104 x *
            _root_.GD.N0232.N0720.N1173.d015937 theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) :=
    hmoment.sub (hfull.const_mul _)
  have hcenter' : Integrable
      (fun theta : _root_.GD.N0232.N0720.N1173.d015933 ↦
        (_root_.GD.N0232.N0720.N1173.d015938 theta -
            _root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104 x) *
          _root_.GD.N0232.N0720.N1173.d015937 theta x)
      (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104) := by
    refine hcenter.congr (ae_of_all _ fun theta ↦ ?_)
    ring
  change Integrable
    (fun theta : _root_.GD.N0232.N0720.N1173.d015933 ↦
      ‖(_root_.GD.N0232.N0720.N1173.d015938 theta -
          _root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104 x) *
        _root_.GD.N0232.N0720.N1173.d015937 theta x‖)
    (_root_.GD.N0232.N0720.N1173.d015934 _root_.GD.N0232.N0720.N1493.d016104)
  exact hcenter'.norm



theorem d017389
    (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    0 < _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104 (fun _ ↦ 1) x := by
  have hintegral :=
    _root_.GD.N0232.N0720.N1490.d016355 x ht
  have hpos := _root_.GD.N0232.N0720.N1493.d016113 (_root_.GD.N0232.N0720.N1467.d012542 2 2 x) ht
  rw [← hintegral] at hpos
  simpa [_root_.GD.N0232.N0720.N1173.d015940, _root_.GD.N0230.N0589.d000088, _root_.GD.N0232.N0720.N1173.d015939] using hpos





theorem d017390
    (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
        (_root_.GD.N0232.N0720.N1491.d017379 k) x)
      atTop
      (nhds (_root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
        (fun _ ↦ 1) x)) := by
  apply _root_.GD.N0232.N0720.N1175.d016004
    _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1491.d017379 x
    (fun theta ↦ _root_.GD.N0232.N0720.N1173.d015937 theta x)
  · exact Filter.Eventually.of_forall fun k ↦ by
      have hmeas : Measurable (fun theta : _root_.GD.N0232.N0720.N1173.d015933 ↦
          _root_.GD.N0232.N0720.N1173.d015937 theta x * _root_.GD.N0232.N0720.N1491.d017379 k theta) :=
        (_root_.GD.N0232.N0720.N1490.d016350 x).measurable.mul
          (_root_.GD.N0232.N0720.N1491.d017380 k)
      simpa [_root_.GD.N0232.N0720.N1173.d015939] using hmeas.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun k ↦ by
      filter_upwards with theta
      by_cases htheta : theta ∈ _root_.GD.N0232.N0720.N1485.d017359 k
      · simp [_root_.GD.N0232.N0720.N1173.d015939, _root_.GD.N0232.N0720.N1491.d017379, htheta,
          Real.norm_eq_abs, abs_of_nonneg
            (_root_.GD.N0232.N0720.N1491.d017386 theta x)]
      · simp [_root_.GD.N0232.N0720.N1173.d015939, _root_.GD.N0232.N0720.N1491.d017379, htheta,
          _root_.GD.N0232.N0720.N1491.d017386 theta x]
  · exact _root_.GD.N0232.N0720.N1490.d016352 x ht
  · exact ae_of_all _ _root_.GD.N0232.N0720.N1491.d017385





theorem d017391
    (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    ∀ᶠ k : ℕ in atTop,
      0 < _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
        (_root_.GD.N0232.N0720.N1491.d017379 k) x := by
  have hlimit := _root_.GD.N0232.N0720.N1491.d017389 x ht
  exact
    (_root_.GD.N0232.N0720.N1491.d017390 x ht).eventually
      (Ioi_mem_nhds hlimit)



theorem d017392
    (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1173.d015945 _root_.GD.N0232.N0720.N1493.d016104
        (_root_.GD.N0232.N0720.N1491.d017379 k) x)
      atTop (nhds 0) := by
  have hfull := _root_.GD.N0232.N0720.N1490.d016352 x ht
  have hmoment :=
    _root_.GD.N0232.N0720.N1490.d016354 x ht
  apply _root_.GD.N0232.N0720.N1175.d016003
    _root_.GD.N0232.N0720.N1493.d016104 _root_.GD.N0232.N0720.N1491.d017379 x
    (_root_.GD.N0232.N0720.N1491.d017387 x)
  · exact Filter.Eventually.of_forall fun k ↦ by
      have hcenter : Measurable (fun theta : _root_.GD.N0232.N0720.N1173.d015933 ↦
          _root_.GD.N0232.N0720.N1173.d015938 theta -
            _root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104 x) := by
        unfold _root_.GD.N0232.N0720.N1173.d015938
        fun_prop
      have hweightedLikelihood : Measurable (fun theta : _root_.GD.N0232.N0720.N1173.d015933 ↦
          _root_.GD.N0232.N0720.N1173.d015937 theta x * _root_.GD.N0232.N0720.N1491.d017379 k theta) :=
        (_root_.GD.N0232.N0720.N1490.d016350 x).measurable.mul
          (_root_.GD.N0232.N0720.N1491.d017380 k)
      have hmeas : Measurable (fun theta : _root_.GD.N0232.N0720.N1173.d015933 ↦
          (_root_.GD.N0232.N0720.N1173.d015938 theta -
              _root_.GD.N0232.N0720.N1173.d015944 _root_.GD.N0232.N0720.N1493.d016104 x) *
            (_root_.GD.N0232.N0720.N1173.d015937 theta x * _root_.GD.N0232.N0720.N1491.d017379 k theta)) :=
        hcenter.mul hweightedLikelihood
      simpa [_root_.GD.N0232.N0720.N1173.d015939] using hmeas.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun k ↦ by
      filter_upwards with theta
      by_cases htheta : theta ∈ _root_.GD.N0232.N0720.N1485.d017359 k
      · simp [_root_.GD.N0232.N0720.N1173.d015939, _root_.GD.N0232.N0720.N1491.d017379, htheta,
          _root_.GD.N0232.N0720.N1491.d017387]
      · simp [_root_.GD.N0232.N0720.N1173.d015939, _root_.GD.N0232.N0720.N1491.d017379, htheta,
          _root_.GD.N0232.N0720.N1491.d017387]
        positivity
  · exact _root_.GD.N0232.N0720.N1491.d017388 x ht
  · exact ae_of_all _ _root_.GD.N0232.N0720.N1491.d017385
  · exact hfull
  · exact hmoment
  · exact (_root_.GD.N0232.N0720.N1491.d017389 x ht).ne'




theorem d017393
    (x : _root_.GD.N0232.N0720.N1173.d015936)
    (ht : ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i) :
    Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1175.d016001 _root_.GD.N0232.N0720.N1493.d016104
        (_root_.GD.N0232.N0720.N1491.d017379 k) x)
      atTop (nhds 0) := by
  exact _root_.GD.N0232.N0720.N1175.d016000
    (_root_.GD.N0232.N0720.N1491.d017392 x ht)
    (_root_.GD.N0232.N0720.N1491.d017390 x ht)
    (_root_.GD.N0232.N0720.N1491.d017389 x ht).ne'





theorem d017394 :
    ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      ∀ i, 0 < (_root_.GD.N0232.N0720.N1467.d012542 2 2 x).meanVariance i := by
  have href :
      _root_.GD.N0232.N0720.N1080.d014172 2 2 =
        (_root_.GD.N0137.d008895 2).prod (_root_.GD.N0137.d008895 2) := by
    unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171 _root_.GD.N0107.d009030
      _root_.GD.N0137.d008914 _root_.GD.N0232.N0720.N1080.d014169
      _root_.GD.N0107.d009024
      _root_.GD.N0107.d009018
    simp
  rw [href]
  have hx :=
    (measurePreserving_fst
      (μ := _root_.GD.N0137.d008895 2)
      (ν := _root_.GD.N0137.d008895 2)).quasiMeasurePreserving.ae
      (_root_.GD.N0232.N0719.N0832.d012009 2 (by norm_num))
  have hy :=
    (measurePreserving_snd
      (μ := _root_.GD.N0137.d008895 2)
      (ν := _root_.GD.N0137.d008895 2)).quasiMeasurePreserving.ae
      (_root_.GD.N0232.N0719.N0832.d012009 2 (by norm_num))
  filter_upwards [hx, hy] with x hx hy
  intro i
  fin_cases i
  · simpa [_root_.GD.N0232.N0720.N1467.d012547,
      _root_.GD.N0107.d009085] using
        (div_pos hx (by norm_num : (0 : ℝ) < 2))
  · simpa [_root_.GD.N0232.N0720.N1467.d012548,
      _root_.GD.N0107.d009085] using
        (div_pos hy (by norm_num : (0 : ℝ) < 2))








theorem d017395 :
    ∀ᵐ x ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      0 < _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104 (fun _ ↦ 1) x ∧
      Tendsto
        (fun k ↦ _root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
          (_root_.GD.N0232.N0720.N1491.d017379 k) x)
        atTop
        (nhds (_root_.GD.N0232.N0720.N1173.d015940 _root_.GD.N0232.N0720.N1493.d016104
          (fun _ ↦ 1) x)) ∧
      Tendsto
        (fun k ↦ _root_.GD.N0232.N0720.N1173.d015945 _root_.GD.N0232.N0720.N1493.d016104
          (_root_.GD.N0232.N0720.N1491.d017379 k) x)
        atTop (nhds 0) ∧
      Tendsto
        (fun k ↦ _root_.GD.N0232.N0720.N1175.d016001 _root_.GD.N0232.N0720.N1493.d016104
          (_root_.GD.N0232.N0720.N1491.d017379 k) x)
        atTop (nhds 0) := by
  filter_upwards [_root_.GD.N0232.N0720.N1491.d017394] with x ht
  exact ⟨_root_.GD.N0232.N0720.N1491.d017389 x ht,
    _root_.GD.N0232.N0720.N1491.d017390 x ht,
    _root_.GD.N0232.N0720.N1491.d017392 x ht,
    _root_.GD.N0232.N0720.N1491.d017393
      x ht⟩

end

end N1491
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1491.d017389
#print axioms _root_.GD.N0232.N0720.N1491.d017392
#print axioms _root_.GD.N0232.N0720.N1491.d017395
