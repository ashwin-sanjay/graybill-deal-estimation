import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

set_option warningAsError true
set_option autoImplicit false






















open MeasureTheory Set Filter Topology

namespace GD.N0232.N0720.N1240

noncomputable section

def d002050 (x : ℝ) : ℝ := 10 * x ^ 2 - 1

def d002051 (x : ℝ) : ℝ := 2520 * x ^ 4 - 420 * x ^ 2

def d002052 (x : ℝ) : ℝ := 70 * x ^ 4 - (45 / 2) * x ^ 2 + 5 / 4


def d002053 (x y v : ℝ) : ℝ :=
  1 - 4 * x * y + v * (1 / 2 - 2 * x ^ 2)

def d002054 (x y v : ℝ) : ℝ :=
  (x - y) * Real.rpow (_root_.GD.N0232.N0720.N1240.d002053 x y v) (-5 / 2)

def d002055 (x y v : ℝ) : ℝ :=
  -Real.rpow (_root_.GD.N0232.N0720.N1240.d002053 x y v) (-5 / 2) +
    10 * x * (x - y) * Real.rpow (_root_.GD.N0232.N0720.N1240.d002053 x y v) (-7 / 2)

def d002056 (x y v : ℝ) : ℝ :=
  -20 * x * Real.rpow (_root_.GD.N0232.N0720.N1240.d002053 x y v) (-7 / 2) +
    140 * x ^ 2 * (x - y) * Real.rpow (_root_.GD.N0232.N0720.N1240.d002053 x y v) (-9 / 2)

def d002057 (x y v : ℝ) : ℝ :=
  -420 * x ^ 2 * Real.rpow (_root_.GD.N0232.N0720.N1240.d002053 x y v) (-9 / 2) +
    2520 * x ^ 3 * (x - y) * Real.rpow (_root_.GD.N0232.N0720.N1240.d002053 x y v) (-11 / 2)

def d002058 (x y v : ℝ) : ℝ :=
  (5 / 2) * (1 / 2 - 2 * x ^ 2) * Real.rpow (_root_.GD.N0232.N0720.N1240.d002053 x y v) (-7 / 2) -
    35 * x * (x - y) * (1 / 2 - 2 * x ^ 2) *
      Real.rpow (_root_.GD.N0232.N0720.N1240.d002053 x y v) (-9 / 2)

def d002059 (x y v : ℝ) : ℝ :=
  (x - y) * (-5 / 2) * (1 / 2 - 2 * x ^ 2) *
    Real.rpow (_root_.GD.N0232.N0720.N1240.d002053 x y v) (-7 / 2)

theorem d002060 (x y v : ℝ) :
    HasDerivAt (fun y ↦ _root_.GD.N0232.N0720.N1240.d002053 x y v) (-4 * x) y := by
  convert! ((hasDerivAt_const y (1 : ℝ)).sub
    ((hasDerivAt_id y).const_mul (4 * x))).add
      (hasDerivAt_const y (v * (1 / 2 - 2 * x ^ 2))) using 1
  norm_num [_root_.GD.N0232.N0720.N1240.d002053]

theorem d002061 (x y v : ℝ) :
    HasDerivAt (fun v ↦ _root_.GD.N0232.N0720.N1240.d002053 x y v) (1 / 2 - 2 * x ^ 2) v := by
  convert! (hasDerivAt_const v (1 - 4 * x * y)).add
    ((hasDerivAt_id v).mul_const (1 / 2 - 2 * x ^ 2)) using 1
  norm_num [_root_.GD.N0232.N0720.N1240.d002053]

theorem d002062 (x y v : ℝ)
    (hb : _root_.GD.N0232.N0720.N1240.d002053 x y v ≠ 0) :
    HasDerivAt (fun y ↦ _root_.GD.N0232.N0720.N1240.d002054 x y v) (_root_.GD.N0232.N0720.N1240.d002055 x y v) y := by
  have hp := (_root_.GD.N0232.N0720.N1240.d002060 x y v).rpow_const
    (p := (-5 / 2 : ℝ)) (Or.inl hb)
  convert! ((hasDerivAt_const y x).sub (hasDerivAt_id y)).mul hp using 1
  norm_num [_root_.GD.N0232.N0720.N1240.d002054, _root_.GD.N0232.N0720.N1240.d002055]
  ring

theorem d002063 (x y v : ℝ)
    (hb : _root_.GD.N0232.N0720.N1240.d002053 x y v ≠ 0) :
    HasDerivAt (fun y ↦ _root_.GD.N0232.N0720.N1240.d002055 x y v)
      (_root_.GD.N0232.N0720.N1240.d002056 x y v) y := by
  have hp₅ := (_root_.GD.N0232.N0720.N1240.d002060 x y v).rpow_const
    (p := (-5 / 2 : ℝ)) (Or.inl hb)
  have hp₇ := (_root_.GD.N0232.N0720.N1240.d002060 x y v).rpow_const
    (p := (-7 / 2 : ℝ)) (Or.inl hb)
  convert! hp₅.neg.add
    (((hasDerivAt_const y (10 * x)).mul
      ((hasDerivAt_const y x).sub (hasDerivAt_id y))).mul hp₇) using 1
  norm_num [_root_.GD.N0232.N0720.N1240.d002055, _root_.GD.N0232.N0720.N1240.d002056]
  ring

theorem d002064 (x y v : ℝ)
    (hb : _root_.GD.N0232.N0720.N1240.d002053 x y v ≠ 0) :
    HasDerivAt (fun y ↦ _root_.GD.N0232.N0720.N1240.d002056 x y v)
      (_root_.GD.N0232.N0720.N1240.d002057 x y v) y := by
  have hp₇ := (_root_.GD.N0232.N0720.N1240.d002060 x y v).rpow_const
    (p := (-7 / 2 : ℝ)) (Or.inl hb)
  have hp₉ := (_root_.GD.N0232.N0720.N1240.d002060 x y v).rpow_const
    (p := (-9 / 2 : ℝ)) (Or.inl hb)
  convert! (hp₇.const_mul (-20 * x)).add
    (((hasDerivAt_const y (140 * x ^ 2)).mul
      ((hasDerivAt_const y x).sub (hasDerivAt_id y))).mul hp₉) using 1
  norm_num [_root_.GD.N0232.N0720.N1240.d002056, _root_.GD.N0232.N0720.N1240.d002057]
  ring

theorem d002065 (x y v : ℝ)
    (hb : _root_.GD.N0232.N0720.N1240.d002053 x y v ≠ 0) :
    HasDerivAt (fun v ↦ _root_.GD.N0232.N0720.N1240.d002055 x y v)
      (_root_.GD.N0232.N0720.N1240.d002058 x y v) v := by
  have hp₅ := (_root_.GD.N0232.N0720.N1240.d002061 x y v).rpow_const
    (p := (-5 / 2 : ℝ)) (Or.inl hb)
  have hp₇ := (_root_.GD.N0232.N0720.N1240.d002061 x y v).rpow_const
    (p := (-7 / 2 : ℝ)) (Or.inl hb)
  convert! hp₅.neg.add (hp₇.const_mul (10 * x * (x - y))) using 1
  norm_num [_root_.GD.N0232.N0720.N1240.d002055, _root_.GD.N0232.N0720.N1240.d002058]
  ring

theorem d002066 (x y v : ℝ)
    (hb : _root_.GD.N0232.N0720.N1240.d002053 x y v ≠ 0) :
    HasDerivAt (fun v ↦ _root_.GD.N0232.N0720.N1240.d002054 x y v) (_root_.GD.N0232.N0720.N1240.d002059 x y v) v := by
  have hp := (_root_.GD.N0232.N0720.N1240.d002061 x y v).rpow_const
    (p := (-5 / 2 : ℝ)) (Or.inl hb)
  convert! hp.const_mul (x - y) using 1
  norm_num [_root_.GD.N0232.N0720.N1240.d002054, _root_.GD.N0232.N0720.N1240.d002059]
  ring

theorem d002067 (x : ℝ) :
    _root_.GD.N0232.N0720.N1240.d002055 x 0 0 = _root_.GD.N0232.N0720.N1240.d002050 x := by
  simp [_root_.GD.N0232.N0720.N1240.d002055, _root_.GD.N0232.N0720.N1240.d002053, _root_.GD.N0232.N0720.N1240.d002050]
  ring

theorem d002068 (x : ℝ) :
    _root_.GD.N0232.N0720.N1240.d002057 x 0 0 = _root_.GD.N0232.N0720.N1240.d002051 x := by
  simp [_root_.GD.N0232.N0720.N1240.d002057, _root_.GD.N0232.N0720.N1240.d002053, _root_.GD.N0232.N0720.N1240.d002051]
  ring

theorem d002069 (x : ℝ) :
    _root_.GD.N0232.N0720.N1240.d002058 x 0 0 = _root_.GD.N0232.N0720.N1240.d002052 x := by
  simp [_root_.GD.N0232.N0720.N1240.d002058, _root_.GD.N0232.N0720.N1240.d002053, _root_.GD.N0232.N0720.N1240.d002052]
  ring

abbrev d002070 := Icc (-1 / 2 : ℝ) (1 / 2)

theorem d002071 {x y v : ℝ}
    (hx : x ∈ Icc (-1 / 2 : ℝ) (1 / 2))
    (hy : y ∈ Icc (-1 / 4 : ℝ) (1 / 4))
    (hv : v ∈ Icc (-1 / 4 : ℝ) (1 / 4)) :
    3 / 8 ≤ _root_.GD.N0232.N0720.N1240.d002053 x y v := by
  have hxabs : |x| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  have hyabs : |y| ≤ 1 / 4 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
  have hvabs : |v| ≤ 1 / 4 := abs_le.mpr ⟨by linarith [hv.1], hv.2⟩
  have hxsq : x ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (sub_nonneg.mpr hx.1)]
  have ha : 0 ≤ 1 / 2 - 2 * x ^ 2 := by nlinarith
  have ha' : 1 / 2 - 2 * x ^ 2 ≤ 1 / 2 := by nlinarith [sq_nonneg x]
  have hxy : |4 * x * y| ≤ 1 / 2 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    calc
      4 * |x| * |y| ≤ 4 * (1 / 2) * (1 / 4) := by gcongr
      _ = 1 / 2 := by norm_num
  have hva : |v * (1 / 2 - 2 * x ^ 2)| ≤ 1 / 8 := by
    rw [abs_mul, abs_of_nonneg ha]
    calc
      |v| * (1 / 2 - 2 * x ^ 2) ≤ (1 / 4) * (1 / 2) := by gcongr
      _ = 1 / 8 := by norm_num
  unfold _root_.GD.N0232.N0720.N1240.d002053
  linarith [(abs_le.mp hxy).2, (abs_le.mp hva).1]



theorem d002072
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (ρ : Measure X) [IsFiniteMeasure ρ]
    (F F' : ℝ → X → ℝ) {l r y : ℝ} (hy : y ∈ Ioo l r)
    (hF : ContinuousOn (fun z : ℝ × X ↦ F z.1 z.2) (Icc l r ×ˢ univ))
    (hF' : ContinuousOn (fun z : ℝ × X ↦ F' z.1 z.2) (Icc l r ×ˢ univ))
    (hd : ∀ q ∈ Ioo l r, ∀ x, HasDerivAt (fun q ↦ F q x) (F' q x) q) :
    HasDerivAt (fun q ↦ ∫ x, F q x ∂ρ) (∫ x, F' y x ∂ρ) y := by
  have hs : Ioo l r ∈ 𝓝 y := isOpen_Ioo.mem_nhds hy
  have hslice : ∀ q ∈ Icc l r, Continuous (F q) := by
    intro q hq
    apply continuousOn_univ.mp
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x _ ↦ ⟨hq, mem_univ x⟩)
  have hslice' : ∀ q ∈ Icc l r, Continuous (F' q) := by
    intro q hq
    apply continuousOn_univ.mp
    exact hF'.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x _ ↦ ⟨hq, mem_univ x⟩)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod
    (isCompact_univ : IsCompact (univ : Set X))).exists_bound_of_continuousOn hF'
  have hi : Integrable (F y) ρ := by
    simpa using (hslice y ⟨hy.1.le, hy.2.le⟩).continuousOn.integrableOn_compact
      (isCompact_univ : IsCompact (univ : Set X)) (μ := ρ)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ ↦ C) hs ?_ hi
      (hslice' y ⟨hy.1.le, hy.2.le⟩).aestronglyMeasurable ?_
      (integrable_const C) ?_).2
  · filter_upwards [hs] with q hq
    exact (hslice q ⟨hq.1.le, hq.2.le⟩).aestronglyMeasurable
  · exact ae_of_all ρ fun x q hq ↦ hC (q, x) ⟨⟨hq.1.le, hq.2.le⟩, mem_univ x⟩
  · exact ae_of_all ρ fun x q hq ↦ hd q hq x

theorem d002073 {v : ℝ}
    (hv : v ∈ Icc (-1 / 4 : ℝ) (1 / 4)) (p : ℝ) :
    ContinuousOn (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦
      Real.rpow (_root_.GD.N0232.N0720.N1240.d002053 z.2 z.1 v) p)
      (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ univ) := by
  have hb : Continuous (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦ _root_.GD.N0232.N0720.N1240.d002053 z.2 z.1 v) := by
    unfold _root_.GD.N0232.N0720.N1240.d002053
    fun_prop
  apply hb.continuousOn.rpow_const
  intro z hz
  left
  have h := _root_.GD.N0232.N0720.N1240.d002071 z.2.property hz.1 hv
  linarith

theorem d002074 {v : ℝ}
    (hv : v ∈ Icc (-1 / 4 : ℝ) (1 / 4)) :
    ContinuousOn (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦ _root_.GD.N0232.N0720.N1240.d002054 z.2 z.1 v)
      (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ univ) := by
  exact (show Continuous (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦ (z.2 : ℝ) - z.1)
      from by fun_prop).continuousOn.mul (_root_.GD.N0232.N0720.N1240.d002073 hv (-5 / 2))

theorem d002075 {v : ℝ}
    (hv : v ∈ Icc (-1 / 4 : ℝ) (1 / 4)) :
    ContinuousOn (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦ _root_.GD.N0232.N0720.N1240.d002055 z.2 z.1 v)
      (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ univ) := by
  exact (_root_.GD.N0232.N0720.N1240.d002073 hv (-5 / 2)).neg.add
    ((show Continuous (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦ 10 * (z.2 : ℝ) * (z.2 - z.1))
      from by fun_prop).continuousOn.mul (_root_.GD.N0232.N0720.N1240.d002073 hv (-7 / 2)))

theorem d002076 {v : ℝ}
    (hv : v ∈ Icc (-1 / 4 : ℝ) (1 / 4)) :
    ContinuousOn (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦ _root_.GD.N0232.N0720.N1240.d002056 z.2 z.1 v)
      (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ univ) := by
  exact ((show Continuous (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦ -20 * (z.2 : ℝ))
    from by fun_prop).continuousOn.mul (_root_.GD.N0232.N0720.N1240.d002073 hv (-7 / 2))).add
    ((show Continuous (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦ 140 * (z.2 : ℝ) ^ 2 * (z.2 - z.1))
      from by fun_prop).continuousOn.mul (_root_.GD.N0232.N0720.N1240.d002073 hv (-9 / 2)))

theorem d002077 {v : ℝ}
    (hv : v ∈ Icc (-1 / 4 : ℝ) (1 / 4)) :
    ContinuousOn (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦ _root_.GD.N0232.N0720.N1240.d002057 z.2 z.1 v)
      (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ univ) := by
  exact ((show Continuous (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦ -420 * (z.2 : ℝ) ^ 2)
    from by fun_prop).continuousOn.mul (_root_.GD.N0232.N0720.N1240.d002073 hv (-9 / 2))).add
    ((show Continuous (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦ 2520 * (z.2 : ℝ) ^ 3 * (z.2 - z.1))
      from by fun_prop).continuousOn.mul (_root_.GD.N0232.N0720.N1240.d002073 hv (-11 / 2)))

theorem d002078
    (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) [IsFiniteMeasure ρ] {y v : ℝ}
    (hy : y ∈ Ioo (-1 / 4 : ℝ) (1 / 4))
    (hv : v ∈ Icc (-1 / 4 : ℝ) (1 / 4)) :
    HasDerivAt (fun y ↦ ∫ x, _root_.GD.N0232.N0720.N1240.d002054 x y v ∂ρ)
      (∫ x, _root_.GD.N0232.N0720.N1240.d002055 x y v ∂ρ) y := by
  apply _root_.GD.N0232.N0720.N1240.d002072 ρ _ _ hy
    (_root_.GD.N0232.N0720.N1240.d002074 hv) (_root_.GD.N0232.N0720.N1240.d002075 hv)
  intro q hq x
  exact _root_.GD.N0232.N0720.N1240.d002062 x q v (by
    have h := _root_.GD.N0232.N0720.N1240.d002071 x.property ⟨hq.1.le, hq.2.le⟩ hv
    linarith)

theorem d002079
    (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) [IsFiniteMeasure ρ] {y v : ℝ}
    (hy : y ∈ Ioo (-1 / 4 : ℝ) (1 / 4))
    (hv : v ∈ Icc (-1 / 4 : ℝ) (1 / 4)) :
    HasDerivAt (fun y ↦ ∫ x, _root_.GD.N0232.N0720.N1240.d002055 x y v ∂ρ)
      (∫ x, _root_.GD.N0232.N0720.N1240.d002056 x y v ∂ρ) y := by
  apply _root_.GD.N0232.N0720.N1240.d002072 ρ _ _ hy
    (_root_.GD.N0232.N0720.N1240.d002075 hv) (_root_.GD.N0232.N0720.N1240.d002076 hv)
  intro q hq x
  exact _root_.GD.N0232.N0720.N1240.d002063 x q v (by
    have h := _root_.GD.N0232.N0720.N1240.d002071 x.property ⟨hq.1.le, hq.2.le⟩ hv
    linarith)

theorem d002080
    (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) [IsFiniteMeasure ρ] {y v : ℝ}
    (hy : y ∈ Ioo (-1 / 4 : ℝ) (1 / 4))
    (hv : v ∈ Icc (-1 / 4 : ℝ) (1 / 4)) :
    HasDerivAt (fun y ↦ ∫ x, _root_.GD.N0232.N0720.N1240.d002056 x y v ∂ρ)
      (∫ x, _root_.GD.N0232.N0720.N1240.d002057 x y v ∂ρ) y := by
  apply _root_.GD.N0232.N0720.N1240.d002072 ρ _ _ hy
    (_root_.GD.N0232.N0720.N1240.d002076 hv) (_root_.GD.N0232.N0720.N1240.d002077 hv)
  intro q hq x
  exact _root_.GD.N0232.N0720.N1240.d002064 x q v (by
    have h := _root_.GD.N0232.N0720.N1240.d002071 x.property ⟨hq.1.le, hq.2.le⟩ hv
    linarith)

theorem d002081 {y : ℝ}
    (hy : y ∈ Icc (-1 / 4 : ℝ) (1 / 4)) (p : ℝ) :
    ContinuousOn (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦
      Real.rpow (_root_.GD.N0232.N0720.N1240.d002053 z.2 y z.1) p)
      (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ univ) := by
  have hb : Continuous (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦ _root_.GD.N0232.N0720.N1240.d002053 z.2 y z.1) := by
    unfold _root_.GD.N0232.N0720.N1240.d002053
    fun_prop
  apply hb.continuousOn.rpow_const
  intro z hz
  left
  have h := _root_.GD.N0232.N0720.N1240.d002071 z.2.property hy hz.1
  linarith

theorem d002082 {y : ℝ}
    (hy : y ∈ Icc (-1 / 4 : ℝ) (1 / 4)) :
    ContinuousOn (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦ _root_.GD.N0232.N0720.N1240.d002055 z.2 y z.1)
      (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ univ) := by
  exact (_root_.GD.N0232.N0720.N1240.d002081 hy (-5 / 2)).neg.add
    ((show Continuous (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦ 10 * (z.2 : ℝ) * (z.2 - y))
      from by fun_prop).continuousOn.mul (_root_.GD.N0232.N0720.N1240.d002081 hy (-7 / 2)))

theorem d002083 {y : ℝ}
    (hy : y ∈ Icc (-1 / 4 : ℝ) (1 / 4)) :
    ContinuousOn (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦ _root_.GD.N0232.N0720.N1240.d002058 z.2 y z.1)
      (Icc (-1 / 4 : ℝ) (1 / 4) ×ˢ univ) := by
  exact ((show Continuous (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦
      (5 / 2 : ℝ) * (1 / 2 - 2 * (z.2 : ℝ) ^ 2))
    from by fun_prop).continuousOn.mul (_root_.GD.N0232.N0720.N1240.d002081 hy (-7 / 2))).sub
    ((show Continuous (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦
        35 * (z.2 : ℝ) * (z.2 - y) * (1 / 2 - 2 * (z.2 : ℝ) ^ 2))
      from by fun_prop).continuousOn.mul (_root_.GD.N0232.N0720.N1240.d002081 hy (-9 / 2)))

theorem d002084
    (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) [IsFiniteMeasure ρ] {y v : ℝ}
    (hy : y ∈ Icc (-1 / 4 : ℝ) (1 / 4))
    (hv : v ∈ Ioo (-1 / 4 : ℝ) (1 / 4)) :
    HasDerivAt (fun v ↦ ∫ x, _root_.GD.N0232.N0720.N1240.d002055 x y v ∂ρ)
      (∫ x, _root_.GD.N0232.N0720.N1240.d002058 x y v ∂ρ) v := by
  apply _root_.GD.N0232.N0720.N1240.d002072 ρ _ _ hv
    (_root_.GD.N0232.N0720.N1240.d002082 hy) (_root_.GD.N0232.N0720.N1240.d002083 hy)
  intro q hq x
  exact _root_.GD.N0232.N0720.N1240.d002065 x y q (by
    have h := _root_.GD.N0232.N0720.N1240.d002071 x.property hy ⟨hq.1.le, hq.2.le⟩
    linarith)

theorem d002085
    (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) [IsFiniteMeasure ρ] {y v : ℝ}
    (hy : y ∈ Icc (-1 / 4 : ℝ) (1 / 4))
    (hv : v ∈ Ioo (-1 / 4 : ℝ) (1 / 4)) :
    HasDerivAt (fun v ↦ ∫ x, _root_.GD.N0232.N0720.N1240.d002054 x y v ∂ρ)
      (∫ x, _root_.GD.N0232.N0720.N1240.d002059 x y v ∂ρ) v := by
  apply _root_.GD.N0232.N0720.N1240.d002072 ρ _ _ hv
  · exact (show Continuous (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦ (z.2 : ℝ) - y)
      from by fun_prop).continuousOn.mul (_root_.GD.N0232.N0720.N1240.d002081 hy (-5 / 2))
  · exact (show Continuous (fun z : ℝ × _root_.GD.N0232.N0720.N1240.d002070 ↦
      ((z.2 : ℝ) - y) * (-5 / 2) * (1 / 2 - 2 * (z.2 : ℝ) ^ 2))
      from by fun_prop).continuousOn.mul (_root_.GD.N0232.N0720.N1240.d002081 hy (-7 / 2))
  · intro q hq x
    exact _root_.GD.N0232.N0720.N1240.d002066 x y q (by
      have h := _root_.GD.N0232.N0720.N1240.d002071 x.property hy ⟨hq.1.le, hq.2.le⟩
      linarith)

theorem d002086 (x : ℝ) :
    39 * _root_.GD.N0232.N0720.N1240.d002050 x - _root_.GD.N0232.N0720.N1240.d002051 x + 36 * _root_.GD.N0232.N0720.N1240.d002052 x = 6 := by
  unfold _root_.GD.N0232.N0720.N1240.d002050 _root_.GD.N0232.N0720.N1240.d002051 _root_.GD.N0232.N0720.N1240.d002052
  ring

theorem d002087 (m₂ m₄ : ℝ)
    (hfirst : 10 * m₂ - 1 = 0)
    (hthird : 2520 * m₄ - 420 * m₂ = 0)
    (hmixed : 70 * m₄ - (45 / 2) * m₂ + 5 / 4 = 0) : False := by
  linarith

theorem d002088 (m₂ m₄ : ℝ)
    (hfirst : 10 * m₂ - 1 = 0)
    (hthird : 2520 * m₄ - 420 * m₂ = 0) :
    m₂ = 1 / 10 ∧ m₄ = 1 / 60 := by
  constructor <;> linarith

theorem d002089 (m₂ m₄ : ℝ)
    (hfirst : 10 * m₂ - 1 = 0)
    (hmixed : 70 * m₄ - (45 / 2) * m₂ + 5 / 4 = 0) :
    m₄ = 1 / 70 := by
  linarith

theorem d002090 {α : Type*} [MeasurableSpace α]
    (ρ : Measure α) [IsProbabilityMeasure ρ] (x : α → ℝ)
    (hfirst : Integrable (fun a ↦ _root_.GD.N0232.N0720.N1240.d002050 (x a)) ρ)
    (hthird : Integrable (fun a ↦ _root_.GD.N0232.N0720.N1240.d002051 (x a)) ρ)
    (hmixed : Integrable (fun a ↦ _root_.GD.N0232.N0720.N1240.d002052 (x a)) ρ) :
    39 * (∫ a, _root_.GD.N0232.N0720.N1240.d002050 (x a) ∂ρ) - (∫ a, _root_.GD.N0232.N0720.N1240.d002051 (x a) ∂ρ) +
      36 * (∫ a, _root_.GD.N0232.N0720.N1240.d002052 (x a) ∂ρ) = 6 := by
  calc
    _ = ∫ a, 39 * _root_.GD.N0232.N0720.N1240.d002050 (x a) - _root_.GD.N0232.N0720.N1240.d002051 (x a) +
        36 * _root_.GD.N0232.N0720.N1240.d002052 (x a) ∂ρ := by
      have hs := integral_sub (hfirst.const_mul 39) hthird
      have ha := integral_add ((hfirst.const_mul 39).sub hthird) (hmixed.const_mul 36)
      simp only [Pi.sub_apply, integral_const_mul] at hs ha
      rw [ha, hs]
    _ = ∫ _ : α, (6 : ℝ) ∂ρ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun a ↦ _root_.GD.N0232.N0720.N1240.d002086 (x a)
    _ = 6 := by simp

theorem d002091 {α : Type*} [MeasurableSpace α]
    (ρ : Measure α) [IsProbabilityMeasure ρ] (x : α → ℝ)
    (hfirst : Integrable (fun a ↦ _root_.GD.N0232.N0720.N1240.d002050 (x a)) ρ)
    (hthird : Integrable (fun a ↦ _root_.GD.N0232.N0720.N1240.d002051 (x a)) ρ)
    (hmixed : Integrable (fun a ↦ _root_.GD.N0232.N0720.N1240.d002052 (x a)) ρ) :
    ¬ ((∫ a, _root_.GD.N0232.N0720.N1240.d002050 (x a) ∂ρ) = 0 ∧
      (∫ a, _root_.GD.N0232.N0720.N1240.d002051 (x a) ∂ρ) = 0 ∧
      (∫ a, _root_.GD.N0232.N0720.N1240.d002052 (x a) ∂ρ) = 0) := by
  intro h
  have hid := _root_.GD.N0232.N0720.N1240.d002090 ρ x hfirst hthird hmixed
  rw [h.1, h.2.1, h.2.2] at hid
  norm_num at hid

theorem d002092 {α : Type*} [MeasurableSpace α]
    (ρ : Measure α) [IsProbabilityMeasure ρ] (x : α → ℝ)
    (hfirst : Integrable (fun a ↦ _root_.GD.N0232.N0720.N1240.d002050 (x a)) ρ)
    (hthird : Integrable (fun a ↦ _root_.GD.N0232.N0720.N1240.d002051 (x a)) ρ)
    (hmixed : Integrable (fun a ↦ _root_.GD.N0232.N0720.N1240.d002052 (x a)) ρ) :
    (3 / 38 : ℝ) ≤ |∫ a, _root_.GD.N0232.N0720.N1240.d002050 (x a) ∂ρ| ∨
      (3 / 38 : ℝ) ≤ |∫ a, _root_.GD.N0232.N0720.N1240.d002051 (x a) ∂ρ| ∨
      (3 / 38 : ℝ) ≤ |∫ a, _root_.GD.N0232.N0720.N1240.d002052 (x a) ∂ρ| := by
  have hid := _root_.GD.N0232.N0720.N1240.d002090 ρ x hfirst hthird hmixed
  by_contra h
  push Not at h
  have h₁ := (abs_lt.mp h.1).2
  have h₃ := (abs_lt.mp h.2.1).1
  have hₘ := (abs_lt.mp h.2.2).2
  linarith



theorem d002093
    (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) [IsProbabilityMeasure ρ] :
    ¬ (∀ y ∈ Ioo (-1 / 4 : ℝ) (1 / 4),
      ∀ v ∈ Icc (0 : ℝ) (1 / 8), ∫ x, _root_.GD.N0232.N0720.N1240.d002054 x y v ∂ρ = 0) := by
  intro hz
  have hy₀ : (0 : ℝ) ∈ Ioo (-1 / 4 : ℝ) (1 / 4) := by norm_num
  have hv₀ : (0 : ℝ) ∈ Icc (0 : ℝ) (1 / 8) := by norm_num
  have hc₀ : (0 : ℝ) ∈ Icc (-1 / 4 : ℝ) (1 / 4) := by norm_num
  have hfirst : ∀ v ∈ Icc (0 : ℝ) (1 / 8),
      ∀ y ∈ Ioo (-1 / 4 : ℝ) (1 / 4),
      (∫ x, _root_.GD.N0232.N0720.N1240.d002055 x y v ∂ρ) = 0 := by
    intro v hv y hy
    have hvc : v ∈ Icc (-1 / 4 : ℝ) (1 / 4) := by constructor <;> linarith [hv.1, hv.2]
    apply (_root_.GD.N0232.N0720.N1240.d002078 ρ hy hvc).unique
    apply (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hy] with q hq
    exact hz q hq v hv
  have hsecond : ∀ y ∈ Ioo (-1 / 4 : ℝ) (1 / 4),
      (∫ x, _root_.GD.N0232.N0720.N1240.d002056 x y 0 ∂ρ) = 0 := by
    intro y hy
    apply (_root_.GD.N0232.N0720.N1240.d002079 ρ hy hc₀).unique
    apply (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hy] with q hq
    exact hfirst 0 hv₀ q hq
  have hthird : (∫ x, _root_.GD.N0232.N0720.N1240.d002057 x 0 0 ∂ρ) = 0 := by
    apply (_root_.GD.N0232.N0720.N1240.d002080 ρ hy₀ hc₀).unique
    apply (hasDerivAt_const 0 (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hy₀] with q hq
    exact hsecond q hq
  have hmixed : (∫ x, _root_.GD.N0232.N0720.N1240.d002058 x 0 0 ∂ρ) = 0 := by
    have hu : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) (1 / 8)) 0 :=
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1 / 8)) 0 hv₀
    have hd₀ : HasDerivWithinAt
        (fun v ↦ ∫ x, _root_.GD.N0232.N0720.N1240.d002055 x 0 v ∂ρ) 0
        (Icc (0 : ℝ) (1 / 8)) 0 := by
      apply (hasDerivAt_const 0 (0 : ℝ)).hasDerivWithinAt.congr
      · intro v hv
        exact hfirst v hv 0 hy₀
      · exact hfirst 0 hv₀ 0 hy₀
    exact ((_root_.GD.N0232.N0720.N1240.d002084 ρ hc₀ hy₀).hasDerivWithinAt.derivWithin hu).symm.trans
      (hd₀.derivWithin hu)
  have hi : ∀ f : ℝ → ℝ, Continuous f → Integrable (fun x : _root_.GD.N0232.N0720.N1240.d002070 ↦ f x) ρ := by
    intro f hf
    simpa [Function.comp_def] using (hf.comp continuous_subtype_val).continuousOn.integrableOn_compact
      (isCompact_univ : IsCompact (univ : Set _root_.GD.N0232.N0720.N1240.d002070)) (μ := ρ)
  apply _root_.GD.N0232.N0720.N1240.d002091 ρ (fun x : _root_.GD.N0232.N0720.N1240.d002070 ↦ (x : ℝ))
    (hi _root_.GD.N0232.N0720.N1240.d002050 (by unfold _root_.GD.N0232.N0720.N1240.d002050; fun_prop))
    (hi _root_.GD.N0232.N0720.N1240.d002051 (by unfold _root_.GD.N0232.N0720.N1240.d002051; fun_prop))
    (hi _root_.GD.N0232.N0720.N1240.d002052 (by unfold _root_.GD.N0232.N0720.N1240.d002052; fun_prop))
  constructor
  · simpa only [_root_.GD.N0232.N0720.N1240.d002067] using hfirst 0 hv₀ 0 hy₀
  constructor
  · simpa only [_root_.GD.N0232.N0720.N1240.d002068] using hthird
  · simpa only [_root_.GD.N0232.N0720.N1240.d002069] using hmixed



theorem d002094
    (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) [IsProbabilityMeasure ρ] :
    ¬ (∀ y ∈ Ioo (-1 / 4 : ℝ) (1 / 4),
      ∀ v ∈ Ioo (0 : ℝ) (1 / 4), ∫ x, _root_.GD.N0232.N0720.N1240.d002054 x y v ∂ρ = 0) := by
  intro hz
  apply _root_.GD.N0232.N0720.N1240.d002093 ρ
  intro y hy v hv
  by_cases hv₀ : v = 0
  · subst v
    have hc := (_root_.GD.N0232.N0720.N1240.d002085 ρ ⟨hy.1.le, hy.2.le⟩
      (by norm_num : (0 : ℝ) ∈ Ioo (-1 / 4 : ℝ) (1 / 4))).continuousAt
    have he : (fun v ↦ ∫ x, _root_.GD.N0232.N0720.N1240.d002054 x y v ∂ρ) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun _ ↦ (0 : ℝ)) := by
      have hlo : ∀ᶠ v in 𝓝[>] (0 : ℝ), 0 < v := self_mem_nhdsWithin
      have hhi : ∀ᶠ v in 𝓝[>] (0 : ℝ), v < 1 / 4 :=
        Filter.Eventually.filter_mono inf_le_left
          (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
      filter_upwards [hlo, hhi] with v hlo hhi
      exact hz y hy v ⟨hlo, hhi⟩
    haveI : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot (le_refl (0 : ℝ))
    exact tendsto_nhds_unique (hc.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left))
      (tendsto_const_nhds.congr' he.symm)
  · exact hz y hy v ⟨lt_of_le_of_ne hv.1 (Ne.symm hv₀), by linarith [hv.2]⟩



def d002095 (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) (u v : ℝ) : ℝ :=
  (∫ x, ((x : ℝ) + 1 / 2) *
      Real.rpow (_root_.GD.N0232.N0720.N1240.d002053 x (u - 1 / 2) v) (-5 / 2) ∂ρ) /
    (∫ x, Real.rpow (_root_.GD.N0232.N0720.N1240.d002053 x (u - 1 / 2) v) (-5 / 2) ∂ρ)

theorem d002096 (t u v : ℝ) :
    _root_.GD.N0232.N0720.N1240.d002053 (t - 1 / 2) (u - 1 / 2) v =
      2 * (t * (1 - t) * v + t * (1 - u) + (1 - t) * u) := by
  unfold _root_.GD.N0232.N0720.N1240.d002053
  ring

theorem d002097
    (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) [IsFiniteMeasure ρ] {y v : ℝ}
    (hy : y ∈ Ioo (-1 / 4 : ℝ) (1 / 4))
    (hv : v ∈ Icc (-1 / 4 : ℝ) (1 / 4))
    (heq : _root_.GD.N0232.N0720.N1240.d002095 ρ (y + 1 / 2) v = y + 1 / 2) :
    (∫ x, _root_.GD.N0232.N0720.N1240.d002054 x y v ∂ρ) = 0 := by
  let w : _root_.GD.N0232.N0720.N1240.d002070 → ℝ := fun x ↦ Real.rpow (_root_.GD.N0232.N0720.N1240.d002053 x y v) (-5 / 2)
  have hw : Continuous w := by
    apply (show Continuous (fun x : _root_.GD.N0232.N0720.N1240.d002070 ↦ _root_.GD.N0232.N0720.N1240.d002053 x y v)
      from by unfold _root_.GD.N0232.N0720.N1240.d002053; fun_prop).rpow_const
    intro x
    left
    have h := _root_.GD.N0232.N0720.N1240.d002071 x.property ⟨hy.1.le, hy.2.le⟩ hv
    linarith
  have hwi : Integrable w ρ := by
    simpa using hw.continuousOn.integrableOn_compact
      (isCompact_univ : IsCompact (univ : Set _root_.GD.N0232.N0720.N1240.d002070)) (μ := ρ)
  have hni : Integrable (fun x : _root_.GD.N0232.N0720.N1240.d002070 ↦ ((x : ℝ) + 1 / 2) * w x) ρ := by
    have hn : Continuous (fun x : _root_.GD.N0232.N0720.N1240.d002070 ↦ ((x : ℝ) + 1 / 2) * w x) :=
      (continuous_subtype_val.add continuous_const).mul hw
    simpa using hn.continuousOn.integrableOn_compact
      (isCompact_univ : IsCompact (univ : Set _root_.GD.N0232.N0720.N1240.d002070)) (μ := ρ)
  have heq' : (∫ x, ((x : ℝ) + 1 / 2) * w x ∂ρ) / (∫ x, w x ∂ρ) = y + 1 / 2 := by
    simpa [_root_.GD.N0232.N0720.N1240.d002095, w] using heq
  have hd : (∫ x, w x ∂ρ) ≠ 0 := by
    intro hd
    rw [hd, div_zero] at heq'
    linarith [hy.1]
  have hm := (div_eq_iff hd).mp heq'
  calc
    (∫ x, _root_.GD.N0232.N0720.N1240.d002054 x y v ∂ρ) =
        ∫ x, ((x : ℝ) + 1 / 2) * w x - (y + 1 / 2) * w x ∂ρ := by
      apply integral_congr_ae
      exact ae_of_all ρ fun x ↦ by unfold _root_.GD.N0232.N0720.N1240.d002054; dsimp [w]; ring
    _ = (∫ x, ((x : ℝ) + 1 / 2) * w x ∂ρ) -
        (y + 1 / 2) * (∫ x, w x ∂ρ) := by
      simpa only [Pi.sub_apply, integral_const_mul] using
        integral_sub hni (hwi.const_mul (y + 1 / 2))
    _ = 0 := sub_eq_zero.mpr hm



theorem d002098
    (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) [IsProbabilityMeasure ρ] :
    ¬ (∀ u ∈ Ioo (1 / 4 : ℝ) (3 / 4),
      ∀ v ∈ Ioo (0 : ℝ) (1 / 4), _root_.GD.N0232.N0720.N1240.d002095 ρ u v = u) := by
  intro h
  apply _root_.GD.N0232.N0720.N1240.d002094 ρ
  intro y hy v hv
  apply _root_.GD.N0232.N0720.N1240.d002097 ρ hy
    (show v ∈ Icc (-1 / 4 : ℝ) (1 / 4) from ⟨by linarith [hv.1], hv.2.le⟩)
  exact h (y + 1 / 2) (by constructor <;> linarith [hy.1, hy.2]) v hv

def d002099 (t u v : ℝ) : ℝ :=
  t * (1 - t) * v + t * (1 - u) + (1 - t) * u


def d002100 (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) (u v : ℝ) : ℝ :=
  (∫ x, ((x : ℝ) + 1 / 2) *
      Real.rpow (_root_.GD.N0232.N0720.N1240.d002099 (x + 1 / 2) u v) (-5 / 2) ∂ρ) /
    (∫ x, Real.rpow (_root_.GD.N0232.N0720.N1240.d002099 (x + 1 / 2) u v) (-5 / 2) ∂ρ)

theorem d002101
    (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) {u v : ℝ}
    (hu : u ∈ Icc (1 / 4 : ℝ) (3 / 4))
    (hv : v ∈ Icc (-1 / 4 : ℝ) (1 / 4)) :
    _root_.GD.N0232.N0720.N1240.d002095 ρ u v = _root_.GD.N0232.N0720.N1240.d002100 ρ u v := by
  let c : ℝ := Real.rpow 2 (-5 / 2)
  have hc : c ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hw (x : _root_.GD.N0232.N0720.N1240.d002070) :
      Real.rpow (_root_.GD.N0232.N0720.N1240.d002053 x (u - 1 / 2) v) (-5 / 2) =
        c * Real.rpow (_root_.GD.N0232.N0720.N1240.d002099 (x + 1 / 2) u v) (-5 / 2) := by
    have hb : _root_.GD.N0232.N0720.N1240.d002053 x (u - 1 / 2) v =
        2 * _root_.GD.N0232.N0720.N1240.d002099 (x + 1 / 2) u v := by
      unfold _root_.GD.N0232.N0720.N1240.d002053 _root_.GD.N0232.N0720.N1240.d002099
      ring
    have hq : 0 ≤ _root_.GD.N0232.N0720.N1240.d002099 (x + 1 / 2) u v := by
      have h := _root_.GD.N0232.N0720.N1240.d002071 x.property
        (show u - 1 / 2 ∈ Icc (-1 / 4 : ℝ) (1 / 4) from
          ⟨by linarith [hu.1], by linarith [hu.2]⟩) hv
      rw [hb] at h
      linarith
    rw [hb]
    exact Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hq
  have hn : (∫ x, ((x : ℝ) + 1 / 2) *
      Real.rpow (_root_.GD.N0232.N0720.N1240.d002053 x (u - 1 / 2) v) (-5 / 2) ∂ρ) =
      c * (∫ x, ((x : ℝ) + 1 / 2) *
        Real.rpow (_root_.GD.N0232.N0720.N1240.d002099 (x + 1 / 2) u v) (-5 / 2) ∂ρ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all ρ fun x ↦ by dsimp only; rw [hw x]; ring
  have hd : (∫ x, Real.rpow (_root_.GD.N0232.N0720.N1240.d002053 x (u - 1 / 2) v) (-5 / 2) ∂ρ) =
      c * (∫ x, Real.rpow (_root_.GD.N0232.N0720.N1240.d002099 (x + 1 / 2) u v) (-5 / 2) ∂ρ) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all ρ hw)
  unfold _root_.GD.N0232.N0720.N1240.d002095 _root_.GD.N0232.N0720.N1240.d002100
  rw [hn, hd, mul_div_mul_left _ _ hc]

theorem d002102
    (ρ : Measure _root_.GD.N0232.N0720.N1240.d002070) [IsProbabilityMeasure ρ] :
    ¬ (∀ u ∈ Ioo (1 / 4 : ℝ) (3 / 4),
      ∀ v ∈ Ioo (0 : ℝ) (1 / 4), _root_.GD.N0232.N0720.N1240.d002100 ρ u v = u) := by
  intro h
  apply _root_.GD.N0232.N0720.N1240.d002098 ρ
  intro u hu v hv
  rw [_root_.GD.N0232.N0720.N1240.d002101 ρ ⟨hu.1.le, hu.2.le⟩
    ⟨by linarith [hv.1], hv.2.le⟩]
  exact h u hu v hv

end

end GD.N0232.N0720.N1240

#print axioms _root_.GD.N0232.N0720.N1240.d002086
#print axioms _root_.GD.N0232.N0720.N1240.d002087
#print axioms _root_.GD.N0232.N0720.N1240.d002090
#print axioms _root_.GD.N0232.N0720.N1240.d002091
#print axioms _root_.GD.N0232.N0720.N1240.d002092
#print axioms _root_.GD.N0232.N0720.N1240.d002072
#print axioms _root_.GD.N0232.N0720.N1240.d002080
#print axioms _root_.GD.N0232.N0720.N1240.d002084
#print axioms _root_.GD.N0232.N0720.N1240.d002093
#print axioms _root_.GD.N0232.N0720.N1240.d002094
#print axioms _root_.GD.N0232.N0720.N1240.d002098
#print axioms _root_.GD.N0232.N0720.N1240.d002102
