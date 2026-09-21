import GD.Module0043
import GD.Module0050

























namespace GD
namespace N0230
namespace N0714

open Filter Topology
open RealInnerProductSpace
open _root_.GD.N0230.N0685
open _root_.GD.N0230.N0646
open _root_.GD.N0230.N0652

set_option linter.unusedSectionVars false

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]







theorem d001263
    {C : Set E} {p x : E} {r : ℕ → E} {ε : ℕ → ℝ}
    (hp : _root_.GD.N0230.N0685.d000511 C 0 p)
    (hprobe : Tendsto (fun n ↦ ⟪r n, x⟫) atTop (nhds (‖x‖ ^ 2)))
    (hx : x ∈ C)
    (hradial : ∀ n, ‖r n‖ ^ 2 ≤ ‖p‖ ^ 2 + ε n)
    (hε : Tendsto ε atTop (nhds 0)) :
    x = p := by
  have hupper : Tendsto (fun n ↦ ‖p‖ ^ 2 + ε n) atTop
      (nhds (‖p‖ ^ 2)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hε
  have hlower : Tendsto (fun n ↦ 2 * ⟪r n, x⟫ - ‖x‖ ^ 2) atTop
      (nhds (‖x‖ ^ 2)) := by
    have hconst : Tendsto (fun _ : ℕ ↦ ‖x‖ ^ 2) atTop
        (nhds (‖x‖ ^ 2)) := tendsto_const_nhds
    have h := (hprobe.const_mul 2).sub hconst
    convert h using 1
    ring_nf
  have hxnorm : ‖x‖ ^ 2 ≤ ‖p‖ ^ 2 := by
    apply le_of_tendsto_of_tendsto' hlower hupper
    intro n
    have hnonneg : 0 ≤ ‖r n - x‖ ^ 2 := sq_nonneg ‖r n - x‖
    rw [norm_sub_sq_real] at hnonneg
    nlinarith [hradial n]
  have htax : ‖x - p‖ ^ 2 + ‖p‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa using _root_.GD.N0230.N0685.d000512 hp hx
  have hzero : ‖x - p‖ = 0 := by
    nlinarith [norm_nonneg (x - p)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)













theorem d001264
    {C : Set E} {p x : E} {r : ℕ → E} {ε : ℕ → ℝ}
    (hp : _root_.GD.N0230.N0685.d000511 C 0 p)
    (hprobe : Tendsto (fun n ↦ ⟪r n, x⟫) atTop (nhds (‖x‖ ^ 2)))
    (hx : x ∈ C)
    (hradial : ∀ n, ‖r n‖ ^ 2 ≤ ‖p‖ ^ 2 + ε n)
    (hε : Tendsto ε atTop (nhds 0)) :
    Tendsto r atTop (nhds p) := by
  have hxp : x = p :=
    _root_.GD.N0230.N0714.d001263
      hp hprobe hx hradial hε
  subst x
  have hmajor : Tendsto
      (fun n ↦ ε n + 2 * (‖p‖ ^ 2 - ⟪r n, p⟫)) atTop
      (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ ↦ ‖p‖ ^ 2) atTop
        (nhds (‖p‖ ^ 2)) := tendsto_const_nhds
    have hgap : Tendsto (fun n ↦ 2 * (‖p‖ ^ 2 - ⟪r n, p⟫)) atTop
        (nhds 0) := by
      simpa only [sub_self, mul_zero] using
        (hconst.sub hprobe).const_mul 2
    simpa only [zero_add] using hε.add hgap
  have hsq : Tendsto (fun n ↦ ‖r n - p‖ ^ 2) atTop (nhds 0) := by
    refine squeeze_zero (fun n ↦ sq_nonneg ‖r n - p‖) ?_ hmajor
    intro n
    rw [norm_sub_sq_real]
    nlinarith [hradial n]
  have hnorm : Tendsto (fun n ↦ ‖r n - p‖) atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm,
      Real.sqrt_zero] using hsqrt
  exact tendsto_iff_norm_sub_tendsto_zero.2 hnorm










theorem d001265
    {C : Set E} {p x : E} {r : ℕ → E} {ε : ℕ → ℝ}
    (hp : _root_.GD.N0230.N0685.d000511 C 0 p)
    (hweak : _root_.GD.N0230.N0646.d000537 r x)
    (hx : x ∈ C)
    (hradial : ∀ n, ‖r n‖ ^ 2 ≤ ‖p‖ ^ 2 + ε n)
    (hε : Tendsto ε atTop (nhds 0)) :
    Tendsto r atTop (nhds p) := by
  apply _root_.GD.N0230.N0714.d001264
    hp _ hx hradial hε
  have hprobe := hweak x
  simpa only [real_inner_self_eq_norm_sq] using hprobe










theorem d001266
    {C : Set E} {p x : E} {r : ℕ → E} {ε : ℕ → ℝ}
    (hp : _root_.GD.N0230.N0685.d000511 C 0 p)
    (hx : x ∈ C)
    (hradial : ∀ n, ‖r n‖ ^ 2 ≤ ‖p‖ ^ 2 + ε n)
    (hε : Tendsto ε atTop (nhds 0)) :
    Tendsto (fun n ↦ ⟪r n, x⟫) atTop (nhds (‖x‖ ^ 2)) ↔
      _root_.GD.N0230.N0646.d000537 r x := by
  constructor
  · intro hprobe
    have hxp : x = p :=
      _root_.GD.N0230.N0714.d001263
        hp hprobe hx hradial hε
    have hstrong : Tendsto r atTop (nhds p) :=
      _root_.GD.N0230.N0714.d001264
        hp hprobe hx hradial hε
    subst x
    exact _root_.GD.N0230.N0646.d000539 hstrong
  · intro hweak
    have hprobe := hweak x
    simpa only [real_inner_self_eq_norm_sq] using hprobe







theorem d001267
    {C : Set E} {p : E} {r : ℕ → E} {ε : ℕ → ℝ}
    (hp : _root_.GD.N0230.N0685.d000511 C 0 p)
    (houter : Tendsto (fun n ↦ Metric.infDist (r n) C) atTop (nhds 0))
    (hradial : ∀ n, ‖r n‖ ^ 2 ≤ ‖p‖ ^ 2 + ε n)
    (hε : Tendsto ε atTop (nhds 0)) :
    Tendsto r atTop (nhds p) := by
  let δ : ℕ → ℝ := fun n ↦ Metric.infDist (r n) C
  let b : ℕ → ℝ := fun n ↦
    δ n + Real.sqrt
      (ε n + 2 * Real.sqrt (‖p‖ ^ 2 + ε n) * δ n + (δ n) ^ 2)
  have hδ : Tendsto δ atTop (nhds 0) := houter
  have hsqrtRadius : Tendsto
      (fun n ↦ Real.sqrt (‖p‖ ^ 2 + ε n)) atTop (nhds ‖p‖) := by
    have hsum : Tendsto (fun n ↦ ‖p‖ ^ 2 + ε n) atTop
        (nhds (‖p‖ ^ 2)) := by
      simpa only [add_zero] using tendsto_const_nhds.add hε
    have hsqrt := (Real.continuous_sqrt.tendsto (‖p‖ ^ 2)).comp hsum
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm] using hsqrt
  have hradicand : Tendsto
      (fun n ↦
        ε n + 2 * Real.sqrt (‖p‖ ^ 2 + ε n) * δ n + (δ n) ^ 2)
      atTop (nhds 0) := by
    have hcross : Tendsto
        (fun n ↦ 2 * Real.sqrt (‖p‖ ^ 2 + ε n) * δ n)
        atTop (nhds 0) := by
      simpa only [mul_zero] using (hsqrtRadius.const_mul 2).mul hδ
    have hsquare : Tendsto (fun n ↦ (δ n) ^ 2) atTop (nhds 0) := by
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hδ.pow 2
    simpa only [zero_add] using (hε.add hcross).add hsquare
  have hb : Tendsto b atTop (nhds 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hradicand
    simpa only [b, Function.comp_def, zero_add, Real.sqrt_zero] using hδ.add hsqrt
  have hbound : ∀ n, ‖r n - p‖ ≤ b n := by
    intro n
    have hquant := _root_.GD.N0230.N0652.d000638
      (C := C) (D := C) (p := p) (q := p) (r := r n)
      (B := ‖p‖) (ε := ε n) (δ := δ n)
      (fun _ hz ↦ hz) hp hp le_rfl Metric.infDist_nonneg le_rfl
      (hradial n)
    simpa only [b, δ, norm_sub_rev] using hquant
  have hnorm : Tendsto (fun n ↦ ‖r n - p‖) atTop (nhds 0) :=
    squeeze_zero (fun n ↦ norm_nonneg (r n - p)) hbound hb
  exact tendsto_iff_norm_sub_tendsto_zero.2 hnorm



theorem d001268
    (T : E → E) {r : ℕ → E} {p : E}
    (hgraph : IsClosed {z : E × E | z.2 = T z.1})
    (hr : Tendsto r atTop (nhds p))
    (hdisplacement : Tendsto (fun n ↦ ‖T (r n) - r n‖) atTop (nhds 0)) :
    T p = p := by
  have hvector : Tendsto (fun n ↦ T (r n) - r n) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 hdisplacement
  have hTr : Tendsto (fun n ↦ T (r n)) atTop (nhds p) := by
    simpa only [sub_add_cancel, zero_add] using hvector.add hr
  have hpgraph : (p, p) ∈ {z : E × E | z.2 = T z.1} := by
    apply hgraph.mem_of_tendsto (hr.prodMk_nhds hTr)
    exact Eventually.of_forall fun n ↦ rfl
  exact hpgraph.symm






theorem d001269
    {C : Set E} {p x : E} {r : ℕ → E} {ε : ℕ → ℝ}
    (hp : _root_.GD.N0230.N0685.d000511 C 0 p)
    (hweak : _root_.GD.N0230.N0646.d000537 r x)
    (hx : x ∈ C)
    (hradial : ∀ n, ‖r n‖ ^ 2 ≤ ‖p‖ ^ 2 + ε n)
    (hε : Tendsto ε atTop (nhds 0))
    (T : E → E)
    (hgraph : IsClosed {z : E × E | z.2 = T z.1})
    (hdisplacement : Tendsto (fun n ↦ ‖T (r n) - r n‖) atTop (nhds 0)) :
    T p = p := by
  exact _root_.GD.N0230.N0714.d001268 T hgraph
    (_root_.GD.N0230.N0714.d001265
      hp hweak hx hradial hε)
    hdisplacement

end N0714
end N0230
end GD

#print axioms _root_.GD.N0230.N0714.d001265
#print axioms _root_.GD.N0230.N0714.d001264
#print axioms _root_.GD.N0230.N0714.d001263
#print axioms _root_.GD.N0230.N0714.d001266
#print axioms _root_.GD.N0230.N0714.d001267
#print axioms _root_.GD.N0230.N0714.d001268
#print axioms _root_.GD.N0230.N0714.d001269
