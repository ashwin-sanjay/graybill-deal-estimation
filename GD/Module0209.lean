import GD.Module0206
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Prod






open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace GD.N0232.N0720.N1379

open _root_.GD.N0232.N0720.N1377

noncomputable section

abbrev d002878 := ℝ × ℝ

def d002879 : _root_.GD.N0232.N0720.N1379.d002878 →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
def d002880 : _root_.GD.N0232.N0720.N1379.d002878 →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ

def d002881 (n : ℕ) (p : _root_.GD.N0232.N0720.N1379.d002878) (r : ℝ) : _root_.GD.N0232.N0720.N1379.d002878 →L[ℝ] ℝ :=
  (-(1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1377.d002851 (n + 2) p.1 p.2 r) • _root_.GD.N0232.N0720.N1379.d002879 +
    _root_.GD.N0232.N0720.N1377.d002851 (n + 1) p.1 p.2 r • _root_.GD.N0232.N0720.N1379.d002880

def d002882 (n : ℕ) (p : _root_.GD.N0232.N0720.N1379.d002878) : _root_.GD.N0232.N0720.N1379.d002878 →L[ℝ] ℝ :=
  (-(1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1377.d002852 (n + 2) p.1 p.2) • _root_.GD.N0232.N0720.N1379.d002879 +
    _root_.GD.N0232.N0720.N1377.d002852 (n + 1) p.1 p.2 • _root_.GD.N0232.N0720.N1379.d002880

theorem d002883 (n : ℕ) (p v : _root_.GD.N0232.N0720.N1379.d002878) :
    _root_.GD.N0232.N0720.N1379.d002882 n p v = -(1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1377.d002852 (n + 2) p.1 p.2 * v.1 +
      _root_.GD.N0232.N0720.N1377.d002852 (n + 1) p.1 p.2 * v.2 := by
  simp [_root_.GD.N0232.N0720.N1379.d002882, _root_.GD.N0232.N0720.N1379.d002879, _root_.GD.N0232.N0720.N1379.d002880, smul_eq_mul]

theorem d002884 (n : ℕ) (p : _root_.GD.N0232.N0720.N1379.d002878) (r : ℝ) :
    HasFDerivAt (fun q : _root_.GD.N0232.N0720.N1379.d002878 ↦ _root_.GD.N0232.N0720.N1377.d002851 n q.1 q.2 r) (_root_.GD.N0232.N0720.N1379.d002881 n p r) p := by
  have he : HasFDerivAt
      (fun q : _root_.GD.N0232.N0720.N1379.d002878 ↦ -q.1 / 2 * r ^ 2 + q.2 * r)
      ((-r ^ 2 / 2) • _root_.GD.N0232.N0720.N1379.d002879 + r • _root_.GD.N0232.N0720.N1379.d002880) p := by
    let L : _root_.GD.N0232.N0720.N1379.d002878 →L[ℝ] ℝ :=
      (-r ^ 2 / 2) • _root_.GD.N0232.N0720.N1379.d002879 + r • _root_.GD.N0232.N0720.N1379.d002880
    convert! L.hasFDerivAt (x := p) using 1
    funext q
    simp [L, _root_.GD.N0232.N0720.N1379.d002879, _root_.GD.N0232.N0720.N1379.d002880, smul_eq_mul] <;> ring
  apply (he.exp.const_mul (r ^ n)).congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp [_root_.GD.N0232.N0720.N1379.d002881, _root_.GD.N0232.N0720.N1377.d002851, _root_.GD.N0232.N0720.N1379.d002879, _root_.GD.N0232.N0720.N1379.d002880,
    pow_add, smul_eq_mul]
  ring

theorem d002885 (n : ℕ) (p : _root_.GD.N0232.N0720.N1379.d002878) :
    Continuous (_root_.GD.N0232.N0720.N1379.d002881 n p) := by
  unfold _root_.GD.N0232.N0720.N1379.d002881
  exact (((_root_.GD.N0232.N0720.N1377.d002853 (n + 2) p.1 p.2).const_mul _).smul continuous_const).add
    ((_root_.GD.N0232.N0720.N1377.d002853 (n + 1) p.1 p.2).smul continuous_const)

theorem d002886 (n : ℕ) {a A b M r : ℝ}
    (hA : 0 < A) (ha : A ≤ a) (hb : b ≤ M) (hr : 0 ≤ r) :
    ‖_root_.GD.N0232.N0720.N1377.d002851 n a b r‖ ≤ _root_.GD.N0232.N0720.N1377.d002857 n A M r := by
  have hle : _root_.GD.N0232.N0720.N1377.d002851 n a b r ≤ _root_.GD.N0232.N0720.N1377.d002851 n A M r := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr _)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg r),
      mul_nonneg (sub_nonneg.mpr hb) hr]
  rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0232.N0720.N1377.d002854 n a b hr)]
  have hmajor := _root_.GD.N0232.N0720.N1377.d002859 n hA M hr
  rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0232.N0720.N1377.d002854 n A M hr)] at hmajor
  exact hle.trans hmajor

theorem d002887 (n : ℕ) (p : _root_.GD.N0232.N0720.N1379.d002878) (r : ℝ) :
    ‖_root_.GD.N0232.N0720.N1379.d002881 n p r‖ ≤ (1 / 2 : ℝ) * ‖_root_.GD.N0232.N0720.N1377.d002851 (n + 2) p.1 p.2 r‖ +
      ‖_root_.GD.N0232.N0720.N1377.d002851 (n + 1) p.1 p.2 r‖ := by
  calc
    ‖_root_.GD.N0232.N0720.N1379.d002881 n p r‖ ≤
        ‖(-(1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1377.d002851 (n + 2) p.1 p.2 r) • _root_.GD.N0232.N0720.N1379.d002879‖ +
          ‖_root_.GD.N0232.N0720.N1377.d002851 (n + 1) p.1 p.2 r • _root_.GD.N0232.N0720.N1379.d002880‖ := norm_add_le _ _
    _ = _ := by
      simp [norm_smul, norm_mul, _root_.GD.N0232.N0720.N1379.d002879, _root_.GD.N0232.N0720.N1379.d002880]

theorem d002888 (n : ℕ) {p : _root_.GD.N0232.N0720.N1379.d002878} (hp : 0 < p.1) :
    (∫ r in Ioi 0, _root_.GD.N0232.N0720.N1379.d002881 n p r) = _root_.GD.N0232.N0720.N1379.d002882 n p := by
  unfold _root_.GD.N0232.N0720.N1379.d002881 _root_.GD.N0232.N0720.N1379.d002882
  rw [integral_add
    (((_root_.GD.N0232.N0720.N1377.d002860 (n + 2) hp p.2).const_mul _).smul_const _)
    ((_root_.GD.N0232.N0720.N1377.d002860 (n + 1) hp p.2).smul_const _)]
  rw [integral_smul_const, integral_smul_const, integral_const_mul]
  rfl

set_option maxHeartbeats 800000 in

theorem d002889 (n : ℕ) {p : _root_.GD.N0232.N0720.N1379.d002878} (hp : 0 < p.1) :
    HasFDerivAt (fun q : _root_.GD.N0232.N0720.N1379.d002878 ↦ _root_.GD.N0232.N0720.N1377.d002852 n q.1 q.2) (_root_.GD.N0232.N0720.N1379.d002882 n p) p := by
  let M : ℝ := |p.2| + 1
  let s : Set _root_.GD.N0232.N0720.N1379.d002878 := {q | p.1 / 2 < q.1} ∩ {q | q.2 < M}
  have hs : s ∈ 𝓝 p := by
    apply ((isOpen_lt continuous_const continuous_fst).inter
      (isOpen_lt continuous_snd continuous_const)).mem_nhds
    exact ⟨by dsimp; linarith, by dsimp [M]; linarith [le_abs_self p.2]⟩
  have hA : 0 < p.1 / 2 := by positivity
  have hbnd : IntegrableOn (fun r ↦
      (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1377.d002857 (n + 2) (p.1 / 2) M r +
        _root_.GD.N0232.N0720.N1377.d002857 (n + 1) (p.1 / 2) M r) (Ioi 0) :=
    ((_root_.GD.N0232.N0720.N1377.d002858 (n + 2) hA M).const_mul _).add
      (_root_.GD.N0232.N0720.N1377.d002858 (n + 1) hA M)
  have hbound : ∀ᵐ r ∂volume.restrict (Ioi 0), ∀ q ∈ s,
      ‖_root_.GD.N0232.N0720.N1379.d002881 n q r‖ ≤ (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1377.d002857 (n + 2) (p.1 / 2) M r +
        _root_.GD.N0232.N0720.N1377.d002857 (n + 1) (p.1 / 2) M r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    intro q hq
    apply (_root_.GD.N0232.N0720.N1379.d002887 n q r).trans
    exact add_le_add
      (mul_le_mul_of_nonneg_left (_root_.GD.N0232.N0720.N1379.d002886 (n + 2) hA hq.1.le hq.2.le hr.le)
        (by norm_num))
      (_root_.GD.N0232.N0720.N1379.d002886 (n + 1) hA hq.1.le hq.2.le hr.le)
  have hmeas : ∀ᶠ q : _root_.GD.N0232.N0720.N1379.d002878 in 𝓝 p,
      AEStronglyMeasurable (fun r : ℝ ↦ _root_.GD.N0232.N0720.N1377.d002851 n q.1 q.2 r)
        (volume.restrict (Ioi 0)) :=
    Eventually.of_forall fun q ↦
      (_root_.GD.N0232.N0720.N1377.d002853 n q.1 q.2).aestronglyMeasurable
  have hint : Integrable (fun r : ℝ ↦ _root_.GD.N0232.N0720.N1377.d002851 n p.1 p.2 r)
      (volume.restrict (Ioi 0)) := _root_.GD.N0232.N0720.N1377.d002860 n hp p.2
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (H := _root_.GD.N0232.N0720.N1379.d002878) (E := ℝ) (α := ℝ)
    (F := fun (q : _root_.GD.N0232.N0720.N1379.d002878) (r : ℝ) ↦ _root_.GD.N0232.N0720.N1377.d002851 n q.1 q.2 r)
    (F' := _root_.GD.N0232.N0720.N1379.d002881 n) (μ := volume.restrict (Ioi 0)) (x₀ := p) (s := s)
    (bound := fun r ↦ (1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1377.d002857 (n + 2) (p.1 / 2) M r +
      _root_.GD.N0232.N0720.N1377.d002857 (n + 1) (p.1 / 2) M r)
    hs hmeas hint (_root_.GD.N0232.N0720.N1379.d002885 n p).aestronglyMeasurable hbound hbnd
    (ae_of_all _ fun r q _ ↦ _root_.GD.N0232.N0720.N1379.d002884 n q r)
  rw [_root_.GD.N0232.N0720.N1379.d002888 n hp] at hd
  exact hd


theorem d002890 (n : ℕ) {A b : ℝ → ℝ} {x A' b' : ℝ}
    (hp : 0 < A x) (hA : HasDerivAt A A' x) (hb : HasDerivAt b b' x) :
    HasDerivAt (fun y ↦ _root_.GD.N0232.N0720.N1377.d002852 n (A y) (b y))
      (-(1 / 2 : ℝ) * _root_.GD.N0232.N0720.N1377.d002852 (n + 2) (A x) (b x) * A' +
        _root_.GD.N0232.N0720.N1377.d002852 (n + 1) (A x) (b x) * b') x := by
  simpa only [Function.comp_def, _root_.GD.N0232.N0720.N1379.d002883] using
    (_root_.GD.N0232.N0720.N1379.d002889 n (p := (A x, b x)) hp).comp_hasDerivAt x (hA.prodMk hb)


theorem d002891 (n : ℕ) :
    ContDiffOn ℝ ∞ (fun p : _root_.GD.N0232.N0720.N1379.d002878 ↦ _root_.GD.N0232.N0720.N1377.d002852 n p.1 p.2) {p | 0 < p.1} := by
  have hopen : IsOpen {p : _root_.GD.N0232.N0720.N1379.d002878 | 0 < p.1} := isOpen_lt continuous_const continuous_fst
  have hall : ∀ k : ℕ, ∀ j : ℕ,
      ContDiffOn ℝ k (fun p : _root_.GD.N0232.N0720.N1379.d002878 ↦ _root_.GD.N0232.N0720.N1377.d002852 j p.1 p.2) {p | 0 < p.1} := by
    intro k
    induction k with
    | zero =>
        intro j
        change ContDiffOn ℝ 0 (fun p : _root_.GD.N0232.N0720.N1379.d002878 ↦ _root_.GD.N0232.N0720.N1377.d002852 j p.1 p.2) {p | 0 < p.1}
        rw [contDiffOn_zero]
        intro p hp
        exact (_root_.GD.N0232.N0720.N1379.d002889 j hp).continuousAt.continuousWithinAt
    | succ k hk =>
        intro j
        rw [Nat.cast_add, Nat.cast_one]
        apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hopen.uniqueDiffOn).2
        refine ⟨by simp, _root_.GD.N0232.N0720.N1379.d002882 j, ?_, ?_⟩
        · exact (((contDiffOn_const (c := -(1 / 2 : ℝ))).mul (hk (j + 2))).smul contDiffOn_const).add
            ((hk (j + 1)).smul contDiffOn_const)
        · intro p hp
          exact (_root_.GD.N0232.N0720.N1379.d002889 j hp).hasFDerivWithinAt
  exact contDiffOn_infty.mpr fun k ↦ hall k n

end

end GD.N0232.N0720.N1379
