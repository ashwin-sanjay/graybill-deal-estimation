import GD.Module0531
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology

namespace GD.N0101.N0362
noncomputable section
open _root_.GD.N0208.N0455

abbrev d007943 := Fin 2 → ℝ

def d007944 : Set _root_.GD.N0101.N0362.d007943 := {β | ∀ i, 0 < β i}

def d007945 (β : _root_.GD.N0101.N0362.d007943) : ℝ := (Real.log (β 0) + Real.log (β 1)) / 2

def d007946 (β : _root_.GD.N0101.N0362.d007943) : ℝ := (Real.log (β 0) - Real.log (β 1)) / 2

def d007947 (N : ℝ) (β : _root_.GD.N0101.N0362.d007943) : ℝ := by
  classical
  exact if β ∈ _root_.GD.N0101.N0362.d007944 then _root_.GD.N0208.N0455.d007937 N (_root_.GD.N0101.N0362.d007945 β) * _root_.GD.N0208.N0455.d007937 N (_root_.GD.N0101.N0362.d007946 β) else 0

theorem d007948 : MeasurableSet _root_.GD.N0101.N0362.d007944 := by
  simp only [_root_.GD.N0101.N0362.d007944, setOf_forall]
  exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)

@[fun_prop] theorem d007949 (N : ℝ) :
    Measurable (_root_.GD.N0101.N0362.d007947 N) := by
  unfold _root_.GD.N0101.N0362.d007947
  apply Measurable.ite _root_.GD.N0101.N0362.d007948 _ measurable_const
  apply Measurable.mul
  · exact (_root_.GD.N0208.N0455.d007938 N).comp (by unfold _root_.GD.N0101.N0362.d007945; fun_prop)
  · exact (_root_.GD.N0208.N0455.d007938 N).comp (by unfold _root_.GD.N0101.N0362.d007946; fun_prop)

theorem d007950 (N : ℝ) (β : _root_.GD.N0101.N0362.d007943) :
    _root_.GD.N0101.N0362.d007947 N β ∈ Icc (0 : ℝ) 1 := by
  have hb (x : ℝ) : _root_.GD.N0208.N0455.d007937 N x ∈ Icc (0 : ℝ) 1 := by
    exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩
  unfold _root_.GD.N0101.N0362.d007947
  split_ifs
  · exact ⟨mul_nonneg (hb _).1 (hb _).1,
      (mul_le_mul (hb _).2 (hb _).2 (hb _).1 (by norm_num)).trans_eq (one_mul _)⟩
  · exact ⟨le_rfl, zero_le_one⟩

theorem d007951 {β : _root_.GD.N0101.N0362.d007943} (hβ : β ∈ _root_.GD.N0101.N0362.d007944) :
    _root_.GD.N0101.N0362.d007945 β = Real.log (β 0 * β 1) / 2 := by
  rw [Real.log_mul (hβ 0).ne' (hβ 1).ne']
  rfl

theorem d007952 {β : _root_.GD.N0101.N0362.d007943} (hβ : β ∈ _root_.GD.N0101.N0362.d007944) :
    _root_.GD.N0101.N0362.d007946 β = Real.log (β 0 / β 1) / 2 := by
  rw [Real.log_div (hβ 0).ne' (hβ 1).ne']
  rfl

theorem d007953 (β : _root_.GD.N0101.N0362.d007943) :
    Real.log (β 0) = _root_.GD.N0101.N0362.d007945 β + _root_.GD.N0101.N0362.d007946 β ∧
      Real.log (β 1) = _root_.GD.N0101.N0362.d007945 β - _root_.GD.N0101.N0362.d007946 β := by
  unfold _root_.GD.N0101.N0362.d007945 _root_.GD.N0101.N0362.d007946
  constructor <;> ring

theorem d007954 {N M : ℝ} (hN : 0 < N) (hNM : N ≤ M) (x : ℝ) :
    _root_.GD.N0208.N0455.d007937 N x ≤ _root_.GD.N0208.N0455.d007937 M x := by
  have hd := div_le_div_of_nonneg_left (abs_nonneg x) hN hNM
  unfold _root_.GD.N0208.N0455.d007937
  exact min_le_min le_rfl (max_le_max le_rfl (by linarith))

theorem d007955 {N M : ℝ} (hN : 0 < N) (hNM : N ≤ M) (β : _root_.GD.N0101.N0362.d007943) :
    _root_.GD.N0101.N0362.d007947 N β ≤ _root_.GD.N0101.N0362.d007947 M β := by
  unfold _root_.GD.N0101.N0362.d007947
  split_ifs
  · exact mul_le_mul (_root_.GD.N0101.N0362.d007954 hN hNM _) (_root_.GD.N0101.N0362.d007954 hN hNM _)
      ((_root_.GD.N0208.N0455.d007939 hN).1 _).1 ((_root_.GD.N0208.N0455.d007939 (hN.trans_le hNM)).1 _).1
  · exact le_rfl



theorem d007956 {N : ℝ} (hN : 0 < N) {β : _root_.GD.N0101.N0362.d007943}
    (hc : _root_.GD.N0101.N0362.d007947 N β ≠ 0) :
    β ∈ Icc (fun _ => Real.exp (-4 * N)) (fun _ => Real.exp (4 * N)) := by
  have hβ : β ∈ _root_.GD.N0101.N0362.d007944 := by
    by_contra hn
    exact hc (by simp [_root_.GD.N0101.N0362.d007947, hn])
  have hp : _root_.GD.N0208.N0455.d007937 N (_root_.GD.N0101.N0362.d007945 β) ≠ 0 := by
    intro hz
    exact hc (by simp [_root_.GD.N0101.N0362.d007947, hβ, hz])
  have hv : _root_.GD.N0208.N0455.d007937 N (_root_.GD.N0101.N0362.d007946 β) ≠ 0 := by
    intro hz
    exact hc (by simp [_root_.GD.N0101.N0362.d007947, hβ, hz])
  have hpabs : |_root_.GD.N0101.N0362.d007945 β| < 2 * N := by
    by_contra hn
    exact hp ((_root_.GD.N0208.N0455.d007939 hN).2.2.2 _ (le_of_not_gt hn))
  have hvabs : |_root_.GD.N0101.N0362.d007946 β| < 2 * N := by
    by_contra hn
    exact hv ((_root_.GD.N0208.N0455.d007939 hN).2.2.2 _ (le_of_not_gt hn))
  have hlogs : ∀ i, -4 * N ≤ Real.log (β i) ∧ Real.log (β i) ≤ 4 * N := by
    intro i
    have hs := abs_lt.mp hpabs
    have ht := abs_lt.mp hvabs
    have hl := _root_.GD.N0101.N0362.d007953 β
    fin_cases i
    · change -4 * N ≤ Real.log (β 0) ∧ Real.log (β 0) ≤ 4 * N
      constructor <;> linarith [hl.1]
    · change -4 * N ≤ Real.log (β 1) ∧ Real.log (β 1) ≤ 4 * N
      constructor <;> linarith [hl.2]
  constructor
  · intro i
    exact (Real.exp_le_exp.mpr (hlogs i).1).trans_eq (Real.exp_log (hβ i))
  · intro i
    exact (Real.exp_log (hβ i)).symm.trans_le (Real.exp_le_exp.mpr (hlogs i).2)

theorem d007957 {N : ℝ} (hN : 0 < N) (β : _root_.GD.N0101.N0362.d007943)
    (hβ : β ∉ Icc (fun _ => Real.exp (-4 * N)) (fun _ => Real.exp (4 * N))) :
    _root_.GD.N0101.N0362.d007947 N β = 0 := by
  by_contra hn
  exact hβ (_root_.GD.N0101.N0362.d007956 hN hn)

theorem d007958 {N : ℝ} (hN : 0 < N) {β : _root_.GD.N0101.N0362.d007943}
    (hβ : β ∈ _root_.GD.N0101.N0362.d007944) (hp : |_root_.GD.N0101.N0362.d007945 β| ≤ N) (hv : |_root_.GD.N0101.N0362.d007946 β| ≤ N) :
    _root_.GD.N0101.N0362.d007947 N β = 1 := by
  simp only [_root_.GD.N0101.N0362.d007947, if_pos hβ,
    (_root_.GD.N0208.N0455.d007939 hN).2.2.1 _ hp, (_root_.GD.N0208.N0455.d007939 hN).2.2.1 _ hv, one_mul]

theorem d007959 {β : _root_.GD.N0101.N0362.d007943} (hβ : β ∈ _root_.GD.N0101.N0362.d007944) :
    ∀ᶠ N : ℝ in atTop, _root_.GD.N0101.N0362.d007947 N β = 1 := by
  filter_upwards [eventually_ge_atTop (max 1 (max |_root_.GD.N0101.N0362.d007945 β| |_root_.GD.N0101.N0362.d007946 β|))] with N hN
  have h1 : 1 ≤ N := (le_max_left _ _).trans hN
  apply _root_.GD.N0101.N0362.d007958 (by linarith) hβ
  · exact ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  · exact ((le_max_right _ _).trans (le_max_right _ _)).trans hN

def d007960 : Set _root_.GD.N0101.N0362.d007943 := {β | β ∈ _root_.GD.N0101.N0362.d007944 ∧ |_root_.GD.N0101.N0362.d007945 β| ≤ 1 ∧ |_root_.GD.N0101.N0362.d007946 β| ≤ 1}

theorem d007961 {N : ℝ} (hN : 1 ≤ N) {β : _root_.GD.N0101.N0362.d007943}
    (hβ : β ∈ _root_.GD.N0101.N0362.d007960) : _root_.GD.N0101.N0362.d007947 N β = 1 :=
  _root_.GD.N0101.N0362.d007958 (by linarith) hβ.1 (hβ.2.1.trans hN) (hβ.2.2.trans hN)

end
end GD.N0101.N0362

#print axioms _root_.GD.N0101.N0362.d007949
#print axioms _root_.GD.N0101.N0362.d007950
#print axioms _root_.GD.N0101.N0362.d007951
#print axioms _root_.GD.N0101.N0362.d007952
#print axioms _root_.GD.N0101.N0362.d007955
#print axioms _root_.GD.N0101.N0362.d007957
#print axioms _root_.GD.N0101.N0362.d007959
#print axioms _root_.GD.N0101.N0362.d007961
