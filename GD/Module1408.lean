import GD.Module1407
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.LiminfLimsup








set_option autoImplicit false
set_option warningAsError true

open Filter
open scoped Topology

namespace GD.N0195
noncomputable section

open _root_.GD.N0196

def d022611 (N : ℕ) : ℝ := (N : ℝ) * _root_.GD.N0196.d022600 N


def d022612 (N : ℕ) : ℝ :=
  2 * _root_.GD.N0196.d022599 +
    2 / ((1 - 1 / (N : ℝ)) * (1 - (1 / (N : ℝ)) ^ 4)) +
    6 * _root_.GD.N0196.d022599 * (Real.log (N : ℝ) / ((N : ℝ) - 1)) +
    4 * (1 / (N : ℝ)) +
    ((7 * _root_.GD.N0196.d022599 / 2) * (1 / (N : ℝ))) / (1 - (1 / (N : ℝ)) ^ 4) +
    _root_.GD.N0196.d022599 * (1 / (N : ℝ)) ^ 2 + (23 * _root_.GD.N0196.d022599 / 2) * (1 / (N : ℝ)) ^ 3

theorem d022613 {N : ℕ} (hN : 16 ≤ N) :
    (N : ℝ) * _root_.GD.N0196.d022601 N = _root_.GD.N0195.d022612 N := by
  have hn : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hm : 0 < (N : ℝ) - 1 := by linarith
  have hi : 0 < 1 - 1 / (N : ℝ) := by
    have h := (div_lt_one hnpos).2 (show (1 : ℝ) < N by linarith)
    linarith
  have hf := _root_.GD.N0196.d022602 hN
  unfold _root_.GD.N0196.d022601 _root_.GD.N0195.d022612
  simp only [div_pow, one_pow]
  field_simp [hnpos.ne', hm.ne', hi.ne', hf.ne'] <;> ring

theorem d022614 :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) / ((N : ℝ) - 1)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  simpa only [Function.comp_def, pow_one, one_mul, sub_eq_add_neg] using h


theorem d022615 :
    Tendsto _root_.GD.N0195.d022612 atTop (𝓝 (2 * _root_.GD.N0196.d022599 + 2)) := by
  have hu : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h1 : Tendsto (fun N : ℕ => 1 - 1 / (N : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hu
  have h4 : Tendsto (fun N : ℕ => 1 - (1 / (N : ℝ)) ^ 4) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hu.pow 4)
  have hsecond : Tendsto
      (fun N : ℕ => 2 / ((1 - 1 / (N : ℝ)) * (1 - (1 / (N : ℝ)) ^ 4)))
      atTop (𝓝 (2 : ℝ)) := by
    simpa [Pi.div_def] using (tendsto_const_nhds (x := (2 : ℝ))).div (h1.mul h4) (by norm_num)
  have hthird : Tendsto
      (fun N : ℕ => 6 * _root_.GD.N0196.d022599 * (Real.log (N : ℝ) / ((N : ℝ) - 1)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using _root_.GD.N0195.d022614.const_mul (6 * _root_.GD.N0196.d022599)
  have hfourth : Tendsto (fun N : ℕ => 4 * (1 / (N : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    simpa using hu.const_mul 4
  have hfifth : Tendsto
      (fun N : ℕ => ((7 * _root_.GD.N0196.d022599 / 2) * (1 / (N : ℝ))) / (1 - (1 / (N : ℝ)) ^ 4))
      atTop (𝓝 (0 : ℝ)) := by
    simpa [Pi.div_def] using (hu.const_mul (7 * _root_.GD.N0196.d022599 / 2)).div h4 (by norm_num)
  have hsixth : Tendsto (fun N : ℕ => _root_.GD.N0196.d022599 * (1 / (N : ℝ)) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa using (hu.pow 2).const_mul _root_.GD.N0196.d022599
  have hseventh : Tendsto
      (fun N : ℕ => (23 * _root_.GD.N0196.d022599 / 2) * (1 / (N : ℝ)) ^ 3) atTop (𝓝 (0 : ℝ)) := by
    simpa using (hu.pow 3).const_mul (23 * _root_.GD.N0196.d022599 / 2)
  change Tendsto (fun N : ℕ => _root_.GD.N0195.d022612 N) atTop (𝓝 (2 * _root_.GD.N0196.d022599 + 2))
  simpa [_root_.GD.N0195.d022612] using
    ((((((tendsto_const_nhds (x := 2 * _root_.GD.N0196.d022599)).add hsecond).add hthird).add hfourth).add
      hfifth).add hsixth).add hseventh

theorem d022616 :
    (∀ᶠ N : ℕ in atTop, 0 ≤ _root_.GD.N0195.d022611 N) ∧
      (∀ᶠ N : ℕ in atTop, _root_.GD.N0195.d022611 N ≤ _root_.GD.N0195.d022612 N) := by
  have hN : ∀ᶠ N : ℕ in atTop, 16 ≤ N := eventually_ge_atTop 16
  constructor
  · filter_upwards [hN] with N hn
    exact mul_nonneg (Nat.cast_nonneg N) (_root_.GD.N0196.d022610 hn).1.le
  · filter_upwards [hN] with N hn
    have h := mul_le_mul_of_nonneg_left (_root_.GD.N0196.d022609 hn) (Nat.cast_nonneg N)
    simpa only [_root_.GD.N0195.d022611, _root_.GD.N0195.d022613 hn] using h


theorem d022617 :
    0 ≤ liminf _root_.GD.N0195.d022611 atTop ∧
    liminf _root_.GD.N0195.d022611 atTop ≤ limsup _root_.GD.N0195.d022611 atTop ∧
    limsup _root_.GD.N0195.d022611 atTop ≤ Real.pi / 2 + 2 := by
  have he := _root_.GD.N0195.d022616
  have hlower : atTop.IsBoundedUnder (· ≥ ·) _root_.GD.N0195.d022611 :=
    isBoundedUnder_of_eventually_ge he.1
  have hupper : atTop.IsBoundedUnder (· ≤ ·) _root_.GD.N0195.d022611 :=
    _root_.GD.N0195.d022615.isBoundedUnder_le.mono_le he.2
  have hsup : limsup _root_.GD.N0195.d022611 atTop ≤ 2 * _root_.GD.N0196.d022599 + 2 := by
    have h := limsup_le_limsup he.2 hlower.isCobounded_flip
      _root_.GD.N0195.d022615.isBoundedUnder_le
    exact h.trans_eq _root_.GD.N0195.d022615.limsup_eq
  refine ⟨le_liminf_of_le hupper.isCobounded_flip he.1,
    liminf_le_limsup hupper hlower, ?_⟩
  exact hsup.trans_eq (by unfold _root_.GD.N0196.d022599; ring)

end
end GD.N0195

#print axioms _root_.GD.N0195.d022613
#print axioms _root_.GD.N0195.d022614
#print axioms _root_.GD.N0195.d022615
#print axioms _root_.GD.N0195.d022616
#print axioms _root_.GD.N0195.d022617
