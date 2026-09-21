import GD.Module0562
import GD.Module0336
import GD.Module1898

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0007
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1066 _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0082.N0334
open _root_.GD.N0082.N0335
open _root_.GD.N0082.N0336
open _root_.GD.N0011


theorem d030822 : _root_.GD.N0082.N0334.d008258 id (1 / 8) = (69 - 28 * Real.log 7) / 27 := by
  let F : ℝ → ℝ := fun u =>
    16 * u / 9 - 28 * Real.log (6 * u + 1) / 27 - 49 / (54 * (6 * u + 1))
  have hden (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : 6 * u + 1 ≠ 0 := by
    linarith [hu.1]
  have hd (u : ℝ) (hu : u ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt F (((u - 1 / 8) / _root_.GD.N0082.N0334.d008256 (1 / 8) u) ^ 2) u := by
    have hne := hden u (by simpa using hu)
    have ha : HasDerivAt (fun x : ℝ => 6 * x + 1) 6 u := by
      simpa using ((hasDerivAt_id u).const_mul 6).add_const 1
    have hd' := (((hasDerivAt_id u).const_mul 16).div_const 9).sub
      (((ha.log hne).const_mul 28).div_const 27)
    have hinv := (hasDerivAt_const u (49 : ℝ)).div (ha.const_mul 54)
      (mul_ne_zero (by norm_num) hne)
    exact (hd'.sub hinv).congr_deriv (by
      dsimp [_root_.GD.N0082.N0334.d008256]
      rw [show u + 1 / 8 - 2 * u * (1 / 8) = (6 * u + 1) / 8 by ring]
      field_simp [hne]
      ring)
  have hi : IntervalIntegrable
      (fun u : ℝ => ((u - 1 / 8) / _root_.GD.N0082.N0334.d008256 (1 / 8) u) ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    apply ContinuousOn.pow
    apply ContinuousOn.div (by fun_prop) (by unfold _root_.GD.N0082.N0334.d008256; fun_prop)
    intro u hu
    dsimp [_root_.GD.N0082.N0334.d008256]
    linarith [hu.1]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  unfold _root_.GD.N0082.N0334.d008258
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  change (∫ u : ℝ in 0..1, ((u - 1 / 8) / _root_.GD.N0082.N0334.d008256 (1 / 8) u) ^ 2) = _
  rw [he]
  dsimp [F]
  norm_num
  ring

theorem d030823 :
    1 + _root_.GD.N0082.N0334.d008258 id (1 / 8) = (96 - 28 * Real.log 7) / 27 := by
  rw [_root_.GD.N0007.d030822]
  ring

theorem d030824 : 1 + _root_.GD.N0082.N0334.d008258 id (1 / 8) < (77 : ℝ) / 50 := by
  rw [_root_.GD.N0007.d030823]
  exact _root_.GD.N0008.d005010

theorem d030825 : _root_.GD.N0082.N0334.d008258 id (7 / 8) = _root_.GD.N0082.N0334.d008258 id (1 / 8) := by
  convert _root_.GD.N0082.N0334.d008276 (H := id) (fun _ => rfl) (1 / 8) using 1
  norm_num

theorem d030826 :
    1 + _root_.GD.N0082.N0334.d008258 id (7 / 8) < (77 : ℝ) / 50 := by
  rw [_root_.GD.N0007.d030825]
  exact _root_.GD.N0007.d030824

theorem d030827 : 1 + _root_.GD.N0082.N0334.d008258 id (1 / 2) = (4 : ℝ) / 3 := by
  rw [_root_.GD.N0082.N0334.d008338]
  norm_num


theorem d030828 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1066.d014320 3 3 (by omega) (by omega) θ =
      ENNReal.ofReal (_root_.GD.N0232.N0720.N1257.d015508 3 3 θ * (1 + _root_.GD.N0082.N0334.d008258 id (_root_.GD.N0082.N0336.d030741 θ))) := by
  rw [_root_.GD.N0082.N0336.d030750, _root_.GD.N0011.d030817]

theorem d030829 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1256.d015547 3 3 θ (_root_.GD.N0232.N0720.N1080.d014175 3 3) =
      ENNReal.ofReal (1 + _root_.GD.N0082.N0334.d008258 id (_root_.GD.N0082.N0336.d030741 θ)) := by
  rw [← _root_.GD.N0082.N0335.d030727]
  rw [_root_.GD.N0011.d030818 _root_.GD.N0082.N0335.d030710 _root_.GD.N0082.N0335.d030713 _root_.GD.N0082.N0335.d030711, _root_.GD.N0082.N0336.d030748]

theorem d030830 (θ : _root_.GD.N0232.N0720.N1080.d014168) (ht : _root_.GD.N0082.N0336.d030741 θ = 1 / 8) :
    _root_.GD.N0232.N0720.N1066.d014320 3 3 (by omega) (by omega) θ ≤
      ENNReal.ofReal ((77 / 50 : ℝ) * _root_.GD.N0232.N0720.N1257.d015508 3 3 θ) := by
  rw [_root_.GD.N0007.d030828, ht]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ _root_.GD.N0232.N0720.N1257.d015508 3 3 θ * (77 / 50) :=
      mul_le_mul_of_nonneg_left _root_.GD.N0007.d030824.le
        ((_root_.GD.N0011.d030817 θ) ▸ (_root_.GD.N0082.N0336.d030744 θ).le)
    _ = _ := mul_comm _ _

theorem d030831 (θ : _root_.GD.N0232.N0720.N1080.d014168) (ht : _root_.GD.N0082.N0336.d030741 θ = 7 / 8) :
    _root_.GD.N0232.N0720.N1066.d014320 3 3 (by omega) (by omega) θ ≤
      ENNReal.ofReal ((77 / 50 : ℝ) * _root_.GD.N0232.N0720.N1257.d015508 3 3 θ) := by
  rw [_root_.GD.N0007.d030828, ht]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ _root_.GD.N0232.N0720.N1257.d015508 3 3 θ * (77 / 50) :=
      mul_le_mul_of_nonneg_left _root_.GD.N0007.d030826.le
        ((_root_.GD.N0011.d030817 θ) ▸ (_root_.GD.N0082.N0336.d030744 θ).le)
    _ = _ := mul_comm _ _

theorem d030832 (θ : _root_.GD.N0232.N0720.N1080.d014168) (ht : _root_.GD.N0082.N0336.d030741 θ = 1 / 2) :
    _root_.GD.N0232.N0720.N1066.d014320 3 3 (by omega) (by omega) θ =
      ENNReal.ofReal ((4 / 3 : ℝ) * _root_.GD.N0232.N0720.N1257.d015508 3 3 θ) := by
  rw [_root_.GD.N0007.d030828, ht, _root_.GD.N0007.d030827, mul_comm]

end
end GD.N0007

#print axioms _root_.GD.N0007.d030822
#print axioms _root_.GD.N0007.d030823
#print axioms _root_.GD.N0007.d030824
#print axioms _root_.GD.N0007.d030825
#print axioms _root_.GD.N0007.d030826
#print axioms _root_.GD.N0007.d030827
#print axioms _root_.GD.N0007.d030828
#print axioms _root_.GD.N0007.d030829
#print axioms _root_.GD.N0007.d030830
#print axioms _root_.GD.N0007.d030831
#print axioms _root_.GD.N0007.d030832
