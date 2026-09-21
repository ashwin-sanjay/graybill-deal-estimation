import GD.Module1399
import GD.Module1461















set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace GD.N0185
noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1257
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0180 _root_.GD.N0163
open _root_.GD.N0193 _root_.GD.N0177
open _root_.GD.N0160


theorem d023075 (t : _root_.GD.N0232.N0720.N1441.d013676)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) {C : ℝ}
    (hcap : (∫ z, (g z - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 3 3 t) ≤
      (C - 1) * t.1 * (1 - t.1)) :
    _root_.GD.N0180.d022173 t g ≤ C - 1 := by
  unfold _root_.GD.N0180.d022173
  rw [_root_.GD.N0180.d022172]
  apply (div_le_iff₀ (mul_pos t.property.1 (sub_pos.mpr t.property.2))).2
  simpa only [mul_assoc] using hcap


theorem d023076
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (hgb : ∀ z, g z ∈ Icc (0 : ℝ) 1) {C : ℝ}
    (hcap : ∀ t : _root_.GD.N0232.N0720.N1441.d013676,
      (∫ z, (g z - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 3 3 t) ≤
        (C - 1) * t.1 * (1 - t.1))
    {N : ℕ} (hN : 2 ≤ N) : _root_.GD.N0160.d022516 N ≤ C - 1 := by
  classical
  letI : Nonempty (_root_.GD.N0193.d007344 N) := ⟨(⟨0, _root_.GD.N0193.d007353 hN⟩, 0)⟩
  have habs : ∀ z, |g z| ≤ 1 := by
    intro z
    rw [abs_of_nonneg (hgb z).1]
    exact (hgb z).2
  rw [_root_.GD.N0160.d022517 hN]
  calc
    _root_.GD.N0163.d022186 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN) ≤
        _root_.GD.N0163.d022185 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N) (_root_.GD.N0177.d022414 hN) g :=
      _root_.GD.N0163.d022210 (fun _ : _root_.GD.N0193.d007344 N => _root_.GD.N0193.d007348 N)
        (_root_.GD.N0177.d022414 hN) (fun _ => _root_.GD.N0193.d007367 hN) g hg habs
    _ ≤ ∑ _i : _root_.GD.N0193.d007344 N, _root_.GD.N0193.d007348 N * (C - 1) := by
      unfold _root_.GD.N0163.d022185
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (_root_.GD.N0185.d023075 (_root_.GD.N0177.d022414 hN i) g
          (hcap (_root_.GD.N0177.d022414 hN i))) (_root_.GD.N0193.d007367 hN).le
    _ = C - 1 := by
      rw [← Finset.sum_mul, _root_.GD.N0193.d007374 hN, one_mul]



theorem d023077
    (C : ℝ) (hC : 0 ≤ C) (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ) (hd : Measurable d)
    (hbound : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 3 3 theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 3 3 theta)) :
    1 + Real.pi / 4 ≤ C := by
  obtain ⟨g, hg, hgb, hcap⟩ :=
    _root_.GD.N0045.d023068
      3 3 (by norm_num) (by norm_num) C hC d hd hbound
  have htail : ∀ᶠ N : ℕ in atTop, _root_.GD.N0160.d022516 N ≤ C - 1 :=
    eventually_atTop.2 ⟨2, fun N hN =>
      _root_.GD.N0185.d023076 g hg hgb hcap hN⟩
  have hlimit : Real.pi / 4 ≤ C - 1 :=
    le_of_tendsto _root_.GD.N0160.d022525 htail
  linarith

end
end GD.N0185

#print axioms _root_.GD.N0185.d023075
#print axioms _root_.GD.N0185.d023076
#print axioms _root_.GD.N0185.d023077
