import GD.Module0637
import GD.Module0410
import GD.Module0567






set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GD.N0106.N0428.N0770.N1753
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0933 _root_.GD.N0106.N0428.N0770.N1750

def d021759 {k : ℕ} (sigma : Fin k → ℝ) (z : Fin k → ℝ) : Fin k → ℝ :=
  fun i => sigma i ^ 2 * z i ^ 2 / 2

theorem d021760 {k : ℕ} (sigma : Fin k → ℝ) :
    Measurable (_root_.GD.N0106.N0428.N0770.N1753.d021759 sigma) := by
  unfold _root_.GD.N0106.N0428.N0770.N1753.d021759
  fun_prop



theorem d021761 (sigma : ℝ) :
    _root_.GD.N0232.N0719.N0933.d009289 2 sigma =
      (gaussianReal 0 1).map (fun z : ℝ => sigma ^ 2 * z ^ 2 / 2) := by
  have hsquare : (gaussianReal 0 1).map (fun z : ℝ => z ^ 2) =
      gammaMeasure (1 / 2) (1 / 2) := by
    simpa [_root_.GD.N0121.d006346] using
      _root_.GD.N0121.d006355
  unfold _root_.GD.N0232.N0719.N0933.d009289
  norm_num only [Nat.reduceSub, Nat.cast_one]
  rw [← hsquare, Measure.map_map (_root_.GD.N0232.N0719.N0933.d009294 2 sigma)
    (by fun_prop : Measurable (fun z : ℝ => z ^ 2))]
  congr 1
  funext z
  simp only [Function.comp_apply, _root_.GD.N0232.N0719.N0933.d009287, Nat.cast_ofNat]
  ring



theorem d021762 {k : ℕ} (sigma : Fin k → ℝ) :
    (_root_.GD.N0106.N0428.N0770.N1750.d008364 (Fin k)).map (_root_.GD.N0106.N0428.N0770.N1753.d021759 sigma) =
      _root_.GD.N0232.N0719.N0933.d009301 k (fun _ => 2) sigma := by
  unfold _root_.GD.N0106.N0428.N0770.N1750.d008364 _root_.GD.N0106.N0428.N0770.N1753.d021759 _root_.GD.N0232.N0719.N0933.d009301
  rw [Measure.pi_map_pi (fun i =>
    (by fun_prop : Measurable (fun z : ℝ => sigma i ^ 2 * z ^ 2 / 2)).aemeasurable)]
  simp_rw [← _root_.GD.N0106.N0428.N0770.N1753.d021761]



theorem d021763 {k : ℕ} (mu : ℝ) (sigma : Fin k → ℝ) :
    (_root_.GD.N0232.N0719.d009176 k (fun _ => 2) mu sigma).map
      (_root_.GD.N0232.N0719.N0933.d009304 k (fun _ => 2)) =
        (_root_.GD.N0232.N0719.N0933.d009300 k (fun _ => 2) mu sigma).prod
          ((_root_.GD.N0106.N0428.N0770.N1750.d008364 (Fin k)).map (_root_.GD.N0106.N0428.N0770.N1753.d021759 sigma)) := by
  rw [_root_.GD.N0232.N0719.N0933.d009309 k (fun _ => 2)
    (fun _ => le_rfl), _root_.GD.N0106.N0428.N0770.N1753.d021762]



theorem d021764 {k : ℕ} (sigma y z : Fin k → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hz : ∀ i, z i ≠ 0) (i : Fin k) :
    _root_.GD.N0232.N0719.N0900.d009106
      (_root_.GD.N0232.N0719.N0933.d009305 k (y, _root_.GD.N0106.N0428.N0770.N1753.d021759 sigma z)) i =
        _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma i z := by
  have hv : 0 < sigma i ^ 2 * z i ^ 2 / 2 :=
    div_pos (mul_pos (sq_pos_of_pos (hsigma i)) (sq_pos_of_ne_zero (hz i))) (by norm_num)
  simp only [_root_.GD.N0232.N0719.N0900.d009106, _root_.GD.N0232.N0719.N0900.d009105,
    _root_.GD.N0232.N0719.N0933.d009305, _root_.GD.N0106.N0428.N0770.N1753.d021759, hv, if_pos,
    _root_.GD.N0106.N0428.N0770.N1750.d008366, _root_.GD.N0106.N0428.N0770.N1702.d008357]
  field_simp



theorem d021765 {k : ℕ} (hk : 0 < k) (sigma y z : Fin k → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hz : ∀ i, z i ≠ 0) (i : Fin k) :
    _root_.GD.N0232.N0719.N0900.d009108
      (_root_.GD.N0232.N0719.N0933.d009305 k (y, _root_.GD.N0106.N0428.N0770.N1753.d021759 sigma z)) i =
        _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i z := by
  have hsum : _root_.GD.N0232.N0719.N0900.d009107
      (_root_.GD.N0232.N0719.N0933.d009305 k (y, _root_.GD.N0106.N0428.N0770.N1753.d021759 sigma z)) =
        _root_.GD.N0106.N0428.N0770.N1750.d008367 sigma z := by
    unfold _root_.GD.N0232.N0719.N0900.d009107 _root_.GD.N0106.N0428.N0770.N1750.d008367
    congr 1
    funext j
    exact _root_.GD.N0106.N0428.N0770.N1753.d021764 sigma y z hsigma hz j
  let j : Fin k := ⟨0, hk⟩
  have hj : 0 < _root_.GD.N0106.N0428.N0770.N1750.d008366 sigma j z :=
    div_pos (by norm_num) (mul_pos (sq_pos_of_pos (hsigma j))
      (sq_pos_of_ne_zero (hz j)))
  have hp := hj.trans_le (_root_.GD.N0106.N0428.N0770.N1750.d008387 sigma j z)
  rw [_root_.GD.N0232.N0719.N0900.d009108, hsum, if_neg hp.ne',
    _root_.GD.N0106.N0428.N0770.N1753.d021764 sigma y z hsigma hz]
  rfl



theorem d021766 {k : ℕ} (hk : 0 < k) (sigma y z : Fin k → ℝ)
    (hsigma : ∀ i, 0 < sigma i) (hz : ∀ i, z i ≠ 0) :
    _root_.GD.N0232.N0719.N0900.d009110
      (_root_.GD.N0232.N0719.N0933.d009305 k (y, _root_.GD.N0106.N0428.N0770.N1753.d021759 sigma z)) =
        ∑ i, _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i z * y i := by
  unfold _root_.GD.N0232.N0719.N0900.d009110
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.GD.N0106.N0428.N0770.N1753.d021765 hk sigma y z hsigma hz]
  rfl


theorem d021767 (k : ℕ) :
    ∀ᵐ z ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 (Fin k), ∀ i, z i ≠ 0 := by
  letI : NoAtoms (gaussianReal 0 1) := noAtoms_gaussianReal (by norm_num)
  exact ae_all_iff.mpr (fun i =>
    Measure.ae_eval_ne (fun _ : Fin k => gaussianReal 0 1) i 0)


theorem d021768 {k : ℕ} (hk : 0 < k) (sigma : Fin k → ℝ)
    (hsigma : ∀ i, 0 < sigma i) :
    ∀ᵐ z ∂_root_.GD.N0106.N0428.N0770.N1750.d008364 (Fin k), ∀ y : Fin k → ℝ,
      _root_.GD.N0232.N0719.N0900.d009110
        (_root_.GD.N0232.N0719.N0933.d009305 k (y, _root_.GD.N0106.N0428.N0770.N1753.d021759 sigma z)) =
          ∑ i, _root_.GD.N0106.N0428.N0770.N1750.d008382 sigma i z * y i := by
  filter_upwards [_root_.GD.N0106.N0428.N0770.N1753.d021767 k] with z hz y
  exact _root_.GD.N0106.N0428.N0770.N1753.d021766 hk sigma y z hsigma hz

end
end GD.N0106.N0428.N0770.N1753

#print axioms _root_.GD.N0106.N0428.N0770.N1753.d021761
#print axioms _root_.GD.N0106.N0428.N0770.N1753.d021762
#print axioms _root_.GD.N0106.N0428.N0770.N1753.d021763
#print axioms _root_.GD.N0106.N0428.N0770.N1753.d021764
#print axioms _root_.GD.N0106.N0428.N0770.N1753.d021765
#print axioms _root_.GD.N0106.N0428.N0770.N1753.d021766
#print axioms _root_.GD.N0106.N0428.N0770.N1753.d021768
