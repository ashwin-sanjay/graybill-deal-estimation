import GD.Module0664
import GD.Module1262

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GD.N0102.N0424

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0983 _root_.GD.N0232.N0719.N0986

noncomputable section
variable {k : ℕ}


theorem d022958 (y : Fin k → ℝ) (p : _root_.GD.N0232.N0719.N0983.d009709 k) (c a : ℝ) :
    _root_.GD.N0232.N0719.N0983.d009713 (fun i => c + a * y i) p = c + a * _root_.GD.N0232.N0719.N0983.d009713 y p := by
  unfold _root_.GD.N0232.N0719.N0983.d009713
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, _root_.GD.N0232.N0719.N0983.d009712, one_mul]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring


theorem d022959 (y r : Fin k → ℝ) (p : _root_.GD.N0232.N0719.N0983.d009709 k) (c a : ℝ) :
    _root_.GD.N0232.N0719.N0983.d009714 (fun i => c + a * y i) (fun i => a ^ 2 * r i) p =
      a ^ 2 * _root_.GD.N0232.N0719.N0983.d009714 y r p := by
  unfold _root_.GD.N0232.N0719.N0983.d009714
  rw [_root_.GD.N0102.N0424.d022958]
  have hfirst : (∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * (a ^ 2 * r i)) =
      a ^ 2 * ∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * r i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsecond : (∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) *
      (c + a * y i - (c + a * _root_.GD.N0232.N0719.N0983.d009713 y p)) ^ 2) =
      a ^ 2 * ∑ i, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * (y i - _root_.GD.N0232.N0719.N0983.d009713 y p) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfirst, hsecond]
  ring

theorem d022960 (q : ℝ) (y r : Fin k → ℝ) (hr : ∀ i, 0 ≤ r i)
    (p : _root_.GD.N0232.N0719.N0983.d009709 k) (c a : ℝ) :
    _root_.GD.N0232.N0719.N0983.d009720 q (fun i => c + a * y i) (fun i => a ^ 2 * r i) p =
      (a ^ 2 : ℝ) ^ (-q) * _root_.GD.N0232.N0719.N0983.d009720 q y r p := by
  unfold _root_.GD.N0232.N0719.N0983.d009720
  rw [_root_.GD.N0102.N0424.d022959, Real.mul_rpow (sq_nonneg a) (_root_.GD.N0232.N0719.N0983.d009717 y r hr p)]

theorem d022961 (q : ℝ) (y r : Fin k → ℝ) (hr : ∀ i, 0 ≤ r i)
    (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) (c a : ℝ) :
    _root_.GD.N0232.N0719.N0983.d009723 q (fun i => c + a * y i) (fun i => a ^ 2 * r i) μ =
      (a ^ 2 : ℝ) ^ (-q) * _root_.GD.N0232.N0719.N0983.d009723 q y r μ := by
  simp only [_root_.GD.N0232.N0719.N0983.d009723, _root_.GD.N0102.N0424.d022960 q y r hr, integral_const_mul]



theorem d022962 (q : ℝ) (y r : Fin k → ℝ) (hr : ∀ i, 0 < r i)
    (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) [IsProbabilityMeasure μ] (c a : ℝ) (ha : a ≠ 0) :
    _root_.GD.N0232.N0719.N0983.d009724 q (fun i => c + a * y i) (fun i => a ^ 2 * r i) μ =
      c + a * _root_.GD.N0232.N0719.N0983.d009724 q y r μ := by
  have hK : Integrable (_root_.GD.N0232.N0719.N0983.d009720 q y r) μ := _root_.GD.N0232.N0719.N0983.d009726 q y r hr μ
  have hB : Integrable (fun p => _root_.GD.N0232.N0719.N0983.d009713 y p * _root_.GD.N0232.N0719.N0983.d009720 q y r p) μ :=
    ((_root_.GD.N0232.N0719.N0983.d009715 y).mul (_root_.GD.N0232.N0719.N0983.d009721 q y r hr)).integrable_of_hasCompactSupport
      (isClosed_tsupport _).isCompact
  have hscale : (a ^ 2 : ℝ) ^ (-q) ≠ 0 :=
    (Real.rpow_pos_of_pos (sq_pos_of_ne_zero ha) _).ne'
  have hmass : _root_.GD.N0232.N0719.N0983.d009723 q y r μ ≠ 0 := (_root_.GD.N0232.N0719.N0983.d009728 q y r hr μ).ne'
  unfold _root_.GD.N0232.N0719.N0983.d009724
  rw [_root_.GD.N0102.N0424.d022961 q y r (fun i => (hr i).le)]
  simp_rw [_root_.GD.N0102.N0424.d022958, _root_.GD.N0102.N0424.d022960 q y r (fun i => (hr i).le)]
  have hnum : (∫ p, (c + a * _root_.GD.N0232.N0719.N0983.d009713 y p) *
      ((a ^ 2 : ℝ) ^ (-q) * _root_.GD.N0232.N0719.N0983.d009720 q y r p) ∂μ) =
      (a ^ 2 : ℝ) ^ (-q) *
        (c * _root_.GD.N0232.N0719.N0983.d009723 q y r μ + a * ∫ p, _root_.GD.N0232.N0719.N0983.d009713 y p * _root_.GD.N0232.N0719.N0983.d009720 q y r p ∂μ) := by
    calc
      _ = ∫ p, (a ^ 2 : ℝ) ^ (-q) *
          (c * _root_.GD.N0232.N0719.N0983.d009720 q y r p + a * (_root_.GD.N0232.N0719.N0983.d009713 y p * _root_.GD.N0232.N0719.N0983.d009720 q y r p)) ∂μ := by
            apply integral_congr_ae
            exact ae_of_all _ fun _ => by ring
      _ = _ := by
        rw [integral_const_mul, integral_add (hK.const_mul c) (hB.const_mul a),
          integral_const_mul, integral_const_mul]
        rfl
  rw [hnum]
  field_simp


theorem d022963 (q : ℝ) (y r : Fin k → ℝ)
    (hr : ∀ i, 0 ≤ r i) (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k))
    (c a : ℝ) (ha : a ≠ 0) (i : Fin k) :
    _root_.GD.N0232.N0719.N0983.d009725 q (fun j => c + a * y j) (fun j => a ^ 2 * r j) μ i =
      _root_.GD.N0232.N0719.N0983.d009725 q y r μ i := by
  have hscale : (a ^ 2 : ℝ) ^ (-q) ≠ 0 :=
    (Real.rpow_pos_of_pos (sq_pos_of_ne_zero ha) _).ne'
  unfold _root_.GD.N0232.N0719.N0983.d009725
  rw [_root_.GD.N0102.N0424.d022961 q y r hr]
  simp_rw [_root_.GD.N0102.N0424.d022960 q y r hr]
  have hnum : (∫ p, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) *
      ((a ^ 2 : ℝ) ^ (-q) * _root_.GD.N0232.N0719.N0983.d009720 q y r p) ∂μ) =
      (a ^ 2 : ℝ) ^ (-q) * ∫ p, (_root_.GD.N0232.N0719.N0983.d009710 i p : ℝ) * _root_.GD.N0232.N0719.N0983.d009720 q y r p ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun _ => by ring
  rw [hnum, mul_div_mul_left _ _ hscale]

theorem d022964 (sizes : Fin k → ℕ) (hn : ∀ i, 0 < sizes i)
    (z : _root_.GD.N0232.N0719.N0986.d020359 sizes) (c a : ℝ) (i : Fin k) :
    _root_.GD.N0232.N0719.N0986.d020360 sizes (fun j l => c + a * z j l) i = c + a * _root_.GD.N0232.N0719.N0986.d020360 sizes z i := by
  have hsize : (sizes i : ℝ) ≠ 0 := by exact_mod_cast (hn i).ne'
  unfold _root_.GD.N0232.N0719.N0986.d020360
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem d022965 (sizes : Fin k → ℕ) (hn : ∀ i, 0 < sizes i)
    (z : _root_.GD.N0232.N0719.N0986.d020359 sizes) (c a : ℝ) (i : Fin k) :
    _root_.GD.N0232.N0719.N0986.d020361 sizes (fun j l => c + a * z j l) i = a ^ 2 * _root_.GD.N0232.N0719.N0986.d020361 sizes z i := by
  unfold _root_.GD.N0232.N0719.N0986.d020361
  rw [_root_.GD.N0102.N0424.d022964 sizes hn]
  have heq : (∑ j, (c + a * z i j - (c + a * _root_.GD.N0232.N0719.N0986.d020360 sizes z i)) ^ 2) =
      a ^ 2 * ∑ j, (z i j - _root_.GD.N0232.N0719.N0986.d020360 sizes z i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  ring

theorem d022966 (sizes : Fin k → ℕ) (hn : ∀ i, 0 < sizes i)
    (q : ℝ) (μ : Measure (_root_.GD.N0232.N0719.N0983.d009709 k)) [IsProbabilityMeasure μ]
    (z : _root_.GD.N0232.N0719.N0986.d020359 sizes) (hr : ∀ i, 0 < _root_.GD.N0232.N0719.N0986.d020361 sizes z i)
    (c a : ℝ) (ha : a ≠ 0) :
    _root_.GD.N0232.N0719.N0983.d009724 q (_root_.GD.N0232.N0719.N0986.d020360 sizes (fun j l => c + a * z j l))
      (_root_.GD.N0232.N0719.N0986.d020361 sizes (fun j l => c + a * z j l)) μ =
      c + a * _root_.GD.N0232.N0719.N0983.d009724 q (_root_.GD.N0232.N0719.N0986.d020360 sizes z) (_root_.GD.N0232.N0719.N0986.d020361 sizes z) μ := by
  simp only [funext (_root_.GD.N0102.N0424.d022964 sizes hn z c a),
    funext (_root_.GD.N0102.N0424.d022965 sizes hn z c a)]
  exact _root_.GD.N0102.N0424.d022962 q _ _ hr μ c a ha

end
end GD.N0102.N0424

#print axioms _root_.GD.N0102.N0424.d022962
#print axioms _root_.GD.N0102.N0424.d022963
#print axioms _root_.GD.N0102.N0424.d022966
