import GD.Module1345






set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace GD.N0106.N0428.N0770.N1749
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0972
open _root_.GD.N0232.N0719.N1023
open _root_.GD.N0106.N0428.N0770.N1750
open _root_.GD.N0106.N0428.N0770.N1748



def d021793 {k : ℕ} (sigma : Fin k → ℝ) (i : Fin k) : ℝ :=
  (sigma i)⁻¹ / (∑ j, (sigma j)⁻¹)

private theorem d021794 {k : ℕ} (hk : 0 < k)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : 0 < ∑ i, (theta.scale i)⁻¹ := by
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have h := _root_.GD.N0106.N0428.N0770.N1750.d008394 theta.scale_pos
  rw [_root_.GD.N0106.N0428.N0770.N1750.d008405] at h
  linarith

private theorem d021795 {k : ℕ} (hk : 0 < k)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (i : Fin k) :
    0 < _root_.GD.N0106.N0428.N0770.N1749.d021793 theta.scale i :=
  div_pos (inv_pos.mpr (theta.scale_pos i)) (_root_.GD.N0106.N0428.N0770.N1749.d021794 hk theta)

private theorem d021796 {k : ℕ} (hk : 0 < k)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : ∑ i, _root_.GD.N0106.N0428.N0770.N1749.d021793 theta.scale i = 1 := by
  simp only [_root_.GD.N0106.N0428.N0770.N1749.d021793, ← Finset.sum_div]
  exact div_self (_root_.GD.N0106.N0428.N0770.N1749.d021794 hk theta).ne'


theorem d021797 {k : ℕ} (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0963.d012141 k (fun _ => 2) theta =
      (2 * ∑ i, ((theta.scale i)⁻¹) ^ 2)⁻¹ := by
  simp only [_root_.GD.N0232.N0719.N0963.d012141,
    _root_.GD.N0232.N0719.N0838.d012097,
    _root_.GD.N0232.N0719.N0838.d012096,
    Nat.cast_ofNat, div_eq_mul_inv, inv_pow, Finset.mul_sum]


theorem d021798 {k : ℕ} (hk : 0 < k)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0972.d012340 k (fun _ => 2) theta /
        _root_.GD.N0232.N0719.N0963.d012141 k (fun _ => 2) theta =
      (∑ i, _root_.GD.N0106.N0428.N0770.N1749.d021793 theta.scale i ^ 2) *
        ((∑ i, (_root_.GD.N0106.N0428.N0770.N1749.d021793 theta.scale i)⁻¹) + k) / 2 := by
  have hC := _root_.GD.N0106.N0428.N0770.N1749.d021794 hk theta
  have hsq : (∑ i, _root_.GD.N0106.N0428.N0770.N1749.d021793 theta.scale i ^ 2) =
      (∑ i, ((theta.scale i)⁻¹) ^ 2) /
        (∑ i, (theta.scale i)⁻¹) ^ 2 := by
    simp only [_root_.GD.N0106.N0428.N0770.N1749.d021793, div_pow, ← Finset.sum_div]
  have hinv : (∑ i, (_root_.GD.N0106.N0428.N0770.N1749.d021793 theta.scale i)⁻¹) =
      (∑ i, (theta.scale i)⁻¹) * (∑ i, theta.scale i) := by
    simp only [_root_.GD.N0106.N0428.N0770.N1749.d021793, inv_div, div_inv_eq_mul,
      ← Finset.mul_sum]
  rw [_root_.GD.N0106.N0428.N0770.N1748.d021782 hk, _root_.GD.N0106.N0428.N0770.N1749.d021797,
    div_inv_eq_mul, hsq, hinv]
  unfold _root_.GD.N0232.N0719.N1023.d001844
  field_simp [hC.ne'] <;> ring


theorem d021799 {k : ℕ} (hk : 0 < k)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    ((k : ℝ) + 1) / 2 ≤
      _root_.GD.N0232.N0719.N0972.d012340 k (fun _ => 2) theta /
        _root_.GD.N0232.N0719.N0963.d012141 k (fun _ => 2) theta := by
  rw [_root_.GD.N0106.N0428.N0770.N1749.d021798 hk theta]
  exact _root_.GD.N0232.N0719.N1023.d001847 hk (_root_.GD.N0106.N0428.N0770.N1749.d021793 theta.scale)
    (_root_.GD.N0106.N0428.N0770.N1749.d021795 hk theta) (_root_.GD.N0106.N0428.N0770.N1749.d021796 hk theta)


theorem d021800 {k : ℕ} (hk : 0 < k)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) {sigma : ℝ} (hsigma : 0 < sigma)
    (hscale : theta.scale = fun _ => sigma) :
    _root_.GD.N0232.N0719.N0972.d012340 k (fun _ => 2) theta =
      sigma ^ 2 * (k + 1) / (4 * k) := by
  rw [_root_.GD.N0106.N0428.N0770.N1748.d021782 hk, hscale]
  exact _root_.GD.N0232.N0719.N1023.d001846 hk hsigma

theorem d021801 {k : ℕ} (hk : 0 < k)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) {sigma : ℝ} (hsigma : 0 < sigma)
    (hscale : theta.scale = fun _ => sigma) :
    _root_.GD.N0232.N0719.N0963.d012141 k (fun _ => 2) theta =
      sigma ^ 2 / (2 * k) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [_root_.GD.N0106.N0428.N0770.N1749.d021797, hscale]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hkR, hsigma.ne'] <;> ring


theorem d021802 {k : ℕ} (hk : 0 < k)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) {sigma : ℝ} (hsigma : 0 < sigma)
    (hscale : theta.scale = fun _ => sigma) :
    _root_.GD.N0232.N0719.N0972.d012340 k (fun _ => 2) theta /
        _root_.GD.N0232.N0719.N0963.d012141 k (fun _ => 2) theta =
      ((k : ℝ) + 1) / 2 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [_root_.GD.N0106.N0428.N0770.N1749.d021800 hk theta hsigma hscale,
    _root_.GD.N0106.N0428.N0770.N1749.d021801 hk theta hsigma hscale]
  field_simp [hkR, hsigma.ne'] <;> ring


theorem d021803 (theta : _root_.GD.N0232.N0719.N0859.d010809 3) {r : ℝ} (hr : 0 < r)
    (hscale : theta.scale = ![1, 1, r]) :
    _root_.GD.N0232.N0719.N0972.d012340 3 (fun _ => 2) theta =
      r / 8 + 3 * r * (4 * r + 1) / (8 * (2 * r + 1) ^ 2) := by
  rw [_root_.GD.N0106.N0428.N0770.N1748.d021782 (by norm_num), hscale]
  exact _root_.GD.N0232.N0719.N1023.d001849 hr

theorem d021804 (theta : _root_.GD.N0232.N0719.N0859.d010809 3) {r : ℝ} (hr : 0 < r)
    (hscale : theta.scale = ![1, 1, r]) :
    r / 8 < _root_.GD.N0232.N0719.N0972.d012340 3 (fun _ => 2) theta := by
  rw [_root_.GD.N0106.N0428.N0770.N1748.d021782 (by norm_num), hscale]
  exact _root_.GD.N0232.N0719.N1023.d001850 hr



theorem d021805 (mu M : ℝ) :
    ∃ r : ℝ, 0 < r ∧ ∃ theta : _root_.GD.N0232.N0719.N0859.d010809 3,
      theta.location = mu ∧ theta.scale = ![1, 1, r] ∧
        M < _root_.GD.N0232.N0719.N0972.d012340 3 (fun _ => 2) theta := by
  obtain ⟨r, hr, hM⟩ := _root_.GD.N0232.N0719.N1023.d001851 M
  have hsigma : ∀ i : Fin 3, 0 < ![1, 1, r] i := by
    intro i
    fin_cases i <;> simp [hr]
  let theta : _root_.GD.N0232.N0719.N0859.d010809 3 := ⟨mu, ![1, 1, r], hsigma⟩
  refine ⟨r, hr, theta, rfl, rfl, ?_⟩
  rw [_root_.GD.N0106.N0428.N0770.N1748.d021782 (by norm_num)]
  exact hM



theorem d021806 (theta : _root_.GD.N0232.N0719.N0859.d010809 2)
    (hscale : theta.scale = fun _ => 1) :
    _root_.GD.N0232.N0719.N0972.d012340 2 (fun _ => 2) theta = 3 / 8 := by
  have h := _root_.GD.N0106.N0428.N0770.N1749.d021800 (by norm_num : 0 < 2) theta
    (by norm_num : (0 : ℝ) < 1) hscale
  norm_num at h ⊢
  exact h

end
end GD.N0106.N0428.N0770.N1749

#print axioms _root_.GD.N0106.N0428.N0770.N1749.d021797
#print axioms _root_.GD.N0106.N0428.N0770.N1749.d021798
#print axioms _root_.GD.N0106.N0428.N0770.N1749.d021799
#print axioms _root_.GD.N0106.N0428.N0770.N1749.d021800
#print axioms _root_.GD.N0106.N0428.N0770.N1749.d021801
#print axioms _root_.GD.N0106.N0428.N0770.N1749.d021802
#print axioms _root_.GD.N0106.N0428.N0770.N1749.d021803
#print axioms _root_.GD.N0106.N0428.N0770.N1749.d021804
#print axioms _root_.GD.N0106.N0428.N0770.N1749.d021805
#print axioms _root_.GD.N0106.N0428.N0770.N1749.d021806
