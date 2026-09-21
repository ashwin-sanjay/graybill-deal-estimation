import GD.Module1348




set_option autoImplicit false
set_option warningAsError true

open Filter
open scoped Topology

namespace GD.N0106.N0428.N0770.N1699
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0972
open _root_.GD.N0106.N0428.N0770.N1749



theorem d021807 {k : ℕ} (hk : 0 < k)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) {sigma : ℝ} (hsigma : 0 < sigma)
    (hscale : theta.scale = fun _ => sigma) :
    sigma ^ 2 / 4 ≤ _root_.GD.N0232.N0719.N0972.d012340 k (fun _ => 2) theta := by
  have hkpos : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  rw [_root_.GD.N0106.N0428.N0770.N1749.d021800 hkpos theta hsigma hscale]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (k : ℝ))).2
  nlinarith [sq_nonneg sigma]



theorem d021808
    (theta : (j : ℕ) → _root_.GD.N0232.N0719.N0859.d010809 (j + 2))
    {sigma : ℝ} (hsigma : 0 < sigma)
    (hscale : ∀ j, (theta j).scale = fun _ => sigma) :
    ¬ Tendsto (fun j => _root_.GD.N0232.N0719.N0972.d012340 (j + 2) (fun _ => 2) (theta j))
      atTop (𝓝 (0 : ℝ)) := by
  intro hlim
  have hle : sigma ^ 2 / 4 ≤ (0 : ℝ) :=
    ge_of_tendsto' hlim (fun j =>
      _root_.GD.N0106.N0428.N0770.N1699.d021807 (by omega) (theta j) hsigma (hscale j))
  have hpos : (0 : ℝ) < sigma ^ 2 / 4 := by positivity
  exact (not_le_of_gt hpos) hle

end
end GD.N0106.N0428.N0770.N1699

#print axioms _root_.GD.N0106.N0428.N0770.N1699.d021807
#print axioms _root_.GD.N0106.N0428.N0770.N1699.d021808
