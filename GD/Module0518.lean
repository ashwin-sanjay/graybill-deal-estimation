import GD.Module0517
import GD.Module0190





set_option autoImplicit false
set_option warningAsError true

namespace GD.N0106.N0428.N0766
noncomputable section

namespace N1692

open _root_.GD.N0232.N0720.N1254

abbrev d007772 (alpha beta e : ℝ) : ℝ → ℝ → ℝ :=
  _root_.GD.N0106.N0428.N0766.d007748 (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) (_root_.GD.N0232.N0720.N1254.d002516 alpha beta e) (_root_.GD.N0232.N0720.N1254.d002517 e)
    (_root_.GD.N0232.N0720.N1254.d002515 alpha beta e) (_root_.GD.N0232.N0720.N1254.d002513 alpha beta)


theorem d007773 {alpha beta : ℝ} (ha : 0 < alpha) (hb : 0 < beta)
    (e : ℝ) :
    _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e 0 0 =
      (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta) * _root_.GD.N0232.N0720.N1254.d002537 alpha beta e ∧
    deriv (fun s => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e s 0) 0 =
      (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta) *
        _root_.GD.N0232.N0720.N1254.d002538 alpha beta e ∧
    deriv (deriv (fun s => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e s 0)) 0 =
      (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta) *
        _root_.GD.N0232.N0720.N1254.d002539 alpha beta e ∧
    deriv (deriv (deriv (fun s => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e s 0))) 0 =
      (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta) *
        _root_.GD.N0232.N0720.N1254.d002541 alpha beta e ∧
    deriv (fun t => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e 0 t) 0 =
      (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta) *
        _root_.GD.N0232.N0720.N1254.d002540 alpha beta e ∧
    deriv (fun s => deriv (fun t => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e s t) 0) 0 =
      (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta) *
        _root_.GD.N0232.N0720.N1254.d002542 alpha beta e := by
  exact _root_.GD.N0106.N0428.N0766.d007771 (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) (_root_.GD.N0232.N0720.N1254.d002516 alpha beta e) (_root_.GD.N0232.N0720.N1254.d002517 e)
    (_root_.GD.N0232.N0720.N1254.d002515 alpha beta e) (_root_.GD.N0232.N0720.N1254.d002513 alpha beta) (_root_.GD.N0232.N0720.N1254.d002523 ha hb).ne'



theorem d007774 {alpha beta : ℝ} (ha : 0 < alpha) (hb : 0 < beta)
    (e : ℝ) :
    _root_.GD.N0232.N0720.N1254.d002545 alpha beta * _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e 0 0 +
      _root_.GD.N0232.N0720.N1254.d002546 alpha beta * deriv (fun s => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e s 0) 0 +
      _root_.GD.N0232.N0720.N1254.d002547 alpha beta * deriv (deriv (fun s => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e s 0)) 0 +
      _root_.GD.N0232.N0720.N1254.d002548 alpha beta *
        deriv (deriv (deriv (fun s => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e s 0))) 0 +
      _root_.GD.N0232.N0720.N1254.d002549 alpha beta * deriv (fun t => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e 0 t) 0 +
      _root_.GD.N0232.N0720.N1254.d002550 alpha beta *
        deriv (fun s => deriv (fun t => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e s t) 0) 0 =
      (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta) := by
  obtain ⟨h0, h1, h2, h3, ht, hst⟩ := _root_.GD.N0106.N0428.N0766.N1692.d007773 ha hb e
  rw [h0, h1, h2, h3, ht, hst]
  exact _root_.GD.N0232.N0720.N1254.d002553 ha hb e _

end N1692
end
end GD.N0106.N0428.N0766

#print axioms _root_.GD.N0106.N0428.N0766.N1692.d007773
#print axioms _root_.GD.N0106.N0428.N0766.N1692.d007774
