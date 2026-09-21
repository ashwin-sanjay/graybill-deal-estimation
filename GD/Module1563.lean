import GD.Module1562





set_option autoImplicit false
set_option warningAsError true

namespace GD.N0106.N0428.N0766.N1692
noncomputable section

open _root_.GD.N0232.N0720.N1254


theorem d024112 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (e : ℝ) :
    (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (_root_.GD.N0232.N0720.N1254.d002513 alpha beta) * _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e 0 0 =
        _root_.GD.N0232.N0720.N1254.d002537 alpha beta e ∧
      (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (_root_.GD.N0232.N0720.N1254.d002513 alpha beta) *
        deriv (fun s => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e s 0) 0 =
          _root_.GD.N0232.N0720.N1254.d002538 alpha beta e ∧
      (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (_root_.GD.N0232.N0720.N1254.d002513 alpha beta) *
        deriv (deriv (fun s => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e s 0)) 0 =
          _root_.GD.N0232.N0720.N1254.d002539 alpha beta e ∧
      (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (_root_.GD.N0232.N0720.N1254.d002513 alpha beta) *
        deriv (deriv (deriv (fun s => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e s 0))) 0 =
          _root_.GD.N0232.N0720.N1254.d002541 alpha beta e ∧
      (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (_root_.GD.N0232.N0720.N1254.d002513 alpha beta) *
        deriv (fun t => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e 0 t) 0 =
          _root_.GD.N0232.N0720.N1254.d002540 alpha beta e ∧
      (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (_root_.GD.N0232.N0720.N1254.d002513 alpha beta) *
        deriv (fun s => deriv (fun t => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e s t) 0) 0 =
          _root_.GD.N0232.N0720.N1254.d002542 alpha beta e := by
  obtain ⟨h0, h1, h2, h3, ht, hst⟩ := _root_.GD.N0106.N0428.N0766.N1692.d007773 ha hb e
  rw [h0, h1, h2, h3, ht, hst]
  have hcancel : (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (_root_.GD.N0232.N0720.N1254.d002513 alpha beta) *
      (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta) = 1 := by
    rw [← Real.rpow_add (_root_.GD.N0232.N0720.N1254.d002523 ha hb), add_neg_cancel, Real.rpow_zero]
  simp only [← mul_assoc, hcancel, one_mul, and_self]



theorem d024113 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (e : ℝ) :
    let c := _root_.GD.N0232.N0720.N1254.d002512 alpha beta
    let r := _root_.GD.N0232.N0720.N1254.d002513 alpha beta
    let a := _root_.GD.N0232.N0720.N1254.d002515 alpha beta e
    let x := _root_.GD.N0232.N0720.N1254.d002516 alpha beta e / c
    let z := _root_.GD.N0232.N0720.N1254.d002517 e / c
    c ^ r * _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e 0 0 = a ∧
      c ^ r * deriv (fun s => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e s 0) 0 = 1 - r * a * x ∧
      c ^ r * deriv (deriv (fun s => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e s 0)) 0 =
        -2 * r * x + r * (r + 1) * a * x ^ 2 ∧
      c ^ r * deriv (deriv (deriv (fun s => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e s 0))) 0 =
        3 * r * (r + 1) * x ^ 2 - r * (r + 1) * (r + 2) * a * x ^ 3 ∧
      c ^ r * deriv (fun t => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e 0 t) 0 = -r * a * z ∧
      c ^ r * deriv (fun s => deriv (fun t => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e s t) 0) 0 =
        r * z * ((r + 1) * a * x - 1) := by
  dsimp only
  obtain ⟨h0, h1, h2, h3, ht, hst⟩ := _root_.GD.N0106.N0428.N0766.N1692.d024112 ha hb e
  rw [h0, h1, h2, h3, ht, hst]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    dsimp [_root_.GD.N0232.N0720.N1254.d002537, _root_.GD.N0232.N0720.N1254.d002538,
      _root_.GD.N0232.N0720.N1254.d002539,
      _root_.GD.N0232.N0720.N1254.d002541,
      _root_.GD.N0232.N0720.N1254.d002540,
      _root_.GD.N0232.N0720.N1254.d002542] <;> ring



theorem d024114 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (e s t : ℝ) :
    _root_.GD.N0106.N0428.N0766.N1692.d007772 beta alpha (1 - e) (-s) t = -_root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e s t := by
  obtain ⟨_, _, hc, hr, hA, hD, hH⟩ :=
    _root_.GD.N0232.N0720.N1254.d002583 alpha beta e (_root_.GD.N0232.N0720.N1254.d002522 ha hb).ne'
  unfold _root_.GD.N0106.N0428.N0766.N1692.d007772 _root_.GD.N0106.N0428.N0766.d007748 _root_.GD.N0106.N0428.N0766.d007747
  rw [hc, hr, hA, hD, hH]
  rw [show _root_.GD.N0232.N0720.N1254.d002512 alpha beta + -_root_.GD.N0232.N0720.N1254.d002516 alpha beta e * -s + _root_.GD.N0232.N0720.N1254.d002517 e * t =
      _root_.GD.N0232.N0720.N1254.d002512 alpha beta + _root_.GD.N0232.N0720.N1254.d002516 alpha beta e * s + _root_.GD.N0232.N0720.N1254.d002517 e * t by ring]
  ring

end
end GD.N0106.N0428.N0766.N1692

#print axioms _root_.GD.N0106.N0428.N0766.N1692.d024114
#print axioms _root_.GD.N0106.N0428.N0766.N1692.d024112
#print axioms _root_.GD.N0106.N0428.N0766.N1692.d024113
