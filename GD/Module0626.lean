import GD.Module0624












namespace GD
namespace N0232
namespace N0719
namespace N0901

noncomputable section

open _root_.GD.N0232.N0719.N0900


theorem d009160
    {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) (j : Fin k) :
    _root_.GD.N0232.N0719.N0900.d009106 s j ≤ _root_.GD.N0232.N0719.N0900.d009107 s := by
  unfold _root_.GD.N0232.N0719.N0900.d009107
  exact Finset.single_le_sum
    (fun i _ ↦ _root_.GD.N0232.N0719.N0900.d009129 s i) (Finset.mem_univ j)





theorem d009161
    {k : ℕ} (s : _root_.GD.N0232.N0719.N0900.d009096 k) (i j : Fin k)
    (hi : 0 < s.meanVariance i) (hj : 0 < s.meanVariance j) :
    _root_.GD.N0232.N0719.N0900.d009108 s i ≤ s.meanVariance j / s.meanVariance i := by
  have hrawj : 0 < _root_.GD.N0232.N0719.N0900.d009106 s j := by
    rw [_root_.GD.N0232.N0719.N0900.d009106, _root_.GD.N0232.N0719.N0900.d009127 hj]
    exact inv_pos.mpr hj
  have htotal : 0 < _root_.GD.N0232.N0719.N0900.d009107 s :=
    hrawj.trans_le (_root_.GD.N0232.N0719.N0901.d009160 s j)
  have htotalNe : _root_.GD.N0232.N0719.N0900.d009107 s ≠ 0 := htotal.ne'
  rw [_root_.GD.N0232.N0719.N0900.d009108, if_neg htotalNe,
    _root_.GD.N0232.N0719.N0900.d009106, _root_.GD.N0232.N0719.N0900.d009127 hi]
  apply (div_le_iff₀ htotal).2
  calc
    (s.meanVariance i)⁻¹ =
        (s.meanVariance j / s.meanVariance i) *
          (s.meanVariance j)⁻¹ := by
      field_simp [hi.ne', hj.ne']
    _ ≤ (s.meanVariance j / s.meanVariance i) *
          _root_.GD.N0232.N0719.N0900.d009107 s := by
      exact mul_le_mul_of_nonneg_left
        (by
          rw [← _root_.GD.N0232.N0719.N0900.d009127 hj]
          exact _root_.GD.N0232.N0719.N0901.d009160 s j)
        (div_nonneg hj.le hi.le)


theorem d009162
    {k : ℕ} (hk : 0 < k) (s : _root_.GD.N0232.N0719.N0900.d009096 k) (i j : Fin k)
    (hi : 0 < s.meanVariance i) (hj : 0 < s.meanVariance j) :
    _root_.GD.N0232.N0719.N0900.d009108 s i ^ 2 ≤
      (s.meanVariance j / s.meanVariance i) ^ 2 := by
  exact (sq_le_sq₀ (_root_.GD.N0232.N0719.N0900.d009132 hk s i)
    (div_nonneg hj.le hi.le)).2
      (_root_.GD.N0232.N0719.N0901.d009161 s i j hi hj)

end

end N0901
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0901.d009161
#print axioms _root_.GD.N0232.N0719.N0901.d009162
