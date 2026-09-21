import GD.Module0515

set_option autoImplicit false
set_option warningAsError true

namespace GD.N0106.N0428.N0766
noncomputable section





theorem d007764 (c d h a r : ℝ) (hc : c ≠ 0) :
    _root_.GD.N0106.N0428.N0766.d007748 c d h a r 0 0 = c ^ (-r) * a ∧
    _root_.GD.N0106.N0428.N0766.d007749 c d h a r 0 0 = c ^ (-r) * (1 - r * a * d / c) ∧
    _root_.GD.N0106.N0428.N0766.d007750 c d h a r 0 0 =
      c ^ (-r) * (-2 * r * d / c + r * (r + 1) * a * d ^ 2 / c ^ 2) ∧
    _root_.GD.N0106.N0428.N0766.d007751 c d h a r 0 0 = c ^ (-r) *
      (3 * r * (r + 1) * d ^ 2 / c ^ 2 -
       r * (r + 1) * (r + 2) * a * d ^ 3 / c ^ 3) ∧
    _root_.GD.N0106.N0428.N0766.d007752 c d h a r 0 0 = c ^ (-r) * (-r * a * h / c) ∧
    _root_.GD.N0106.N0428.N0766.d007753 c d h a r 0 0 =
      c ^ (-r) * (-r * h / c + r * (r + 1) * a * d * h / c ^ 2) := by
  have h1 := Real.rpow_sub_one hc (-r)
  have h2 : c ^ (-r - 2) = c ^ (-r) / c ^ 2 := by
    simpa only [Nat.cast_ofNat] using Real.rpow_sub_natCast hc (-r) 2
  have h3 : c ^ (-r - 3) = c ^ (-r) / c ^ 3 := by
    simpa only [Nat.cast_ofNat] using Real.rpow_sub_natCast hc (-r) 3
  simp only [_root_.GD.N0106.N0428.N0766.d007748, _root_.GD.N0106.N0428.N0766.d007749, _root_.GD.N0106.N0428.N0766.d007750, _root_.GD.N0106.N0428.N0766.d007751, _root_.GD.N0106.N0428.N0766.d007752, _root_.GD.N0106.N0428.N0766.d007753, _root_.GD.N0106.N0428.N0766.d007747, mul_zero, add_zero,
    h1, h2, h3]
  exact ⟨by ring, by ring, by ring, by ring, by ring, by ring⟩

end
end GD.N0106.N0428.N0766

#print axioms _root_.GD.N0106.N0428.N0766.d007764
