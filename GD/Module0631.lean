import GD.Module0630










open MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0719
namespace N0804

noncomputable section

open _root_.GD.N0232.N0719.N0900



theorem d009189
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i)
    (shift location : ℝ) (dilation : ℝ) (hdilation : dilation ≠ 0)
    (scales : Fin k → ℝ) :
    _root_.GD.N0141.d006684
        (_root_.GD.N0232.N0719.d009176 k sizes
          (shift + dilation * location)
          (fun i ↦ dilation * scales i))
        (fun omega ↦
          _root_.GD.N0232.N0719.N0900.d009111 k sizes omega - (shift + dilation * location)) =
      dilation ^ 2 *
        _root_.GD.N0141.d006684
          (_root_.GD.N0232.N0719.d009176 k sizes location scales)
          (fun omega ↦ _root_.GD.N0232.N0719.N0900.d009111 k sizes omega - location) := by
  have hmap := _root_.GD.N0232.N0719.d009188
    k sizes shift dilation location scales
  unfold _root_.GD.N0141.d006684
  rw [← hmap]
  rw [integral_map_of_stronglyMeasurable
    (μ := _root_.GD.N0232.N0719.d009176 k sizes location scales)
    (φ := _root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation)
    (f := fun omega ↦
      (_root_.GD.N0232.N0719.N0900.d009111 k sizes omega -
        (shift + dilation * location)) ^ 2)
    (_root_.GD.N0232.N0719.N0900.d009112 k sizes shift dilation)
    (((_root_.GD.N0232.N0719.N0900.d009122 k sizes).sub measurable_const).pow_const 2
      |>.stronglyMeasurable)]
  calc
    (∫ omega,
        (_root_.GD.N0232.N0719.N0900.d009111 k sizes
            (_root_.GD.N0232.N0719.N0900.d009095 k sizes shift dilation omega) -
          (shift + dilation * location)) ^ 2
        ∂_root_.GD.N0232.N0719.d009176 k sizes location scales) =
      ∫ omega,
        dilation ^ 2 * (_root_.GD.N0232.N0719.N0900.d009111 k sizes omega - location) ^ 2
        ∂_root_.GD.N0232.N0719.d009176 k sizes location scales := by
          apply integral_congr_ae
          filter_upwards [] with omega
          rw [_root_.GD.N0232.N0719.N0900.d009146
            hk hsizes shift hdilation omega]
          ring
    _ = dilation ^ 2 *
        ∫ omega, (_root_.GD.N0232.N0719.N0900.d009111 k sizes omega - location) ^ 2
          ∂_root_.GD.N0232.N0719.d009176 k sizes location scales := by
      rw [integral_const_mul]

end

end N0804
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0804.d009189
