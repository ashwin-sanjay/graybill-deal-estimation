import GD.Module0091
import GD.Module0912






















open Set MeasureTheory
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1080

noncomputable section

open _root_.GD.N0230.N0633
open _root_.GD.N0230.N0602

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)



noncomputable def d014248 : ℝ :=
  ‖_root_.GD.N0232.N0720.N1080.d014181 m n hm hn‖



theorem d014249
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hd : d ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    ‖d‖ ^ 2 ≤ ‖_root_.GD.N0232.N0720.N1080.d014181 m n hm hn‖ ^ 2 := by
  have href := hd _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
  simp only [zero_sub, norm_neg] at href
  exact
    (ENNReal.ofReal_le_ofReal_iff
      (sq_nonneg ‖_root_.GD.N0232.N0720.N1080.d014181 m n hm hn‖)).mp href


theorem d014250
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hd : d ∈ _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) :
    ‖d‖ ≤ _root_.GD.N0232.N0720.N1080.d014248 m n hm hn := by
  exact
    (sq_le_sq₀ (norm_nonneg d) (norm_nonneg (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn))).1
      (_root_.GD.N0232.N0720.N1080.d014249 m n hm hn d hd)




theorem d014251 :
    IsCompact
      (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) ''
        _root_.GD.N0232.N0720.N1080.d014187 m n hm hn) := by
  exact _root_.GD.N0230.N0633.d001201
    (_root_.GD.N0232.N0720.N1080.d014248 m n hm hn)
    (_root_.GD.N0232.N0720.N1080.d014189 m n hm hn)
    (_root_.GD.N0232.N0720.N1080.d014188 m n hm hn)
    (_root_.GD.N0232.N0720.N1080.d014250 m n hm hn)

end
end N1080
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1080.d014249
#print axioms _root_.GD.N0232.N0720.N1080.d014250
#print axioms _root_.GD.N0232.N0720.N1080.d014251
