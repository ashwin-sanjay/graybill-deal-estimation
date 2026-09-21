import GD.Module0050
import GD.Module0975






















open Set

namespace GD
namespace N0232
namespace N0720
namespace N1205

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0652
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1100

variable (m n : ℕ)



theorem d015505
    {s t : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hdesc : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s t) :
    _root_.GD.N0232.N0720.N1159.d014630 m n t ⊆ _root_.GD.N0232.N0720.N1159.d014630 m n s := by
  intro d hd
  exact _root_.GD.N0230.N0608.d000677 (_root_.GD.N0232.N0720.N1080.d014182 m n) hd hdesc





theorem d015506
    (s t : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdesc : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value t.value)
    (hradial : ‖t.value‖ ≤ ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖) :
    _root_.GD.N0232.N0720.N1159.d014633 m n s.value =
        _root_.GD.N0232.N0720.N1159.d014633 m n t.value ∧
      _root_.GD.N0232.N0720.N1159.d014633 m n t.value = t.value ∧
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) t.value := by
  have hrigid := _root_.GD.N0230.N0652.d000635
    (_root_.GD.N0232.N0720.N1205.d015505 m n hdesc)
    (_root_.GD.N0232.N0720.N1100.d015487 m n s.value)
    (_root_.GD.N0232.N0720.N1100.d015487 m n t.value)
    (_root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) t.value)
    hradial
  refine ⟨hrigid.1, hrigid.2, ?_⟩
  exact (_root_.GD.N0232.N0720.N1159.d014635 m n t.value).1 hrigid.2






theorem d015507
    (s t : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdesc : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value t.value)
    (r : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    {B ε δ : ℝ}
    (hnear : Metric.infDist r (_root_.GD.N0232.N0720.N1159.d014630 m n t.value) ≤ δ)
    (hδ : 0 ≤ δ)
    (hpB : ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ≤ B)
    (hradial : ‖r‖ ^ 2 ≤
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 + ε) :
    ‖_root_.GD.N0232.N0720.N1159.d014633 m n t.value - r‖ ≤
      δ + Real.sqrt
        (ε + 2 * Real.sqrt (B ^ 2 + ε) * δ + δ ^ 2) := by
  exact _root_.GD.N0230.N0652.d000638
    (_root_.GD.N0232.N0720.N1205.d015505 m n hdesc)
    (_root_.GD.N0232.N0720.N1100.d015487 m n s.value)
    (_root_.GD.N0232.N0720.N1100.d015487 m n t.value)
    hnear hδ hpB hradial

end
end N1205
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1205.d015505
#print axioms _root_.GD.N0232.N0720.N1205.d015506
#print axioms _root_.GD.N0232.N0720.N1205.d015507
