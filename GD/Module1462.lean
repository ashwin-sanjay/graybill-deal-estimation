import GD.Module1375
import GD.Module1461
import GD.Module0983

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0067
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1226


theorem d023072 : _root_.GD.N0232.N0720.N1256.d015549 2 4 = ⊤ := by
  apply _root_.GD.N0045.d023070
    2 4 (by decide) (by decide)
  exact _root_.GD.N0055.d022141


theorem d023073
    (d : _root_.GD.N0232.N0720.N1080.d014170 2 4 → ℝ) (hd : Measurable d) (C : ℝ) (hC : 0 ≤ C) :
    ¬ (∀ θ, _root_.GD.N0232.N0720.N1080.d014197 2 4 θ d ≤ ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 2 4 θ)) := by
  intro hcap
  obtain ⟨g, hg, hb, hc⟩ := _root_.GD.N0045.d023068
    2 4 (by decide) (by decide) C hC d hd hcap
  exact _root_.GD.N0055.d022141 g hg hb (C - 1) hc


theorem d023074 :
    ∃ d ∈ _root_.GD.N0232.N0720.N1256.d015551 2 4, _root_.GD.N0232.N0720.N1226.d015577 2 4 d := by
  obtain ⟨d, hd⟩ := _root_.GD.N0232.N0720.N1226.d015586
    2 4 (by decide) (by decide) _root_.GD.N0067.d023072
  exact ⟨d, _root_.GD.N0232.N0720.N1226.d015576.d015579 2 4 hd.1, hd⟩

end
end GD.N0067

#print axioms _root_.GD.N0067.d023072
#print axioms _root_.GD.N0067.d023073
#print axioms _root_.GD.N0067.d023074
