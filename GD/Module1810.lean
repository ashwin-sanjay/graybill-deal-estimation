import GD.Module1808
import GD.Module1809

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace GD.N0005.N0249

open _root_.GD.N0228.N0547
open _root_.GD.N0228.N0547.N0793 _root_.GD.N0228.N0547.N0792
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0897
open _root_.GD.N0235.N0744
open _root_.GD.N0005.N0252 _root_.GD.N0005.N0250
open _root_.GD.N0005.N0251

noncomputable section

theorem d030040
    {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (muX muY : ℝ) {sigmaX sigmaY : ℝ}
    (hX : 0 < sigmaX) (hY : 0 < sigmaY) (nullContrast : ℝ) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ NoAtoms ν ∧
      (_root_.GD.N0232.N0719.N0897.d009332 2 (_root_.GD.N0228.N0547.N0793.d012954 r s) (_root_.GD.N0228.N0547.N0792.d012996 muX muY)
        (_root_.GD.N0228.N0547.N0793.d012955 sigmaX sigmaY)).map
          (_root_.GD.N0005.N0250.d030028 nullContrast ∘ _root_.GD.N0232.N0719.N0900.d009104 2 (_root_.GD.N0228.N0547.N0793.d012954 r s)) = ν ∧
      ∃ Q : ℝ → ℝ, ∀ p ∈ Ioo (0 : ℝ) 1, ν (Iic (Q p)) = ENNReal.ofReal p := by
  let rho := _root_.GD.N0228.N0547.N0793.d012978 r s sigmaX sigmaY
  let shift := _root_.GD.N0005.N0250.d030030 r s muX muY sigmaX sigmaY nullContrast
  have h0 : 0 < rho := _root_.GD.N0228.N0547.N0793.d012979 hX hY
  have h1 : rho < 1 := _root_.GD.N0228.N0547.N0793.d012980 hX hY
  refine ⟨_root_.GD.N0005.N0252.d030010 r s rho shift,
    _root_.GD.N0005.N0252.d030021 hr hs rho shift,
    _root_.GD.N0005.N0251.d030037 hr hs h0 h1 shift,
    _root_.GD.N0005.N0250.d030035 hr hs muX muY hX hY nullContrast,
    _root_.GD.N0235.N0744.d004268 (_root_.GD.N0005.N0252.d030010 r s rho shift), ?_⟩
  intro p hp
  exact _root_.GD.N0005.N0251.d030039 hr hs h0 h1 shift hp.1 hp.2

end
end GD.N0005.N0249

#print axioms _root_.GD.N0005.N0252.d030015
#print axioms _root_.GD.N0005.N0252.d030026
#print axioms _root_.GD.N0005.N0252.d030024
#print axioms _root_.GD.N0005.N0252.d030027
#print axioms _root_.GD.N0005.N0250.d030031
#print axioms _root_.GD.N0005.N0250.d030035
#print axioms _root_.GD.N0005.N0250.d030036
#print axioms _root_.GD.N0005.N0251.d030037
#print axioms _root_.GD.N0005.N0251.d030038
#print axioms _root_.GD.N0005.N0251.d030039
#print axioms _root_.GD.N0005.N0249.d030040
