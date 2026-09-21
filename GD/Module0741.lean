import GD.Module0063
import GD.Module0730
import GD.Module0736



















open Set

namespace GD
namespace N0232
namespace N0719
namespace N0813

noncomputable section

open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0816
open _root_.GD.N0230.N0566
open _root_.GD.N0230.N0596



def d011058
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    Set (_root_.GD.N0232.N0719.N0816.d010976 k sizes) :=
  toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes) ''
    _root_.GD.N0232.N0719.N0858.d010858 k sizes hk hsizes



theorem d011059
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes).Nonempty := by
  exact (_root_.GD.N0232.N0719.N0858.d010860 k sizes hk hsizes).image
    (toWeakSpace ℝ (_root_.GD.N0232.N0719.N0816.d010975 k sizes))



theorem d011060
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    IsCompact (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes) := by
  exact _root_.GD.N0232.N0719.N0858.d011035 k sizes hk hsizes




theorem d011061
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k) :
    ∃ p : _root_.GD.N0232.N0719.N0816.d010976 k sizes,
      p ∈ _root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes ∧
      _root_.GD.N0230.N0596.d000730
        (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
        (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes) p := by
  obtain ⟨p, _hpfaces, hlex⟩ :=
    _root_.GD.N0230.N0566.d000757
      (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
      (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0813.d011059 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0813.d011060 k sizes hk hsizes)
      (_root_.GD.N0232.N0719.N0816.d010984
        k sizes hk hsizes stage)
  exact ⟨p, hlex.1, hlex⟩



theorem d011062
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (stage : ℕ → _root_.GD.N0232.N0719.N0816.d010982 k) :
    ∀ n,
      (_root_.GD.N0230.N0566.d000753
          (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
          (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes) n).Nonempty ∧
      IsCompact
        (_root_.GD.N0230.N0566.d000753
          (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
          (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes) n) ∧
      IsClosed
        (_root_.GD.N0230.N0566.d000753
          (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
          (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes) n) := by
  exact _root_.GD.N0230.N0566.d000758
    (_root_.GD.N0232.N0719.N0816.d010983 k sizes hk hsizes stage)
    (_root_.GD.N0232.N0719.N0813.d011058 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0813.d011059 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0813.d011060 k sizes hk hsizes)
    (_root_.GD.N0232.N0719.N0816.d010984
      k sizes hk hsizes stage)

end

end N0813
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0813.d011059
#print axioms _root_.GD.N0232.N0719.N0813.d011060
#print axioms _root_.GD.N0232.N0719.N0813.d011061
#print axioms _root_.GD.N0232.N0719.N0813.d011062
