import GD.Module0781
import GD.Module0785


















open Filter Set

namespace GD
namespace N0232
namespace N0719
namespace N0848

noncomputable section

open _root_.GD.N0232.N0719.N0847
open _root_.GD.N0232.N0719.N0846
open _root_.GD.N0232.N0719.N0824
open _root_.GD.N0232.N0719.N0845
open _root_.GD.N0232.N0719.N0820
open _root_.GD.N0232.N0719.N0817


def d012022
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) : Prop :=
  ∃ z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes,
    3 ≤ z.1.active.card ∧ z.1.active.card < k




structure d012023
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) where
  witness : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes
  fullSupport : witness.1.active = Finset.univ
  normalizedBaseConverges :
    Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k)
        (witness.1.thetaSeq n))
      atTop (nhds (_root_.GD.N0232.N0719.N0817.d011944 witness fullSupport))


def d012024
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) : Prop :=
  Nonempty (_root_.GD.N0232.N0719.N0848.d012023 k sizes hk hsizes)



theorem d012025
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes)
    (hfull : z.1.active = Finset.univ) :
    _root_.GD.N0232.N0719.N0848.d012024 k sizes hk hsizes := by
  exact ⟨⟨z, hfull,
    _root_.GD.N0232.N0719.N0817.d011950 z hfull⟩⟩







theorem d012026
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0846.d011894 k sizes hk hsizes ↔
      _root_.GD.N0232.N0719.N0848.d012022
          k sizes hk hsizes ∨
        _root_.GD.N0232.N0719.N0848.d012024
          k sizes hk hsizes := by
  constructor
  · rintro ⟨z, hthree⟩
    by_cases hproper : z.1.active.card < k
    · exact Or.inl ⟨z, hthree, hproper⟩
    · right
      have hle : z.1.active.card ≤ k := by
        simpa using Finset.card_le_univ z.1.active
      have hcard : z.1.active.card = k := by omega
      have hfull : z.1.active = Finset.univ :=
        Finset.eq_univ_of_card z.1.active (by simpa using hcard)
      exact _root_.GD.N0232.N0719.N0848.d012025 z hfull
  · rintro (hproper | hfull)
    · obtain ⟨z, hthree, _hproper⟩ := hproper
      exact ⟨z, hthree⟩
    · obtain ⟨z⟩ := hfull
      refine ⟨z.witness, ?_⟩
      rw [z.fullSupport]
      simpa using hk










theorem d012027
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0847.d011875 k sizes ∨
      _root_.GD.N0232.N0719.N0846.d011893 k sizes hk hsizes ∨
      _root_.GD.N0232.N0719.N0848.d012022
        k sizes hk hsizes ∨
      _root_.GD.N0232.N0719.N0848.d012024
        k sizes hk hsizes := by
  rcases _root_.GD.N0232.N0719.N0846.d011896
      k sizes hk hsizes with hterminal | hlow | hinterior
  · exact Or.inl hterminal
  · exact Or.inr (Or.inl hlow)
  · rcases
      (_root_.GD.N0232.N0719.N0848.d012026
        k sizes hk hsizes).1 hinterior with hproper | hfull
    · exact Or.inr (Or.inr (Or.inl hproper))
    · exact Or.inr (Or.inr (Or.inr hfull))
















theorem d012028
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0847.d011875 k sizes ∨
      (_root_.GD.N0232.N0719.N0824.d011722 k sizes hk hsizes ∧
        (_root_.GD.N0232.N0719.N0846.d011893 k sizes hk hsizes ∨
          _root_.GD.N0232.N0719.N0848.d012022
            k sizes hk hsizes ∨
          _root_.GD.N0232.N0719.N0848.d012024
            k sizes hk hsizes)) := by
  rcases _root_.GD.N0232.N0719.N0847.d011877
      k sizes hk hsizes with hterminal | hescape
  · exact Or.inl hterminal
  · right
    refine ⟨hescape, ?_⟩
    rcases _root_.GD.N0232.N0719.N0846.d011895
        k sizes hk hsizes hescape with hlow | hinterior
    · exact Or.inl hlow
    · rcases
        (_root_.GD.N0232.N0719.N0848.d012026
          k sizes hk hsizes).1 hinterior with hproper | hfull
      · exact Or.inr (Or.inl hproper)
      · exact Or.inr (Or.inr hfull)



theorem d012029
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hnoTerminal : ¬ _root_.GD.N0232.N0719.N0847.d011875 k sizes) :
    _root_.GD.N0232.N0719.N0846.d011893 k sizes hk hsizes ∨
      _root_.GD.N0232.N0719.N0848.d012022
        k sizes hk hsizes ∨
      _root_.GD.N0232.N0719.N0848.d012024
        k sizes hk hsizes := by
  rcases _root_.GD.N0232.N0719.N0848.d012027
      k sizes hk hsizes with hterminal | hlow | hproper | hfull
  · exact False.elim (hnoTerminal hterminal)
  · exact Or.inl hlow
  · exact Or.inr (Or.inl hproper)
  · exact Or.inr (Or.inr hfull)




theorem d012030
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hnoTerminal : ¬ _root_.GD.N0232.N0719.N0847.d011875 k sizes) :
    _root_.GD.N0232.N0719.N0824.d011722 k sizes hk hsizes ∧
      (_root_.GD.N0232.N0719.N0846.d011893 k sizes hk hsizes ∨
        _root_.GD.N0232.N0719.N0848.d012022
          k sizes hk hsizes ∨
        _root_.GD.N0232.N0719.N0848.d012024
          k sizes hk hsizes) := by
  rcases _root_.GD.N0232.N0719.N0848.d012028
      k sizes hk hsizes with hterminal | hescape
  · exact False.elim (hnoTerminal hterminal)
  · exact hescape



theorem d012031
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hnoLow :
      ¬ _root_.GD.N0232.N0719.N0846.d011893 k sizes hk hsizes)
    (hnoProper :
      ¬ _root_.GD.N0232.N0719.N0848.d012022
        k sizes hk hsizes)
    (hnoFull :
      ¬ _root_.GD.N0232.N0719.N0848.d012024
        k sizes hk hsizes) :
    _root_.GD.N0232.N0719.N0847.d011875 k sizes := by
  rcases _root_.GD.N0232.N0719.N0848.d012027
      k sizes hk hsizes with hterminal | hlow | hproper | hfull
  · exact hterminal
  · exact False.elim (hnoLow hlow)
  · exact False.elim (hnoProper hproper)
  · exact False.elim (hnoFull hfull)

end

end N0848
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0848.d012026
#print axioms _root_.GD.N0232.N0719.N0848.d012027
#print axioms _root_.GD.N0232.N0719.N0848.d012028
#print axioms _root_.GD.N0232.N0719.N0848.d012029
#print axioms _root_.GD.N0232.N0719.N0848.d012030
#print axioms _root_.GD.N0232.N0719.N0848.d012031
