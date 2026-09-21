import GD.Module1823

set_option autoImplicit false

open Set

namespace GD.N0236.N0745

variable {X : Type*}

def d030157 (A : ℝ → Set X) (a : ℝ) : Set X :=
  {x | ∀ b ∈ Ioo (0 : ℝ) a, x ∈ A b}

theorem d030158 (A : ℝ → Set X) : Antitone (_root_.GD.N0236.N0745.d030157 A) := by
  intro a b hab x hx c hc
  exact hx c ⟨hc.1, hc.2.trans_le hab⟩

theorem d030159 {A B : ℝ → Set X} (h : ∀ a, A a ⊆ B a) :
    ∀ a, _root_.GD.N0236.N0745.d030157 A a ⊆ _root_.GD.N0236.N0745.d030157 B a := by
  intro a x hx b hb
  exact h b (hx b hb)

theorem d030160 (A : ℝ → Set X) :
    _root_.GD.N0236.N0745.d030157 (_root_.GD.N0236.N0745.d030157 A) = _root_.GD.N0236.N0745.d030157 A := by
  funext a
  ext x
  constructor
  · intro hx b hb
    let c := (a+b)/2
    have hc : c ∈ Ioo (0 : ℝ) a := by
      dsimp [c]; constructor <;> linarith [hb.1,hb.2]
    have hbc : b ∈ Ioo (0 : ℝ) c := by
      dsimp [c]; constructor <;> linarith [hb.1,hb.2]
    exact hx c hc b hbc
  · intro hx b hb c hc
    exact hx c ⟨hc.1,hc.2.trans hb.2⟩

theorem d030161 {A : ℝ → Set X} (hA : _root_.GD.N0236.N0745.d030147 A)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) : A a ⊆ _root_.GD.N0236.N0745.d030157 A a := by
  intro x hx b hb
  exact hA b ⟨hb.1,hb.2.trans ha.2⟩ a ha hb.2.le hx

theorem d030162 {A B : ℝ → Set X}
    (hAB : ∀ a, A a ⊆ B a) (hB : _root_.GD.N0236.N0745.d030157 B = B) :
    ∀ a, _root_.GD.N0236.N0745.d030157 A a ⊆ B a := by
  intro a
  rw [← hB]
  exact _root_.GD.N0236.N0745.d030159 hAB a

theorem d030163 {A : ℝ → Set X} (hA : _root_.GD.N0236.N0745.d030147 A)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0236.N0745.d030157 A a = {x | a ≤ _root_.GD.N0236.N0745.d030146 A x} := by
  ext x
  exact (_root_.GD.N0236.N0745.d030154 hA ha).symm

#print axioms _root_.GD.N0236.N0745.d030160
#print axioms _root_.GD.N0236.N0745.d030162
#print axioms _root_.GD.N0236.N0745.d030163

end GD.N0236.N0745
