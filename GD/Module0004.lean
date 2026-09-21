import Mathlib.Data.Real.Basic




















namespace GD
namespace N0230
namespace N0556

variable {Θ Rule : Type*}


def d000028 (risk : Θ → Rule → ℝ) (e d : Rule) : Prop :=
  ∀ θ, risk θ e ≤ risk θ d





def d000029 (risk : Θ → Rule → ℝ) (e d : Rule) : Prop :=
  _root_.GD.N0230.N0556.d000028 risk e d ∧ ∃ θ, risk θ e < risk θ d


def d000030 (risk : Θ → Rule → ℝ) (bar d : Rule) : Prop :=
  _root_.GD.N0230.N0556.d000028 risk d bar


def d000031 (risk : Θ → Rule → ℝ) (d : Rule) : Prop :=
  ¬ ∃ e, _root_.GD.N0230.N0556.d000029 risk e d

theorem d000032
    (risk : Θ → Rule → ℝ) (d : Rule) :
    _root_.GD.N0230.N0556.d000028 risk d d := by
  intro θ
  exact le_rfl

theorem d000033
    (risk : Θ → Rule → ℝ) {d₁ d₂ d₃ : Rule}
    (h₁₂ : _root_.GD.N0230.N0556.d000028 risk d₁ d₂)
    (h₂₃ : _root_.GD.N0230.N0556.d000028 risk d₂ d₃) :
    _root_.GD.N0230.N0556.d000028 risk d₁ d₃ := by
  intro θ
  exact le_trans (h₁₂ θ) (h₂₃ θ)


theorem d000034
    (risk : Θ → Rule → ℝ) {bar d e : Rule}
    (hd : _root_.GD.N0230.N0556.d000030 risk bar d)
    (hed : _root_.GD.N0230.N0556.d000028 risk e d) :
    _root_.GD.N0230.N0556.d000030 risk bar e :=
  _root_.GD.N0230.N0556.d000033 risk hed hd








theorem d000035
    (risk : Θ → Rule → ℝ)
    (objective : Rule → ℝ)
    (bar star : Rule)
    (hstar : _root_.GD.N0230.N0556.d000030 risk bar star)
    (hmin : ∀ d, _root_.GD.N0230.N0556.d000030 risk bar d → objective star ≤ objective d)
    (hdecrease :
      ∀ e, _root_.GD.N0230.N0556.d000029 risk e star → objective e < objective star) :
    _root_.GD.N0230.N0556.d000031 risk star := by
  rintro ⟨e, he⟩
  have heBelow : _root_.GD.N0230.N0556.d000030 risk bar e :=
    _root_.GD.N0230.N0556.d000034 risk hstar he.1
  exact (not_lt_of_ge (hmin e heBelow)) (hdecrease e he)









theorem d000036
    (risk : Θ → Rule → ℝ)
    (objective : Rule → ℝ)
    (bar star : Rule)
    (hstar : _root_.GD.N0230.N0556.d000030 risk bar star)
    (hmin : ∀ d, _root_.GD.N0230.N0556.d000030 risk bar d → objective star ≤ objective d)
    (hstrictify :
      ∀ e, _root_.GD.N0230.N0556.d000029 risk e star →
        ∃ m, _root_.GD.N0230.N0556.d000028 risk m star ∧ objective m < objective star) :
    _root_.GD.N0230.N0556.d000031 risk star := by
  rintro ⟨e, he⟩
  obtain ⟨m, hmDom, hmObj⟩ := hstrictify e he
  have hmBelow : _root_.GD.N0230.N0556.d000030 risk bar m :=
    _root_.GD.N0230.N0556.d000034 risk hstar hmDom
  exact (not_lt_of_ge (hmin m hmBelow)) hmObj






theorem d000037
    (risk : Θ → Rule → ℝ)
    (θ₀ : Θ)
    (bar star : Rule)
    (hstar : _root_.GD.N0230.N0556.d000030 risk bar star)
    (hmin : ∀ d, _root_.GD.N0230.N0556.d000030 risk bar d → risk θ₀ star ≤ risk θ₀ d)
    (hstrictify :
      ∀ e, _root_.GD.N0230.N0556.d000029 risk e star →
        ∃ m, _root_.GD.N0230.N0556.d000028 risk m star ∧ risk θ₀ m < risk θ₀ star) :
    _root_.GD.N0230.N0556.d000031 risk star :=
  _root_.GD.N0230.N0556.d000036
    risk (risk θ₀) bar star hstar hmin hstrictify





theorem d000038
    (risk : Θ → Rule → ℝ)
    (equivariant : Rule → Prop)
    (bar : Rule) :
    (∃ d, equivariant d ∧ _root_.GD.N0230.N0556.d000030 risk bar d ∧ _root_.GD.N0230.N0556.d000031 risk d) ↔
      ¬ (∀ d, equivariant d → _root_.GD.N0230.N0556.d000030 risk bar d →
        ∃ e, _root_.GD.N0230.N0556.d000029 risk e d) := by
  classical
  constructor
  · rintro ⟨d, hdEq, hdBelow, hdAdm⟩ hall
    exact hdAdm (hall d hdEq hdBelow)
  · intro hnot
    by_contra hnone
    apply hnot
    intro d hdEq hdBelow
    by_contra hdom
    exact hnone ⟨d, hdEq, hdBelow, hdom⟩





theorem d000039
    {Correction Nuisance : Type*}
    (D : Correction → Nuisance → ℝ) :
    (∃ φ, ∀ q, D φ q < 0) ↔
      ¬ (∀ φ, ∃ q, 0 ≤ D φ q) := by
  classical
  simp only [not_forall, not_exists, not_le]

end N0556
end N0230
end GD
