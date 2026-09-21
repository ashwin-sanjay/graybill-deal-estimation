import GD.Module0080























open Set

namespace GD
namespace N0230
namespace N0697

open _root_.GD.N0230.N0556
open _root_.GD.N0230.N0630
open _root_.GD.N0230.N0682
open _root_.GD.N0230.N0695

variable {Θ Rule : Type*}








def d001075
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop) : Set Rule :=
  ⋂₀ {C : Set Rule | _root_.GD.N0230.N0695.d001055 risk safe C}









theorem d001076
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    (hsafe : _root_.GD.N0230.N0682.d000500 risk safe)
    (hminor : _root_.GD.N0230.N0695.d001056 risk safe) :
    _root_.GD.N0230.N0695.d001054 risk safe = _root_.GD.N0230.N0697.d001075 risk safe := by
  apply Set.Subset.antisymm
  · intro d hd
    rw [_root_.GD.N0230.N0697.d001075, Set.mem_sInter]
    intro C hC
    exact _root_.GD.N0230.N0695.d001061 risk safe C hC hd
  · intro d hd
    have hcomplete :
        _root_.GD.N0230.N0695.d001055 risk safe (_root_.GD.N0230.N0695.d001054 risk safe) :=
      _root_.GD.N0230.N0695.d001060 risk safe hsafe hminor
    exact (Set.mem_sInter.mp hd) (_root_.GD.N0230.N0695.d001054 risk safe) hcomplete









def d001077
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    (d : Rule) : Set Rule :=
  {t |
    safe t ∧
      _root_.GD.N0230.N0630.d000786 risk t ∧
      _root_.GD.N0230.N0556.d000028 risk t d}


theorem d001078
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    (d t : Rule) :
    t ∈ _root_.GD.N0230.N0697.d001077 risk safe d ↔
      safe t ∧
        _root_.GD.N0230.N0630.d000786 risk t ∧
        _root_.GD.N0230.N0556.d000028 risk t d :=
  Iff.rfl


theorem d001079
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    {d t : Rule}
    (ht : t ∈ _root_.GD.N0230.N0697.d001077 risk safe d) :
    safe t :=
  ht.1


theorem d001080
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    {d t : Rule}
    (ht : t ∈ _root_.GD.N0230.N0697.d001077 risk safe d) :
    _root_.GD.N0230.N0630.d000786 risk t :=
  ht.2.1


theorem d001081
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    {d t : Rule}
    (ht : t ∈ _root_.GD.N0230.N0697.d001077 risk safe d) :
    _root_.GD.N0230.N0556.d000028 risk t d :=
  ht.2.2


theorem d001082
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    (d : Rule) :
    _root_.GD.N0230.N0697.d001077 risk safe d ⊆
      _root_.GD.N0230.N0695.d001054 risk safe := by
  intro t ht
  exact ⟨ht.1, ht.2.1⟩





theorem d001083
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    (hsafe : _root_.GD.N0230.N0682.d000500 risk safe)
    (hminor : _root_.GD.N0230.N0695.d001056 risk safe)
    {d : Rule}
    (hd : safe d) :
    (_root_.GD.N0230.N0697.d001077 risk safe d).Nonempty := by
  obtain ⟨t, htTerminal, htd⟩ := hminor d hd
  have htSafe : safe t :=
    _root_.GD.N0230.N0695.d001059 risk safe hsafe hd htd
  exact ⟨t, htSafe, htTerminal, htd⟩








theorem d001084
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    {t : Rule}
    (htSafe : safe t)
    (htTerminal : _root_.GD.N0230.N0630.d000786 risk t) :
    _root_.GD.N0230.N0697.d001077 risk safe t = {t} := by
  ext a
  constructor
  · intro ha
    have hat : _root_.GD.N0230.N0556.d000028 risk a t := ha.2.2
    have hEq : a = t := htTerminal a hat
    exact Set.mem_singleton_iff.mpr hEq
  · intro ha
    have hEq : a = t := Set.mem_singleton_iff.mp ha
    subst a
    exact ⟨htSafe, htTerminal, _root_.GD.N0230.N0556.d000032 risk t⟩








theorem d001085
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    {e d : Rule}
    (hed : _root_.GD.N0230.N0556.d000028 risk e d) :
    _root_.GD.N0230.N0697.d001077 risk safe e ⊆
      _root_.GD.N0230.N0697.d001077 risk safe d := by
  intro t ht
  exact
    ⟨ht.1, ht.2.1,
      _root_.GD.N0230.N0556.d000033 risk ht.2.2 hed⟩

end N0697
end N0230
end GD
