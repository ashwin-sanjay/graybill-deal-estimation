import GD.Module0066
import GD.Module0040






















open Set

namespace GD
namespace N0230
namespace N0695

open _root_.GD.N0230.N0556
open _root_.GD.N0230.N0630
open _root_.GD.N0230.N0682

variable {Θ Rule : Type*}


def d001053 (risk : Θ → Rule → ℝ) : Set Rule :=
  {d | _root_.GD.N0230.N0630.d000786 risk d}


def d001054
    (risk : Θ → Rule → ℝ) (safe : Rule → Prop) : Set Rule :=
  {d | safe d ∧ _root_.GD.N0230.N0630.d000786 risk d}





def d001055
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    (C : Set Rule) : Prop :=
  (∀ ⦃c⦄, c ∈ C → safe c) ∧
    ∀ d, safe d → ∃ c, c ∈ C ∧ _root_.GD.N0230.N0556.d000028 risk c d







def d001056
    (risk : Θ → Rule → ℝ) (safe : Rule → Prop) : Prop :=
  ∀ d, safe d →
    ∃ a, _root_.GD.N0230.N0630.d000786 risk a ∧ _root_.GD.N0230.N0556.d000028 risk a d


def d001057
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    (C : Set Rule) : Prop :=
  _root_.GD.N0230.N0695.d001055 risk safe C ∧
    ∀ D : Set Rule, _root_.GD.N0230.N0695.d001055 risk safe D → C ⊆ D


theorem d001058
    (risk : Θ → Rule → ℝ) (bar : Rule) :
    _root_.GD.N0230.N0682.d000500 risk (_root_.GD.N0230.N0556.d000030 risk bar) := by
  intro d e hd hed
  exact _root_.GD.N0230.N0556.d000034 risk hd hed





theorem d001059
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    (hsafe : _root_.GD.N0230.N0682.d000500 risk safe)
    {d a : Rule}
    (hd : safe d)
    (had : _root_.GD.N0230.N0556.d000028 risk a d) :
    safe a :=
  hsafe hd had





theorem d001060
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    (hsafe : _root_.GD.N0230.N0682.d000500 risk safe)
    (hminor : _root_.GD.N0230.N0695.d001056 risk safe) :
    _root_.GD.N0230.N0695.d001055 risk safe (_root_.GD.N0230.N0695.d001054 risk safe) := by
  constructor
  · intro c hc
    exact hc.1
  · intro d hd
    obtain ⟨a, haTerminal, had⟩ := hminor d hd
    have haSafe : safe a :=
      _root_.GD.N0230.N0695.d001059 risk safe hsafe hd had
    exact ⟨a, ⟨haSafe, haTerminal⟩, had⟩








theorem d001061
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    (C : Set Rule)
    (hC : _root_.GD.N0230.N0695.d001055 risk safe C) :
    _root_.GD.N0230.N0695.d001054 risk safe ⊆ C := by
  intro a ha
  obtain ⟨c, hc, hca⟩ := hC.2 a ha.1
  have hEq : c = a := ha.2 c hca
  simpa [hEq] using hc




theorem d001062
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    (hsafe : _root_.GD.N0230.N0682.d000500 risk safe)
    (hminor : _root_.GD.N0230.N0695.d001056 risk safe) :
    _root_.GD.N0230.N0695.d001057
      risk safe (_root_.GD.N0230.N0695.d001054 risk safe) := by
  refine
    ⟨_root_.GD.N0230.N0695.d001060 risk safe hsafe hminor, ?_⟩
  intro C hC
  exact _root_.GD.N0230.N0695.d001061 risk safe C hC


theorem d001063
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    {C D : Set Rule}
    (hC : _root_.GD.N0230.N0695.d001057 risk safe C)
    (hD : _root_.GD.N0230.N0695.d001057 risk safe D) :
    C = D :=
  Set.Subset.antisymm (hC.2 D hD.1) (hD.2 C hC.1)





theorem d001064
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    (hsafe : _root_.GD.N0230.N0682.d000500 risk safe)
    (hminor : _root_.GD.N0230.N0695.d001056 risk safe)
    {C : Set Rule}
    (hC : _root_.GD.N0230.N0695.d001057 risk safe C) :
    C = _root_.GD.N0230.N0695.d001054 risk safe :=
  _root_.GD.N0230.N0695.d001063 risk safe hC
    (_root_.GD.N0230.N0695.d001062 risk safe hsafe hminor)


def d001065
    (risk : Θ → Rule → ℝ) (C : Set Rule) : Prop :=
  _root_.GD.N0230.N0695.d001055 risk (fun _ => True) C


def d001066 (risk : Θ → Rule → ℝ) : Prop :=
  ∀ d, ∃ a, _root_.GD.N0230.N0630.d000786 risk a ∧ _root_.GD.N0230.N0556.d000028 risk a d


def d001067
    (risk : Θ → Rule → ℝ) (C : Set Rule) : Prop :=
  _root_.GD.N0230.N0695.d001057 risk (fun _ => True) C


theorem d001068
    (risk : Θ → Rule → ℝ) :
    _root_.GD.N0230.N0695.d001054 risk (fun _ => True) = _root_.GD.N0230.N0695.d001053 risk := by
  ext d
  simp [_root_.GD.N0230.N0695.d001054, _root_.GD.N0230.N0695.d001053]





theorem d001069
    (risk : Θ → Rule → ℝ)
    (hminor : _root_.GD.N0230.N0695.d001066 risk) :
    _root_.GD.N0230.N0695.d001067 risk (_root_.GD.N0230.N0695.d001053 risk) := by
  have hminorWithin :
      _root_.GD.N0230.N0695.d001056 risk (fun _ => True) := by
    intro d _
    exact hminor d
  have h :=
    _root_.GD.N0230.N0695.d001062
      risk (fun _ => True)
      (by
        intro d e _ _
        trivial)
      hminorWithin
  rw [_root_.GD.N0230.N0695.d001068 risk] at h
  exact h




theorem d001070
    (risk : Θ → Rule → ℝ)
    (C : Set Rule)
    (hC : _root_.GD.N0230.N0695.d001065 risk C) :
    _root_.GD.N0230.N0695.d001053 risk ⊆ C := by
  rw [← _root_.GD.N0230.N0695.d001068 risk]
  exact _root_.GD.N0230.N0695.d001061
    risk (fun _ => True) C hC

section Hilbert

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]








theorem d001071
    (risk : Θ → H → ℝ)
    (safe : H → Prop)
    (θ₀ : Θ) (target : H)
    (hcomplete :
      ∀ d, safe d → IsComplete {e : H | _root_.GD.N0230.N0556.d000030 risk d e})
    (hconvex :
      ∀ d, safe d → Convex ℝ {e : H | _root_.GD.N0230.N0556.d000030 risk d e})
    (href : ∀ d, risk θ₀ d = ‖target - d‖ ^ 2) :
    _root_.GD.N0230.N0695.d001056 risk safe := by
  intro d hd
  obtain ⟨star, hstar, hterminal, _hadmissible, _hmin⟩ :=
    _root_.GD.N0230.N0630.d000792
      risk θ₀ target d (hcomplete d hd) (hconvex d hd) href
  exact ⟨star, hterminal, hstar⟩





theorem d001072
    (risk : Θ → H → ℝ)
    (safe : H → Prop)
    (hsafe : _root_.GD.N0230.N0682.d000500 risk safe)
    (θ₀ : Θ) (target : H)
    (hcomplete :
      ∀ d, safe d → IsComplete {e : H | _root_.GD.N0230.N0556.d000030 risk d e})
    (hconvex :
      ∀ d, safe d → Convex ℝ {e : H | _root_.GD.N0230.N0556.d000030 risk d e})
    (href : ∀ d, risk θ₀ d = ‖target - d‖ ^ 2) :
    _root_.GD.N0230.N0695.d001057
      risk safe (_root_.GD.N0230.N0695.d001054 risk safe) := by
  exact _root_.GD.N0230.N0695.d001062
    risk safe hsafe
    (_root_.GD.N0230.N0695.d001071
      risk safe θ₀ target hcomplete hconvex href)






theorem d001073
    (risk : Θ → H → ℝ)
    (bar : H)
    (θ₀ : Θ) (target : H)
    (hcomplete :
      ∀ d, _root_.GD.N0230.N0556.d000030 risk bar d →
        IsComplete {e : H | _root_.GD.N0230.N0556.d000030 risk d e})
    (hconvex :
      ∀ d, _root_.GD.N0230.N0556.d000030 risk bar d →
        Convex ℝ {e : H | _root_.GD.N0230.N0556.d000030 risk d e})
    (href : ∀ d, risk θ₀ d = ‖target - d‖ ^ 2) :
    _root_.GD.N0230.N0695.d001057
      risk (_root_.GD.N0230.N0556.d000030 risk bar)
      (_root_.GD.N0230.N0695.d001054 risk (_root_.GD.N0230.N0556.d000030 risk bar)) := by
  exact _root_.GD.N0230.N0695.d001072
    risk (_root_.GD.N0230.N0556.d000030 risk bar) (_root_.GD.N0230.N0695.d001058 risk bar)
    θ₀ target hcomplete hconvex href





theorem d001074
    (risk : Θ → H → ℝ)
    (θ₀ : Θ) (target : H)
    (hcomplete :
      ∀ d, IsComplete {e : H | _root_.GD.N0230.N0556.d000030 risk d e})
    (hconvex :
      ∀ d, Convex ℝ {e : H | _root_.GD.N0230.N0556.d000030 risk d e})
    (href : ∀ d, risk θ₀ d = ‖target - d‖ ^ 2) :
    _root_.GD.N0230.N0695.d001067 risk (_root_.GD.N0230.N0695.d001053 risk) := by
  apply _root_.GD.N0230.N0695.d001069 risk
  intro d
  exact _root_.GD.N0230.N0695.d001071
    risk (fun _ => True) θ₀ target
    (fun e _ => hcomplete e)
    (fun e _ => hconvex e)
    href d trivial

end Hilbert

end N0695
end N0230
end GD
