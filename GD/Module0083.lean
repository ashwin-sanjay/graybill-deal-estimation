import GD.Module0067
import GD.Module0081






















open Set

namespace GD
namespace N0230
namespace N0700

open _root_.GD.N0230.N0556
open _root_.GD.N0230.N0625
open _root_.GD.N0230.N0630
open _root_.GD.N0230.N0695
open _root_.GD.N0230.N0697

variable {G Θ Rule : Type*}
variable [Group G] [MulAction G Θ] [MulAction G Rule]


theorem d001104
    (safe : Rule → Prop)
    (hSafe : _root_.GD.N0230.N0625.d000800 (G := G) {d : Rule | safe d})
    (g : G) (d : Rule) :
    safe (g • d) ↔ safe d := by
  constructor
  · intro hgd
    have hback := hSafe g⁻¹ (g • d) hgd
    simpa using hback
  · intro hd
    exact hSafe g d hd


theorem d001105
    (risk : Θ → Rule → ℝ)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    (g : G) (e d : Rule) :
    _root_.GD.N0230.N0556.d000028 risk (g • e) (g • d) ↔
      _root_.GD.N0230.N0556.d000028 risk e d := by
  constructor
  · intro h
    have hback :=
      _root_.GD.N0230.N0625.d000804 risk hRisk h g⁻¹
    simpa using hback
  · intro h
    exact _root_.GD.N0230.N0625.d000804 risk hRisk h g






theorem d001106
    (risk : Θ → Rule → ℝ)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    {d : Rule}
    (hd : _root_.GD.N0230.N0630.d000786 risk d)
    (g : G) :
    _root_.GD.N0230.N0630.d000786 risk (g • d) := by
  intro e he
  have hback :
      _root_.GD.N0230.N0556.d000028 risk (g⁻¹ • e) d := by
    have :=
      _root_.GD.N0230.N0625.d000804 risk hRisk he g⁻¹
    simpa using this
  have heq : g⁻¹ • e = d :=
    hd (g⁻¹ • e) hback
  calc
    e = g • (g⁻¹ • e) := by simp
    _ = g • d := by rw [heq]


theorem d001107
    (risk : Θ → Rule → ℝ)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    (g : G) (d : Rule) :
    _root_.GD.N0230.N0630.d000786 risk (g • d) ↔
      _root_.GD.N0230.N0630.d000786 risk d := by
  constructor
  · intro hgd
    have hback :=
      _root_.GD.N0230.N0700.d001106 risk hRisk hgd g⁻¹
    simpa using hback
  · intro hd
    exact _root_.GD.N0230.N0700.d001106 risk hRisk hd g





theorem d001108
    (risk : Θ → Rule → ℝ)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk) :
    _root_.GD.N0230.N0625.d000800 (G := G) (_root_.GD.N0230.N0695.d001053 risk) := by
  intro g d hd
  exact _root_.GD.N0230.N0700.d001106 risk hRisk hd g


theorem d001109
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    (hSafe : _root_.GD.N0230.N0625.d000800 (G := G) {d : Rule | safe d}) :
    _root_.GD.N0230.N0625.d000800 (G := G) (_root_.GD.N0230.N0695.d001054 risk safe) := by
  intro g d hd
  exact
    ⟨hSafe g d hd.1,
      _root_.GD.N0230.N0700.d001106 risk hRisk hd.2 g⟩







theorem d001110
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    (hSafe : _root_.GD.N0230.N0625.d000800 (G := G) {d : Rule | safe d})
    (g : G) (d t : Rule) :
    g • t ∈ _root_.GD.N0230.N0697.d001077 risk safe (g • d) ↔
      t ∈ _root_.GD.N0230.N0697.d001077 risk safe d := by
  simp only [_root_.GD.N0230.N0697.d001078]
  rw [_root_.GD.N0230.N0700.d001104 safe hSafe g t,
      _root_.GD.N0230.N0700.d001107 risk hRisk g t,
      _root_.GD.N0230.N0700.d001105 risk hRisk g t d]





theorem d001111
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    (hSafe : _root_.GD.N0230.N0625.d000800 (G := G) {d : Rule | safe d})
    (g : G) (d : Rule) :
    (fun t => g • t) '' _root_.GD.N0230.N0697.d001077 risk safe d =
      _root_.GD.N0230.N0697.d001077 risk safe (g • d) := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact
      (_root_.GD.N0230.N0700.d001110
        risk safe hRisk hSafe g d t).2 ht
  · intro hu
    refine ⟨g⁻¹ • u, ?_, ?_⟩
    · have hback :
          g⁻¹ • u ∈
            _root_.GD.N0230.N0697.d001077 risk safe (g⁻¹ • (g • d)) :=
        (_root_.GD.N0230.N0700.d001110
          risk safe hRisk hSafe g⁻¹ (g • d) u).2 hu
      simpa using hback
    · simp





theorem d001112
    (risk : Θ → Rule → ℝ)
    (safe : Rule → Prop)
    (hRisk : _root_.GD.N0230.N0625.d000798 (G := G) risk)
    (hSafe : _root_.GD.N0230.N0625.d000800 (G := G) {d : Rule | safe d})
    (hhereditary : _root_.GD.N0230.N0682.d000500 risk safe)
    (hminor : _root_.GD.N0230.N0695.d001056 risk safe) :
    _root_.GD.N0230.N0625.d000800 (G := G) (_root_.GD.N0230.N0697.d001075 risk safe) := by
  rw [← _root_.GD.N0230.N0697.d001076
    risk safe hhereditary hminor]
  exact _root_.GD.N0230.N0700.d001109
    risk safe hRisk hSafe

end N0700
end N0230
end GD
