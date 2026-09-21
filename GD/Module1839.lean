import GD.Module1320
import GD.Module0466
import GD.Module1836
import GD.Module1838
import GD.Module1363

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0034.N0286

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1226
open _root_.GD.N0046.N0305
open _root_.GD.N0034.N0293 _root_.GD.N0034.N0296

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

def d030282 : Prop :=
  ∀ p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn, _root_.GD.N0034.N0287.d021571 m n p = 0

def d030283 : Prop :=
  ∃ p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn, 0 < _root_.GD.N0034.N0287.d021571 m n p

theorem d030284 :
    ¬ _root_.GD.N0034.N0286.d030282 m n hm hn ↔ _root_.GD.N0034.N0286.d030283 m n hm hn :=
  _root_.GD.N0034.N0292.d007211
    (_root_.GD.N0046.N0305.d030202 m n hm hn) (_root_.GD.N0034.N0287.d021571 m n) (fun p _ => _root_.GD.N0034.N0287.d021575 m n p)

theorem d030285 :
    _root_.GD.N0034.N0286.d030283 m n hm hn ↔ (_root_.GD.N0046.N0305.d030212 m n hm hn).Nonempty := by
  constructor
  · rintro ⟨p, hp, he⟩
    rcases (_root_.GD.N0034.N0287.d021581 m n p
      (_root_.GD.N0046.N0305.d030204 m n hp)).mp he with hTwo | hThree
    · exact _root_.GD.N0034.N0293.d030261 m n hm hn _root_.GD.N0232.N0720.N1482.d015130 hp hTwo
    · exact _root_.GD.N0034.N0293.d030261 m n hm hn _root_.GD.N0232.N0720.N1482.d015131 hp hThree
  · intro h
    obtain ⟨p, hp, _, hmove⟩ :=
      _root_.GD.N0034.N0296.d030281 m n hm hn h
    exact ⟨p, hp.1, (_root_.GD.N0034.N0287.d021581 m n p
      (_root_.GD.N0046.N0305.d030204 m n hp.1)).mpr hmove⟩

theorem d030286 :
    _root_.GD.N0034.N0286.d030283 m n hm hn ↔ _root_.GD.N0232.N0720.N1226.d015578 m n := by
  rw [_root_.GD.N0034.N0286.d030285,
    _root_.GD.N0046.N0305.d030214 m n hm hn]

theorem d030287 :
    _root_.GD.N0034.N0286.d030282 m n hm hn ↔ (_root_.GD.N0046.N0305.d030202 m n hm hn).Subsingleton := by
  constructor
  · intro h p hp q hq
    by_contra hpq
    have hstrict : (_root_.GD.N0046.N0305.d030212 m n hm hn).Nonempty :=
      (_root_.GD.N0046.N0305.d030214 m n hm hn).mp
        (_root_.GD.N0046.N0305.d030211 m n hp hq hpq)
    obtain ⟨t, ht, he⟩ :=
      (_root_.GD.N0034.N0286.d030285 m n hm hn).mpr hstrict
    exact he.ne' (h t ht)
  · intro h p hp
    apply (_root_.GD.N0034.N0287.d021580 m n p
      (_root_.GD.N0046.N0305.d030204 m n hp)).mpr
    intro g
    exact _root_.GD.N0034.N0293.d030263 m n hm hn h g hp

theorem d030288 :
    _root_.GD.N0034.N0286.d030283 m n hm hn ↔
      ∃ p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn, ∃ q ∈ _root_.GD.N0046.N0305.d030202 m n hm hn, p ≠ q := by
  rw [← _root_.GD.N0034.N0286.d030284, _root_.GD.N0034.N0286.d030287]
  simp only [Set.Subsingleton, not_forall, exists_prop]

theorem d030289 :
    _root_.GD.N0034.N0286.d030282 m n hm hn ↔
      _root_.GD.N0046.N0305.d030202 m n hm hn = ∅ ∨
        ∃ p : _root_.GD.N0046.N0305.d030201 m n, _root_.GD.N0046.N0305.d030202 m n hm hn = {p} ∧
          ∃ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ p = _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) := by
  have h : _root_.GD.N0034.N0286.d030282 m n hm hn ↔ ¬ _root_.GD.N0232.N0720.N1226.d015578 m n := by
    rw [← _root_.GD.N0034.N0286.d030286 m n hm hn,
      ← _root_.GD.N0034.N0286.d030284]
    exact not_not.symm
  exact h.trans (_root_.GD.N0046.N0305.d030219 m n hm hn)

theorem d030290
    {p : _root_.GD.N0046.N0305.d030201 m n} (hK : _root_.GD.N0046.N0305.d030202 m n hm hn = {p}) :
    ¬ (∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ p < _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) := by
  intro hs
  have hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn := by rw [hK]; exact mem_singleton p
  have hU : _root_.GD.N0034.N0286.d030282 m n hm hn :=
    (_root_.GD.N0034.N0286.d030287 m n hm hn).mpr (by rw [hK]; exact subsingleton_singleton)
  have he : _root_.GD.N0034.N0286.d030283 m n hm hn :=
    (_root_.GD.N0034.N0286.d030285 m n hm hn).mpr ⟨p, hp, hs⟩
  exact (_root_.GD.N0034.N0286.d030284 m n hm hn).mpr he hU

theorem d030291
    (hV : _root_.GD.N0232.N0720.N1256.d015549 m n = ⊤) :
    _root_.GD.N0034.N0286.d030283 m n hm hn :=
  (_root_.GD.N0034.N0286.d030286 m n hm hn).mpr
    (_root_.GD.N0232.N0720.N1226.d015586 m n hm hn hV)

theorem d030292 :
    (¬ _root_.GD.N0034.N0286.d030282 m n hm hn ↔ _root_.GD.N0034.N0286.d030283 m n hm hn) ∧
    (_root_.GD.N0034.N0286.d030283 m n hm hn ↔ (_root_.GD.N0046.N0305.d030212 m n hm hn).Nonempty) ∧
    (_root_.GD.N0034.N0286.d030283 m n hm hn ↔ _root_.GD.N0232.N0720.N1226.d015578 m n) ∧
    (_root_.GD.N0034.N0286.d030282 m n hm hn ↔ (_root_.GD.N0046.N0305.d030202 m n hm hn).Subsingleton) :=
  ⟨_root_.GD.N0034.N0286.d030284 m n hm hn,
    _root_.GD.N0034.N0286.d030285 m n hm hn,
    _root_.GD.N0034.N0286.d030286 m n hm hn,
    _root_.GD.N0034.N0286.d030287 m n hm hn⟩

end
end GD.N0034.N0286

#print axioms _root_.GD.N0034.N0286.d030284
#print axioms _root_.GD.N0034.N0286.d030285
#print axioms _root_.GD.N0034.N0286.d030286
#print axioms _root_.GD.N0034.N0286.d030287
#print axioms _root_.GD.N0034.N0286.d030288
#print axioms _root_.GD.N0034.N0286.d030289
#print axioms _root_.GD.N0034.N0286.d030290
#print axioms _root_.GD.N0034.N0286.d030291
#print axioms _root_.GD.N0034.N0286.d030292
