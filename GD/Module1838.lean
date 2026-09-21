import GD.Module1830
import GD.Module1276

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0034.N0296

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1482
open _root_.GD.N0232.N0720.N1319
open _root_.GD.N0230.N0608
open _root_.GD.N0046.N0305

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

theorem d030279
    {p : _root_.GD.N0046.N0305.d030201 m n} (hp : p ∈ _root_.GD.N0046.N0305.d030212 m n hm hn) :
    _root_.GD.N0232.N0720.N1159.d014633 m n p ∈ _root_.GD.N0046.N0305.d030212 m n hm hn := by
  have hbelow := (_root_.GD.N0232.N0720.N1159.d014634 m n p).1
  refine ⟨?_, ?_⟩
  · intro θ
    exact ⟨(hbelow θ).trans (hp.1 θ).1, (hbelow θ).trans (hp.1 θ).2⟩
  · intro θ
    exact (hbelow θ).trans_lt (hp.2 θ)

theorem d030280
    {p : _root_.GD.N0046.N0305.d030201 m n} (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) p (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn))
    (hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p) :
    ¬ (_root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p hp = p ∧
      _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p hp = p) := by
  rintro ⟨hTwo, hThree⟩
  have hall := _root_.GD.N0232.N0720.N1482.d015167 p hp hTwo hThree
  have hrep := (_root_.GD.N0232.N0720.N1159.d014655 m n hm hn p hp).mp hall
  apply _root_.GD.N0232.N0720.N1319.d020618 m n hm hn
  exact (_root_.GD.N0232.N0720.N1159.d014664
    m n hm hn).mpr ⟨p, hrep, hstrict, hterminal⟩

theorem d030281
    (hne : (_root_.GD.N0046.N0305.d030212 m n hm hn).Nonempty) :
    ∃ (p : _root_.GD.N0046.N0305.d030201 m n) (hp : p ∈ _root_.GD.N0046.N0305.d030212 m n hm hn),
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p ∧
        (_root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015130 p
          (_root_.GD.N0046.N0305.d030204 m n hp.1) ≠ p ∨
        _root_.GD.N0232.N0720.N1159.d014642 m n _root_.GD.N0232.N0720.N1482.d015131 p
          (_root_.GD.N0046.N0305.d030204 m n hp.1) ≠ p) := by
  obtain ⟨s, hs⟩ := hne
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n s
  have hp : p ∈ _root_.GD.N0046.N0305.d030212 m n hm hn :=
    _root_.GD.N0034.N0296.d030279 m n hm hn hs
  have ht : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p :=
    (_root_.GD.N0232.N0720.N1159.d014634 m n s).2.1
  refine ⟨p, hp, ht, ?_⟩
  exact not_and_or.mp (_root_.GD.N0034.N0296.d030280 m n hm hn
    (_root_.GD.N0046.N0305.d030204 m n hp.1) hp.2 ht)

end
end GD.N0034.N0296

#print axioms _root_.GD.N0034.N0296.d030279
#print axioms _root_.GD.N0034.N0296.d030280
#print axioms _root_.GD.N0034.N0296.d030281
