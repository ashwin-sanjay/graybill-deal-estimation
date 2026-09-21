import GD.Module1839
import GD.Module1831

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0034.N0299

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0230.N0608
open _root_.GD.N0046.N0305
open _root_.GD.N0034.N0286

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

def d030297 : Prop :=
  ∀ (p : _root_.GD.N0046.N0305.d030201 m n), _root_.GD.N0232.N0720.N1159.d014637 m n p →
    _root_.GD.N0232.N0720.N1159.d014652 m n p →
    (∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ p ≤ _root_.GD.N0232.N0720.N1080.d014182 m n θ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) →
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) p → False

theorem d030298 (hNo : _root_.GD.N0034.N0299.d030297 m n hm hn) :
    _root_.GD.N0034.N0286.d030282 m n hm hn ↔ _root_.GD.N0046.N0305.d030202 m n hm hn = ∅ := by
  constructor
  · intro hU
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    let t := _root_.GD.N0232.N0720.N1159.d014633 m n p
    have hbelow := (_root_.GD.N0232.N0720.N1159.d014634 m n p).1
    have ht : t ∈ _root_.GD.N0046.N0305.d030202 m n hm hn := by
      intro θ
      exact ⟨(hbelow θ).trans (hp θ).1, (hbelow θ).trans (hp θ).2⟩
    have htfin := _root_.GD.N0046.N0305.d030204 m n ht
    have hfixed := (_root_.GD.N0034.N0287.d021580 m n t htfin).mp (hU t ht)
    have hrep := (_root_.GD.N0232.N0720.N1159.d014655 m n hm hn t htfin).mp hfixed
    exact hNo t htfin hrep (fun θ => (ht θ).2)
      (_root_.GD.N0232.N0720.N1159.d014634 m n p).2.1
  · intro hK p hp
    rw [hK] at hp
    exact hp.elim

theorem d030299 (hNo : _root_.GD.N0034.N0299.d030297 m n hm hn) :
    _root_.GD.N0034.N0286.d030283 m n hm hn ↔ (_root_.GD.N0046.N0305.d030202 m n hm hn).Nonempty := by
  rw [← _root_.GD.N0034.N0286.d030284, _root_.GD.N0034.N0299.d030298 m n hm hn hNo,
    Set.nonempty_iff_ne_empty]

theorem d030300 (hNo : _root_.GD.N0034.N0299.d030297 m n hm hn) :
    _root_.GD.N0034.N0286.d030283 m n hm hn ↔ _root_.GD.N0034.N0289.d030224 m n hm hn :=
  (_root_.GD.N0034.N0299.d030299 m n hm hn hNo).trans
    (_root_.GD.N0034.N0289.d030225 m n hm hn)

theorem d030301 (hNo : _root_.GD.N0034.N0299.d030297 m n hm hn)
    (p : _root_.GD.N0046.N0305.d030201 m n) : _root_.GD.N0046.N0305.d030202 m n hm hn ≠ {p} := by
  intro hK
  have hU := (_root_.GD.N0034.N0286.d030287 m n hm hn).mpr
    (by rw [hK]; exact subsingleton_singleton)
  have he := (_root_.GD.N0034.N0299.d030298 m n hm hn hNo).mp hU
  have hp : p ∈ _root_.GD.N0046.N0305.d030202 m n hm hn := by rw [hK]; exact mem_singleton p
  rw [he] at hp
  exact hp.elim

end
end GD.N0034.N0299

#print axioms _root_.GD.N0034.N0299.d030298
#print axioms _root_.GD.N0034.N0299.d030299
#print axioms _root_.GD.N0034.N0299.d030300
#print axioms _root_.GD.N0034.N0299.d030301
