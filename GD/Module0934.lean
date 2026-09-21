import GD.Module0092
import GD.Module0932














open Set

namespace GD
namespace N0232
namespace N0720
namespace N1142

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0613
open _root_.GD.N0230.N0685

variable (m n : ℕ)


def d014673
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
  {d | _root_.GD.N0232.N0720.N1080.d014182 m n theta d ≤ _root_.GD.N0232.N0720.N1080.d014182 m n theta s}


theorem d014674
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    IsClosed (_root_.GD.N0232.N0720.N1142.d014673 m n s theta) := by
  simpa [_root_.GD.N0232.N0720.N1142.d014673, _root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000122
      (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (fun _ : Unit ↦ _root_.GD.N0232.N0720.N1080.d014171 m n theta)
      (fun _ : Unit ↦ theta.location)
      (fun _ : Unit ↦ _root_.GD.N0232.N0720.N1080.d014182 m n theta s)
      (fun _ : Unit ↦ _root_.GD.N0232.N0720.N1080.d014173 m n theta))


theorem d014675
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    Convex ℝ (_root_.GD.N0232.N0720.N1142.d014673 m n s theta) := by
  simpa [_root_.GD.N0232.N0720.N1142.d014673, _root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000123
      (_root_.GD.N0232.N0720.N1080.d014172 m n)
      (fun _ : Unit ↦ _root_.GD.N0232.N0720.N1080.d014171 m n theta)
      (fun _ : Unit ↦ theta.location)
      (fun _ : Unit ↦ _root_.GD.N0232.N0720.N1080.d014182 m n theta s)
      (fun _ : Unit ↦ _root_.GD.N0232.N0720.N1080.d014173 m n theta))



theorem d014676
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    (⋂ theta, _root_.GD.N0232.N0720.N1142.d014673 m n s theta) = _root_.GD.N0232.N0720.N1159.d014630 m n s := by
  ext d
  simp [_root_.GD.N0232.N0720.N1142.d014673, _root_.GD.N0232.N0720.N1159.d014630, _root_.GD.N0230.N0608.d000673, _root_.GD.N0230.N0608.d000672]







theorem d014677
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :
    _root_.GD.N0230.N0685.d000511 (⋂ theta, _root_.GD.N0232.N0720.N1142.d014673 m n s theta) 0
      (_root_.GD.N0232.N0720.N1159.d014633 m n s) := by
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n s
  have hp : p ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s :=
    (_root_.GD.N0232.N0720.N1159.d014634 m n s).1
  refine ⟨?_, ?_⟩
  · simpa [_root_.GD.N0232.N0720.N1142.d014676 m n s] using hp
  · intro d hd
    have hd' : d ∈ _root_.GD.N0232.N0720.N1159.d014630 m n s := by
      simpa [_root_.GD.N0232.N0720.N1142.d014676 m n s] using hd
    have htax := _root_.GD.N0232.N0720.N1159.d014648 m n s d hd'
    have hexpand :
        ‖d‖ ^ 2 =
          ‖d - p‖ ^ 2 + 2 * inner ℝ (d - p) p + ‖p‖ ^ 2 := by
      calc
        ‖d‖ ^ 2 = ‖(d - p) + p‖ ^ 2 := by
          congr 1
          abel
        _ = ‖d - p‖ ^ 2 + 2 * inner ℝ (d - p) p + ‖p‖ ^ 2 := by
          rw [← real_inner_self_eq_norm_sq, real_inner_add_add_self,
            real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    change inner ℝ ((0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) - p) (d - p) ≤ 0
    rw [zero_sub, inner_neg_left, real_inner_comm]
    nlinarith



theorem d014678
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    {a : ℝ} (ha : a < ‖_root_.GD.N0232.N0720.N1159.d014633 m n s‖ ^ 2) :
    ∃ F : Finset _root_.GD.N0232.N0720.N1080.d014168, ∀ d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
      (∀ theta ∈ F, _root_.GD.N0232.N0720.N1080.d014182 m n theta d ≤ _root_.GD.N0232.N0720.N1080.d014182 m n theta s) →
        a < ‖d‖ ^ 2 := by
  obtain ⟨F, hF⟩ :=
    _root_.GD.N0230.N0613.d001202
      (_root_.GD.N0232.N0720.N1142.d014673 m n s)
      (_root_.GD.N0232.N0720.N1142.d014674 m n s)
      (_root_.GD.N0232.N0720.N1142.d014675 m n s)
      (_root_.GD.N0232.N0720.N1159.d014633 m n s)
      (_root_.GD.N0232.N0720.N1142.d014677 m n s) ha
  refine ⟨F, ?_⟩
  intro d hd
  exact hF d (by simpa [_root_.GD.N0232.N0720.N1142.d014673] using hd)



theorem d014679
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset _root_.GD.N0232.N0720.N1080.d014168, ∀ d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
      (∀ theta ∈ F, _root_.GD.N0232.N0720.N1080.d014182 m n theta d ≤ _root_.GD.N0232.N0720.N1080.d014182 m n theta s) →
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n s‖ ^ 2 - ε < ‖d‖ ^ 2 := by
  exact _root_.GD.N0232.N0720.N1142.d014678 m n s (by linarith)

end

end N1142
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1142.d014678
#print axioms _root_.GD.N0232.N0720.N1142.d014679
