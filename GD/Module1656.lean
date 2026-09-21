import GD.Module1655
import GD.Module0983

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0098
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1256 _root_.GD.N0232.N0720.N1214 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1226


def d028160 (m n : ℕ) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) : Prop :=
  ∀ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable e →
    (∀ θ : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 m n θ e ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ d) →
    ∀ θ : _root_.GD.N0232.N0720.N1080.d014168, e =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n θ] d



theorem d028161 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n, _root_.GD.N0098.d028160 m n d ∧
      _root_.GD.N0232.N0720.N1256.d015548 m n d = _root_.GD.N0232.N0720.N1256.d015549 m n := by
  obtain ⟨s, hs, hval⟩ := _root_.GD.N0232.N0720.N1222.d015570 m n hm hn
  have hsm : MemLp s 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014285 m n s hs.1.1 (hs.2 _root_.GD.N0232.N0720.N1080.d014169)
  let p := _root_.GD.N0232.N0720.N1159.d014633 m n (MemLp.toLp s hsm)
  let d := _root_.GD.N0232.N0720.N1214.d014265 m n p
  have hd : Measurable d := _root_.GD.N0232.N0720.N1214.d014266 m n p
  have hbelow : ∀ θ : _root_.GD.N0232.N0720.N1080.d014168, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ _root_.GD.N0232.N0720.N1080.d014197 m n θ s := by
    intro θ
    rw [_root_.GD.N0232.N0720.N1080.d014198 m n θ s hsm]
    change _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1214.d014265 m n p) ≤ _
    rw [_root_.GD.N0232.N0720.N1215.d014286]
    exact (_root_.GD.N0232.N0720.N1159.d014634 m n (MemLp.toLp s hsm)).1 θ
  refine ⟨d, ⟨hd, fun θ => ne_top_of_le_ne_top (hs.2 θ) (hbelow θ)⟩, ?_, ?_⟩
  · exact _root_.GD.N0232.N0720.N1226.d015581 m n p
      (_root_.GD.N0232.N0720.N1159.d014634 m n (MemLp.toLp s hsm)).2.1
  · apply le_antisymm
    · exact (_root_.GD.N0232.N0720.N1226.d015580 m n hbelow).trans_eq hval
    · exact _root_.GD.N0230.N0611.d003520
        (_root_.GD.N0232.N0720.N1256.d015547 m n) hd


theorem d028162 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hlarge : 6 ≤ m ∨ 6 ≤ n) :
    ∃ d ∈ _root_.GD.N0232.N0720.N1256.d015552 m n,
      _root_.GD.N0232.N0720.N1256.d015548 m n d = _root_.GD.N0232.N0720.N1256.d015549 m n ∧ _root_.GD.N0232.N0720.N1256.d015548 m n d ≠ ⊤ := by
  obtain ⟨d, hd, hv⟩ := _root_.GD.N0232.N0720.N1222.d015570 m n hm hn
  refine ⟨d, hd, hv, ?_⟩
  rw [hv]
  exact _root_.GD.N0098.d028159 m n hm hn hlarge


theorem d028163 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hlarge : 6 ≤ m ∨ 6 ≤ n) :
    ∃ d ∈ _root_.GD.N0232.N0720.N1256.d015551 m n, _root_.GD.N0098.d028160 m n d ∧
      _root_.GD.N0232.N0720.N1256.d015548 m n d = _root_.GD.N0232.N0720.N1256.d015549 m n ∧ _root_.GD.N0232.N0720.N1256.d015548 m n d ≠ ⊤ := by
  obtain ⟨d, hd, ht, hv⟩ := _root_.GD.N0098.d028161 m n hm hn
  refine ⟨d, hd, ht, hv, ?_⟩
  rw [hv]
  exact _root_.GD.N0098.d028159 m n hm hn hlarge

end
end GD.N0098

#print axioms _root_.GD.N0098.d028161
#print axioms _root_.GD.N0098.d028162
#print axioms _root_.GD.N0098.d028163
