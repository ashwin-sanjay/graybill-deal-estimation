import GD.Module1276
import GD.Module1142











open Filter Set Topology

namespace GD.N0232.N0720.N1038

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1062
open _root_.GD.N0232.N0720.N1130
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1125
open _root_.GD.N0232.N0720.N1103
open _root_.GD.N0230.N0608

noncomputable section

theorem d020621
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    0 < _root_.GD.N0232.N0720.N1201.d015333 m n s := by
  obtain ⟨epsilon, hepsilon, hfloor⟩ :=
    _root_.GD.N0232.N0720.N1135.d018346 hm hn
      (_root_.GD.N0232.N0720.N1319.d020618 m n hm hn) s hstrict
  apply hepsilon.trans_le
  apply (_root_.GD.N0232.N0720.N1062.d018379 s epsilon).1
  intro C
  rw [_root_.GD.N0232.N0720.N1062.d018361 C s.value s.finiteRisk]
  exact hfloor C

theorem d020622
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ C : _root_.GD.N0232.N0720.N1130.d017074,
      epsilon ≤ _root_.GD.N0232.N0720.N1062.d018360 C s.value :=
  (_root_.GD.N0232.N0720.N1062.d018380 s).1
    (_root_.GD.N0232.N0720.N1038.d020621 m n hm hn s hstrict)


theorem d020623
    {m n : ℕ} (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    (⨅ C : _root_.GD.N0232.N0720.N1130.d017074, _root_.GD.N0232.N0720.N1062.d018360 C s.value) =
      _root_.GD.N0232.N0720.N1201.d015333 m n s := by
  letI : Nonempty _root_.GD.N0232.N0720.N1130.d017074 :=
    ⟨(_root_.GD.N0232.N0720.N1103.d018292 s).candidate 0⟩
  have hbounded : BddBelow (range fun C : _root_.GD.N0232.N0720.N1130.d017074 ↦
      _root_.GD.N0232.N0720.N1062.d018360 C s.value) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨C, rfl⟩
    exact (_root_.GD.N0232.N0720.N1062.d018381 s C).le
  apply le_antisymm
  · apply (_root_.GD.N0232.N0720.N1062.d018379 s _).1
    intro C
    exact ciInf_le hbounded C
  · exact le_ciInf (fun C ↦ _root_.GD.N0232.N0720.N1062.d018370 s C)

theorem d020624
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    0 < ⨅ C : _root_.GD.N0232.N0720.N1130.d017074, _root_.GD.N0232.N0720.N1062.d018360 C s.value := by
  rw [_root_.GD.N0232.N0720.N1038.d020623]
  exact _root_.GD.N0232.N0720.N1038.d020621 m n hm hn s hstrict



theorem d020625
    {m n : ℕ} (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    (⨅ C : _root_.GD.N0232.N0720.N1130.d017074,
      _root_.GD.N0232.N0720.N1062.d018367 C s.value / _root_.GD.N0232.N0720.N1062.d018364 C) =
      _root_.GD.N0232.N0720.N1201.d015333 m n s := by
  simp only [_root_.GD.N0232.N0720.N1062.d018368]
  exact _root_.GD.N0232.N0720.N1038.d020623 s

theorem d020626
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ¬ _root_.GD.N0232.N0720.N1062.d018373 s := by
  rw [_root_.GD.N0232.N0720.N1062.d018376]
  exact (_root_.GD.N0232.N0720.N1038.d020621 m n hm hn s hstrict).ne'

end
end GD.N0232.N0720.N1038

#print axioms _root_.GD.N0232.N0720.N1038.d020622
#print axioms _root_.GD.N0232.N0720.N1038.d020623
#print axioms _root_.GD.N0232.N0720.N1038.d020624
#print axioms _root_.GD.N0232.N0720.N1038.d020625
#print axioms _root_.GD.N0232.N0720.N1038.d020626
