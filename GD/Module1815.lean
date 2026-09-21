import GD.Module0505
import GD.Module1814

set_option autoImplicit false
noncomputable section

namespace GD.N0152.N0439

open _root_.GD.N0152.N0437
open _root_.GD.N0005.N0248



theorem d030091 {m n a b x y : ℝ}
    (hm : 0 < m) (hn : 0 < n) (ha : 0 < a) (hb : 0 < b)
    (S : Finset ℝ)
    (hS : ∀ u ∈ S, ∀ v, _root_.GD.N0005.N0248.d030071 m n a b x y v ≤ _root_.GD.N0005.N0248.d030071 m n a b x y u) :
    S.card ≤ 2 := by
  apply _root_.GD.N0152.N0437.d007700 (_root_.GD.N0005.N0248.d030083 ha hb)
    (_root_.GD.N0005.N0248.d030073 m n a b x y) (_root_.GD.N0005.N0248.d030078 hm hn a b x y)
    (fun u hu => (_root_.GD.N0005.N0248.d030080 ha hb).mp hu) S hS 2
  have h := _root_.GD.N0005.N0248.d030076 m n a b x y
  omega



theorem d030092 {m n a b x y : ℝ}
    (hm : 0 < m) (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) :
    ∃ S : Finset ℝ, S.Nonempty ∧ S.card ≤ 2 ∧
      ∀ u, u ∈ S ↔ ∀ v, _root_.GD.N0005.N0248.d030071 m n a b x y v ≤ _root_.GD.N0005.N0248.d030071 m n a b x y u := by
  obtain ⟨C, hcard, hC⟩ := _root_.GD.N0005.N0248.d030082 hm hn ha hb
    (x := x) (y := y)
  apply _root_.GD.N0152.N0437.d007701 (_root_.GD.N0005.N0248.d030083 ha hb) C 2
    (fun u hu => (hC u).mpr hu) (by omega)
  obtain ⟨u, _, hu⟩ := _root_.GD.N0005.N0248.d030085 hm.le hn.le ha hb (x := x) (y := y)
  exact ⟨u, hu⟩

end GD.N0152.N0439

#print axioms _root_.GD.N0152.N0439.d030091
#print axioms _root_.GD.N0152.N0439.d030092
