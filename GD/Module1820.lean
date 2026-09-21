import GD.Module1815
import GD.Module1819

set_option autoImplicit false
noncomputable section

namespace GD.N0152.N0438

open _root_.GD.N0005.N0248
open _root_.GD.N0152.N0439

def d030127 (a b x y u : ℝ) : ℝ × ℝ × ℝ :=
  (u, _root_.GD.N0005.N0248.d030070 a x u, _root_.GD.N0005.N0248.d030070 b y u)

def d030128 (m n a b x y : ℝ) (p : ℝ × ℝ × ℝ) : Prop :=
  0 < p.2.1 ∧ 0 < p.2.2 ∧
    ∀ u v w : ℝ, 0 < v → 0 < w →
      _root_.GD.N0005.N0248.d030122 m n a b x y u v w ≤
        _root_.GD.N0005.N0248.d030122 m n a b x y p.1 p.2.1 p.2.2

theorem d030129 (a b x y : ℝ) :
    Function.Injective (_root_.GD.N0152.N0438.d030127 a b x y) := by
  intro u v h
  exact congrArg Prod.fst h



theorem d030130 {m n a b x y : ℝ}
    (hm : 0 < m) (hn : 0 < n) (ha : 0 < a) (hb : 0 < b)
    (S : Finset ℝ)
    (hS : ∀ u, u ∈ S ↔ ∀ v, _root_.GD.N0005.N0248.d030071 m n a b x y v ≤ _root_.GD.N0005.N0248.d030071 m n a b x y u)
    (p : ℝ × ℝ × ℝ) :
    p ∈ S.image (_root_.GD.N0152.N0438.d030127 a b x y) ↔ _root_.GD.N0152.N0438.d030128 m n a b x y p := by
  classical
  constructor
  · intro hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨_root_.GD.N0005.N0248.d030074 ha x u, _root_.GD.N0005.N0248.d030074 hb y u, ?_⟩
    exact (_root_.GD.N0005.N0248.d030126 hm hn ha hb
      (_root_.GD.N0005.N0248.d030074 ha x u) (_root_.GD.N0005.N0248.d030074 hb y u)).mpr
        ⟨rfl, rfl, (hS u).mp hu⟩
  · rintro ⟨hv, hw, hmax⟩
    obtain ⟨hveq, hweq, hu⟩ := (_root_.GD.N0005.N0248.d030126 hm hn ha hb hv hw).mp hmax
    apply Finset.mem_image.mpr
    refine ⟨p.1, (hS p.1).mpr hu, ?_⟩
    exact Prod.ext rfl (Prod.ext hveq.symm hweq.symm)



theorem d030131 {m n a b x y : ℝ}
    (hm : 0 < m) (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) :
    ∃ J : Finset (ℝ × ℝ × ℝ), J.Nonempty ∧ J.card ≤ 2 ∧
      ∀ p, p ∈ J ↔ _root_.GD.N0152.N0438.d030128 m n a b x y p := by
  classical
  obtain ⟨S, hSne, hScard, hS⟩ := _root_.GD.N0152.N0439.d030092
    (x := x) (y := y) hm hn ha hb
  refine ⟨S.image (_root_.GD.N0152.N0438.d030127 a b x y), hSne.image _, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (_root_.GD.N0152.N0438.d030129 a b x y)]
    exact hScard
  · exact _root_.GD.N0152.N0438.d030130 hm hn ha hb S hS

theorem d030132 {m n a b x y : ℝ}
    (hm : 0 < m) (hn : 0 < n) (ha : 0 < a) (hb : 0 < b)
    (p : ℝ × ℝ × ℝ) (hp : _root_.GD.N0152.N0438.d030128 m n a b x y p) :
    p.1 ∈ Set.Icc (min x y) (max x y) := by
  have hu := ((_root_.GD.N0005.N0248.d030126 hm hn ha hb hp.1 hp.2.1).mp hp.2.2).2.2
  exact _root_.GD.N0005.N0248.d030081 hm hn ha hb (_root_.GD.N0005.N0248.d030086 hu)

end GD.N0152.N0438

#print axioms _root_.GD.N0152.N0438.d030130
#print axioms _root_.GD.N0152.N0438.d030131
