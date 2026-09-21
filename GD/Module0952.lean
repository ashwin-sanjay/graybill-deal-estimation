import GD.Module0948























open Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1262

noncomputable section

open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1065
open _root_.GD.N0232.N0720.N1483
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0703
open _root_.GD.N0230.N0709
open _root_.GD.N0230.N0710

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)





structure d014962
    (F : Set (_root_.GD.N0232.N0720.N1025.d014303 m n)) : Prop where
  subset_cap : F ⊆ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn
  nonempty : F.Nonempty
  isCompact : IsCompact F
  convex : Convex ℝ F
  invariant : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
    MapsTo (_root_.GD.N0232.N0720.N1065.d014576 m n hm hn g) F F
  terminal : ∀ d ∈ F, _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1025.d014305 m n) d




structure d014963
    (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) : Prop where
  fixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
    _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p
  terminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1025.d014305 m n) p.1


def d014964 : Prop :=
  ∃ F : Set (_root_.GD.N0232.N0720.N1025.d014303 m n),
    _root_.GD.N0232.N0720.N1262.d014962 m n hm hn F


def d014965 : Prop :=
  ∃ p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn,
    _root_.GD.N0232.N0720.N1262.d014963 m n hm hn p







theorem d014966
    (F : Set (_root_.GD.N0232.N0720.N1025.d014303 m n))
    (hF : _root_.GD.N0232.N0720.N1262.d014962 m n hm hn F) :
    ∃ p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn,
      p.1 ∈ F ∧ _root_.GD.N0232.N0720.N1262.d014963 m n hm hn p := by
  let inner : ℝ → _root_.GD.N0232.N0720.N1025.d014303 m n → _root_.GD.N0232.N0720.N1025.d014303 m n :=
    fun t ↦ _root_.GD.N0232.N0720.N1065.d014576 m n hm hn (_root_.GD.N0232.N0720.N1065.d014602 t)
  let outer : ℝ → _root_.GD.N0232.N0720.N1025.d014303 m n → _root_.GD.N0232.N0720.N1025.d014303 m n :=
    fun s ↦ _root_.GD.N0232.N0720.N1065.d014576 m n hm hn (_root_.GD.N0232.N0720.N1065.d014603 s)
  have hbounded : _root_.GD.N0230.N0709.d001221 F :=
    _root_.GD.N0230.N0709.d001221.d001222 (_root_.GD.N0232.N0720.N1065.d014599 m n hm hn) hF.subset_cap
  obtain ⟨x, hxF, hxinner, hxouter⟩ :=
    _root_.GD.N0230.N0710.d001248
      inner outer F hF.isCompact hF.convex hF.nonempty hbounded
      (fun t ↦ hF.invariant (_root_.GD.N0232.N0720.N1065.d014602 t))
      (fun t ↦ (_root_.GD.N0232.N0720.N1483.d014905
        m n hm hn (_root_.GD.N0232.N0720.N1065.d014602 t)).mono hF.subset_cap)
      (fun t u hu v hv a b ha hb hab ↦
        _root_.GD.N0232.N0720.N1065.d014586 m n hm hn (_root_.GD.N0232.N0720.N1065.d014602 t)
          (hF.subset_cap hu) (hF.subset_cap hv) ha hb hab)
      (_root_.GD.N0232.N0720.N1065.d014609 m n hm hn)
      (_root_.GD.N0232.N0720.N1065.d014611 m n hm hn)
      (fun s ↦ hF.invariant (_root_.GD.N0232.N0720.N1065.d014603 s))
      (fun s ↦ (_root_.GD.N0232.N0720.N1483.d014905
        m n hm hn (_root_.GD.N0232.N0720.N1065.d014603 s)).mono hF.subset_cap)
      (fun s u hu v hv a b ha hb hab ↦
        _root_.GD.N0232.N0720.N1065.d014586 m n hm hn (_root_.GD.N0232.N0720.N1065.d014603 s)
          (hF.subset_cap hu) (hF.subset_cap hv) ha hb hab)
      (_root_.GD.N0232.N0720.N1065.d014610 m n hm hn)
  have hxCap : x ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn := hF.subset_cap hxF
  let p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn := ⟨x, hxCap⟩
  have hpFixed : ∀ g : _root_.GD.N0232.N0720.N1025.d014301,
      _root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p = p := by
    intro g
    apply Subtype.ext
    have hfactor := _root_.GD.N0232.N0720.N1065.d014606 g
    have hmul := _root_.GD.N0232.N0720.N1065.d014596 m n hm hn
      (_root_.GD.N0232.N0720.N1065.d014602 g.shift) (_root_.GD.N0232.N0720.N1065.d014603 g.logScale) hxCap
    have hfixAmbient : _root_.GD.N0232.N0720.N1065.d014576 m n hm hn g x = x := by
      rw [← hfactor, ← hmul]
      change inner g.shift (outer g.logScale x) = x
      rw [hxouter g.logScale, hxinner g.shift]
    exact (_root_.GD.N0232.N0720.N1065.d014577 m n hm hn g hxCap).symm.trans
      hfixAmbient
  exact ⟨p, hxF, hpFixed, hF.terminal x hxF⟩



theorem d014967
    (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hp : _root_.GD.N0232.N0720.N1262.d014963 m n hm hn p) :
    _root_.GD.N0232.N0720.N1262.d014962 m n hm hn
      ({p.1} : Set (_root_.GD.N0232.N0720.N1025.d014303 m n)) := by
  refine ⟨?_, Set.singleton_nonempty p.1, isCompact_singleton,
    convex_singleton p.1, ?_, ?_⟩
  · intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact p.2
  · intro g x hx
    rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff]
    calc
      _root_.GD.N0232.N0720.N1065.d014576 m n hm hn g p.1 =
          (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1 :=
        _root_.GD.N0232.N0720.N1065.d014577 m n hm hn g p.2
      _ = p.1 := congrArg Subtype.val (hp.fixed g)
  · intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact hp.terminal



theorem d014968 :
    _root_.GD.N0232.N0720.N1262.d014964 m n hm hn ↔
      _root_.GD.N0232.N0720.N1262.d014965 m n hm hn := by
  constructor
  · rintro ⟨F, hF⟩
    obtain ⟨p, _hpF, hp⟩ :=
      _root_.GD.N0232.N0720.N1262.d014966 m n hm hn F hF
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨{p.1},
      _root_.GD.N0232.N0720.N1262.d014967
        m n hm hn p hp⟩




theorem d014969
    (F : Set (_root_.GD.N0232.N0720.N1025.d014303 m n))
    (hF : _root_.GD.N0232.N0720.N1262.d014962 m n hm hn F) :
    ∃ p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn,
      _root_.GD.N0232.N0720.N1262.d014963 m n hm hn p ∧
      ({p.1} : Set (_root_.GD.N0232.N0720.N1025.d014303 m n)) ⊆ F ∧
      _root_.GD.N0232.N0720.N1262.d014962 m n hm hn ({p.1} : Set
        (_root_.GD.N0232.N0720.N1025.d014303 m n)) := by
  obtain ⟨p, hpF, hp⟩ :=
    _root_.GD.N0232.N0720.N1262.d014966 m n hm hn F hF
  exact ⟨p, hp, Set.singleton_subset_iff.mpr hpF,
    _root_.GD.N0232.N0720.N1262.d014967
      m n hm hn p hp⟩

end

end N1262
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1262.d014966
#print axioms _root_.GD.N0232.N0720.N1262.d014967
#print axioms _root_.GD.N0232.N0720.N1262.d014968
#print axioms _root_.GD.N0232.N0720.N1262.d014969
