import Mathlib.Analysis.Convex.Basic
import Mathlib.Order.Zorn
import Mathlib.Topology.Compactness.Compact
import GD.Module0066















open Set

namespace GD
namespace N0230
namespace N0645

noncomputable section



variable {I X : Type*} [TopologicalSpace X]


structure d000848
    (act : I → X → X) (K : Set X) : Prop where
  nonempty : K.Nonempty
  isClosed : IsClosed K
  invariant : ∀ i, MapsTo (act i) K K


theorem d000849
    [Nonempty X] (act : I → X → X) :
    _root_.GD.N0230.N0645.d000848 act (Set.univ : Set X) := by
  exact ⟨Set.univ_nonempty, isClosed_univ, fun _ _ _ ↦ Set.mem_univ _⟩









theorem d000850
    [CompactSpace X] [Nonempty X] (act : I → X → X) :
    ∃ K : Set X,
      _root_.GD.N0230.N0645.d000848 act K ∧
      ∀ L : Set X,
        _root_.GD.N0230.N0645.d000848 act L → L ⊆ K → K ⊆ L := by
  let S : Set (Set X) := {K | _root_.GD.N0230.N0645.d000848 act K}
  obtain ⟨K, hK⟩ : ∃ K, Minimal (· ∈ S) K := by
    refine zorn_superset S ?_
    intro c hcS hchain
    obtain rfl | hcne := c.eq_empty_or_nonempty
    · exact ⟨Set.univ, _root_.GD.N0230.N0645.d000849 act, fun _ h ↦ False.elim h⟩
    · refine ⟨⋂₀ c, ?_, fun K hK ↦ Set.sInter_subset_of_mem hK⟩
      haveI : Nonempty (↥c) := hcne.to_subtype
      have hinter : (⋂₀ c).Nonempty := by
        rw [Set.sInter_eq_iInter]
        refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
          ((↑) : c → Set X) ?_ ?_ ?_ ?_
        · exact DirectedOn.directed_val (IsChain.directedOn hchain.symm)
        · intro K
          exact (hcS K.property).nonempty
        · intro K
          exact (hcS K.property).isClosed.isCompact
        · intro K
          exact (hcS K.property).isClosed
      refine ⟨hinter, isClosed_sInter fun K hK ↦ (hcS hK).isClosed, ?_⟩
      intro i x hx
      rw [Set.mem_sInter] at hx ⊢
      intro K hK
      exact (hcS hK).invariant i (hx K hK)
  exact ⟨K, hK.prop, fun L hL hLK ↦ hK.le_of_le hL hLK⟩



variable {E : Type*}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]


structure d000851
    (act : I → E → E) (C K : Set E) : Prop where
  nonempty : K.Nonempty
  subset_cap : K ⊆ C
  isClosed : IsClosed K
  convex : Convex ℝ K
  invariant : ∀ i, MapsTo (act i) K K


theorem d000852
    (act : I → E → E) (C : Set E)
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hmaps : ∀ i, MapsTo (act i) C C) :
    _root_.GD.N0230.N0645.d000851 act C C := by
  exact ⟨hne, Subset.rfl, hclosed, hconvex, hmaps⟩





theorem d000853
    (act : I → E → E) (C : Set E)
    (hcompact : IsCompact C) (hne : C.Nonempty)
    (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    (hmaps : ∀ i, MapsTo (act i) C C) :
    ∃ K : Set E,
      _root_.GD.N0230.N0645.d000851 act C K ∧
      ∀ L : Set E,
        _root_.GD.N0230.N0645.d000851 act C L → L ⊆ K → K ⊆ L := by
  let S : Set (Set E) := {K | _root_.GD.N0230.N0645.d000851 act C K}
  obtain ⟨K, hK⟩ : ∃ K, Minimal (· ∈ S) K := by
    refine zorn_superset S ?_
    intro c hcS hchain
    obtain rfl | hcne := c.eq_empty_or_nonempty
    · exact ⟨C,
        _root_.GD.N0230.N0645.d000852 act C hne hclosed hconvex hmaps,
        fun _ h ↦ False.elim h⟩
    · refine ⟨⋂₀ c, ?_, fun K hK ↦ Set.sInter_subset_of_mem hK⟩
      haveI : Nonempty (↥c) := hcne.to_subtype
      have hinter : (⋂₀ c).Nonempty := by
        rw [Set.sInter_eq_iInter]
        refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
          ((↑) : c → Set E) ?_ ?_ ?_ ?_
        · exact DirectedOn.directed_val (IsChain.directedOn hchain.symm)
        · intro K
          exact (hcS K.property).nonempty
        · intro K
          exact hcompact.of_isClosed_subset
            (hcS K.property).isClosed (hcS K.property).subset_cap
        · intro K
          exact (hcS K.property).isClosed
      refine ⟨hinter, ?_, ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨K, hK⟩ := hcne
        exact (hcS hK).subset_cap (Set.mem_sInter.mp hx K hK)
      · exact isClosed_sInter fun K hK ↦ (hcS hK).isClosed
      · exact convex_sInter fun K hK ↦ (hcS hK).convex
      · intro i x hx
        rw [Set.mem_sInter] at hx ⊢
        intro K hK
        exact (hcS hK).invariant i (hx K hK)
  exact ⟨K, hK.prop, fun L hL hLK ↦ hK.le_of_le hL hLK⟩









open _root_.GD.N0230.N0630

variable {Θ Rule : Type*}



theorem d000854
    (risk : Θ → Rule → ℝ) (act : I → Rule → Rule)
    (F : Set Rule)
    (hterminal : ∀ d ∈ F, _root_.GD.N0230.N0630.d000786 risk d)
    (hfixed : ∃ d ∈ F, ∀ i, act i d = d) :
    ∃ d, (∀ i, act i d = d) ∧ _root_.GD.N0230.N0630.d000786 risk d := by
  obtain ⟨d, hdF, hdfix⟩ := hfixed
  exact ⟨d, hdfix, hterminal d hdF⟩




abbrev d000855 := {x : ℝ // x ∈ Set.Icc (0 : ℝ) 1}


def d000856 (x : _root_.GD.N0230.N0645.d000855) : _root_.GD.N0230.N0645.d000855 :=
  ⟨1 - x.1, by constructor <;> linarith [x.2.1, x.2.2]⟩



def d000857 : Bool → _root_.GD.N0230.N0645.d000855 → ℝ
  | false, x => x.1 + 4 * x.1 * (1 - x.1)
  | true, x => (1 - x.1) + 4 * x.1 * (1 - x.1)

def d000858 : _root_.GD.N0230.N0645.d000855 := ⟨0, by norm_num⟩
def d000859 : _root_.GD.N0230.N0645.d000855 := ⟨1, by norm_num⟩
def d000860 : _root_.GD.N0230.N0645.d000855 := ⟨(1 / 2 : ℝ), by norm_num⟩


@[simp] theorem d000861 (x : _root_.GD.N0230.N0645.d000855) :
    _root_.GD.N0230.N0645.d000856 (_root_.GD.N0230.N0645.d000856 x) = x := by
  apply Subtype.ext
  dsimp [_root_.GD.N0230.N0645.d000856]
  ring


theorem d000862 (x : _root_.GD.N0230.N0645.d000855) :
    _root_.GD.N0230.N0645.d000857 false (_root_.GD.N0230.N0645.d000856 x) = _root_.GD.N0230.N0645.d000857 true x := by
  dsimp [_root_.GD.N0230.N0645.d000857, _root_.GD.N0230.N0645.d000856]
  ring


theorem d000863 (x : _root_.GD.N0230.N0645.d000855) :
    _root_.GD.N0230.N0645.d000857 true (_root_.GD.N0230.N0645.d000856 x) = _root_.GD.N0230.N0645.d000857 false x := by
  dsimp [_root_.GD.N0230.N0645.d000857, _root_.GD.N0230.N0645.d000856]
  ring


theorem d000864 (θ : Bool) (x : _root_.GD.N0230.N0645.d000855) :
    _root_.GD.N0230.N0645.d000857 θ (_root_.GD.N0230.N0645.d000856 x) =
      _root_.GD.N0230.N0645.d000857 (!θ) x := by
  cases θ
  · exact _root_.GD.N0230.N0645.d000862 x
  · exact _root_.GD.N0230.N0645.d000863 x


theorem d000865 :
    _root_.GD.N0230.N0630.d000786 _root_.GD.N0230.N0645.d000857 _root_.GD.N0230.N0645.d000858 := by
  intro e he
  have hprod : 0 ≤ e.1 * (1 - e.1) :=
    mul_nonneg e.2.1 (sub_nonneg.mpr e.2.2)
  have hle : e.1 + 4 * e.1 * (1 - e.1) ≤ 0 := by
    simpa [_root_.GD.N0230.N0645.d000857, _root_.GD.N0230.N0645.d000858] using he false
  have he0 : e.1 = 0 := by
    nlinarith
  exact Subtype.ext he0


theorem d000866 :
    _root_.GD.N0230.N0630.d000786 _root_.GD.N0230.N0645.d000857 _root_.GD.N0230.N0645.d000859 := by
  intro e he
  have hprod : 0 ≤ e.1 * (1 - e.1) :=
    mul_nonneg e.2.1 (sub_nonneg.mpr e.2.2)
  have hle : (1 - e.1) + 4 * e.1 * (1 - e.1) ≤ 0 := by
    simpa [_root_.GD.N0230.N0645.d000857, _root_.GD.N0230.N0645.d000859] using he true
  have he1 : e.1 = 1 := by
    nlinarith
  exact Subtype.ext he1


theorem d000867 :
    _root_.GD.N0230.N0556.d000028
      _root_.GD.N0230.N0645.d000857 _root_.GD.N0230.N0645.d000858 _root_.GD.N0230.N0645.d000860 := by
  intro θ
  cases θ <;> norm_num [_root_.GD.N0230.N0645.d000857, _root_.GD.N0230.N0645.d000858, _root_.GD.N0230.N0645.d000860]


theorem d000868 :
    ¬ _root_.GD.N0230.N0630.d000786 _root_.GD.N0230.N0645.d000857 _root_.GD.N0230.N0645.d000860 := by
  intro h
  have heq := h _root_.GD.N0230.N0645.d000858 _root_.GD.N0230.N0645.d000867
  have hval := congrArg Subtype.val heq
  norm_num [_root_.GD.N0230.N0645.d000858, _root_.GD.N0230.N0645.d000860] at hval


@[simp] theorem d000869 :
    _root_.GD.N0230.N0645.d000856 _root_.GD.N0230.N0645.d000860 = _root_.GD.N0230.N0645.d000860 := by
  apply Subtype.ext
  norm_num [_root_.GD.N0230.N0645.d000856, _root_.GD.N0230.N0645.d000860]


theorem d000870 (x : _root_.GD.N0230.N0645.d000855) :
    _root_.GD.N0230.N0645.d000856 x = x ↔ x = _root_.GD.N0230.N0645.d000860 := by
  constructor
  · intro hx
    apply Subtype.ext
    have hval := congrArg Subtype.val hx
    dsimp [_root_.GD.N0230.N0645.d000856] at hval
    dsimp [_root_.GD.N0230.N0645.d000860]
    linarith
  · rintro rfl
    exact _root_.GD.N0230.N0645.d000869



theorem d000871 :
    ¬ ∃ x : _root_.GD.N0230.N0645.d000855,
      _root_.GD.N0230.N0645.d000856 x = x ∧ _root_.GD.N0230.N0630.d000786 _root_.GD.N0230.N0645.d000857 x := by
  rintro ⟨x, hxfix, hxterminal⟩
  have hx : x = _root_.GD.N0230.N0645.d000860 := (_root_.GD.N0230.N0645.d000870 x).mp hxfix
  subst x
  exact _root_.GD.N0230.N0645.d000868 hxterminal



theorem d000872 :
    _root_.GD.N0230.N0645.d000851
      (fun _ : Unit ↦ fun x : ℝ ↦ 1 - x)
      (Set.Icc (0 : ℝ) 1) ({(1 / 2 : ℝ)} : Set ℝ) := by
  refine ⟨Set.singleton_nonempty _, ?_, isClosed_singleton,
    convex_singleton _, ?_⟩
  · rintro x rfl
    norm_num
  · intro _ x hx
    have hx' : x = (1 / 2 : ℝ) := Set.mem_singleton_iff.mp hx
    subst x
    norm_num



theorem d000873 :
    ∀ L : Set ℝ,
      _root_.GD.N0230.N0645.d000851
        (fun _ : Unit ↦ fun x : ℝ ↦ 1 - x)
        (Set.Icc (0 : ℝ) 1) L →
      L ⊆ ({(1 / 2 : ℝ)} : Set ℝ) →
      ({(1 / 2 : ℝ)} : Set ℝ) ⊆ L := by
  intro L hL hsub
  obtain ⟨x, hxL⟩ := hL.nonempty
  have hx : x = (1 / 2 : ℝ) := Set.mem_singleton_iff.mp (hsub hxL)
  simpa only [Set.singleton_subset_iff, hx] using hxL






theorem d000874 :
    (_root_.GD.N0230.N0630.d000786 _root_.GD.N0230.N0645.d000857 _root_.GD.N0230.N0645.d000858) ∧
    (_root_.GD.N0230.N0630.d000786 _root_.GD.N0230.N0645.d000857 _root_.GD.N0230.N0645.d000859) ∧
    (_root_.GD.N0230.N0645.d000856 _root_.GD.N0230.N0645.d000860 = _root_.GD.N0230.N0645.d000860) ∧
    (¬ _root_.GD.N0230.N0630.d000786 _root_.GD.N0230.N0645.d000857 _root_.GD.N0230.N0645.d000860) ∧
    _root_.GD.N0230.N0645.d000851
      (fun _ : Unit ↦ fun x : ℝ ↦ 1 - x)
      (Set.Icc (0 : ℝ) 1) ({(1 / 2 : ℝ)} : Set ℝ) ∧
    (∀ L : Set ℝ,
      _root_.GD.N0230.N0645.d000851
        (fun _ : Unit ↦ fun x : ℝ ↦ 1 - x)
        (Set.Icc (0 : ℝ) 1) L →
      L ⊆ ({(1 / 2 : ℝ)} : Set ℝ) →
      ({(1 / 2 : ℝ)} : Set ℝ) ⊆ L) := by
  exact ⟨_root_.GD.N0230.N0645.d000865,
    _root_.GD.N0230.N0645.d000866,
    _root_.GD.N0230.N0645.d000869,
    _root_.GD.N0230.N0645.d000868,
    _root_.GD.N0230.N0645.d000872,
    _root_.GD.N0230.N0645.d000873⟩

end

end N0645
end N0230
end GD

#print axioms _root_.GD.N0230.N0645.d000850
#print axioms _root_.GD.N0230.N0645.d000853
#print axioms _root_.GD.N0230.N0645.d000865
#print axioms _root_.GD.N0230.N0645.d000874
