import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.Topology.Algebra.ContinuousAffineMap
import Mathlib.Topology.Sequences
import GD.Module0086
























namespace GD
namespace N0230
namespace N0709

open Filter Function Set
open scoped Topology
open _root_.GD.N0230.N0703

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



def d001221 (C : Set (WeakSpace ℝ E)) : Prop :=
  Bornology.IsBounded ((toWeakSpace ℝ E).symm '' C)


theorem d001221.d001222
    {C K : Set (WeakSpace ℝ E)}
    (hC : _root_.GD.N0230.N0709.d001221 C) (hKC : K ⊆ C) :
    _root_.GD.N0230.N0709.d001221 K := by
  exact hC.subset (image_mono hKC)



theorem d001223
    (f : WeakSpace ℝ E →ᴬ[ℝ] WeakSpace ℝ E)
    (x : WeakSpace ℝ E) {n : ℕ} (hn : n ≠ 0) :
    f (birkhoffAverage ℝ (fun y ↦ f y) id n x) =
      birkhoffAverage ℝ (fun y ↦ f y) id n (f x) := by
  classical
  let w : ℕ → ℝ := fun _ ↦ (n : ℝ)⁻¹
  let p : ℕ → WeakSpace ℝ E :=
    fun k ↦ ((fun y ↦ f y)^[k]) x
  have hw : ∑ k ∈ Finset.range n, w k = 1 := by
    simp [w, hn]
  simp only [birkhoffAverage, birkhoffSum, id_eq]
  rw [Finset.smul_sum, Finset.smul_sum]
  change f (∑ k ∈ Finset.range n, w k • p k) =
    ∑ k ∈ Finset.range n,
      w k • ((fun y ↦ f y)^[k]) (f x)
  rw [← Finset.affineCombination_eq_linear_combination
    (Finset.range n) p w hw]
  calc
    f ((Finset.range n).affineCombination ℝ p w) =
        (Finset.range n).affineCombination ℝ (f ∘ p) w := by
          simpa using Finset.map_affineCombination
            (Finset.range n) p w hw f.toAffineMap
    _ = ∑ k ∈ Finset.range n,
        w k • ((fun y ↦ f y)^[k]) (f x) := by
          rw [Finset.affineCombination_eq_linear_combination _ _ _ hw]
          apply Finset.sum_congr rfl
          intro k hk
          simp only [Function.comp_apply]
          apply congrArg (w k • ·)
          change f (((fun y ↦ f y)^[k]) x) =
            ((fun y ↦ f y)^[k]) (f x)
          exact (Function.Commute.self_iterate (fun y ↦ f y) k).eq x



theorem d001224
    (f : WeakSpace ℝ E →ᴬ[ℝ] WeakSpace ℝ E)
    (C : Set (WeakSpace ℝ E))
    (hconvex : Convex ℝ C) (hmaps : MapsTo f C C)
    {x : WeakSpace ℝ E} (hx : x ∈ C) {n : ℕ} (hn : n ≠ 0) :
    birkhoffAverage ℝ (fun y ↦ f y) id n x ∈ C := by
  have horbit : ∀ k : ℕ, ((fun y ↦ f y)^[k]) x ∈ C := by
    intro k
    induction k with
    | zero => simpa
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hmaps ih
  rw [birkhoffAverage, birkhoffSum, Finset.smul_sum]
  apply hconvex.sum_mem
  · intro k hk
    positivity
  · simp [hn]
  · intro k hk
    simpa using horbit k



theorem d001225
    (f : WeakSpace ℝ E →ᴬ[ℝ] WeakSpace ℝ E)
    (C : Set (WeakSpace ℝ E))
    (hbounded : _root_.GD.N0230.N0709.d001221 C)
    (hmaps : MapsTo f C C)
    {x : WeakSpace ℝ E} (hx : x ∈ C) :
    Tendsto
      (fun n ↦
        birkhoffAverage ℝ (fun y ↦ f y)
            (fun y ↦ (toWeakSpace ℝ E).symm y) n (f x) -
          birkhoffAverage ℝ (fun y ↦ f y)
            (fun y ↦ (toWeakSpace ℝ E).symm y) n x)
      atTop (nhds 0) := by
  have horbit : ∀ k : ℕ, ((fun y ↦ f y)^[k]) x ∈ C := by
    intro k
    induction k with
    | zero => simpa
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact hmaps ih
  have horbitBounded : Bornology.IsBounded
      (range (fun k : ℕ ↦
        (toWeakSpace ℝ E).symm (((fun y ↦ f y)^[k]) x))) := by
    apply hbounded.subset
    rintro y ⟨k, rfl⟩
    exact ⟨((fun y ↦ f y)^[k]) x, horbit k, rfl⟩
  exact tendsto_birkhoffAverage_apply_sub_birkhoffAverage
    (𝕜 := ℝ) horbitBounded




theorem d001226
    (f : WeakSpace ℝ E →ᴬ[ℝ] WeakSpace ℝ E)
    (C : Set (WeakSpace ℝ E))
    (hbounded : _root_.GD.N0230.N0709.d001221 C)
    (hmaps : MapsTo f C C)
    {x : WeakSpace ℝ E} (hx : x ∈ C) :
    Tendsto
      (fun n ↦
        f (birkhoffAverage ℝ (fun y ↦ f y) id (n + 1) x) -
          birkhoffAverage ℝ (fun y ↦ f y) id (n + 1) x)
      atTop (nhds 0) := by
  have hstrong :=
    _root_.GD.N0230.N0709.d001225
      f C hbounded hmaps hx
  have hweak : Tendsto
      (fun n ↦ toWeakSpace ℝ E
        (birkhoffAverage ℝ (fun y ↦ f y)
            (fun y ↦ (toWeakSpace ℝ E).symm y) n (f x) -
          birkhoffAverage ℝ (fun y ↦ f y)
            (fun y ↦ (toWeakSpace ℝ E).symm y) n x))
      atTop (nhds 0) := by
    have hmap :=
      (toWeakSpaceCLM ℝ E).continuous.continuousAt.tendsto.comp hstrong
    simpa [Function.comp_def] using hmap
  refine (hweak.comp (tendsto_add_atTop_nat 1)).congr'
    (Eventually.of_forall fun n ↦ ?_)
  simp only [Function.comp_apply]
  rw [_root_.GD.N0230.N0709.d001223 f x (Nat.add_one_ne_zero n)]
  rfl



theorem d001227
    (f : WeakSpace ℝ E →ᴬ[ℝ] WeakSpace ℝ E)
    (C : Set (WeakSpace ℝ E))
    (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hne : C.Nonempty) (hbounded : _root_.GD.N0230.N0709.d001221 C)
    (hmaps : MapsTo f C C) :
    ∃ x ∈ C, f x = x := by
  obtain ⟨x, hx⟩ := hne
  let avg : ℕ → WeakSpace ℝ E := fun n ↦
    birkhoffAverage ℝ (fun y ↦ f y) id (n + 1) x
  have havgC : ∀ n, avg n ∈ C := by
    intro n
    exact _root_.GD.N0230.N0709.d001224 f C hconvex hmaps hx
      (Nat.add_one_ne_zero n)
  have hdisplacement : Tendsto (fun n ↦ f (avg n) - avg n)
      atTop (nhds 0) := by
    exact _root_.GD.N0230.N0709.d001226
      f C hbounded hmaps hx
  have hdispContinuous : Continuous
      (fun z : WeakSpace ℝ E ↦ f z - z) :=
    f.continuous.sub continuous_id
  have hdispCompact : IsCompact
      ((fun z : WeakSpace ℝ E ↦ f z - z) '' C) :=
    hcompact.image hdispContinuous
  have hzeroMem : (0 : WeakSpace ℝ E) ∈
      ((fun z : WeakSpace ℝ E ↦ f z - z) '' C) := by
    apply hdispCompact.isClosed.mem_of_tendsto hdisplacement
    exact Eventually.of_forall fun n ↦ ⟨avg n, havgC n, rfl⟩
  obtain ⟨y, hyC, hy⟩ := hzeroMem
  exact ⟨y, hyC, sub_eq_zero.mp hy⟩




theorem d001228
    {I : Type*}
    (act : I → (WeakSpace ℝ E →ᴬ[ℝ] WeakSpace ℝ E))
    (C : Set (WeakSpace ℝ E))
    (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hne : C.Nonempty) (hbounded : _root_.GD.N0230.N0709.d001221 C)
    (hmaps : ∀ i, MapsTo (act i) C C)
    (hcomm : ∀ i j, Function.Commute (act i) (act j))
    (s : Finset I) :
    ∃ x ∈ C, ∀ i ∈ s, act i x = x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, hx, by simp⟩
  | @insert i s hi ih =>
      let K : Set (WeakSpace ℝ E) := _root_.GD.N0230.N0703.d001139
        (fun j : ↑s ↦ act j) C
      have hKcompact : IsCompact K :=
        _root_.GD.N0230.N0703.d001144 (fun j : ↑s ↦ act j) C hcompact
          (fun j ↦ (act j).continuous)
      have hKconvex : Convex ℝ K :=
        _root_.GD.N0230.N0703.d001146 (fun j : ↑s ↦ act j) C hconvex
      have hKne : K.Nonempty := by
        obtain ⟨x, hxC, hxs⟩ := ih
        exact ⟨x, hxC, fun j ↦ hxs j j.property⟩
      have hKbounded : _root_.GD.N0230.N0709.d001221 K :=
        hbounded.d001222 (_root_.GD.N0230.N0703.d001141
          (fun j : ↑s ↦ act j) C)
      have hmapK : MapsTo (act i) K K := by
        intro x hx
        refine ⟨hmaps i hx.1, ?_⟩
        intro j
        calc
          act j (act i x) = act i (act j x) :=
            ((hcomm i j).eq x).symm
          _ = act i x := congrArg (act i) (hx.2 j)
      obtain ⟨x, hxK, hfixi⟩ :=
        _root_.GD.N0230.N0709.d001227
          (act i) K hKcompact hKconvex hKne hKbounded hmapK
      refine ⟨x, hxK.1, ?_⟩
      intro j hj
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact hfixi
      · exact hxK.2 ⟨j, hj⟩






theorem d001229
    {I : Type*}
    (act : I → (WeakSpace ℝ E →ᴬ[ℝ] WeakSpace ℝ E))
    (C : Set (WeakSpace ℝ E))
    (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hne : C.Nonempty) (hbounded : _root_.GD.N0230.N0709.d001221 C)
    (hmaps : ∀ i, MapsTo (act i) C C)
    (hcomm : ∀ i j, Function.Commute (act i) (act j)) :
    ∃ x ∈ C, ∀ i, act i x = x := by
  classical
  have hall :
      (C ∩ ⋂ i, fixedPoints (act i)).Nonempty :=
    hcompact.inter_iInter_nonempty
      (fun i ↦ fixedPoints (act i))
      (fun i ↦ isClosed_fixedPoints (act i).continuous)
      (fun s ↦ by
        obtain ⟨x, hxC, hxs⟩ :=
          _root_.GD.N0230.N0709.d001228
            act C hcompact hconvex hne hbounded hmaps hcomm s
        refine ⟨x, hxC, ?_⟩
        rw [mem_iInter]
        intro i
        rw [mem_iInter]
        intro hi
        exact mem_fixedPoints_iff.mpr (hxs i hi))
  obtain ⟨x, hxC, hxfixed⟩ := hall
  refine ⟨x, hxC, ?_⟩
  intro i
  exact mem_fixedPoints_iff.mp (mem_iInter.mp hxfixed i)



theorem d001230
    {I : Type*}
    (act : I → (WeakSpace ℝ E →ᴬ[ℝ] WeakSpace ℝ E))
    (C : Set (WeakSpace ℝ E))
    (hbounded : _root_.GD.N0230.N0709.d001221 C) :
    _root_.GD.N0230.N0703.d001149 act C := by
  intro hcompact hconvex hne hmaps hcomm
  obtain ⟨x, hxC, hfix⟩ :=
    _root_.GD.N0230.N0709.d001229
      act C hcompact hconvex hne hbounded hmaps hcomm
  exact ⟨x, hxC, hfix⟩






theorem d001231
    {T A : Type*}
    (inner : T →
      (WeakSpace ℝ E →ᴬ[ℝ] WeakSpace ℝ E))
    (outer : A →
      (WeakSpace ℝ E →ᴬ[ℝ] WeakSpace ℝ E))
    (C : Set (WeakSpace ℝ E))
    (hcompact : IsCompact C)
    (hconvex : Convex ℝ C)
    (hne : C.Nonempty)
    (hbounded : _root_.GD.N0230.N0709.d001221 C)
    (hinnerC : ∀ t, MapsTo (inner t) C C)
    (hinnerCommutes : _root_.GD.N0230.N0703.d001148 (fun t ↦ inner t))
    (hnormal : _root_.GD.N0230.N0703.d001147 (fun a ↦ outer a) (fun t ↦ inner t))
    (houterC : ∀ a, MapsTo (outer a) C C)
    (houterCommutes : _root_.GD.N0230.N0703.d001148 (fun a ↦ outer a)) :
    ∃ x, x ∈ C ∧ (∀ t, inner t x = x) ∧
      ∀ a, outer a x = x := by
  exact _root_.GD.N0230.N0703.d001153
    inner outer C hcompact hconvex hne hinnerC hinnerCommutes
    hnormal houterC houterCommutes
    (_root_.GD.N0230.N0709.d001230 inner C hbounded)
    (_root_.GD.N0230.N0709.d001230 outer
      (_root_.GD.N0230.N0703.d001139 (fun t ↦ inner t) C)
      (hbounded.d001222 (_root_.GD.N0230.N0703.d001141
        (fun t ↦ inner t) C)))

#print axioms _root_.GD.N0230.N0709.d001227
#print axioms _root_.GD.N0230.N0709.d001228
#print axioms _root_.GD.N0230.N0709.d001229
#print axioms _root_.GD.N0230.N0709.d001230
#print axioms _root_.GD.N0230.N0709.d001231

end N0709
end N0230
end GD
