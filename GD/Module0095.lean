import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import GD.Module0094
















namespace GD
namespace N0230
namespace N0710

open Filter Function Set
open scoped Topology
open _root_.GD.N0230.N0709
open _root_.GD.N0230.N0703

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section




def d001232
    (f : WeakSpace ℝ E → WeakSpace ℝ E)
    (C : Set (WeakSpace ℝ E)) : Prop :=
  ∀ ⦃x⦄, x ∈ C → ∀ ⦃y⦄, y ∈ C →
    ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) = a • f x + b • f y



def d001233
    (f : WeakSpace ℝ E → WeakSpace ℝ E) :
    ℕ → WeakSpace ℝ E → WeakSpace ℝ E
  | 0, x => x
  | n + 1, x =>
      ((n + 1 : ℝ) / (n + 2 : ℝ)) • d001233 f n x +
        (1 / (n + 2 : ℝ)) • (f^[n + 1]) x

private theorem d001234 (n : ℕ) :
    0 ≤ (n + 1 : ℝ) / (n + 2 : ℝ) ∧
      0 ≤ 1 / (n + 2 : ℝ) := by
  constructor <;> positivity

private theorem d001235 (n : ℕ) :
    (n + 1 : ℝ) / (n + 2 : ℝ) + 1 / (n + 2 : ℝ) = 1 := by
  have hne : (n + 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

private theorem d001236
    (f : WeakSpace ℝ E → WeakSpace ℝ E)
    (C : Set (WeakSpace ℝ E))
    (hmaps : MapsTo f C C)
    {x : WeakSpace ℝ E} (hx : x ∈ C) :
    ∀ n, (f^[n]) x ∈ C := by
  intro n
  induction n with
  | zero => simpa
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact hmaps ih



theorem d001237
    (f : WeakSpace ℝ E → WeakSpace ℝ E)
    (C : Set (WeakSpace ℝ E))
    (hconvex : Convex ℝ C) (hmaps : MapsTo f C C)
    {x : WeakSpace ℝ E} (hx : x ∈ C) :
    ∀ n, _root_.GD.N0230.N0710.d001233 f n x ∈ C := by
  intro n
  induction n with
  | zero => simpa [_root_.GD.N0230.N0710.d001233]
  | succ n ih =>
      rw [_root_.GD.N0230.N0710.d001233]
      apply hconvex ih
      · exact _root_.GD.N0230.N0710.d001236 f C hmaps hx (n + 1)
      · exact (_root_.GD.N0230.N0710.d001234 n).1
      · exact (_root_.GD.N0230.N0710.d001234 n).2
      · exact _root_.GD.N0230.N0710.d001235 n



theorem d001238
    (f : WeakSpace ℝ E → WeakSpace ℝ E)
    (n : ℕ) (x : WeakSpace ℝ E) :
    _root_.GD.N0230.N0710.d001233 f n x = birkhoffAverage ℝ f id (n + 1) x := by
  induction n with
  | zero =>
      simp [_root_.GD.N0230.N0710.d001233, birkhoffAverage, birkhoffSum]
  | succ n ih =>
      rw [_root_.GD.N0230.N0710.d001233, ih, birkhoffAverage, birkhoffAverage]
      conv_rhs => rw [birkhoffSum_succ]
      have hcoef :
          ((n + 1 : ℝ) / (n + 2 : ℝ)) * (n + 1 : ℝ)⁻¹ =
            (n + 2 : ℝ)⁻¹ := by
        field_simp
      have hcoef' :
          (n + 1 : ℝ) * (n + 2 : ℝ)⁻¹ * (n + 1 : ℝ)⁻¹ =
            (n + 2 : ℝ)⁻¹ := by
        simpa [div_eq_mul_inv] using hcoef
      have hden : (n : ℝ) + 1 + 1 = n + 2 := by ring
      push_cast
      simp only [div_eq_mul_inv, one_mul, smul_add, smul_smul, id_eq]
      rw [hcoef', hden]



theorem d001239
    (f : WeakSpace ℝ E → WeakSpace ℝ E)
    (C : Set (WeakSpace ℝ E))
    (hconvex : Convex ℝ C) (hmaps : MapsTo f C C)
    (haffine : _root_.GD.N0230.N0710.d001232 f C)
    {x : WeakSpace ℝ E} (hx : x ∈ C) :
    ∀ n, f (_root_.GD.N0230.N0710.d001233 f n x) = _root_.GD.N0230.N0710.d001233 f n (f x) := by
  intro n
  induction n with
  | zero => simp [_root_.GD.N0230.N0710.d001233]
  | succ n ih =>
      rw [_root_.GD.N0230.N0710.d001233, _root_.GD.N0230.N0710.d001233]
      rw [haffine (_root_.GD.N0230.N0710.d001237 f C hconvex hmaps hx n)
        (_root_.GD.N0230.N0710.d001236 f C hmaps hx (n + 1))
        (_root_.GD.N0230.N0710.d001234 n).1
        (_root_.GD.N0230.N0710.d001234 n).2
        (_root_.GD.N0230.N0710.d001235 n)]
      rw [ih]
      rw [(Function.Commute.self_iterate f (n + 1)).eq x]




theorem d001240
    (f : WeakSpace ℝ E → WeakSpace ℝ E)
    (C : Set (WeakSpace ℝ E))
    (hbounded : _root_.GD.N0230.N0709.d001221 C)
    (hmaps : MapsTo f C C)
    {x : WeakSpace ℝ E} (hx : x ∈ C) :
    Tendsto
      (fun n ↦
        birkhoffAverage ℝ f
            (fun y ↦ (toWeakSpace ℝ E).symm y) n (f x) -
          birkhoffAverage ℝ f
            (fun y ↦ (toWeakSpace ℝ E).symm y) n x)
      atTop (nhds 0) := by
  have horbit : ∀ k : ℕ, (f^[k]) x ∈ C := by
    intro k
    exact _root_.GD.N0230.N0710.d001236 f C hmaps hx k
  have horbitBounded : Bornology.IsBounded
      (range (fun k : ℕ ↦ (toWeakSpace ℝ E).symm ((f^[k]) x))) := by
    apply hbounded.subset
    rintro y ⟨k, rfl⟩
    exact ⟨(f^[k]) x, horbit k, rfl⟩
  exact tendsto_birkhoffAverage_apply_sub_birkhoffAverage
    (𝕜 := ℝ) horbitBounded



theorem d001241
    (f : WeakSpace ℝ E → WeakSpace ℝ E)
    (C : Set (WeakSpace ℝ E))
    (hconvex : Convex ℝ C)
    (hbounded : _root_.GD.N0230.N0709.d001221 C)
    (hmaps : MapsTo f C C)
    (haffine : _root_.GD.N0230.N0710.d001232 f C)
    {x : WeakSpace ℝ E} (hx : x ∈ C) :
    Tendsto (fun n ↦ f (_root_.GD.N0230.N0710.d001233 f n x) - _root_.GD.N0230.N0710.d001233 f n x)
      atTop (nhds 0) := by
  have hstrong :=
    _root_.GD.N0230.N0710.d001240
      f C hbounded hmaps hx
  have hweak : Tendsto
      (fun n ↦ toWeakSpace ℝ E
        (birkhoffAverage ℝ f
            (fun y ↦ (toWeakSpace ℝ E).symm y) n (f x) -
          birkhoffAverage ℝ f
            (fun y ↦ (toWeakSpace ℝ E).symm y) n x))
      atTop (nhds 0) := by
    have hmap :=
      (toWeakSpaceCLM ℝ E).continuous.continuousAt.tendsto.comp hstrong
    simpa [Function.comp_def] using hmap
  refine (hweak.comp (tendsto_add_atTop_nat 1)).congr'
    (Eventually.of_forall fun n ↦ ?_)
  simp only [Function.comp_apply]
  rw [_root_.GD.N0230.N0710.d001239 f C hconvex hmaps haffine hx n,
    _root_.GD.N0230.N0710.d001238,
    _root_.GD.N0230.N0710.d001238]
  rfl




theorem d001242
    (f : WeakSpace ℝ E → WeakSpace ℝ E)
    (C : Set (WeakSpace ℝ E))
    (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hne : C.Nonempty) (hbounded : _root_.GD.N0230.N0709.d001221 C)
    (hmaps : MapsTo f C C)
    (hcontinuous : ContinuousOn f C)
    (haffine : _root_.GD.N0230.N0710.d001232 f C) :
    ∃ x ∈ C, f x = x := by
  obtain ⟨x, hx⟩ := hne
  have hmeanC : ∀ n, _root_.GD.N0230.N0710.d001233 f n x ∈ C :=
    _root_.GD.N0230.N0710.d001237 f C hconvex hmaps hx
  have hdisplacement :
      Tendsto (fun n ↦ f (_root_.GD.N0230.N0710.d001233 f n x) - _root_.GD.N0230.N0710.d001233 f n x)
        atTop (nhds 0) :=
    _root_.GD.N0230.N0710.d001241
      f C hconvex hbounded hmaps haffine hx
  have hdispContinuous : ContinuousOn
      (fun z : WeakSpace ℝ E ↦ f z - z) C :=
    hcontinuous.sub continuousOn_id
  have hdispCompact : IsCompact
      ((fun z : WeakSpace ℝ E ↦ f z - z) '' C) :=
    hcompact.image_of_continuousOn hdispContinuous
  have hzeroMem : (0 : WeakSpace ℝ E) ∈
      ((fun z : WeakSpace ℝ E ↦ f z - z) '' C) := by
    apply hdispCompact.isClosed.mem_of_tendsto hdisplacement
    exact Eventually.of_forall fun n ↦ ⟨_root_.GD.N0230.N0710.d001233 f n x, hmeanC n, rfl⟩
  obtain ⟨y, hyC, hy⟩ := hzeroMem
  exact ⟨y, hyC, sub_eq_zero.mp hy⟩



theorem d001243
    {I : Type*}
    (act : I → WeakSpace ℝ E → WeakSpace ℝ E)
    (C : Set (WeakSpace ℝ E))
    (hC : IsClosed C)
    (hcontinuous : ∀ i, ContinuousOn (act i) C) :
    IsClosed (_root_.GD.N0230.N0703.d001139 act C) := by
  have heq : _root_.GD.N0230.N0703.d001139 act C =
      C ∩ ⋂ i, {x | x ∈ C ∧ act i x = x} := by
    ext x
    constructor
    · rintro ⟨hxC, hfix⟩
      exact ⟨hxC, mem_iInter.mpr fun i ↦ ⟨hxC, hfix i⟩⟩
    · rintro ⟨hxC, hall⟩
      exact ⟨hxC, fun i ↦ (mem_iInter.mp hall i).2⟩
  rw [heq]
  exact hC.inter (isClosed_iInter fun i ↦
    hC.isClosed_eq (hcontinuous i) continuousOn_id)



theorem d001244
    {I : Type*}
    (act : I → WeakSpace ℝ E → WeakSpace ℝ E)
    (C : Set (WeakSpace ℝ E))
    (hC : IsCompact C)
    (hcontinuous : ∀ i, ContinuousOn (act i) C) :
    IsCompact (_root_.GD.N0230.N0703.d001139 act C) := by
  refine hC.of_isClosed_subset
    (_root_.GD.N0230.N0710.d001243 act C hC.isClosed hcontinuous)
    (_root_.GD.N0230.N0703.d001141 act C)



theorem d001245
    {I : Type*}
    (act : I → WeakSpace ℝ E → WeakSpace ℝ E)
    (C : Set (WeakSpace ℝ E))
    (hC : Convex ℝ C)
    (haffine : ∀ i, _root_.GD.N0230.N0710.d001232 (act i) C) :
    Convex ℝ (_root_.GD.N0230.N0703.d001139 act C) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hC hx.1 hy.1 ha hb hab, ?_⟩
  intro i
  rw [haffine i hx.1 hy.1 ha hb hab, hx.2 i, hy.2 i]



theorem d001246
    {I : Type*}
    (act : I → WeakSpace ℝ E → WeakSpace ℝ E)
    (C : Set (WeakSpace ℝ E))
    (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hne : C.Nonempty) (hbounded : _root_.GD.N0230.N0709.d001221 C)
    (hmaps : ∀ i, MapsTo (act i) C C)
    (hcontinuous : ∀ i, ContinuousOn (act i) C)
    (haffine : ∀ i, _root_.GD.N0230.N0710.d001232 (act i) C)
    (hcomm : ∀ i j, Function.Commute (act i) (act j))
    (s : Finset I) :
    ∃ x ∈ C, ∀ i ∈ s, act i x = x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, hx, by simp⟩
  | @insert i s hi ih =>
      let K : Set (WeakSpace ℝ E) :=
        _root_.GD.N0230.N0703.d001139 (fun j : ↑s ↦ act j) C
      have hKcompact : IsCompact K :=
        _root_.GD.N0230.N0710.d001244
          (fun j : ↑s ↦ act j) C hcompact
          (fun j ↦ hcontinuous j)
      have hKconvex : Convex ℝ K :=
        _root_.GD.N0230.N0710.d001245
          (fun j : ↑s ↦ act j) C hconvex
          (fun j ↦ haffine j)
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
      have hcontK : ContinuousOn (act i) K :=
        (hcontinuous i).mono
          (_root_.GD.N0230.N0703.d001141 (fun j : ↑s ↦ act j) C)
      have haffineK : _root_.GD.N0230.N0710.d001232 (act i) K := by
        intro x hx y hy a b ha hb hab
        exact haffine i hx.1 hy.1 ha hb hab
      obtain ⟨x, hxK, hfixi⟩ :=
        _root_.GD.N0230.N0710.d001242
          (act i) K hKcompact hKconvex hKne hKbounded
          hmapK hcontK haffineK
      refine ⟨x, hxK.1, ?_⟩
      intro j hj
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact hfixi
      · exact hxK.2 ⟨j, hj⟩




theorem d001247
    {I : Type*}
    (act : I → WeakSpace ℝ E → WeakSpace ℝ E)
    (C : Set (WeakSpace ℝ E))
    (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hne : C.Nonempty) (hbounded : _root_.GD.N0230.N0709.d001221 C)
    (hmaps : ∀ i, MapsTo (act i) C C)
    (hcontinuous : ∀ i, ContinuousOn (act i) C)
    (haffine : ∀ i, _root_.GD.N0230.N0710.d001232 (act i) C)
    (hcomm : ∀ i j, Function.Commute (act i) (act j)) :
    ∃ x ∈ C, ∀ i, act i x = x := by
  classical
  have hall :
      (C ∩ ⋂ i, {x | x ∈ C ∧ act i x = x}).Nonempty :=
    hcompact.inter_iInter_nonempty
      (fun i ↦ {x | x ∈ C ∧ act i x = x})
      (fun i ↦ hcompact.isClosed.isClosed_eq
        (hcontinuous i) continuousOn_id)
      (fun s ↦ by
        obtain ⟨x, hxC, hxs⟩ :=
          _root_.GD.N0230.N0710.d001246
            act C hcompact hconvex hne hbounded hmaps
            hcontinuous haffine hcomm s
        refine ⟨x, hxC, ?_⟩
        rw [mem_iInter]
        intro i
        rw [mem_iInter]
        intro hi
        exact ⟨hxC, hxs i hi⟩)
  obtain ⟨x, hxC, hxfixed⟩ := hall
  refine ⟨x, hxC, ?_⟩
  intro i
  exact (mem_iInter.mp hxfixed i).2




theorem d001248
    {T A : Type*}
    (inner : T → WeakSpace ℝ E → WeakSpace ℝ E)
    (outer : A → WeakSpace ℝ E → WeakSpace ℝ E)
    (C : Set (WeakSpace ℝ E))
    (hcompact : IsCompact C) (hconvex : Convex ℝ C)
    (hne : C.Nonempty) (hbounded : _root_.GD.N0230.N0709.d001221 C)
    (hinnerC : ∀ t, MapsTo (inner t) C C)
    (hinnerContinuous : ∀ t, ContinuousOn (inner t) C)
    (hinnerAffine : ∀ t, _root_.GD.N0230.N0710.d001232 (inner t) C)
    (hinnerCommutes : _root_.GD.N0230.N0703.d001148 inner)
    (hnormal : _root_.GD.N0230.N0703.d001147 outer inner)
    (houterC : ∀ a, MapsTo (outer a) C C)
    (houterContinuous : ∀ a, ContinuousOn (outer a) C)
    (houterAffine : ∀ a, _root_.GD.N0230.N0710.d001232 (outer a) C)
    (houterCommutes : _root_.GD.N0230.N0703.d001148 outer) :
    ∃ x, x ∈ C ∧ (∀ t, inner t x = x) ∧
      ∀ a, outer a x = x := by
  obtain ⟨x, hxC, hxinner⟩ :=
    _root_.GD.N0230.N0710.d001247
      inner C hcompact hconvex hne hbounded hinnerC
      hinnerContinuous hinnerAffine hinnerCommutes
  let K : Set (WeakSpace ℝ E) := _root_.GD.N0230.N0703.d001139 inner C
  have hKcompact : IsCompact K :=
    _root_.GD.N0230.N0710.d001244 inner C hcompact hinnerContinuous
  have hKconvex : Convex ℝ K :=
    _root_.GD.N0230.N0710.d001245 inner C hconvex hinnerAffine
  have hKne : K.Nonempty := ⟨x, hxC, hxinner⟩
  have hKbounded : _root_.GD.N0230.N0709.d001221 K :=
    hbounded.d001222 (_root_.GD.N0230.N0703.d001141 inner C)
  have houterK : ∀ a, MapsTo (outer a) K K := by
    intro a y hy
    refine ⟨houterC a hy.1, ?_⟩
    intro t
    obtain ⟨t', ht'⟩ := hnormal a t
    have hpoint := congrFun ht' y
    simpa [Function.comp_apply, hy.2 t'] using hpoint
  have houterContK : ∀ a, ContinuousOn (outer a) K :=
    fun a ↦ (houterContinuous a).mono
      (_root_.GD.N0230.N0703.d001141 inner C)
  have houterAffineK : ∀ a,
      _root_.GD.N0230.N0710.d001232 (outer a) K := by
    intro a u hu v hv c d hc hd hcd
    exact houterAffine a hu.1 hv.1 hc hd hcd
  obtain ⟨y, hyK, hyouter⟩ :=
    _root_.GD.N0230.N0710.d001247
      outer K hKcompact hKconvex hKne hKbounded houterK
      houterContK houterAffineK houterCommutes
  exact ⟨y, hyK.1, hyK.2, hyouter⟩

end

end N0710
end N0230
end GD

#print axioms _root_.GD.N0230.N0710.d001238
#print axioms _root_.GD.N0230.N0710.d001239
#print axioms _root_.GD.N0230.N0710.d001242
#print axioms _root_.GD.N0230.N0710.d001247
#print axioms _root_.GD.N0230.N0710.d001248
