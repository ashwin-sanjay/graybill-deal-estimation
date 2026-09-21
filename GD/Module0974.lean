import GD.Module0973
import GD.Module0045




























open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace GD
namespace N0232
namespace N0720
namespace N1110

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0685
open _root_.GD.N0230.N0648
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1102



variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]




theorem d015455
    (C : ℕ → Set H) (p : ℕ → H)
    (hanti : Antitone C)
    (hp : ∀ N, _root_.GD.N0230.N0685.d000511 (C N) 0 (p N))
    (B : ℝ) (hbound : ∀ N, ‖p N‖ ^ 2 ≤ B) :
    CauchySeq p := by
  have hmono : Monotone (fun N ↦ ‖p N‖ ^ 2) := by
    intro N M hNM
    have htax := _root_.GD.N0230.N0648.d000574 C p hanti hp hNM
    nlinarith [sq_nonneg ‖p M - p N‖]
  have hbdd : BddAbove (Set.range (fun N ↦ ‖p N‖ ^ 2)) := by
    exact ⟨B, Set.forall_mem_range.2 hbound⟩
  have hscalar : CauchySeq (fun N ↦ ‖p N‖ ^ 2) :=
    (tendsto_atTop_ciSup hmono hbdd).cauchySeq
  rw [Metric.cauchySeq_iff] at hscalar ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hscalar (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, ?_⟩
  intro i hi j hj
  rcases le_total i j with hij | hji
  · have htax := _root_.GD.N0230.N0648.d000574 C p hanti hp hij
    have hdiff := hN j hj i hi
    rw [Real.dist_eq] at hdiff
    have hnonneg : 0 ≤ ‖p j‖ ^ 2 - ‖p i‖ ^ 2 :=
      sub_nonneg.mpr (hmono hij)
    have hsq : ‖p j - p i‖ ^ 2 < ε ^ 2 := by
      rw [abs_of_nonneg hnonneg] at hdiff
      linarith
    rw [dist_eq_norm]
    have hrev : ‖p i - p j‖ = ‖p j - p i‖ := norm_sub_rev _ _
    rw [hrev]
    by_contra hcon
    push Not at hcon
    exact absurd hsq
      (not_lt.mpr (pow_le_pow_left₀ hε.le hcon 2))
  · have htax := _root_.GD.N0230.N0648.d000574 C p hanti hp hji
    have hdiff := hN i hi j hj
    rw [Real.dist_eq] at hdiff
    have hnonneg : 0 ≤ ‖p i‖ ^ 2 - ‖p j‖ ^ 2 :=
      sub_nonneg.mpr (hmono hji)
    have hsq : ‖p i - p j‖ ^ 2 < ε ^ 2 := by
      rw [abs_of_nonneg hnonneg] at hdiff
      linarith
    rw [dist_eq_norm]
    by_contra hcon
    push Not at hcon
    exact absurd hsq
      (not_lt.mpr (pow_le_pow_left₀ hε.le hcon 2))



variable (m n : ℕ)


def d015456
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n) (N : ℕ) :
    Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
  {d | ∀ i, i ≤ N → _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d}

theorem d015457
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n) (N : ℕ) :
    IsClosed (_root_.GD.N0232.N0720.N1110.d015456 m n seed N) := by
  unfold _root_.GD.N0232.N0720.N1110.d015456
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun i ↦
    isClosed_iInter fun _ ↦ _root_.GD.N0232.N0720.N1159.d014631 m n (seed i).value

theorem d015458
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n) (N : ℕ) :
    Convex ℝ (_root_.GD.N0232.N0720.N1110.d015456 m n seed N) := by
  unfold _root_.GD.N0232.N0720.N1110.d015456
  simp only [Set.setOf_forall]
  exact convex_iInter fun i ↦
    convex_iInter fun _ ↦ _root_.GD.N0232.N0720.N1159.d014632 m n (seed i).value

theorem d015459
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n) :
    Antitone (_root_.GD.N0232.N0720.N1110.d015456 m n seed) := by
  intro N M hNM d hd i hi
  exact hd i (hi.trans hNM)



def d015460
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n) : Prop :=
  ∀ u : Finset ℕ, ∃ d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
    ∀ i ∈ u, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d

theorem d015461
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hfinite : _root_.GD.N0232.N0720.N1110.d015460 m n seed) (N : ℕ) :
    (_root_.GD.N0232.N0720.N1110.d015456 m n seed N).Nonempty := by
  obtain ⟨d, hd⟩ := hfinite (Finset.range (N + 1))
  refine ⟨d, ?_⟩
  intro i hi
  exact hd i (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hi))




theorem d015462
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hfinite : _root_.GD.N0232.N0720.N1110.d015460 m n seed) :
    ∃ d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
      ∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d := by
  let C : ℕ → Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
    _root_.GD.N0232.N0720.N1110.d015456 m n seed
  have hne : ∀ N, (C N).Nonempty := by
    intro N
    exact _root_.GD.N0232.N0720.N1110.d015461
      m n seed hfinite N
  have hclosed : ∀ N, IsClosed (C N) := by
    intro N
    exact _root_.GD.N0232.N0720.N1110.d015457 m n seed N
  have hconvex : ∀ N, Convex ℝ (C N) := by
    intro N
    exact _root_.GD.N0232.N0720.N1110.d015458 m n seed N
  have hproj : ∀ N, ∃ p, _root_.GD.N0230.N0685.d000511 (C N) 0 p := by
    intro N
    exact _root_.GD.N0230.N0685.d000521 (hne N) (hclosed N).isComplete (hconvex N) 0
  choose p hp using hproj
  have hbound : ∀ N, ‖p N‖ ^ 2 ≤ ‖(seed 0).value‖ ^ 2 := by
    intro N
    have hpBelow : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed 0).value (p N) :=
      (hp N).1 0 (Nat.zero_le N)
    have href := hpBelow _root_.GD.N0232.N0720.N1080.d014169
    rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
    simp only [zero_sub, norm_neg] at href
    exact (ENNReal.ofReal_le_ofReal_iff
      (sq_nonneg ‖(seed 0).value‖)).mp href
  have hpCauchy : CauchySeq p :=
    _root_.GD.N0232.N0720.N1110.d015455
      C p (_root_.GD.N0232.N0720.N1110.d015459 m n seed) hp
      (‖(seed 0).value‖ ^ 2) hbound
  obtain ⟨d, hd⟩ := cauchySeq_tendsto_of_complete hpCauchy
  refine ⟨d, ?_⟩
  intro i
  apply (_root_.GD.N0232.N0720.N1159.d014631 m n (seed i).value).mem_of_tendsto hd
  filter_upwards [eventually_ge_atTop i] with N hN
  exact (hp N).1 i hN



theorem d015463
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hfinite : _root_.GD.N0232.N0720.N1110.d015460 m n seed)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.d015333 m n (seed i) < ε)
    (iStrict : ℕ)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed iStrict).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  obtain ⟨d, hbelow⟩ :=
    _root_.GD.N0232.N0720.N1110.d015462
      m n seed hfinite
  exact _root_.GD.N0232.N0720.N1102.d015433
    m n hm hn seed d hsmall hbelow iStrict hstrict



def d015464
    (hm : 2 ≤ m) (hn : 2 ≤ n) : Prop :=
  ∃ seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n,
    _root_.GD.N0232.N0720.N1110.d015460 m n seed ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.d015333 m n (seed i) < ε) ∧
    ∃ iStrict, _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed iStrict).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)


theorem d015465
    (hm : 2 ≤ m) (hn : 2 ≤ n) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ↔
      _root_.GD.N0232.N0720.N1110.d015464 m n hm hn := by
  constructor
  · intro hendpoint
    obtain ⟨s, hstrict, hgap⟩ :=
      (_root_.GD.N0232.N0720.N1201.d015341
        m n hm hn).1 hendpoint
    refine ⟨fun _ ↦ s, ?_, ?_, 0, ?_⟩
    · intro u
      refine ⟨s.value, ?_⟩
      intro i hi
      change _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value s.value
      exact _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
    · intro ε hε
      refine ⟨0, ?_⟩
      change _root_.GD.N0232.N0720.N1201.d015333 m n s < ε
      rw [hgap]
      exact hε
    · change _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
        s.value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)
      exact hstrict
  · rintro ⟨seed, hfinite, hsmall, iStrict, hstrict⟩
    exact
      _root_.GD.N0232.N0720.N1110.d015463
        m n hm hn seed hfinite hsmall iStrict hstrict



theorem d015466
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hno : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.d015333 m n (seed i) < ε)
    (iStrict : ℕ)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed iStrict).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ∃ u : Finset ℕ,
      ¬ ∃ d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
        ∀ i ∈ u, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d := by
  by_contra hcontra
  apply hno
  apply _root_.GD.N0232.N0720.N1110.d015463
    m n hm hn seed _ hsmall iStrict hstrict
  intro u
  by_contra hu
  exact hcontra ⟨u, hu⟩



theorem d015467
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hno : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.d015333 m n (seed i) < ε)
    (iStrict : ℕ)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed iStrict).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ∃ N, _root_.GD.N0232.N0720.N1110.d015456 m n seed N = ∅ := by
  obtain ⟨u, hu⟩ :=
    _root_.GD.N0232.N0720.N1110.d015466
      m n hm hn hno seed hsmall iStrict hstrict
  refine ⟨u.sup id, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  intro d hd
  apply hu
  refine ⟨d, ?_⟩
  intro i hi
  exact hd i (Finset.le_sup (f := id) hi)



variable {I : Type*}





theorem d015468
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : I → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hfinite : ∀ u : Finset I,
      ∃ d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
        ∀ i ∈ u, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.d015333 m n (seed i) < ε)
    (iStrict : I)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed iStrict).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  classical
  have hchoose : ∀ N : ℕ, ∃ i : I,
      _root_.GD.N0232.N0720.N1201.d015333 m n (seed i) <
        1 / ((N : ℝ) + 1) := by
    intro N
    exact hsmall (1 / ((N : ℝ) + 1)) (by positivity)
  choose pick hpick using hchoose
  let index : ℕ → I
    | 0 => iStrict
    | N + 1 => pick N
  let seq : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n := fun N ↦ seed (index N)
  have hseqFinite : _root_.GD.N0232.N0720.N1110.d015460 m n seq := by
    intro u
    obtain ⟨d, hd⟩ := hfinite (u.image index)
    refine ⟨d, ?_⟩
    intro N hN
    exact hd (index N) (Finset.mem_image.mpr ⟨N, hN, rfl⟩)
  have hgapTendsto : Tendsto
      (fun N ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed (pick N)))
      atTop (nhds 0) := by
    exact squeeze_zero
      (fun N ↦ _root_.GD.N0232.N0720.N1201.d015334 m n (seed (pick N)))
      (fun N ↦ (hpick N).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hseqSmall : ∀ ε : ℝ, 0 < ε →
      ∃ N, _root_.GD.N0232.N0720.N1201.d015333 m n (seq N) < ε := by
    intro ε hε
    rw [Metric.tendsto_atTop] at hgapTendsto
    obtain ⟨N, hN⟩ := hgapTendsto ε hε
    refine ⟨N + 1, ?_⟩
    have h := hN N le_rfl
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (_root_.GD.N0232.N0720.N1201.d015334 m n (seed (pick N)))] at h
    simpa [seq, index] using h
  apply _root_.GD.N0232.N0720.N1110.d015463
    m n hm hn seq hseqFinite hseqSmall 0
  simpa [seq, index] using hstrict






theorem d015469
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : I → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.d015333 m n (seed i) < ε)
    (iStrict : I)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed iStrict).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n ∨
      ∃ u : Finset I,
        ¬ ∃ d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
          ∀ i ∈ u, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d := by
  classical
  by_cases hendpoint : _root_.GD.N0232.N0720.N1159.d014661 m n
  · exact Or.inl hendpoint
  · right
    by_contra hcontra
    apply hendpoint
    apply
      _root_.GD.N0232.N0720.N1110.d015468
        m n hm hn seed _ hsmall iStrict hstrict
    intro u
    by_contra hu
    exact hcontra ⟨u, hu⟩




theorem d015470
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hno : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n)
    (seed : I → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.d015333 m n (seed i) < ε)
    (iStrict : I)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed iStrict).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ∃ u : Finset I,
      ¬ ∃ d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
        ∀ i ∈ u, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d := by
  classical
  by_contra hcontra
  apply hno
  apply
    _root_.GD.N0232.N0720.N1110.d015468
      m n hm hn seed _ hsmall iStrict hstrict
  intro u
  by_contra hu
  exact hcontra ⟨u, hu⟩



namespace N1757

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0720.N1201.N1758
open _root_.GD.N0232.N0720.N1102.N1756

variable (k : ℕ) (sizes : Fin k → ℕ)

def d015471
    (seed : ℕ → _root_.GD.N0232.N0719.N0896.d011106 k sizes) (N : ℕ) :
    Set (_root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :=
  {d | ∀ i, i ≤ N → _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed i).value d}

theorem d015472
    (seed : ℕ → _root_.GD.N0232.N0719.N0896.d011106 k sizes) (N : ℕ) :
    IsClosed (_root_.GD.N0232.N0720.N1110.N1757.d015471 k sizes seed N) := by
  unfold _root_.GD.N0232.N0720.N1110.N1757.d015471
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun i ↦
    isClosed_iInter fun _ ↦ _root_.GD.N0232.N0719.N0896.d011097 k sizes (seed i).value

theorem d015473
    (seed : ℕ → _root_.GD.N0232.N0719.N0896.d011106 k sizes) (N : ℕ) :
    Convex ℝ (_root_.GD.N0232.N0720.N1110.N1757.d015471 k sizes seed N) := by
  unfold _root_.GD.N0232.N0720.N1110.N1757.d015471
  simp only [Set.setOf_forall]
  exact convex_iInter fun i ↦
    convex_iInter fun _ ↦ _root_.GD.N0232.N0719.N0896.d011098 k sizes (seed i).value

theorem d015474
    (seed : ℕ → _root_.GD.N0232.N0719.N0896.d011106 k sizes) :
    Antitone (_root_.GD.N0232.N0720.N1110.N1757.d015471 k sizes seed) := by
  intro N M hNM d hd i hi
  exact hd i (hi.trans hNM)

def d015475
    (seed : ℕ → _root_.GD.N0232.N0719.N0896.d011106 k sizes) : Prop :=
  ∀ u : Finset ℕ,
    ∃ d : _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes),
      ∀ i ∈ u, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed i).value d

theorem d015476
    (seed : ℕ → _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hfinite : _root_.GD.N0232.N0720.N1110.N1757.d015475 k sizes seed) (N : ℕ) :
    (_root_.GD.N0232.N0720.N1110.N1757.d015471 k sizes seed N).Nonempty := by
  obtain ⟨d, hd⟩ := hfinite (Finset.range (N + 1))
  refine ⟨d, ?_⟩
  intro i hi
  exact hd i (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hi))

theorem d015477
    (seed : ℕ → _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hfinite : _root_.GD.N0232.N0720.N1110.N1757.d015475 k sizes seed) :
    ∃ d : _root_.GD.N0230.N0602.d000116
        (_root_.GD.N0232.N0719.N0859.d010813 k sizes),
      ∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed i).value d := by
  let C : ℕ → Set (_root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :=
    _root_.GD.N0232.N0720.N1110.N1757.d015471 k sizes seed
  have hne : ∀ N, (C N).Nonempty := by
    intro N
    exact _root_.GD.N0232.N0720.N1110.N1757.d015476
      k sizes seed hfinite N
  have hclosed : ∀ N, IsClosed (C N) := by
    intro N
    exact _root_.GD.N0232.N0720.N1110.N1757.d015472 k sizes seed N
  have hconvex : ∀ N, Convex ℝ (C N) := by
    intro N
    exact _root_.GD.N0232.N0720.N1110.N1757.d015473 k sizes seed N
  have hproj : ∀ N, ∃ p, _root_.GD.N0230.N0685.d000511 (C N) 0 p := by
    intro N
    exact _root_.GD.N0230.N0685.d000521 (hne N) (hclosed N).isComplete (hconvex N) 0
  choose p hp using hproj
  have hbound : ∀ N, ‖p N‖ ^ 2 ≤ ‖(seed 0).value‖ ^ 2 := by
    intro N
    have hpBelow : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed 0).value (p N) :=
      (hp N).1 0 (Nat.zero_le N)
    have href := hpBelow (_root_.GD.N0232.N0719.N0859.d010810 k)
    rw [_root_.GD.N0232.N0719.N0859.d010829 k sizes, _root_.GD.N0232.N0719.N0859.d010829 k sizes] at href
    simp only [zero_sub, norm_neg] at href
    exact (ENNReal.ofReal_le_ofReal_iff
      (sq_nonneg ‖(seed 0).value‖)).mp href
  have hpCauchy : CauchySeq p :=
    _root_.GD.N0232.N0720.N1110.d015455
      C p (_root_.GD.N0232.N0720.N1110.N1757.d015474 k sizes seed) hp
      (‖(seed 0).value‖ ^ 2) hbound
  obtain ⟨d, hd⟩ := cauchySeq_tendsto_of_complete hpCauchy
  refine ⟨d, ?_⟩
  intro i
  apply (_root_.GD.N0232.N0719.N0896.d011097 k sizes (seed i).value).mem_of_tendsto hd
  filter_upwards [eventually_ge_atTop i] with N hN
  exact (hp N).1 i hN


theorem d015478
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (seed : ℕ → _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hfinite : _root_.GD.N0232.N0720.N1110.N1757.d015475 k sizes seed)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed i) < ε)
    (iStrict : ℕ)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (seed iStrict).value (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)) :
    _root_.GD.N0232.N0719.N0896.d011132 k sizes := by
  obtain ⟨d, hbelow⟩ :=
    _root_.GD.N0232.N0720.N1110.N1757.d015477
      k sizes seed hfinite
  exact _root_.GD.N0232.N0720.N1102.N1756.d015446
    k sizes hk hsizes seed d hsmall hbelow iStrict hstrict


def d015479
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) : Prop :=
  ∃ seed : ℕ → _root_.GD.N0232.N0719.N0896.d011106 k sizes,
    _root_.GD.N0232.N0720.N1110.N1757.d015475 k sizes seed ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed i) < ε) ∧
    ∃ iStrict, _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (seed iStrict).value (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)


theorem d015480
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0896.d011132 k sizes ↔
      _root_.GD.N0232.N0720.N1110.N1757.d015479 k sizes hk hsizes := by
  constructor
  · intro hendpoint
    obtain ⟨s, hstrict, hgap⟩ :=
      (_root_.GD.N0232.N0720.N1201.N1758.d015351
        k sizes hk hsizes).1 hendpoint
    refine ⟨fun _ ↦ s, ?_, ?_, 0, ?_⟩
    · intro u
      refine ⟨s.value, ?_⟩
      intro i hi
      change _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value s.value
      exact _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value
    · intro ε hε
      refine ⟨0, ?_⟩
      change _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes s < ε
      rw [hgap]
      exact hε
    · change _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
        s.value (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)
      exact hstrict
  · rintro ⟨seed, hfinite, hsmall, iStrict, hstrict⟩
    exact
      _root_.GD.N0232.N0720.N1110.N1757.d015478
        k sizes hk hsizes seed hfinite hsmall iStrict hstrict



theorem d015481
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hno : ¬ _root_.GD.N0232.N0719.N0896.d011132 k sizes)
    (seed : ℕ → _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed i) < ε)
    (iStrict : ℕ)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (seed iStrict).value (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)) :
    ∃ u : Finset ℕ,
      ¬ ∃ d : _root_.GD.N0230.N0602.d000116
          (_root_.GD.N0232.N0719.N0859.d010813 k sizes),
        ∀ i ∈ u, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed i).value d := by
  by_contra hcontra
  apply hno
  apply _root_.GD.N0232.N0720.N1110.N1757.d015478
    k sizes hk hsizes seed _ hsmall iStrict hstrict
  intro u
  by_contra hu
  exact hcontra ⟨u, hu⟩


theorem d015482
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hno : ¬ _root_.GD.N0232.N0719.N0896.d011132 k sizes)
    (seed : ℕ → _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed i) < ε)
    (iStrict : ℕ)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (seed iStrict).value (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)) :
    ∃ N, _root_.GD.N0232.N0720.N1110.N1757.d015471 k sizes seed N = ∅ := by
  obtain ⟨u, hu⟩ :=
    _root_.GD.N0232.N0720.N1110.N1757.d015481
      k sizes hk hsizes hno seed hsmall iStrict hstrict
  refine ⟨u.sup id, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  intro d hd
  apply hu
  refine ⟨d, ?_⟩
  intro i hi
  exact hd i (Finset.le_sup (f := id) hi)

variable {J : Type*}


theorem d015483
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (seed : J → _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hfinite : ∀ u : Finset J,
      ∃ d : _root_.GD.N0230.N0602.d000116
          (_root_.GD.N0232.N0719.N0859.d010813 k sizes),
        ∀ i ∈ u, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed i).value d)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed i) < ε)
    (iStrict : J)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (seed iStrict).value (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)) :
    _root_.GD.N0232.N0719.N0896.d011132 k sizes := by
  classical
  have hchoose : ∀ N : ℕ, ∃ i : J,
      _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed i) <
        1 / ((N : ℝ) + 1) := by
    intro N
    exact hsmall (1 / ((N : ℝ) + 1)) (by positivity)
  choose pick hpick using hchoose
  let index : ℕ → J
    | 0 => iStrict
    | N + 1 => pick N
  let seq : ℕ → _root_.GD.N0232.N0719.N0896.d011106 k sizes := fun N ↦ seed (index N)
  have hseqFinite : _root_.GD.N0232.N0720.N1110.N1757.d015475 k sizes seq := by
    intro u
    obtain ⟨d, hd⟩ := hfinite (u.image index)
    refine ⟨d, ?_⟩
    intro N hN
    exact hd (index N) (Finset.mem_image.mpr ⟨N, hN, rfl⟩)
  have hgapTendsto : Tendsto
      (fun N ↦ _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed (pick N)))
      atTop (nhds 0) := by
    exact squeeze_zero
      (fun N ↦ _root_.GD.N0232.N0720.N1201.N1758.d015344 k sizes (seed (pick N)))
      (fun N ↦ (hpick N).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hseqSmall : ∀ ε : ℝ, 0 < ε →
      ∃ N, _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seq N) < ε := by
    intro ε hε
    rw [Metric.tendsto_atTop] at hgapTendsto
    obtain ⟨N, hN⟩ := hgapTendsto ε hε
    refine ⟨N + 1, ?_⟩
    have h := hN N le_rfl
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg
        (_root_.GD.N0232.N0720.N1201.N1758.d015344 k sizes (seed (pick N)))] at h
    simpa [seq, index] using h
  apply _root_.GD.N0232.N0720.N1110.N1757.d015478
    k sizes hk hsizes seq hseqFinite hseqSmall 0
  simpa [seq, index] using hstrict




theorem d015484
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (seed : J → _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed i) < ε)
    (iStrict : J)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (seed iStrict).value (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)) :
    _root_.GD.N0232.N0719.N0896.d011132 k sizes ∨
      ∃ u : Finset J,
        ¬ ∃ d : _root_.GD.N0230.N0602.d000116
            (_root_.GD.N0232.N0719.N0859.d010813 k sizes),
          ∀ i ∈ u, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed i).value d := by
  classical
  by_cases hendpoint : _root_.GD.N0232.N0719.N0896.d011132 k sizes
  · exact Or.inl hendpoint
  · right
    by_contra hcontra
    apply hendpoint
    apply
      _root_.GD.N0232.N0720.N1110.N1757.d015483
        k sizes hk hsizes seed _ hsmall iStrict hstrict
    intro u
    by_contra hu
    exact hcontra ⟨u, hu⟩


theorem d015485
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hno : ¬ _root_.GD.N0232.N0719.N0896.d011132 k sizes)
    (seed : J → _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed i) < ε)
    (iStrict : J)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (seed iStrict).value (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)) :
    ∃ u : Finset J,
      ¬ ∃ d : _root_.GD.N0230.N0602.d000116
          (_root_.GD.N0232.N0719.N0859.d010813 k sizes),
        ∀ i ∈ u, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed i).value d := by
  classical
  by_contra hcontra
  apply hno
  apply
    _root_.GD.N0232.N0720.N1110.N1757.d015483
      k sizes hk hsizes seed _ hsmall iStrict hstrict
  intro u
  by_contra hu
  exact hcontra ⟨u, hu⟩

end N1757

end

end N1110
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1110.d015455
#print axioms _root_.GD.N0232.N0720.N1110.d015462
#print axioms _root_.GD.N0232.N0720.N1110.d015463
#print axioms _root_.GD.N0232.N0720.N1110.d015465
#print axioms _root_.GD.N0232.N0720.N1110.d015466
#print axioms _root_.GD.N0232.N0720.N1110.d015467
#print axioms _root_.GD.N0232.N0720.N1110.d015468
#print axioms _root_.GD.N0232.N0720.N1110.d015469
#print axioms _root_.GD.N0232.N0720.N1110.d015470
#print axioms _root_.GD.N0232.N0720.N1110.N1757.d015477
#print axioms _root_.GD.N0232.N0720.N1110.N1757.d015478
#print axioms _root_.GD.N0232.N0720.N1110.N1757.d015480
#print axioms _root_.GD.N0232.N0720.N1110.N1757.d015481
#print axioms _root_.GD.N0232.N0720.N1110.N1757.d015482
#print axioms _root_.GD.N0232.N0720.N1110.N1757.d015483
#print axioms _root_.GD.N0232.N0720.N1110.N1757.d015484
#print axioms _root_.GD.N0232.N0720.N1110.N1757.d015485
