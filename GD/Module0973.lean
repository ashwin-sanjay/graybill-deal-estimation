import GD.Module0969





































open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace GD
namespace N0232
namespace N0720
namespace N1102

noncomputable section

open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229



variable {I H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]



theorem d015428
    (p : I → H) (gap : I → ℝ) (d e : H)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ i, gap i < ε)
    (hd : ∀ i, ‖d - p i‖ ^ 2 ≤ gap i)
    (he : ∀ i, ‖e - p i‖ ^ 2 ≤ gap i) :
    e = d := by
  by_contra hne
  have hdistPos : 0 < ‖e - d‖ ^ 2 := by
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))
  obtain ⟨i, hi⟩ := hsmall (‖e - d‖ ^ 2 / 4) (by positivity)
  have htri : ‖e - d‖ ≤ ‖e - p i‖ + ‖d - p i‖ := by
    calc
      ‖e - d‖ = ‖(e - p i) + (p i - d)‖ := by congr 1 <;> abel
      _ ≤ ‖e - p i‖ + ‖p i - d‖ := norm_add_le _ _
      _ = ‖e - p i‖ + ‖d - p i‖ := by
        rw [show ‖p i - d‖ = ‖d - p i‖ from norm_sub_rev _ _]
  have hdp := hd i
  have hep := he i
  nlinarith [norm_nonneg (e - d), norm_nonneg (e - p i),
    norm_nonneg (d - p i), sq_nonneg (‖e - p i‖ - ‖d - p i‖)]



variable (m n : ℕ)



theorem d015429
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hd : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value d) :
    ‖d - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1201.d015333 m n s := by
  have htax := _root_.GD.N0232.N0720.N1159.d014648
    m n s.value d hd
  have href := hd _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at href
  simp only [zero_sub, norm_neg] at href
  have hnorm : ‖d‖ ^ 2 ≤ ‖s.value‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖s.value‖)).mp href
  unfold _root_.GD.N0232.N0720.N1201.d015333
  linarith


theorem d015430
    (s t : _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hts : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value t.value) :
    _root_.GD.N0232.N0720.N1201.d015333 m n t ≤
      _root_.GD.N0232.N0720.N1201.d015333 m n s := by
  have htprojBelowS : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value
      (_root_.GD.N0232.N0720.N1159.d014633 m n t.value) :=
    _root_.GD.N0230.N0608.d000677 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1159.d014634 m n t.value).1 hts
  have hproj := (_root_.GD.N0232.N0720.N1159.d014634 m n s.value).2.2
    (_root_.GD.N0232.N0720.N1159.d014633 m n t.value) htprojBelowS
  have hseed := hts _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n, _root_.GD.N0232.N0720.N1080.d014190 m n] at hproj hseed
  simp only [zero_sub, norm_neg] at hproj hseed
  have hprojNorm :
      ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤
        ‖_root_.GD.N0232.N0720.N1159.d014633 m n t.value‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff
      (sq_nonneg ‖_root_.GD.N0232.N0720.N1159.d014633 m n t.value‖)).mp hproj
  have hseedNorm : ‖t.value‖ ^ 2 ≤ ‖s.value‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖s.value‖)).mp hseed
  unfold _root_.GD.N0232.N0720.N1201.d015333
  linarith



theorem d015431
    (seed : I → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (d e : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.d015333 m n (seed i) < ε)
    (hd : ∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d)
    (he : ∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value e) :
    e = d := by
  exact _root_.GD.N0232.N0720.N1102.d015428
    (fun i ↦ _root_.GD.N0232.N0720.N1159.d014633 m n (seed i).value)
    (fun i ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed i)) d e hsmall
    (fun i ↦ _root_.GD.N0232.N0720.N1102.d015429
      m n (seed i) d (hd i))
    (fun i ↦ _root_.GD.N0232.N0720.N1102.d015429
      m n (seed i) e (he i))




theorem d015432
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : I → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.d015333 m n (seed i) < ε)
    (hbelow : ∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) d ∧
      _root_.GD.N0232.N0720.N1159.d014652 m n d := by
  obtain ⟨i₀, _hi₀⟩ := hsmall 1 zero_lt_one
  let hdFinite : _root_.GD.N0232.N0720.N1159.d014637 m n d :=
    _root_.GD.N0232.N0720.N1159.d014644 m n (seed i₀) d (hbelow i₀)
  have hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) d := by
    intro e hed
    apply _root_.GD.N0232.N0720.N1102.d015431
      m n seed d e hsmall hbelow
    intro i
    exact _root_.GD.N0230.N0608.d000677 (_root_.GD.N0232.N0720.N1080.d014182 m n) hed (hbelow i)
  have hfixed : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      _root_.GD.N0232.N0720.N1159.d014642 m n g d hdFinite = d := by
    intro g
    apply _root_.GD.N0232.N0720.N1102.d015431
      m n seed d (_root_.GD.N0232.N0720.N1159.d014642 m n g d hdFinite)
      hsmall hbelow
    intro i
    have hmap :=
      (_root_.GD.N0232.N0720.N1159.d014645 m n (seed i) g ⟨d, hbelow i⟩).2
    change _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value
      (_root_.GD.N0232.N0720.N1159.d014642 m n g d hdFinite) at hmap
    exact hmap
  exact ⟨hterminal,
    (_root_.GD.N0232.N0720.N1159.d014655 m n hm hn d hdFinite).1 hfixed⟩



theorem d015433
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : I → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.d015333 m n (seed i) < ε)
    (hbelow : ∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d)
    (iStrict : I)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed iStrict).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  obtain ⟨hterminal, hrep⟩ :=
    _root_.GD.N0232.N0720.N1102.d015432
      m n hm hn seed d hsmall hbelow
  apply (_root_.GD.N0232.N0720.N1159.d014664
    m n hm hn).2
  refine ⟨d, hrep, ?_, hterminal⟩
  intro theta
  exact lt_of_le_of_lt (hbelow iStrict theta) (hstrict theta)




theorem d015434
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value)
    {i j : ℕ} (hij : i ≤ j) :
    _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value (seed j).value := by
  induction j, hij using Nat.le_induction with
  | base => exact _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value
  | succ j hij hprev =>
      exact _root_.GD.N0230.N0608.d000677 (_root_.GD.N0232.N0720.N1080.d014182 m n) (hdesc j) hprev



theorem d015435
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value)
    {i j : ℕ} (hij : i ≤ j) :
    ‖_root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value -
        _root_.GD.N0232.N0720.N1159.d014633 m n (seed i).value‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1201.d015333 m n (seed i) := by
  apply _root_.GD.N0232.N0720.N1102.d015429
    m n (seed i) (_root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value)
  exact _root_.GD.N0230.N0608.d000677 (_root_.GD.N0232.N0720.N1080.d014182 m n)
    (_root_.GD.N0232.N0720.N1159.d014634 m n (seed j).value).1
    (_root_.GD.N0232.N0720.N1102.d015434 m n seed hdesc hij)



theorem d015436
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value)
    (hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
      atTop (nhds 0)) :
    ∃ d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n),
      (∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d) ∧
      Tendsto (fun j ↦ _root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value)
        atTop (nhds d) := by
  let p : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    fun j ↦ _root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value
  have hcauchy : CauchySeq p := by
    apply cauchySeq_of_le_tendsto_0'
      (fun j ↦ Real.sqrt (_root_.GD.N0232.N0720.N1201.d015333 m n (seed j)))
    · intro i j hij
      have hsq := _root_.GD.N0232.N0720.N1102.d015435
        m n seed hdesc hij
      have hnonneg := _root_.GD.N0232.N0720.N1201.d015334 m n (seed i)
      rw [dist_eq_norm]
      change ‖_root_.GD.N0232.N0720.N1159.d014633 m n (seed i).value -
          _root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value‖ ≤ _
      rw [norm_sub_rev]
      nlinarith [Real.sq_sqrt hnonneg,
        norm_nonneg (_root_.GD.N0232.N0720.N1159.d014633 m n (seed j).value -
          _root_.GD.N0232.N0720.N1159.d014633 m n (seed i).value),
        Real.sqrt_nonneg (_root_.GD.N0232.N0720.N1201.d015333 m n (seed i))]
    · have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hgap
      change Tendsto
        (fun j ↦ Real.sqrt (_root_.GD.N0232.N0720.N1201.d015333 m n (seed j)))
        atTop (nhds (Real.sqrt 0)) at hsqrt
      simpa only [Real.sqrt_zero] using hsqrt
  obtain ⟨d, hd⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨d, ?_, hd⟩
  intro i
  apply (_root_.GD.N0232.N0720.N1159.d014631 m n (seed i).value).mem_of_tendsto hd
  filter_upwards [eventually_ge_atTop i] with j hij
  exact _root_.GD.N0230.N0608.d000677 (_root_.GD.N0232.N0720.N1080.d014182 m n)
    (_root_.GD.N0232.N0720.N1159.d014634 m n (seed j).value).1
    (_root_.GD.N0232.N0720.N1102.d015434 m n seed hdesc hij)




theorem d015437
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value)
    (hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
      atTop (nhds 0))
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  obtain ⟨d, hbelow, _hd⟩ :=
    _root_.GD.N0232.N0720.N1102.d015436 m n seed hdesc hgap
  apply _root_.GD.N0232.N0720.N1102.d015433
    m n hm hn seed d _ hbelow 0 hstrict
  intro ε hε
  rw [Metric.tendsto_atTop] at hgap
  obtain ⟨N, hN⟩ := hgap ε hε
  refine ⟨N, ?_⟩
  have h := hN N le_rfl
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (_root_.GD.N0232.N0720.N1201.d015334 m n (seed N))] at h
  exact h






theorem d015438
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (seed : I → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdirected : ∀ i j, ∃ r,
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value (seed r).value ∧
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed r).value)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.d015333 m n (seed i) < ε)
    (iStrict : I)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed iStrict).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    _root_.GD.N0232.N0720.N1159.d014661 m n := by
  let small : ℕ → I := fun j ↦ Classical.choose
    (hsmall (1 / ((j : ℝ) + 1)) (by positivity))
  have small_spec (j : ℕ) :
      _root_.GD.N0232.N0720.N1201.d015333 m n (seed (small j)) <
        1 / ((j : ℝ) + 1) :=
    Classical.choose_spec (hsmall (1 / ((j : ℝ) + 1)) (by positivity))
  let merge : I → I → I := fun i j ↦ Classical.choose (hdirected i j)
  have merge_left (i j : I) :
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value (seed (merge i j)).value :=
    (Classical.choose_spec (hdirected i j)).1
  have merge_right (i j : I) :
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (merge i j)).value :=
    (Classical.choose_spec (hdirected i j)).2
  let chain : ℕ → I := fun j ↦
    Nat.rec iStrict (fun depth current ↦ merge current (small depth)) j
  have chain_zero : chain 0 = iStrict := rfl
  have chain_succ (j : ℕ) :
      chain (j + 1) = merge (chain j) (small j) := by
    simp only [chain, Nat.rec_add_one]
  have chain_desc (j : ℕ) :
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed (chain j)).value
        (seed (chain (j + 1))).value := by
    rw [chain_succ]
    exact merge_left (chain j) (small j)
  have chain_gap_shift : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed (chain (j + 1))))
      atTop (nhds 0) := by
    apply squeeze_zero (g := fun j : ℕ ↦ 1 / ((j : ℝ) + 1))
    · intro j
      exact _root_.GD.N0232.N0720.N1201.d015334 m n (seed (chain (j + 1)))
    · intro j
      rw [chain_succ]
      exact (_root_.GD.N0232.N0720.N1102.d015430
        m n (seed (small j)) (seed (merge (chain j) (small j)))
        (merge_right (chain j) (small j))).trans
          (small_spec j).le
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  have chain_gap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed (chain j)))
      atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).1 chain_gap_shift
  apply _root_.GD.N0232.N0720.N1102.d015437
    m n hm hn (fun j ↦ seed (chain j)) chain_desc chain_gap
  simpa only [chain_zero] using hstrict





theorem d015439
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hnot : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n)
    (seed : I → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hbelow : ∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value d)
    (iStrict : I)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed iStrict).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ i, ε ≤ _root_.GD.N0232.N0720.N1201.d015333 m n (seed i) := by
  by_contra hfloor
  have hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.d015333 m n (seed i) < ε := by
    intro ε hε
    by_contra hnone
    apply hfloor
    refine ⟨ε, hε, ?_⟩
    intro i
    exact le_of_not_gt (fun hlt ↦ hnone ⟨i, hlt⟩)
  exact hnot (_root_.GD.N0232.N0720.N1102.d015433
    m n hm hn seed d hsmall hbelow iStrict hstrict)



theorem d015440
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hnot : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n)
    (seed : ℕ → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed (j + 1)).value)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed 0).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ j, ε ≤ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j) := by
  by_contra hfloor
  have hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ j, _root_.GD.N0232.N0720.N1201.d015333 m n (seed j) < ε := by
    intro ε hε
    by_contra hnone
    apply hfloor
    refine ⟨ε, hε, ?_⟩
    intro j
    exact le_of_not_gt (fun hlt ↦ hnone ⟨j, hlt⟩)
  have hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n (seed j))
      atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hsmall ε hε
    refine ⟨N, ?_⟩
    intro j hj
    have hmono := _root_.GD.N0232.N0720.N1102.d015430
      m n (seed N) (seed j)
      (_root_.GD.N0232.N0720.N1102.d015434 m n seed hdesc hj)
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (_root_.GD.N0232.N0720.N1201.d015334 m n (seed j))]
    exact lt_of_le_of_lt hmono hN
  exact hnot (_root_.GD.N0232.N0720.N1102.d015437
    m n hm hn seed hdesc hgap hstrict)



theorem d015441
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hnot : ¬ _root_.GD.N0232.N0720.N1159.d014661 m n)
    (seed : I → _root_.GD.N0232.N0720.N1159.d014639 m n)
    (hdirected : ∀ i j, ∃ r,
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed i).value (seed r).value ∧
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) (seed j).value (seed r).value)
    (iStrict : I)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (seed iStrict).value (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ i, ε ≤ _root_.GD.N0232.N0720.N1201.d015333 m n (seed i) := by
  by_contra hfloor
  have hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.d015333 m n (seed i) < ε := by
    intro ε hε
    by_contra hnone
    apply hfloor
    refine ⟨ε, hε, ?_⟩
    intro i
    exact le_of_not_gt (fun hlt ↦ hnone ⟨i, hlt⟩)
  exact hnot
    (_root_.GD.N0232.N0720.N1102.d015438
      m n hm hn seed hdirected hsmall iStrict hstrict)



namespace N1756

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0720.N1201.N1758

variable (k : ℕ) (sizes : Fin k → ℕ)

theorem d015442
    (s : _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (d : _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hd : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value d) :
    ‖d - _root_.GD.N0232.N0719.N0896.d011099 k sizes s.value‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes s := by
  have htax := _root_.GD.N0232.N0719.N0896.d011115
    k sizes s.value d hd
  have href := hd (_root_.GD.N0232.N0719.N0859.d010810 k)
  rw [_root_.GD.N0232.N0719.N0859.d010829 k sizes, _root_.GD.N0232.N0719.N0859.d010829 k sizes] at href
  simp only [zero_sub, norm_neg] at href
  have hnorm : ‖d‖ ^ 2 ≤ ‖s.value‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖s.value‖)).mp href
  unfold _root_.GD.N0232.N0720.N1201.N1758.d015343
  linarith

theorem d015443
    (s t : _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hts : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value t.value) :
    _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes t ≤
      _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes s := by
  have htprojBelowS : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value
      (_root_.GD.N0232.N0719.N0896.d011099 k sizes t.value) :=
    _root_.GD.N0230.N0608.d000677 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (_root_.GD.N0232.N0719.N0896.d011100 k sizes t.value).1 hts
  have hproj := (_root_.GD.N0232.N0719.N0896.d011100 k sizes s.value).2.2
    (_root_.GD.N0232.N0719.N0896.d011099 k sizes t.value) htprojBelowS
  have hseed := hts (_root_.GD.N0232.N0719.N0859.d010810 k)
  rw [_root_.GD.N0232.N0719.N0859.d010829 k sizes, _root_.GD.N0232.N0719.N0859.d010829 k sizes] at hproj hseed
  simp only [zero_sub, norm_neg] at hproj hseed
  have hprojNorm :
      ‖_root_.GD.N0232.N0719.N0896.d011099 k sizes s.value‖ ^ 2 ≤
        ‖_root_.GD.N0232.N0719.N0896.d011099 k sizes t.value‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff
      (sq_nonneg ‖_root_.GD.N0232.N0719.N0896.d011099 k sizes t.value‖)).mp hproj
  have hseedNorm : ‖t.value‖ ^ 2 ≤ ‖s.value‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg ‖s.value‖)).mp hseed
  unfold _root_.GD.N0232.N0720.N1201.N1758.d015343
  linarith

theorem d015444
    (seed : I → _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (d e : _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed i) < ε)
    (hd : ∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed i).value d)
    (he : ∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed i).value e) :
    e = d := by
  exact _root_.GD.N0232.N0720.N1102.d015428
    (fun i ↦ _root_.GD.N0232.N0719.N0896.d011099 k sizes (seed i).value)
    (fun i ↦ _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed i)) d e hsmall
    (fun i ↦ _root_.GD.N0232.N0720.N1102.N1756.d015442
      k sizes (seed i) d (hd i))
    (fun i ↦ _root_.GD.N0232.N0720.N1102.N1756.d015442
      k sizes (seed i) e (he i))

theorem d015445
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (seed : I → _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (d : _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed i) < ε)
    (hbelow : ∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed i).value d) :
    _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) d ∧
      _root_.GD.N0232.N0719.N0896.d011121 k sizes d := by
  obtain ⟨i₀, _hi₀⟩ := hsmall 1 zero_lt_one
  let hdFinite : _root_.GD.N0232.N0719.N0896.d011103 k sizes d :=
    _root_.GD.N0232.N0719.N0896.d011111 k sizes (seed i₀) d (hbelow i₀)
  have hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) d := by
    intro e hed
    apply _root_.GD.N0232.N0720.N1102.N1756.d015444
      k sizes seed d e hsmall hbelow
    intro i
    exact _root_.GD.N0230.N0608.d000677 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) hed (hbelow i)
  have hfixed : ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
      _root_.GD.N0232.N0719.N0896.d011109 k sizes g d hdFinite = d := by
    intro g
    apply _root_.GD.N0232.N0720.N1102.N1756.d015444
      k sizes seed d (_root_.GD.N0232.N0719.N0896.d011109 k sizes g d hdFinite)
      hsmall hbelow
    intro i
    have hmap :=
      (_root_.GD.N0232.N0719.N0896.d011112
        k sizes (seed i) g ⟨d, hbelow i⟩).2
    change _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed i).value
      (_root_.GD.N0232.N0719.N0896.d011109 k sizes g d hdFinite) at hmap
    exact hmap
  exact ⟨hterminal,
    (_root_.GD.N0232.N0719.N0896.d011127
      k sizes hk hsizes d hdFinite).1 hfixed⟩

theorem d015446
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (seed : I → _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (d : _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed i) < ε)
    (hbelow : ∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed i).value d)
    (iStrict : I)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (seed iStrict).value (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)) :
    _root_.GD.N0232.N0719.N0896.d011132 k sizes := by
  obtain ⟨hterminal, hrep⟩ :=
    _root_.GD.N0232.N0720.N1102.N1756.d015445
      k sizes hk hsizes seed d hsmall hbelow
  apply (_root_.GD.N0232.N0719.N0896.d011133
    k sizes hk hsizes).2
  refine ⟨d, hrep, ?_, hterminal⟩
  intro theta
  exact lt_of_le_of_lt (hbelow iStrict theta) (hstrict theta)

theorem d015447
    (seed : ℕ → _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed j).value (seed (j + 1)).value)
    {i j : ℕ} (hij : i ≤ j) :
    _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed i).value (seed j).value := by
  induction j, hij using Nat.le_induction with
  | base => exact _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed i).value
  | succ j hij hprev =>
      exact _root_.GD.N0230.N0608.d000677 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (hdesc j) hprev

theorem d015448
    (seed : ℕ → _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed j).value (seed (j + 1)).value)
    {i j : ℕ} (hij : i ≤ j) :
    ‖_root_.GD.N0232.N0719.N0896.d011099 k sizes (seed j).value -
        _root_.GD.N0232.N0719.N0896.d011099 k sizes (seed i).value‖ ^ 2 ≤
      _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed i) := by
  apply _root_.GD.N0232.N0720.N1102.N1756.d015442
    k sizes (seed i) (_root_.GD.N0232.N0719.N0896.d011099 k sizes (seed j).value)
  exact _root_.GD.N0230.N0608.d000677 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
    (_root_.GD.N0232.N0719.N0896.d011100 k sizes (seed j).value).1
    (_root_.GD.N0232.N0720.N1102.N1756.d015447 k sizes seed hdesc hij)

theorem d015449
    (seed : ℕ → _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed j).value (seed (j + 1)).value)
    (hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed j))
      atTop (nhds 0)) :
    ∃ d : _root_.GD.N0230.N0602.d000116
        (_root_.GD.N0232.N0719.N0859.d010813 k sizes),
      (∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed i).value d) ∧
      Tendsto (fun j ↦ _root_.GD.N0232.N0719.N0896.d011099 k sizes (seed j).value)
        atTop (nhds d) := by
  let p : ℕ → _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
    fun j ↦ _root_.GD.N0232.N0719.N0896.d011099 k sizes (seed j).value
  have hcauchy : CauchySeq p := by
    apply cauchySeq_of_le_tendsto_0'
      (fun j ↦ Real.sqrt (_root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed j)))
    · intro i j hij
      have hsq := _root_.GD.N0232.N0720.N1102.N1756.d015448
        k sizes seed hdesc hij
      have hnonneg := _root_.GD.N0232.N0720.N1201.N1758.d015344 k sizes (seed i)
      rw [dist_eq_norm]
      change ‖_root_.GD.N0232.N0719.N0896.d011099 k sizes (seed i).value -
          _root_.GD.N0232.N0719.N0896.d011099 k sizes (seed j).value‖ ≤ _
      rw [norm_sub_rev]
      nlinarith [Real.sq_sqrt hnonneg,
        norm_nonneg (_root_.GD.N0232.N0719.N0896.d011099 k sizes (seed j).value -
          _root_.GD.N0232.N0719.N0896.d011099 k sizes (seed i).value),
        Real.sqrt_nonneg (_root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed i))]
    · have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hgap
      change Tendsto
        (fun j ↦ Real.sqrt (_root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed j)))
        atTop (nhds (Real.sqrt 0)) at hsqrt
      simpa only [Real.sqrt_zero] using hsqrt
  obtain ⟨d, hd⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨d, ?_, hd⟩
  intro i
  apply (_root_.GD.N0232.N0719.N0896.d011097 k sizes (seed i).value).mem_of_tendsto hd
  filter_upwards [eventually_ge_atTop i] with j hij
  exact _root_.GD.N0230.N0608.d000677 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
    (_root_.GD.N0232.N0719.N0896.d011100 k sizes (seed j).value).1
    (_root_.GD.N0232.N0720.N1102.N1756.d015447 k sizes seed hdesc hij)

theorem d015450
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (seed : ℕ → _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed j).value (seed (j + 1)).value)
    (hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed j))
      atTop (nhds 0))
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (seed 0).value (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)) :
    _root_.GD.N0232.N0719.N0896.d011132 k sizes := by
  obtain ⟨d, hbelow, _hd⟩ :=
    _root_.GD.N0232.N0720.N1102.N1756.d015449
      k sizes seed hdesc hgap
  apply _root_.GD.N0232.N0720.N1102.N1756.d015446
    k sizes hk hsizes seed d _ hbelow 0 hstrict
  intro ε hε
  rw [Metric.tendsto_atTop] at hgap
  obtain ⟨N, hN⟩ := hgap ε hε
  refine ⟨N, ?_⟩
  have h := hN N le_rfl
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (_root_.GD.N0232.N0720.N1201.N1758.d015344 k sizes (seed N))] at h
  exact h

theorem d015451
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (seed : I → _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hdirected : ∀ i j, ∃ r,
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed i).value (seed r).value ∧
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed j).value (seed r).value)
    (hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed i) < ε)
    (iStrict : I)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (seed iStrict).value (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)) :
    _root_.GD.N0232.N0719.N0896.d011132 k sizes := by
  let small : ℕ → I := fun j ↦ Classical.choose
    (hsmall (1 / ((j : ℝ) + 1)) (by positivity))
  have small_spec (j : ℕ) :
      _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed (small j)) <
        1 / ((j : ℝ) + 1) :=
    Classical.choose_spec (hsmall (1 / ((j : ℝ) + 1)) (by positivity))
  let merge : I → I → I := fun i j ↦ Classical.choose (hdirected i j)
  have merge_left (i j : I) :
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed i).value (seed (merge i j)).value :=
    (Classical.choose_spec (hdirected i j)).1
  have merge_right (i j : I) :
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed j).value (seed (merge i j)).value :=
    (Classical.choose_spec (hdirected i j)).2
  let chain : ℕ → I := fun j ↦
    Nat.rec iStrict (fun depth current ↦ merge current (small depth)) j
  have chain_zero : chain 0 = iStrict := rfl
  have chain_succ (j : ℕ) :
      chain (j + 1) = merge (chain j) (small j) := by
    simp only [chain, Nat.rec_add_one]
  have chain_desc (j : ℕ) :
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed (chain j)).value
        (seed (chain (j + 1))).value := by
    rw [chain_succ]
    exact merge_left (chain j) (small j)
  have chain_gap_shift : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed (chain (j + 1))))
      atTop (nhds 0) := by
    apply squeeze_zero (g := fun j : ℕ ↦ 1 / ((j : ℝ) + 1))
    · intro j
      exact _root_.GD.N0232.N0720.N1201.N1758.d015344 k sizes (seed (chain (j + 1)))
    · intro j
      rw [chain_succ]
      exact (_root_.GD.N0232.N0720.N1102.N1756.d015443
        k sizes (seed (small j)) (seed (merge (chain j) (small j)))
        (merge_right (chain j) (small j))).trans
          (small_spec j).le
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  have chain_gap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed (chain j)))
      atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).1 chain_gap_shift
  apply _root_.GD.N0232.N0720.N1102.N1756.d015450
    k sizes hk hsizes (fun j ↦ seed (chain j)) chain_desc chain_gap
  simpa only [chain_zero] using hstrict

theorem d015452
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hnot : ¬ _root_.GD.N0232.N0719.N0896.d011132 k sizes)
    (seed : I → _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (d : _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hbelow : ∀ i, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed i).value d)
    (iStrict : I)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (seed iStrict).value (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ i, ε ≤ _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed i) := by
  by_contra hfloor
  have hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed i) < ε := by
    intro ε hε
    by_contra hnone
    apply hfloor
    refine ⟨ε, hε, ?_⟩
    intro i
    exact le_of_not_gt (fun hlt ↦ hnone ⟨i, hlt⟩)
  exact hnot (_root_.GD.N0232.N0720.N1102.N1756.d015446
    k sizes hk hsizes seed d hsmall hbelow iStrict hstrict)

theorem d015453
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hnot : ¬ _root_.GD.N0232.N0719.N0896.d011132 k sizes)
    (seed : ℕ → _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hdesc : ∀ j, _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed j).value (seed (j + 1)).value)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (seed 0).value (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ j, ε ≤ _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed j) := by
  by_contra hfloor
  have hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ j, _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed j) < ε := by
    intro ε hε
    by_contra hnone
    apply hfloor
    refine ⟨ε, hε, ?_⟩
    intro j
    exact le_of_not_gt (fun hlt ↦ hnone ⟨j, hlt⟩)
  have hgap : Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed j))
      atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := hsmall ε hε
    refine ⟨N, ?_⟩
    intro j hj
    have hmono := _root_.GD.N0232.N0720.N1102.N1756.d015443
      k sizes (seed N) (seed j)
      (_root_.GD.N0232.N0720.N1102.N1756.d015447 k sizes seed hdesc hj)
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (_root_.GD.N0232.N0720.N1201.N1758.d015344 k sizes (seed j))]
    exact lt_of_le_of_lt hmono hN
  exact hnot (_root_.GD.N0232.N0720.N1102.N1756.d015450
    k sizes hk hsizes seed hdesc hgap hstrict)

theorem d015454
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hnot : ¬ _root_.GD.N0232.N0719.N0896.d011132 k sizes)
    (seed : I → _root_.GD.N0232.N0719.N0896.d011106 k sizes)
    (hdirected : ∀ i j, ∃ r,
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed i).value (seed r).value ∧
      _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (seed j).value (seed r).value)
    (iStrict : I)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)
      (seed iStrict).value (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ i, ε ≤ _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed i) := by
  by_contra hfloor
  have hsmall : ∀ ε : ℝ, 0 < ε →
      ∃ i, _root_.GD.N0232.N0720.N1201.N1758.d015343 k sizes (seed i) < ε := by
    intro ε hε
    by_contra hnone
    apply hfloor
    refine ⟨ε, hε, ?_⟩
    intro i
    exact le_of_not_gt (fun hlt ↦ hnone ⟨i, hlt⟩)
  exact hnot
    (_root_.GD.N0232.N0720.N1102.N1756.d015451
      k sizes hk hsizes seed hdirected hsmall iStrict hstrict)

end N1756

end

end N1102
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1102.d015430
#print axioms _root_.GD.N0232.N0720.N1102.d015432
#print axioms _root_.GD.N0232.N0720.N1102.d015433
#print axioms _root_.GD.N0232.N0720.N1102.d015436
#print axioms _root_.GD.N0232.N0720.N1102.d015437
#print axioms _root_.GD.N0232.N0720.N1102.d015438
#print axioms _root_.GD.N0232.N0720.N1102.d015439
#print axioms _root_.GD.N0232.N0720.N1102.d015440
#print axioms _root_.GD.N0232.N0720.N1102.d015441
#print axioms _root_.GD.N0232.N0720.N1102.N1756.d015443
#print axioms _root_.GD.N0232.N0720.N1102.N1756.d015445
#print axioms _root_.GD.N0232.N0720.N1102.N1756.d015446
#print axioms _root_.GD.N0232.N0720.N1102.N1756.d015449
#print axioms _root_.GD.N0232.N0720.N1102.N1756.d015450
#print axioms _root_.GD.N0232.N0720.N1102.N1756.d015451
#print axioms _root_.GD.N0232.N0720.N1102.N1756.d015452
#print axioms _root_.GD.N0232.N0720.N1102.N1756.d015453
#print axioms _root_.GD.N0232.N0720.N1102.N1756.d015454
