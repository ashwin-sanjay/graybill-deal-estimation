import GD.Module0643
import GD.Module0653



























open MeasureTheory Set
open scoped BigOperators

namespace GD
namespace N0232
namespace N0719
namespace N0929

noncomputable section

open _root_.GD.N0232.N0719.N0928





theorem d009631
    {k : ℕ} (hk : 0 < k)
    {q : _root_.GD.N0232.N0719.N0857.d009377 k}
    (hq : q ∈ _root_.GD.N0232.N0719.N0955.d009607 k) :
    ∀ i, 0 < _root_.GD.N0232.N0719.N0853.d009567 hk q i := by
  intro i
  cases hi : (_root_.GD.N0232.N0719.N0954.d009344 k hk).symm i with
  | inl j =>
      simpa [_root_.GD.N0232.N0719.N0853.d009567, hi] using hq.1 j
  | inr j =>
      fin_cases j
      simpa [_root_.GD.N0232.N0719.N0853.d009567, hi] using hq.2


theorem d009632
    {k : ℕ} (hk : 0 < k)
    {q : _root_.GD.N0232.N0719.N0857.d009377 k}
    (hq : q ∈ _root_.GD.N0232.N0719.N0955.d009607 k) :
    ∀ i, _root_.GD.N0232.N0719.N0853.d009567 hk q i ≤ 1 := by
  intro i
  let p := _root_.GD.N0232.N0719.N0853.d009567 hk q
  have hp : ∀ j, 0 ≤ p j := fun j => (_root_.GD.N0232.N0719.N0929.d009631 hk hq j).le
  have hiSum : p i ≤ ∑ j, p j :=
    Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
  rw [_root_.GD.N0232.N0719.N0853.d009570 hk q] at hiSum
  exact hiSum


theorem d009633
    {k : ℕ} (hk : 0 < k) :
    _root_.GD.N0232.N0719.N0955.d009607 k ⊆
      Set.Icc
        (0 : _root_.GD.N0232.N0719.N0857.d009377 k) 1 := by
  intro q hq
  constructor
  · intro j
    exact (hq.1 j).le
  · intro j
    have hj := _root_.GD.N0232.N0719.N0929.d009632 hk hq
      (_root_.GD.N0232.N0719.N0954.d009344 k hk (Sum.inl j))
    simpa using hj



theorem d009634
    {k : ℕ} (hk : 0 < k) :
    volume (_root_.GD.N0232.N0719.N0955.d009607 k) < ⊤ := by
  calc
    volume (_root_.GD.N0232.N0719.N0955.d009607 k) ≤
        volume (Set.Icc
          (0 : _root_.GD.N0232.N0719.N0857.d009377 k) 1) :=
      measure_mono (_root_.GD.N0232.N0719.N0929.d009633 hk)
    _ = 1 := by
      rw [Real.volume_Icc_pi]
      simp
    _ < ⊤ := ENNReal.one_lt_top


theorem d009635 (k : ℕ) :
    IsOpen (_root_.GD.N0232.N0719.N0955.d009607 k) := by
  rw [show _root_.GD.N0232.N0719.N0955.d009607 k =
      (⋂ j : Fin (k - 1),
        {q : _root_.GD.N0232.N0719.N0857.d009377 k | 0 < q j}) ∩
        {q : _root_.GD.N0232.N0719.N0857.d009377 k |
          0 < 1 - ∑ j, q j} by
    ext q
    simp [_root_.GD.N0232.N0719.N0955.d009607]]
  exact
    (isOpen_iInter_of_finite fun j =>
      isOpen_lt continuous_const (continuous_apply j)).inter
      (isOpen_lt continuous_const
        (continuous_const.sub
          (continuous_finset_sum _ fun j _ => continuous_apply j)))



theorem d009636
    {k : ℕ} (hk : 0 < k) :
    (_root_.GD.N0232.N0719.N0955.d009607 k).Nonempty := by
  let q : _root_.GD.N0232.N0719.N0857.d009377 k :=
    fun _ => 1 / (k : ℝ)
  refine ⟨q, ?_⟩
  constructor
  · intro j
    unfold q
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    positivity
  · unfold q
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    have heq :
        1 - ((k : ℝ) - 1) * (1 / (k : ℝ)) = 1 / (k : ℝ) := by
      field_simp [hkR.ne']
      ring
    norm_num only [Nat.cast_one] at ⊢
    rw [heq]
    exact one_div_pos.mpr hkR


theorem d009637
    {k : ℕ} (hk : 0 < k) :
    0 < volume (_root_.GD.N0232.N0719.N0955.d009607 k) :=
  (_root_.GD.N0232.N0719.N0929.d009635 k).measure_pos volume
    (_root_.GD.N0232.N0719.N0929.d009636 hk)





theorem d009638
    {k : ℕ} (hk : 0 < k)
    (shape : Fin k → ℝ) (hshape : ∀ i, 0 < shape i)
    {q : _root_.GD.N0232.N0719.N0857.d009377 k}
    (hq : q ∈ _root_.GD.N0232.N0719.N0955.d009607 k) :
    _root_.GD.N0232.N0719.N0928.d009409 shape
        (_root_.GD.N0232.N0719.N0853.d009567 hk q) ≤ 1 := by
  unfold _root_.GD.N0232.N0719.N0928.d009409
  calc
    (∏ i,
        _root_.GD.N0232.N0719.N0853.d009567 hk q i ^
          (shape i + 1 / 2)) ≤ ∏ _i : Fin k, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro i _
        exact Real.rpow_nonneg (_root_.GD.N0232.N0719.N0929.d009631 hk hq i).le _
      · intro i _
        exact Real.rpow_le_one
          (_root_.GD.N0232.N0719.N0929.d009631 hk hq i).le
          (_root_.GD.N0232.N0719.N0929.d009632 hk hq i)
          (by linarith [hshape i])
    _ = 1 := by simp



theorem d009639
    {k : ℕ} (hk : 0 < k)
    (shape : Fin k → ℝ) (hshape : ∀ i, 0 < shape i) :
    Continuous
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 k =>
        _root_.GD.N0232.N0719.N0928.d009409 shape
          (_root_.GD.N0232.N0719.N0853.d009567 hk q)) := by
  unfold _root_.GD.N0232.N0719.N0928.d009409
  apply continuous_finset_prod
  intro i _
  exact
    (_root_.GD.N0232.N0719.N0853.d009582 hk i).rpow_const
      (fun _ => Or.inr (by linarith [hshape i]))



theorem d009640
    {k : ℕ} (hk : 0 < k)
    (shape : Fin k → ℝ) (hshape : ∀ i, 0 < shape i) :
    IntegrableOn
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 k =>
        _root_.GD.N0232.N0719.N0928.d009409 shape
          (_root_.GD.N0232.N0719.N0853.d009567 hk q))
      (_root_.GD.N0232.N0719.N0955.d009607 k) := by
  have hone : IntegrableOn
      (fun _q : _root_.GD.N0232.N0719.N0857.d009377 k => (1 : ℝ))
      (_root_.GD.N0232.N0719.N0955.d009607 k) :=
    integrableOn_const (_root_.GD.N0232.N0719.N0929.d009634 hk).ne
  apply hone.mono'
  · exact
      (_root_.GD.N0232.N0719.N0929.d009639 hk shape hshape).aestronglyMeasurable
  · apply (ae_restrict_iff'
      (_root_.GD.N0232.N0719.N0955.d009608 k)).2
    filter_upwards [] with q hq
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact _root_.GD.N0232.N0719.N0929.d009638 hk shape hshape hq
    · unfold _root_.GD.N0232.N0719.N0928.d009409
      exact Finset.prod_nonneg fun i _ =>
        Real.rpow_nonneg (_root_.GD.N0232.N0719.N0929.d009631 hk hq i).le _



theorem d009641
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) :
    Continuous
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 k =>
        _root_.GD.N0232.N0719.N0928.d009407 shape
          (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t) := by
  unfold _root_.GD.N0232.N0719.N0928.d009407 _root_.GD.N0232.N0719.N0928.d009406 _root_.GD.N0232.N0719.N0928.d009405
  fun_prop



theorem d009642
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s c : ℝ)
    (hshape : ∀ i, 0 < shape i)
    (hc : 0 < c) (hfloor : ∀ i, c ≤ shape i * t i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    ContinuousOn
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 k =>
        _root_.GD.N0232.N0719.N0928.d009437 shape
          (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s)
      (_root_.GD.N0232.N0719.N0955.d009607 k) := by
  have hmono : ContinuousOn
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 k =>
        _root_.GD.N0232.N0719.N0928.d009409 shape
          (_root_.GD.N0232.N0719.N0853.d009567 hk q))
      (_root_.GD.N0232.N0719.N0955.d009607 k) :=
    (_root_.GD.N0232.N0719.N0929.d009639 hk shape hshape).continuousOn
  have henergy : ContinuousOn
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 k =>
        _root_.GD.N0232.N0719.N0928.d009407 shape
          (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t)
      (_root_.GD.N0232.N0719.N0955.d009607 k) :=
    (_root_.GD.N0232.N0719.N0929.d009641 hk shape y t).continuousOn
  have henergyNe :
      ∀ q ∈ _root_.GD.N0232.N0719.N0955.d009607 k,
        _root_.GD.N0232.N0719.N0928.d009407 shape
          (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t ≠ 0 := by
    intro q hq
    have hge := _root_.GD.N0232.N0719.N0928.d009442 shape
      (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t c
      (fun i => (_root_.GD.N0232.N0719.N0929.d009631 hk hq i).le)
      (_root_.GD.N0232.N0719.N0853.d009570 hk q)
      hfloor
    linarith
  unfold _root_.GD.N0232.N0719.N0928.d009437
  exact
    (((continuousOn_const.mul hmono).mul
      (henergy.rpow_const fun q hq => Or.inl (henergyNe q hq))).mul
        continuousOn_const)



theorem d009643
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s c : ℝ)
    (hshape : ∀ i, 0 < shape i)
    (hc : 0 < c) (hfloor : ∀ i, c ≤ shape i * t i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    IntegrableOn
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 k =>
        _root_.GD.N0232.N0719.N0928.d009437 shape
          (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s)
      (_root_.GD.N0232.N0719.N0955.d009607 k) := by
  let C := Real.sqrt (2 * Real.pi) *
    c ^ (-_root_.GD.N0232.N0719.N0928.d009415 shape s) *
    Real.Gamma (_root_.GD.N0232.N0719.N0928.d009415 shape s)
  have hmajorant :=
    (_root_.GD.N0232.N0719.N0929.d009640
      hk shape hshape).const_mul C
  apply hmajorant.mono'
  · exact
      (_root_.GD.N0232.N0719.N0929.d009642
        hk shape y t s c hshape hc hfloor hpower).aestronglyMeasurable
        (_root_.GD.N0232.N0719.N0955.d009608 k)
  · apply (ae_restrict_iff'
      (_root_.GD.N0232.N0719.N0955.d009608 k)).2
    filter_upwards [] with q hq
    have hbound := _root_.GD.N0232.N0719.N0928.d009443
      shape (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s c
      (fun i => (_root_.GD.N0232.N0719.N0929.d009631 hk hq i).le)
      (_root_.GD.N0232.N0719.N0853.d009570 hk q)
      hc hfloor hpower
    have hevidenceNonneg :
        0 ≤ _root_.GD.N0232.N0719.N0928.d009437 shape
          (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s := by
      have henergyPos :
          0 < _root_.GD.N0232.N0719.N0928.d009407 shape
            (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t := by
        have hge := _root_.GD.N0232.N0719.N0928.d009442 shape
          (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t c
          (fun i => (_root_.GD.N0232.N0719.N0929.d009631 hk hq i).le)
          (_root_.GD.N0232.N0719.N0853.d009570 hk q)
          hfloor
        linarith
      unfold _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0928.d009409
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (Real.sqrt_nonneg _)
            (Finset.prod_nonneg fun i _ =>
              Real.rpow_nonneg (_root_.GD.N0232.N0719.N0929.d009631 hk hq i).le _))
          (Real.rpow_nonneg henergyPos.le _))
        (Real.Gamma_pos_of_pos hpower).le
    rw [Real.norm_eq_abs, abs_of_nonneg hevidenceNonneg]
    change _root_.GD.N0232.N0719.N0928.d009437 shape
        (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s ≤
      C * _root_.GD.N0232.N0719.N0928.d009409 shape
        (_root_.GD.N0232.N0719.N0853.d009567 hk q)
    unfold C
    calc
      _root_.GD.N0232.N0719.N0928.d009437 shape
          (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s ≤
        Real.sqrt (2 * Real.pi) *
          _root_.GD.N0232.N0719.N0928.d009409 shape
            (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
          c ^ (-_root_.GD.N0232.N0719.N0928.d009415 shape s) *
          Real.Gamma (_root_.GD.N0232.N0719.N0928.d009415 shape s) := hbound
      _ = _ := by ring





theorem d009644
    {k : ℕ} (hk : 0 < k)
    (shape t : Fin k → ℝ)
    (hshape : ∀ i, 0 < shape i) (ht : ∀ i, 0 < t i) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ shape i * t i := by
  let values : Finset ℝ := Finset.univ.image (fun i => shape i * t i)
  have hvalues : values.Nonempty := by
    have huniv : (Finset.univ : Finset (Fin k)).Nonempty :=
      ⟨⟨0, hk⟩, Finset.mem_univ _⟩
    exact huniv.image _
  let c : ℝ := values.min' hvalues
  have hc : 0 < c := by
    have hmem : c ∈ values := by
      exact values.min'_mem hvalues
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
    rw [← hi]
    exact mul_pos (hshape i) (ht i)
  refine ⟨c, hc, ?_⟩
  intro i
  exact values.min'_le _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)



theorem d009645
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s : ℝ)
    (hshape : ∀ i, 0 < shape i) (ht : ∀ i, 0 < t i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    IntegrableOn
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 k =>
        _root_.GD.N0232.N0719.N0928.d009437 shape
          (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s)
      (_root_.GD.N0232.N0719.N0955.d009607 k) := by
  obtain ⟨c, hc, hfloor⟩ :=
    _root_.GD.N0232.N0719.N0929.d009644 hk shape t hshape ht
  exact _root_.GD.N0232.N0719.N0929.d009643
    hk shape y t s c hshape hc hfloor hpower



theorem d009646
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s : ℝ)
    (hshape : ∀ i, 0 < shape i) (ht : ∀ i, 0 < t i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s)
    {q : _root_.GD.N0232.N0719.N0857.d009377 k}
    (hq : q ∈ _root_.GD.N0232.N0719.N0955.d009607 k) :
    0 < _root_.GD.N0232.N0719.N0928.d009437 shape
      (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s := by
  obtain ⟨c, hc, hfloor⟩ :=
    _root_.GD.N0232.N0719.N0929.d009644 hk shape t hshape ht
  have henergy :
      0 < _root_.GD.N0232.N0719.N0928.d009407 shape
        (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t := by
    have hge := _root_.GD.N0232.N0719.N0928.d009442 shape
      (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t c
      (fun i => (_root_.GD.N0232.N0719.N0929.d009631 hk hq i).le)
      (_root_.GD.N0232.N0719.N0853.d009570 hk q)
      hfloor
    linarith
  unfold _root_.GD.N0232.N0719.N0928.d009437 _root_.GD.N0232.N0719.N0928.d009409
  exact mul_pos
    (mul_pos
      (mul_pos
        (Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos))
        (Finset.prod_pos fun i _ =>
          Real.rpow_pos_of_pos (_root_.GD.N0232.N0719.N0929.d009631 hk hq i) _))
      (Real.rpow_pos_of_pos henergy _))
    (Real.Gamma_pos_of_pos hpower)



def d009647
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s : ℝ) : ℝ :=
  ∫ q in _root_.GD.N0232.N0719.N0955.d009607 k,
    _root_.GD.N0232.N0719.N0928.d009437 shape
      (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s




theorem d009648
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s : ℝ)
    (hshape : ∀ i, 0 < shape i) (ht : ∀ i, 0 < t i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    0 < _root_.GD.N0232.N0719.N0929.d009647 hk shape y t s := by
  let S := _root_.GD.N0232.N0719.N0955.d009607 k
  let f : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun q => _root_.GD.N0232.N0719.N0928.d009437 shape
      (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s
  have hf : Integrable f (volume.restrict S) := by
    simpa [IntegrableOn, f, S] using
      _root_.GD.N0232.N0719.N0929.d009645
        hk shape y t s hshape ht hpower
  have hfNonneg : 0 ≤ᵐ[volume.restrict S] f := by
    apply (ae_restrict_iff'
      (_root_.GD.N0232.N0719.N0955.d009608 k)).2
    filter_upwards [] with q hq
    exact (_root_.GD.N0232.N0719.N0929.d009646
      hk shape y t s hshape ht hpower hq).le
  have hSsupport : S ⊆ Function.support f := by
    intro q hq
    exact ne_of_gt
      (_root_.GD.N0232.N0719.N0929.d009646
        hk shape y t s hshape ht hpower hq)
  have hmeasureSupport :
      0 < (volume.restrict S) (Function.support f) := by
    calc
      0 < (volume.restrict S) S := by
        rw [Measure.restrict_apply
          (_root_.GD.N0232.N0719.N0955.d009608 k)]
        simpa [S] using _root_.GD.N0232.N0719.N0929.d009637 hk
      _ ≤ (volume.restrict S) (Function.support f) :=
        measure_mono hSsupport
  have hpos : 0 < ∫ q, f q ∂volume.restrict S :=
    (integral_pos_iff_support_of_nonneg_ae hfNonneg hf).2 hmeasureSupport
  simpa [_root_.GD.N0232.N0719.N0929.d009647, f, S, IntegrableOn] using hpos



theorem d009649
    {k : ℕ} (hk : 0 < k) (y : Fin k → ℝ) :
    Continuous
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 k =>
        _root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0719.N0853.d009567 hk q) y) := by
  unfold _root_.GD.N0232.N0719.N0928.d009405
  fun_prop


theorem d009650
    {k : ℕ} (hk : 0 < k) (y : Fin k → ℝ)
    {q : _root_.GD.N0232.N0719.N0857.d009377 k}
    (hq : q ∈ _root_.GD.N0232.N0719.N0955.d009607 k) :
    |_root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0719.N0853.d009567 hk q) y| ≤
      ∑ i, |y i| := by
  unfold _root_.GD.N0232.N0719.N0928.d009405
  calc
    |∑ i, _root_.GD.N0232.N0719.N0853.d009567 hk q i * y i| ≤
        ∑ i, |_root_.GD.N0232.N0719.N0853.d009567 hk q i * y i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i,
        _root_.GD.N0232.N0719.N0853.d009567 hk q i * |y i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_pos (_root_.GD.N0232.N0719.N0929.d009631 hk hq i)]
    _ ≤ ∑ i, 1 * |y i| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right
        (_root_.GD.N0232.N0719.N0929.d009632 hk hq i) (abs_nonneg (y i))
    _ = ∑ i, |y i| := by simp



theorem d009651
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s : ℝ)
    (hshape : ∀ i, 0 < shape i) (ht : ∀ i, 0 < t i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    IntegrableOn
      (fun q : _root_.GD.N0232.N0719.N0857.d009377 k =>
        _root_.GD.N0232.N0719.N0928.d009437 shape
            (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s *
          _root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0719.N0853.d009567 hk q) y)
      (_root_.GD.N0232.N0719.N0955.d009607 k) := by
  let S := _root_.GD.N0232.N0719.N0955.d009607 k
  let evidence : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun q => _root_.GD.N0232.N0719.N0928.d009437 shape
      (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s
  let mean : _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun q => _root_.GD.N0232.N0719.N0928.d009405
      (_root_.GD.N0232.N0719.N0853.d009567 hk q) y
  have hevidence : Integrable evidence (volume.restrict S) := by
    simpa [IntegrableOn, evidence, S] using
      _root_.GD.N0232.N0719.N0929.d009645
        hk shape y t s hshape ht hpower
  have hmeanMeas : AEStronglyMeasurable mean (volume.restrict S) :=
    (_root_.GD.N0232.N0719.N0929.d009649 hk y).aestronglyMeasurable
  have hmeanBound :
      ∀ᵐ q ∂volume.restrict S, ‖mean q‖ ≤ ∑ i, |y i| := by
    apply (ae_restrict_iff'
      (_root_.GD.N0232.N0719.N0955.d009608 k)).2
    filter_upwards [] with q hq
    simpa [mean, Real.norm_eq_abs] using
      _root_.GD.N0232.N0719.N0929.d009650 hk y hq
  have hproduct := hevidence.bdd_mul hmeanMeas hmeanBound
  simpa [IntegrableOn, evidence, mean, S, mul_comm] using hproduct


def d009652
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s : ℝ) : ℝ :=
  ∫ q in _root_.GD.N0232.N0719.N0955.d009607 k,
    _root_.GD.N0232.N0719.N0928.d009437 shape
        (_root_.GD.N0232.N0719.N0853.d009567 hk q) y t s *
      _root_.GD.N0232.N0719.N0928.d009405 (_root_.GD.N0232.N0719.N0853.d009567 hk q) y




def d009653
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s : ℝ) : ℝ :=
  _root_.GD.N0232.N0719.N0929.d009652 hk shape y t s /
    _root_.GD.N0232.N0719.N0929.d009647 hk shape y t s

theorem d009654
    {k : ℕ} (hk : 0 < k)
    (shape y t : Fin k → ℝ) (s : ℝ)
    (hshape : ∀ i, 0 < shape i) (ht : ∀ i, 0 < t i)
    (hpower : 0 < _root_.GD.N0232.N0719.N0928.d009415 shape s) :
    _root_.GD.N0232.N0719.N0929.d009647 hk shape y t s ≠ 0 :=
  (_root_.GD.N0232.N0719.N0929.d009648 hk shape y t s hshape ht hpower).ne'

end

end N0929
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0929.d009634
#print axioms _root_.GD.N0232.N0719.N0929.d009637
#print axioms _root_.GD.N0232.N0719.N0929.d009640
#print axioms _root_.GD.N0232.N0719.N0929.d009643
#print axioms _root_.GD.N0232.N0719.N0929.d009648
#print axioms _root_.GD.N0232.N0719.N0929.d009651
#print axioms _root_.GD.N0232.N0719.N0929.d009654
