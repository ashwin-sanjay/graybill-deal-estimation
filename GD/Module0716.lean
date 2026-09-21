import GD.Module0715





















open MeasureTheory Set
open scoped BigOperators

namespace GD.N0232.N0719.N0913

noncomputable section


theorem d010629
    {k : ℕ} (hk : 0 < k) (hk3 : 3 ≤ k) :
    IsCompact (_root_.GD.N0232.N0719.N0853.d009581 hk) := by
  exact
    IsCompact.of_isClosed_subset isCompact_Icc
      (_root_.GD.N0232.N0719.N0853.d009583 hk)
      (_root_.GD.N0232.N0719.N0853.d009584 hk hk3)



theorem d010630
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) :
    Continuous (_root_.GD.N0232.N0719.N0855.d010601 hk triangle) := by
  unfold _root_.GD.N0232.N0719.N0855.d010601 _root_.GD.N0232.N0719.N0951.d003585
  exact continuous_finset_sum _ fun j _ =>
    _root_.GD.N0232.N0719.N0853.d009582 hk (triangle j)



theorem d010631
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k) (j : Fin 3) :
    ContinuousOn
      (fun q =>
        _root_.GD.N0232.N0719.N0951.d003586 triangle (_root_.GD.N0232.N0719.N0853.d009567 hk q) j)
      (_root_.GD.N0232.N0719.N0853.d009581 hk) := by
  unfold _root_.GD.N0232.N0719.N0951.d003586
  exact
    (_root_.GD.N0232.N0719.N0853.d009582 hk (triangle j)).continuousOn.div
      (_root_.GD.N0232.N0719.N0913.d010630 hk triangle).continuousOn
      (fun q hq =>
        (_root_.GD.N0232.N0719.N0951.d003593 hk triangle hq).ne')



theorem d010632
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (w : Fin 3 → ℝ) :
    ContinuousOn
      (fun q => _root_.GD.N0232.N0719.N0853.d009591 hk triangle q w)
      (_root_.GD.N0232.N0719.N0853.d009581 hk) := by
  let q : Fin 3 → _root_.GD.N0232.N0719.N0857.d009377 k → ℝ :=
    fun j u =>
      _root_.GD.N0232.N0719.N0951.d003586 triangle (_root_.GD.N0232.N0719.N0853.d009567 hk u) j
  have hq : ∀ j, ContinuousOn (q j) (_root_.GD.N0232.N0719.N0853.d009581 hk) :=
    fun j => _root_.GD.N0232.N0719.N0913.d010631 hk triangle j
  have hqpos :
      ∀ u ∈ _root_.GD.N0232.N0719.N0853.d009581 hk, ∀ j, 0 < q j u :=
    fun u hu j => _root_.GD.N0232.N0719.N0951.d003596 hk triangle hu j
  unfold _root_.GD.N0232.N0719.N0853.d009591 _root_.GD.N0232.N0719.N0856.d009528 _root_.GD.N0232.N0719.N1016.d003608
  exact
    (((((hq 0).mul continuousOn_const).sub
          ((hq 1).mul continuousOn_const)).pow 2).div
        ((hq 0).add (hq 1))
        (fun u hu => (add_pos (hqpos u hu 0) (hqpos u hu 1)).ne')).add
      (((((hq 0).mul continuousOn_const).sub
          ((hq 2).mul continuousOn_const)).pow 2).div
        ((hq 0).add (hq 2))
        (fun u hu => (add_pos (hqpos u hu 0) (hqpos u hu 2)).ne')) |>.add
      (((((hq 1).mul continuousOn_const).sub
          ((hq 2).mul continuousOn_const)).pow 2).div
        ((hq 1).add (hq 2))
        (fun u hu => (add_pos (hqpos u hu 1) (hqpos u hu 2)).ne'))



theorem d010633
    {k : ℕ} (hk : 0 < k)
    (triangle : Fin 3 ↪ Fin k)
    (w : Fin 3 → ℝ) :
    ContinuousOn
      (_root_.GD.N0232.N0719.N0855.d010602 hk triangle · w)
      (_root_.GD.N0232.N0719.N0853.d009581 hk) := by
  unfold _root_.GD.N0232.N0719.N0855.d010602
  exact
    ((_root_.GD.N0232.N0719.N0913.d010630 hk triangle).continuousOn.pow 2).mul
      (_root_.GD.N0232.N0719.N0913.d010632 hk triangle w)



theorem d010634
    {k : ℕ} (hk : 0 < k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i) :
    ContinuousOn
      (_root_.GD.N0232.N0719.N0855.d010603 hk shape rate)
      (_root_.GD.N0232.N0719.N0853.d009581 hk) := by
  let qrate := _root_.GD.N0232.N0719.N0954.d009506 rate
  have hqrate :
      _root_.GD.N0232.N0719.N0951.d003581 qrate :=
    _root_.GD.N0232.N0719.N0954.d009513 hk hrate
  have hcoord :
      ContinuousOn
        (fun u =>
          ∏ i,
            (_root_.GD.N0232.N0719.N0853.d009567 hk u i) ^ (-(shape i + 1)))
        (_root_.GD.N0232.N0719.N0853.d009581 hk) := by
    apply continuousOn_finset_prod
    intro i _
    exact
      (_root_.GD.N0232.N0719.N0853.d009582 hk i).continuousOn.rpow_const
        (fun u hu =>
          Or.inl (_root_.GD.N0232.N0719.N0951.d003590 hk hu i).ne')
  have hrateCont :
      ContinuousOn
        (fun u =>
          _root_.GD.N0232.N0719.N0951.d003587 qrate (_root_.GD.N0232.N0719.N0853.d009567 hk u))
        (_root_.GD.N0232.N0719.N0853.d009581 hk) := by
    unfold _root_.GD.N0232.N0719.N0951.d003587
    apply continuousOn_finset_sum
    intro i _
    exact
      continuousOn_const.div
        (_root_.GD.N0232.N0719.N0853.d009582 hk i).continuousOn
        (fun u hu =>
          (_root_.GD.N0232.N0719.N0951.d003590 hk hu i).ne')
  have hratePow :
      ContinuousOn
        (fun u =>
          (_root_.GD.N0232.N0719.N0951.d003587 qrate (_root_.GD.N0232.N0719.N0853.d009567 hk u)) ^
            (-_root_.GD.N0232.N0719.N0954.d009503 shape))
        (_root_.GD.N0232.N0719.N0853.d009581 hk) :=
    hrateCont.rpow_const
      (fun u hu =>
        Or.inl (_root_.GD.N0232.N0719.N0951.d003602 hk hqrate hu).ne')
  unfold _root_.GD.N0232.N0719.N0855.d010603 _root_.GD.N0232.N0719.N0954.d009510
  exact hcoord.mul hratePow



theorem d010635
    {k : ℕ} (hk : 0 < k) (hk3 : 3 ≤ k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    (triangle : Fin 3 ↪ Fin k)
    (w : Fin 3 → ℝ) :
    IntegrableOn
      (fun q =>
        _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q *
          _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w)
      (_root_.GD.N0232.N0719.N0853.d009581 hk) := by
  exact
    ((_root_.GD.N0232.N0719.N0913.d010634 hk hshape hrate).mul
      (_root_.GD.N0232.N0719.N0913.d010633 hk triangle w)).integrableOn_compact
      (_root_.GD.N0232.N0719.N0913.d010629 hk hk3)



theorem d010636
    {k : ℕ} (hk : 0 < k) (hk3 : 3 ≤ k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    (triangle : Fin 3 ↪ Fin k)
    (V : ℝ) :
    IntegrableOn
      (fun q =>
        _root_.GD.N0232.N0719.N0855.d010603 hk shape rate q *
          _root_.GD.N0232.N0719.N0914.d010624 hk triangle V q)
      (_root_.GD.N0232.N0719.N0853.d009581 hk) := by
  have henergy :
      ContinuousOn
        (_root_.GD.N0232.N0719.N0914.d010624 hk triangle V)
        (_root_.GD.N0232.N0719.N0853.d009581 hk) := by
    unfold _root_.GD.N0232.N0719.N0914.d010624
    exact
      ((continuousOn_const.mul
        ((_root_.GD.N0232.N0719.N0913.d010630 hk triangle).continuousOn.pow 2)).mul
          continuousOn_const)
  exact
    ((_root_.GD.N0232.N0719.N0913.d010634 hk hshape hrate).mul
      henergy).integrableOn_compact
      (_root_.GD.N0232.N0719.N0913.d010629 hk hk3)



theorem d010637
    {k : ℕ} (hk : 0 < k) (hk3 : 3 ≤ k)
    {shape variance : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hvariance : ∀ i, 0 < variance i)
    (triangle : Fin 3 ↪ Fin k)
    {V : ℝ} (hV : 0 < V)
    (w : Fin 3 → ℝ) :
    IntegrableOn
      (fun q =>
        _root_.GD.N0232.N0719.N0954.d009508
            shape (_root_.GD.N0232.N0719.N0960.d009692 shape variance)
            (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
          (_root_.GD.N0232.N0719.N0950.d010591 shape triangle / V) *
          _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w)
      (_root_.GD.N0232.N0719.N0853.d009581 hk) := by
  let rate := _root_.GD.N0232.N0719.N0960.d009692 shape variance
  have hrate : ∀ i, 0 < rate i :=
    _root_.GD.N0232.N0719.N0914.d010619 hshape hvariance
  have hbase :=
    (_root_.GD.N0232.N0719.N0913.d010635
      hk hk3 hshape hrate triangle w).const_mul
        (_root_.GD.N0232.N0719.N0954.d009509 shape rate *
          (_root_.GD.N0232.N0719.N0950.d010591 shape triangle / V))
  apply MeasureTheory.IntegrableOn.congr_fun hbase
  · intro q hq
    have hp : ∀ i, 0 < _root_.GD.N0232.N0719.N0853.d009567 hk q i :=
      fun i => _root_.GD.N0232.N0719.N0951.d003590 hk hq i
    change
      _root_.GD.N0232.N0719.N0954.d009509 shape rate *
            (_root_.GD.N0232.N0719.N0950.d010591 shape triangle / V) *
          (_root_.GD.N0232.N0719.N0855.d010603 hk shape rate q *
            _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w) =
        _root_.GD.N0232.N0719.N0954.d009508 shape rate
              (_root_.GD.N0232.N0719.N0853.d009567 hk q) *
            (_root_.GD.N0232.N0719.N0950.d010591 shape triangle / V) *
          _root_.GD.N0232.N0719.N0855.d010602 hk triangle q w
    rw [_root_.GD.N0232.N0719.N0954.d009515
      hk hshape hrate hp]
    unfold _root_.GD.N0232.N0719.N0855.d010603
    ring
  · exact (_root_.GD.N0232.N0719.N0853.d009583 hk).measurableSet



theorem d010638
    {k : ℕ} (hk : 0 < k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i) :
    IntegrableOn
      (_root_.GD.N0232.N0719.N0954.d009483
        (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
        (_root_.GD.N0232.N0719.N0954.d009350 hk rate))
      (_root_.GD.N0232.N0719.N0953.d003311 (k - 1)) := by
  by_contra hnot
  have hzero :
      (∫ x in _root_.GD.N0232.N0719.N0953.d003311 (k - 1),
        _root_.GD.N0232.N0719.N0954.d009483
          (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
          (_root_.GD.N0232.N0719.N0954.d009350 hk rate) x) = 0 :=
    integral_undef hnot
  have htransport :=
    _root_.GD.N0232.N0719.N0954.d009491
      hk hshape hrate (fun _ => (1 : ℝ))
  letI :
      IsProbabilityMeasure (_root_.GD.N0232.N0719.N0954.d009342 shape rate) := by
    unfold _root_.GD.N0232.N0719.N0954.d009342
    letI :
        ∀ i : Fin k,
          IsProbabilityMeasure
            (ProbabilityTheory.gammaMeasure (shape i) (rate i)) :=
      fun i =>
        ProbabilityTheory.isProbabilityMeasure_gammaMeasure
          (hshape i) (hrate i)
    infer_instance
  have hone :
      (∫ _t, (1 : ℝ) ∂_root_.GD.N0232.N0719.N0954.d009342 shape rate) = 1 := by
    simp
  rw [hone] at htransport
  simp only [one_mul] at htransport
  rw [hzero] at htransport
  norm_num at htransport






theorem d010639
    {k : ℕ} (hk : 0 < k)
    {shape rate : Fin k → ℝ}
    (hshape : ∀ i, 0 < shape i)
    (hrate : ∀ i, 0 < rate i)
    (Gchart : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) → ℝ)
    (hG :
      AEStronglyMeasurable Gchart
        (volume.restrict (_root_.GD.N0232.N0719.N0953.d003311 (k - 1))))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound :
      ∀ x ∈ _root_.GD.N0232.N0719.N0953.d003311 (k - 1), ‖Gchart x‖ ≤ C) :
    IntegrableOn
      (fun x =>
        Gchart x *
          _root_.GD.N0232.N0719.N0954.d009483
            (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
            (_root_.GD.N0232.N0719.N0954.d009350 hk rate) x)
      (_root_.GD.N0232.N0719.N0953.d003311 (k - 1)) := by
  let density :=
    _root_.GD.N0232.N0719.N0954.d009483
      (_root_.GD.N0232.N0719.N0954.d009350 hk shape)
      (_root_.GD.N0232.N0719.N0954.d009350 hk rate)
  have hdensity :
      IntegrableOn density (_root_.GD.N0232.N0719.N0953.d003311 (k - 1)) :=
    _root_.GD.N0232.N0719.N0913.d010638 hk hshape hrate
  have hmajorant :
      IntegrableOn (fun x => C * ‖density x‖)
        (_root_.GD.N0232.N0719.N0953.d003311 (k - 1)) :=
    hdensity.norm.const_mul C
  apply hmajorant.mono'
  · exact hG.mul hdensity.aestronglyMeasurable
  · apply (ae_restrict_iff' (_root_.GD.N0232.N0719.N0953.d003333 _)).2
    filter_upwards [] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (hbound x hx) (norm_nonneg (density x))
















theorem d010640
    {k : ℕ}
    (Hchart : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) → ℝ)
    (hH :
      IntegrableOn Hchart (_root_.GD.N0232.N0719.N0953.d003311 (k - 1))) :
    IntegrableOn
      (fun q =>
        ∫ ω in Ioi 0, Hchart (_root_.GD.N0232.N0719.N0955.d009612 q ω))
      (_root_.GD.N0232.N0719.N0955.d009607 k) := by
  let e := _root_.GD.N0232.N0719.N0955.d009609 k
  let K : _root_.GD.N0232.N0719.N0857.d009377 k × ℝ → ℝ :=
    fun z => Hchart (e.symm z)
  have hImage :
      e '' _root_.GD.N0232.N0719.N0953.d003311 (k - 1) =
        _root_.GD.N0232.N0719.N0955.d009607 k ×ˢ Ioi 0 :=
    _root_.GD.N0232.N0719.N0955.d009628 k
  have hK :
      IntegrableOn K
        (_root_.GD.N0232.N0719.N0955.d009607 k ×ˢ Ioi 0) := by
    rw [← hImage]
    apply
      ((_root_.GD.N0232.N0719.N0955.d009626 k).integrableOn_image
        e.measurableEmbedding).2
    have hKe : K ∘ e = Hchart := by
      funext x
      simp [K, e]
    rw [hKe]
    exact hH
  have hKprod :
      Integrable K
        ((volume.restrict (_root_.GD.N0232.N0719.N0955.d009607 k)).prod
          (volume.restrict (Ioi 0))) := by
    simpa only [IntegrableOn, Measure.prod_restrict, ← Measure.volume_eq_prod] using hK
  have hsection := hKprod.integral_prod_left
  simpa [IntegrableOn, K, e, _root_.GD.N0232.N0719.N0955.d009612] using hsection





theorem d010641
    {k : ℕ} (hk : 0 < k)
    (Hchart : _root_.GD.N0232.N0719.N0953.d003306 (k - 1) → ℝ)
    (hH :
      IntegrableOn Hchart (_root_.GD.N0232.N0719.N0953.d003311 (k - 1))) :
    IntegrableOn
      (fun q =>
        ∫ ω in Ioi 0, Hchart (_root_.GD.N0232.N0719.N0955.d009612 q ω))
      (_root_.GD.N0232.N0719.N0853.d009581 hk) :=
  (_root_.GD.N0232.N0719.N0913.d010640 Hchart hH).mono_set
    (_root_.GD.N0232.N0719.N0955.d009622 hk)

end

end GD.N0232.N0719.N0913
