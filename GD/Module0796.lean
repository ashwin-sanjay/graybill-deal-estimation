import GD.Module0795
import GD.Module0292




















open Filter Set Bornology

namespace GD
namespace N0232
namespace N0719
namespace N0827

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0845
open _root_.GD.N0232.N0719.N0820
open _root_.GD.N0232.N0719.N0847
open _root_.GD.N0232.N0719.N0822
open _root_.GD.N0232.N0719.N0952
open _root_.GD.N0238.N0750


def d012077 {k : ℕ} (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : ℝ × ℝ :=
  (theta.location, Real.log (_root_.GD.N0232.N0719.N0845.d010886 theta))


def d012078 {k : ℕ} (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : ℝ :=
  ‖_root_.GD.N0232.N0719.N0827.d012077 theta‖




theorem d012079
    {k : ℕ} (hk : 0 < k) (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (extraction : ℕ → ℕ) (hextraction : Tendsto extraction atTop atTop)
    (gaugeLimit : ℝ × ℝ)
    (hgauge : Tendsto (_root_.GD.N0232.N0719.N0827.d012077 ∘ thetaSeq ∘ extraction)
      atTop (nhds gaugeLimit)) :
    _root_.GD.N0232.N0719.N0952.d012068 thetaSeq := by
  have hlocation : Tendsto
      (fun n ↦ (thetaSeq (extraction n)).location)
      atTop (nhds gaugeLimit.1) := by
    simpa [_root_.GD.N0232.N0719.N0827.d012077, Function.comp_def] using
      (continuous_fst.tendsto gaugeLimit).comp hgauge
  have hlogScale : Tendsto
      (fun n ↦ Real.log (_root_.GD.N0232.N0719.N0845.d010886 (thetaSeq (extraction n))))
      atTop (nhds gaugeLimit.2) := by
    simpa [_root_.GD.N0232.N0719.N0827.d012077, Function.comp_def] using
      (continuous_snd.tendsto gaugeLimit).comp hgauge
  have hscale : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0845.d010886 (thetaSeq (extraction n)))
      atTop (nhds (Real.exp gaugeLimit.2)) := by
    have hexp := (Real.continuous_exp.tendsto gaugeLimit.2).comp hlogScale
    convert hexp using 1
    funext n
    exact (Real.exp_log (_root_.GD.N0232.N0719.N0845.d010887 hk (thetaSeq (extraction n)))).symm
  exact ⟨extraction, hextraction, gaugeLimit.1, Real.exp gaugeLimit.2,
    Real.exp_pos _, hlocation, hscale⟩



theorem d012080
    {k : ℕ} (hk : 0 < k) (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0952.d012068 thetaSeq ↔
      _root_.GD.N0238.N0750.d004292 (fun n ↦ _root_.GD.N0232.N0719.N0827.d012077 (thetaSeq n)) := by
  constructor
  · rintro ⟨extraction, hextraction, locationLimit, scaleLimit,
      hscaleLimit, hlocation, htotalScale⟩
    have hlogScale : Tendsto
        (fun n ↦ Real.log (_root_.GD.N0232.N0719.N0845.d010886 (thetaSeq (extraction n))))
        atTop (nhds (Real.log scaleLimit)) :=
      (Real.continuousAt_log hscaleLimit.ne').tendsto.comp htotalScale
    refine ⟨extraction, hextraction,
      (locationLimit, Real.log scaleLimit), ?_⟩
    simpa [_root_.GD.N0232.N0719.N0827.d012077, Function.comp_def] using
      hlocation.prodMk_nhds hlogScale
  · rintro ⟨extraction, hextraction, gaugeLimit, hgauge⟩
    apply _root_.GD.N0232.N0719.N0827.d012079
      hk thetaSeq extraction hextraction gaugeLimit
    simpa [Function.comp_def] using hgauge




theorem d012081
    {k : ℕ} (hk : 0 < k) (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (hfrequent : ∃ᶠ n in atTop, _root_.GD.N0232.N0719.N0827.d012077 (thetaSeq n) ∈ K) :
    _root_.GD.N0232.N0719.N0952.d012068 thetaSeq := by
  obtain ⟨gaugeLimit, _hgaugeLimitMem, extraction, hextractionMono,
      hgauge⟩ :=
    tendsto_subseq_of_frequently_bounded hK.isBounded hfrequent
  apply _root_.GD.N0232.N0719.N0827.d012079
    hk thetaSeq extraction hextractionMono.tendsto_atTop gaugeLimit
  simpa [Function.comp_def] using hgauge




theorem d012082
    {k : ℕ} (hk : 0 < k) (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (hcluster : ¬ _root_.GD.N0232.N0719.N0952.d012068 thetaSeq) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0827.d012077 (thetaSeq n)) atTop
      (Filter.cocompact (ℝ × ℝ)) := by
  refine Filter.hasBasis_cocompact.tendsto_right_iff.mpr ?_
  intro K hK
  by_contra hnot
  have hfrequent : ∃ᶠ n in atTop, _root_.GD.N0232.N0719.N0827.d012077 (thetaSeq n) ∈ K := by
    simpa only [Set.mem_compl_iff, not_not] using (not_eventually.mp hnot)
  exact hcluster
    (_root_.GD.N0232.N0719.N0827.d012081
      hk thetaSeq K hK hfrequent)










theorem d012083
    {k : ℕ} (hk : 0 < k) (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (hcluster : ¬ _root_.GD.N0232.N0719.N0952.d012068 thetaSeq) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0827.d012078 (thetaSeq n)) atTop atTop := by
  exact tendsto_norm_cocompact_atTop.comp
    (_root_.GD.N0232.N0719.N0827.d012082
      hk thetaSeq hcluster)



theorem d012084
    {k : ℕ} (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (haction : Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0827.d012078 (thetaSeq n))
      atTop atTop) :
    ¬ _root_.GD.N0232.N0719.N0952.d012068 thetaSeq := by
  rintro ⟨extraction, hextraction, locationLimit, scaleLimit,
    hscaleLimit, hlocation, htotalScale⟩
  have hlogScale : Tendsto
      (fun n ↦ Real.log (_root_.GD.N0232.N0719.N0845.d010886 (thetaSeq (extraction n))))
      atTop (nhds (Real.log scaleLimit)) :=
    (Real.continuousAt_log hscaleLimit.ne').tendsto.comp htotalScale
  have hgauge : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0827.d012077 (thetaSeq (extraction n)))
      atTop (nhds (locationLimit, Real.log scaleLimit)) := by
    simpa [_root_.GD.N0232.N0719.N0827.d012077] using hlocation.prodMk_nhds hlogScale
  have hfinite : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0827.d012078 (thetaSeq (extraction n)))
      atTop (nhds ‖(locationLimit, Real.log scaleLimit)‖) := by
    simpa [_root_.GD.N0232.N0719.N0827.d012078] using hgauge.norm
  have hinfinite : Tendsto
      (fun n ↦ _root_.GD.N0232.N0719.N0827.d012078 (thetaSeq (extraction n)))
      atTop atTop := haction.comp hextraction
  exact not_tendsto_atTop_of_tendsto_nhds hfinite hinfinite




theorem d012085
    {k : ℕ} (hk : 0 < k) (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k) :
    (¬ _root_.GD.N0232.N0719.N0952.d012068 thetaSeq) ↔
      Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0827.d012078 (thetaSeq n)) atTop atTop := by
  constructor
  · exact _root_.GD.N0232.N0719.N0827.d012083 hk thetaSeq
  · exact _root_.GD.N0232.N0719.N0827.d012084 thetaSeq



theorem d012086
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes)
    (hfull : z.1.active = Finset.univ) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0827.d012078 (z.1.thetaSeq n)) atTop atTop := by
  exact _root_.GD.N0232.N0719.N0827.d012083
    (by omega : 0 < k) z.1.thetaSeq
    (_root_.GD.N0232.N0719.N0952.d012069 z hfull)













theorem d012087
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0847.d011875 k sizes ∨
      ∃ z : _root_.GD.N0232.N0719.N0822.d011886
          k sizes hk hsizes,
        z.localized.1.1.active.card ≤ 2 ∨
        (3 ≤ z.localized.1.1.active.card ∧
          z.localized.1.1.active.card < k) ∨
        (z.localized.1.1.active = Finset.univ ∧
          Tendsto
            (fun n ↦ _root_.GD.N0232.N0719.N0827.d012078 (z.localized.1.1.thetaSeq n))
            atTop atTop) := by
  rcases _root_.GD.N0232.N0719.N0952.d012076
      k sizes hk hsizes with hterminal | ⟨z, hsupport⟩
  · exact Or.inl hterminal
  · right
    refine ⟨z, ?_⟩
    rcases hsupport with hlow | hproper | ⟨hfull, hnoCluster⟩
    · exact Or.inl hlow
    · exact Or.inr (Or.inl hproper)
    · exact Or.inr (Or.inr ⟨hfull,
        _root_.GD.N0232.N0719.N0827.d012083
          (by omega : 0 < k) z.localized.1.1.thetaSeq hnoCluster⟩)

end

end N0827
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0827.d012079
#print axioms _root_.GD.N0232.N0719.N0827.d012080
#print axioms _root_.GD.N0232.N0719.N0827.d012081
#print axioms _root_.GD.N0232.N0719.N0827.d012082
#print axioms _root_.GD.N0232.N0719.N0827.d012083
#print axioms _root_.GD.N0232.N0719.N0827.d012084
#print axioms _root_.GD.N0232.N0719.N0827.d012085
#print axioms _root_.GD.N0232.N0719.N0827.d012086
#print axioms _root_.GD.N0232.N0719.N0827.d012087
