import GD.Module0796



















open Filter Set Bornology

namespace GD
namespace N0232
namespace N0719
namespace N0826

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0845
open _root_.GD.N0232.N0719.N0820
open _root_.GD.N0232.N0719.N0847
open _root_.GD.N0232.N0719.N0822
open _root_.GD.N0232.N0719.N0952
open _root_.GD.N0232.N0719.N0827



theorem d012088 (x y : ℝ) :
    ‖(x, y)‖ ≤ x ∨ ‖(x, y)‖ ≤ -x ∨
      ‖(x, y)‖ ≤ y ∨ ‖(x, y)‖ ≤ -y := by
  rcases le_total ‖x‖ ‖y‖ with hxy | hyx
  · rcases le_total 0 y with hy | hy
    · right
      right
      left
      rw [Prod.norm_def, max_le_iff]
      exact ⟨hxy.trans_eq (Real.norm_of_nonneg hy),
        le_of_eq (Real.norm_of_nonneg hy)⟩
    · right
      right
      right
      rw [Prod.norm_def, max_le_iff]
      exact ⟨hxy.trans_eq (Real.norm_of_nonpos hy),
        le_of_eq (Real.norm_of_nonpos hy)⟩
  · rcases le_total 0 x with hx | hx
    · left
      rw [Prod.norm_def, max_le_iff]
      exact ⟨le_of_eq (Real.norm_of_nonneg hx),
        hyx.trans_eq (Real.norm_of_nonneg hx)⟩
    · right
      left
      rw [Prod.norm_def, max_le_iff]
      exact ⟨le_of_eq (Real.norm_of_nonpos hx),
        hyx.trans_eq (Real.norm_of_nonpos hx)⟩







theorem d012089
    (f g : ℕ → ℝ)
    (hescape : Tendsto (fun n ↦ ‖(f n, g n)‖) atTop atTop) :
    ∃ extraction : ℕ → ℕ,
      Tendsto extraction atTop atTop ∧
      (Tendsto (f ∘ extraction) atTop atTop ∨
        Tendsto (f ∘ extraction) atTop atBot ∨
        Tendsto (g ∘ extraction) atTop atTop ∨
        Tendsto (g ∘ extraction) atTop atBot) := by
  have hall : ∀ᶠ n in atTop,
      ‖(f n, g n)‖ ≤ f n ∨ ‖(f n, g n)‖ ≤ -f n ∨
        ‖(f n, g n)‖ ≤ g n ∨ ‖(f n, g n)‖ ≤ -g n :=
    Filter.Eventually.of_forall fun n ↦
      _root_.GD.N0232.N0719.N0826.d012088 (f n) (g n)
  rcases frequently_or_distrib.mp hall.frequently with hposf | hrest
  · obtain ⟨extraction, hextractionMono, hchannel⟩ :=
      extraction_of_frequently_atTop hposf
    have hnorm : Tendsto
        (fun n ↦ ‖(f (extraction n), g (extraction n))‖)
        atTop atTop := hescape.comp hextractionMono.tendsto_atTop
    have hend : Tendsto (f ∘ extraction) atTop atTop :=
      tendsto_atTop_mono (fun n ↦ hchannel n) hnorm
    exact ⟨extraction, hextractionMono.tendsto_atTop, Or.inl hend⟩
  · rcases frequently_or_distrib.mp hrest with hnegf | hrest
    · obtain ⟨extraction, hextractionMono, hchannel⟩ :=
        extraction_of_frequently_atTop hnegf
      have hnorm : Tendsto
          (fun n ↦ ‖(f (extraction n), g (extraction n))‖)
          atTop atTop := hescape.comp hextractionMono.tendsto_atTop
      have hneg : Tendsto (fun n ↦ -f (extraction n)) atTop atTop :=
        tendsto_atTop_mono (fun n ↦ hchannel n) hnorm
      have hend : Tendsto (f ∘ extraction) atTop atBot := by
        simpa [Function.comp_def] using tendsto_neg_atTop_atBot.comp hneg
      exact ⟨extraction, hextractionMono.tendsto_atTop,
        Or.inr (Or.inl hend)⟩
    · rcases frequently_or_distrib.mp hrest with hposg | hnegg
      · obtain ⟨extraction, hextractionMono, hchannel⟩ :=
          extraction_of_frequently_atTop hposg
        have hnorm : Tendsto
            (fun n ↦ ‖(f (extraction n), g (extraction n))‖)
            atTop atTop := hescape.comp hextractionMono.tendsto_atTop
        have hend : Tendsto (g ∘ extraction) atTop atTop :=
          tendsto_atTop_mono (fun n ↦ hchannel n) hnorm
        exact ⟨extraction, hextractionMono.tendsto_atTop,
          Or.inr (Or.inr (Or.inl hend))⟩
      · obtain ⟨extraction, hextractionMono, hchannel⟩ :=
          extraction_of_frequently_atTop hnegg
        have hnorm : Tendsto
            (fun n ↦ ‖(f (extraction n), g (extraction n))‖)
            atTop atTop := hescape.comp hextractionMono.tendsto_atTop
        have hneg : Tendsto (fun n ↦ -g (extraction n)) atTop atTop :=
          tendsto_atTop_mono (fun n ↦ hchannel n) hnorm
        have hend : Tendsto (g ∘ extraction) atTop atBot := by
          simpa [Function.comp_def] using tendsto_neg_atTop_atBot.comp hneg
        exact ⟨extraction, hextractionMono.tendsto_atTop,
          Or.inr (Or.inr (Or.inr hend))⟩



theorem d012090
    {k : ℕ} (hk : 0 < k) (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (extraction : ℕ → ℕ)
    (hlog : Tendsto
      (fun n ↦ Real.log (_root_.GD.N0232.N0719.N0845.d010886 (thetaSeq (extraction n))))
      atTop atTop) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0845.d010886 (thetaSeq (extraction n)))
      atTop atTop := by
  have hexp := Real.tendsto_exp_atTop.comp hlog
  convert hexp using 1
  funext n
  exact (Real.exp_log (_root_.GD.N0232.N0719.N0845.d010887 hk (thetaSeq (extraction n)))).symm



theorem d012091
    {k : ℕ} (hk : 0 < k) (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (extraction : ℕ → ℕ)
    (hlog : Tendsto
      (fun n ↦ Real.log (_root_.GD.N0232.N0719.N0845.d010886 (thetaSeq (extraction n))))
      atTop atBot) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0845.d010886 (thetaSeq (extraction n)))
      atTop (nhds 0) := by
  have hexp := Real.tendsto_exp_atBot.comp hlog
  convert hexp using 1
  funext n
  exact (Real.exp_log (_root_.GD.N0232.N0719.N0845.d010887 hk (thetaSeq (extraction n)))).symm







theorem d012092
    {k : ℕ} (hk : 0 < k) (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (haction : Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0827.d012078 (thetaSeq n))
      atTop atTop) :
    ∃ extraction : ℕ → ℕ,
      Tendsto extraction atTop atTop ∧
      (Tendsto (fun n ↦ (thetaSeq (extraction n)).location)
          atTop atTop ∨
        Tendsto (fun n ↦ (thetaSeq (extraction n)).location)
          atTop atBot ∨
        Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0845.d010886 (thetaSeq (extraction n)))
          atTop atTop ∨
        Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0845.d010886 (thetaSeq (extraction n)))
          atTop (nhds 0)) := by
  have hgauge : Tendsto
      (fun n ↦ ‖((thetaSeq n).location,
        Real.log (_root_.GD.N0232.N0719.N0845.d010886 (thetaSeq n)))‖)
      atTop atTop := by
    simpa [_root_.GD.N0232.N0719.N0827.d012078, _root_.GD.N0232.N0719.N0827.d012077] using haction
  obtain ⟨extraction, hextraction, hend⟩ :=
    _root_.GD.N0232.N0719.N0826.d012089
      (fun n ↦ (thetaSeq n).location)
      (fun n ↦ Real.log (_root_.GD.N0232.N0719.N0845.d010886 (thetaSeq n))) hgauge
  refine ⟨extraction, hextraction, ?_⟩
  rcases hend with hlocationTop | hlocationBot | hlogTop | hlogBot
  · exact Or.inl (by simpa [Function.comp_def] using hlocationTop)
  · exact Or.inr (Or.inl (by
      simpa [Function.comp_def] using hlocationBot))
  · exact Or.inr (Or.inr (Or.inl
      (_root_.GD.N0232.N0719.N0826.d012090
        hk thetaSeq extraction (by
          simpa [Function.comp_def] using hlogTop))))
  · exact Or.inr (Or.inr (Or.inr
      (_root_.GD.N0232.N0719.N0826.d012091
        hk thetaSeq extraction (by
          simpa [Function.comp_def] using hlogBot))))



theorem d012093
    {k : ℕ} (hk : 0 < k) (thetaSeq : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (hcluster : ¬ _root_.GD.N0232.N0719.N0952.d012068 thetaSeq) :
    ∃ extraction : ℕ → ℕ,
      Tendsto extraction atTop atTop ∧
      (Tendsto (fun n ↦ (thetaSeq (extraction n)).location)
          atTop atTop ∨
        Tendsto (fun n ↦ (thetaSeq (extraction n)).location)
          atTop atBot ∨
        Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0845.d010886 (thetaSeq (extraction n)))
          atTop atTop ∨
        Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0845.d010886 (thetaSeq (extraction n)))
          atTop (nhds 0)) := by
  exact _root_.GD.N0232.N0719.N0826.d012092
    hk thetaSeq
    (_root_.GD.N0232.N0719.N0827.d012083
      hk thetaSeq hcluster)



theorem d012094
    {k : ℕ} {sizes : Fin k → ℕ}
    {hk : 3 ≤ k} {hsizes : ∀ i, 2 ≤ sizes i}
    (z : _root_.GD.N0232.N0719.N0820.d011744 k sizes hk hsizes)
    (hfull : z.1.active = Finset.univ) :
    ∃ extraction : ℕ → ℕ,
      Tendsto extraction atTop atTop ∧
      (Tendsto (fun n ↦ (z.1.thetaSeq (extraction n)).location)
          atTop atTop ∨
        Tendsto (fun n ↦ (z.1.thetaSeq (extraction n)).location)
          atTop atBot ∨
        Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0845.d010886 (z.1.thetaSeq (extraction n)))
          atTop atTop ∨
        Tendsto (fun n ↦ _root_.GD.N0232.N0719.N0845.d010886 (z.1.thetaSeq (extraction n)))
          atTop (nhds 0)) := by
  exact _root_.GD.N0232.N0719.N0826.d012092
    (by omega : 0 < k) z.1.thetaSeq
    (_root_.GD.N0232.N0719.N0827.d012086 z hfull)








theorem d012095
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0232.N0719.N0847.d011875 k sizes ∨
      ∃ z : _root_.GD.N0232.N0719.N0822.d011886
          k sizes hk hsizes,
        z.localized.1.1.active.card ≤ 2 ∨
        (3 ≤ z.localized.1.1.active.card ∧
          z.localized.1.1.active.card < k) ∨
        (z.localized.1.1.active = Finset.univ ∧
          ∃ extraction : ℕ → ℕ,
            Tendsto extraction atTop atTop ∧
            (Tendsto
                (fun n ↦
                  (z.localized.1.1.thetaSeq (extraction n)).location)
                atTop atTop ∨
              Tendsto
                (fun n ↦
                  (z.localized.1.1.thetaSeq (extraction n)).location)
                atTop atBot ∨
              Tendsto
                (fun n ↦ _root_.GD.N0232.N0719.N0845.d010886
                  (z.localized.1.1.thetaSeq (extraction n)))
                atTop atTop ∨
              Tendsto
                (fun n ↦ _root_.GD.N0232.N0719.N0845.d010886
                  (z.localized.1.1.thetaSeq (extraction n)))
                atTop (nhds 0))) := by
  rcases _root_.GD.N0232.N0719.N0952.d012076
      k sizes hk hsizes with hterminal | ⟨z, hsupport⟩
  · exact Or.inl hterminal
  · right
    refine ⟨z, ?_⟩
    rcases hsupport with hlow | hproper | ⟨hfull, hnoCluster⟩
    · exact Or.inl hlow
    · exact Or.inr (Or.inl hproper)
    · exact Or.inr (Or.inr ⟨hfull,
        _root_.GD.N0232.N0719.N0826.d012093
          (by omega : 0 < k) z.localized.1.1.thetaSeq hnoCluster⟩)

end

end N0826
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0826.d012088
#print axioms _root_.GD.N0232.N0719.N0826.d012089
#print axioms _root_.GD.N0232.N0719.N0826.d012090
#print axioms _root_.GD.N0232.N0719.N0826.d012091
#print axioms _root_.GD.N0232.N0719.N0826.d012092
#print axioms _root_.GD.N0232.N0719.N0826.d012093
#print axioms _root_.GD.N0232.N0719.N0826.d012094
#print axioms _root_.GD.N0232.N0719.N0826.d012095
