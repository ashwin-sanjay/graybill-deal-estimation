import GD.Module0017
import GD.Module0241











open Set
open scoped BigOperators ENNReal

namespace GD.N0230.N0626

noncomputable section

set_option linter.unusedSectionVars false



theorem d003526
    {E I : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype I] [DecidableEq I]
    (D : Set E) (hD : Convex ℝ D) (hne : D.Nonempty)
    (risk : I → E → ℝ) (cap : I → ℝ)
    (hconvex : ∀ i, ConvexOn ℝ D (risk i))
    (htest : ∀ w : I → ℝ, (∀ i, 0 ≤ w i) → ∀ a : ℝ,
      (∀ x ∈ D, a ≤ ∑ i, w i * risk i x) → a ≤ ∑ i, w i * cap i)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ x ∈ D, ∀ i, risk i x ≤ cap i + ε := by
  classical
  by_contra hnot
  let domain : Set (E × ℝ) := D ×ˢ univ
  let objective : E × ℝ → ℝ := fun x ↦ x.2
  let constraint : I → E × ℝ → ℝ :=
    fun i x ↦ risk i x.1 - cap i - x.2
  have hdomain : Convex ℝ domain := hD.prod convex_univ
  have hobj : ConvexOn ℝ domain objective := by
    refine ⟨hdomain, ?_⟩
    intro x hx y hy a b ha hb hab
    simp [objective]
  have hcon : ∀ i, ConvexOn ℝ domain (constraint i) := by
    intro i
    refine ⟨hdomain, ?_⟩
    intro x hx y hy a b ha hb hab
    have hc := (hconvex i).2 hx.1 hy.1 ha hb hab
    simp only [smul_eq_mul] at hc
    change risk i (a • x.1 + b • y.1) - cap i - (a * x.2 + b * y.2) ≤
      a * (risk i x.1 - cap i - x.2) +
        b * (risk i y.1 - cap i - y.2)
    have hcapid : (a + b) * cap i = cap i := by rw [hab]; ring
    nlinarith [hcapid]
  have hlower : ∀ x ∈ domain, (∀ i, constraint i x ≤ 0) → ε ≤ objective x := by
    intro x hx hc
    by_contra hlt
    have hxe : x.2 < ε := lt_of_not_ge hlt
    apply hnot
    refine ⟨x.1, hx.1, fun i ↦ ?_⟩
    have hi := hc i
    dsimp [constraint] at hi
    linarith
  have hslater : ∃ x ∈ domain, ∀ i, constraint i x < 0 := by
    obtain ⟨s, hs⟩ := hne
    let t := (∑ i, max 0 (risk i s - cap i)) + 1
    refine ⟨(s, t), ⟨hs, mem_univ _⟩, fun i ↦ ?_⟩
    have hi : max 0 (risk i s - cap i) ≤ ∑ j, max 0 (risk j s - cap j) :=
      Finset.single_le_sum (fun j _ ↦ le_max_left 0 (risk j s - cap j))
        (Finset.mem_univ i)
    have him := le_max_right (0 : ℝ) (risk i s - cap i)
    dsimp [constraint, t]
    linarith
  obtain ⟨w, hw, hcert⟩ :=
    _root_.GD.N0230.N0614.d000150
      domain objective constraint hdomain hobj hcon ε hlower hslater
  have hlowerWeighted : ∀ x ∈ D,
      ε + ∑ i, w i * cap i ≤ ∑ i, w i * risk i x := by
    intro x hx
    have hbound := hcert (x, 0) ⟨hx, mem_univ _⟩
    simp only [objective, constraint, sub_zero, zero_add] at hbound
    simp only [mul_sub, Finset.sum_sub_distrib] at hbound
    linarith
  have hbound := htest w hw (ε + ∑ i, w i * cap i) hlowerWeighted
  linarith


theorem d003527
    {E I : Type*} [AddCommGroup E] [Module ℝ E]
    [Fintype I] [DecidableEq I]
    (D : Set E) (hD : Convex ℝ D) (hne : D.Nonempty)
    (risk : I → E → ℝ) (cap : I → ℝ)
    (hconvex : ∀ i, ConvexOn ℝ D (risk i))
    (htest : ∀ w : I → ℝ, (∀ i, 0 ≤ w i) →
      ∃ x ∈ D, ∑ i, w i * risk i x ≤ ∑ i, w i * cap i)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ x ∈ D, ∀ i, risk i x ≤ cap i + ε := by
  apply _root_.GD.N0230.N0626.d003526
    D hD hne risk cap hconvex _ ε hε
  intro w hw a ha
  obtain ⟨x, hx, hb⟩ := htest w hw
  exact (ha x hx).trans hb



theorem d003528
    {E Θ : Type*} [TopologicalSpace E]
    (risk : Θ → E → ℝ≥0∞) (cap : Θ → ℝ)
    (hcap : ∀ θ, 0 ≤ cap θ) (anchor : Θ)
    (hcompact : IsCompact {x | risk anchor x ≤ ENNReal.ofReal (cap anchor + 1)})
    (hclosed : ∀ θ c, IsClosed {x | risk θ x ≤ ENNReal.ofReal c})
    (hfinite : ∀ F : Finset Θ, ∀ ε : ℝ, 0 < ε →
      ∃ x, ∀ θ ∈ F, risk θ x ≤ ENNReal.ofReal (cap θ + ε)) :
    ∃ x, ∀ θ, risk θ x ≤ ENNReal.ofReal (cap θ) := by
  classical
  let I := Θ × {ε : ℝ // 0 < ε}
  let K : I → Set E := fun i ↦ {x | risk i.1 x ≤ ENNReal.ofReal (cap i.1 + i.2.val)}
  have hinter :
      ({x | risk anchor x ≤ ENNReal.ofReal (cap anchor + 1)} ∩ ⋂ i, K i).Nonempty := by
    apply hcompact.inter_iInter_nonempty K
      (fun i ↦ hclosed i.1 (cap i.1 + i.2.val))
    intro u
    let epsilons : Finset ℝ := insert 1 (u.image fun i ↦ i.2.val)
    have heps : epsilons.Nonempty := Finset.insert_nonempty _ _
    let δ := epsilons.min' heps
    have hδpos : 0 < δ := by
      have hm := epsilons.min'_mem heps
      rcases Finset.mem_insert.mp hm with hm | hm
      · change 0 < epsilons.min' heps
        rw [hm]
        norm_num
      · obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hm
        change 0 < epsilons.min' heps
        rw [← heq]
        exact i.2.property
    have hδone : δ ≤ 1 := epsilons.min'_le 1 (Finset.mem_insert_self _ _)
    obtain ⟨x, hx⟩ := hfinite (insert anchor (u.image Prod.fst)) δ hδpos
    refine ⟨x, ?_, ?_⟩
    · exact (hx anchor (Finset.mem_insert_self _ _)).trans
        (ENNReal.ofReal_le_ofReal (by linarith))
    · simp only [mem_iInter]
      intro i hi
      have hδi : δ ≤ i.2.val :=
        epsilons.min'_le i.2.val (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
      exact (hx i.1 (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩))).trans
        (ENNReal.ofReal_le_ofReal (by linarith))
  obtain ⟨x, _, hx⟩ := hinter
  refine ⟨x, fun θ ↦ ?_⟩
  apply _root_.GD.N0230.N0586.d003515 (hcap θ)
  intro c hc
  have hb := mem_iInter.mp hx (θ, ⟨c - cap θ, sub_pos.mpr hc⟩)
  simpa [K] using hb




theorem d003529
    {E Θ : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (risk : Θ → E → ℝ≥0∞) (cap : Θ → ℝ)
    (D : Set E) (hD : Convex ℝ D) (hne : D.Nonempty)
    (hfiniteDomain : ∀ x, x ∈ D ↔ ∀ θ, risk θ x ≠ ⊤)
    (hconvex : ∀ θ, ConvexOn ℝ D (fun x ↦ (risk θ x).toReal))
    (hcap : ∀ θ, 0 ≤ cap θ) (anchor : Θ)
    (hcompact : IsCompact {x | risk anchor x ≤ ENNReal.ofReal (cap anchor + 1)})
    (hclosed : ∀ θ c, IsClosed {x | risk θ x ≤ ENNReal.ofReal c}) :
    (∃ x, ∀ θ, risk θ x ≤ ENNReal.ofReal (cap θ)) ↔
      ∀ (F : Finset Θ) (w : Θ → ℝ), (∀ θ ∈ F, 0 ≤ w θ) →
        ∃ x ∈ D, ∑ θ ∈ F, w θ * (risk θ x).toReal ≤ ∑ θ ∈ F, w θ * cap θ := by
  classical
  constructor
  · rintro ⟨x, hx⟩ F w hw
    have hxD : x ∈ D := (hfiniteDomain x).mpr fun θ ↦
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hx θ)
    refine ⟨x, hxD, Finset.sum_le_sum fun θ hθ ↦ ?_⟩
    apply mul_le_mul_of_nonneg_left _ (hw θ hθ)
    exact (ENNReal.toReal_le_toReal ((hfiniteDomain x).mp hxD θ)
      ENNReal.ofReal_ne_top).mpr (hx θ) |>.trans_eq (ENNReal.toReal_ofReal (hcap θ))
  · intro htest
    apply _root_.GD.N0230.N0626.d003528 risk cap hcap anchor hcompact hclosed
    intro F ε hε
    have htests : ∀ w : F → ℝ, (∀ i, 0 ≤ w i) →
        ∃ x ∈ D, ∑ i, w i * (risk i.val x).toReal ≤ ∑ i, w i * cap i.val := by
      intro w hw
      let w' : Θ → ℝ := fun θ ↦ if hθ : θ ∈ F then w ⟨θ, hθ⟩ else 0
      obtain ⟨x, hx, hb⟩ := htest F w' (by
        intro θ hθ
        simpa [w', hθ] using hw ⟨θ, hθ⟩)
      refine ⟨x, hx, ?_⟩
      have hb' : (∑ i : F, w' i.val * (risk i.val x).toReal) ≤
          ∑ i : F, w' i.val * cap i.val := by
        rw [← Finset.sum_coe_sort F (fun θ ↦ w' θ * (risk θ x).toReal),
          ← Finset.sum_coe_sort F (fun θ ↦ w' θ * cap θ)] at hb
        exact hb
      simpa [w'] using hb'
    obtain ⟨x, hxD, hx⟩ := _root_.GD.N0230.N0626.d003527
      D hD hne (fun i : F ↦ fun x ↦ (risk i.val x).toReal)
      (fun i : F ↦ cap i.val) (fun i ↦ hconvex i.val) htests ε hε
    refine ⟨x, fun θ hθ ↦ ?_⟩
    have hb := hx ⟨θ, hθ⟩
    apply (ENNReal.toReal_le_toReal ((hfiniteDomain x).mp hxD θ)
      ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (show 0 ≤ cap θ + ε by linarith [hcap θ])]
    exact hb




theorem d003530
    {E Θ : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (risk : Θ → E → ℝ≥0∞) (cap : Θ → ℝ)
    (D : Set E) (hD : Convex ℝ D) (hne : D.Nonempty)
    (hfiniteDomain : ∀ x, x ∈ D ↔ ∀ θ, risk θ x ≠ ⊤)
    (hconvex : ∀ θ, ConvexOn ℝ D (fun x ↦ (risk θ x).toReal))
    (hcap : ∀ θ, 0 ≤ cap θ) (anchor : Θ)
    (hcompact : IsCompact {x | risk anchor x ≤ ENNReal.ofReal (cap anchor + 1)})
    (hclosed : ∀ θ c, IsClosed {x | risk θ x ≤ ENNReal.ofReal c}) :
    (∃ x, ∀ θ, risk θ x ≤ ENNReal.ofReal (cap θ)) ↔
      ∀ (F : Finset Θ) (w : Θ → ℝ), (∀ θ ∈ F, 0 ≤ w θ) → ∀ a : ℝ,
        (∀ x ∈ D, a ≤ ∑ θ ∈ F, w θ * (risk θ x).toReal) →
          a ≤ ∑ θ ∈ F, w θ * cap θ := by
  classical
  constructor
  · intro h F w hw a ha
    obtain ⟨x, hx, hb⟩ :=
      (_root_.GD.N0230.N0626.d003529 risk cap D hD hne
        hfiniteDomain hconvex hcap anchor hcompact hclosed).mp h F w hw
    exact (ha x hx).trans hb
  · intro htest
    apply _root_.GD.N0230.N0626.d003528 risk cap hcap anchor hcompact hclosed
    intro F ε hε
    have htests : ∀ w : F → ℝ, (∀ i, 0 ≤ w i) → ∀ a : ℝ,
        (∀ x ∈ D, a ≤ ∑ i, w i * (risk i.val x).toReal) →
          a ≤ ∑ i, w i * cap i.val := by
      intro w hw a ha
      let w' : Θ → ℝ := fun θ ↦ if hθ : θ ∈ F then w ⟨θ, hθ⟩ else 0
      have hsum (f : Θ → ℝ) :
          (∑ θ ∈ F, w' θ * f θ) = ∑ i : F, w i * f i.val := by
        rw [← Finset.sum_coe_sort]
        simp [w']
      have hb := htest F w' (by
        intro θ hθ
        simpa [w', hθ] using hw ⟨θ, hθ⟩) a (by
          intro x hx
          rw [hsum]
          exact ha x hx)
      rwa [hsum] at hb
    obtain ⟨x, hxD, hx⟩ := _root_.GD.N0230.N0626.d003526
      D hD hne (fun i : F ↦ fun x ↦ (risk i.val x).toReal)
      (fun i : F ↦ cap i.val) (fun i ↦ hconvex i.val) htests ε hε
    refine ⟨x, fun θ hθ ↦ ?_⟩
    apply (ENNReal.toReal_le_toReal ((hfiniteDomain x).mp hxD θ)
      ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (show 0 ≤ cap θ + ε by linarith [hcap θ])]
    exact hx ⟨θ, hθ⟩



theorem d003531
    {E Θ : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (risk : Θ → E → ℝ≥0∞) (cap : Θ → ℝ)
    (D : Set E) (hD : Convex ℝ D) (hne : D.Nonempty)
    (hfiniteDomain : ∀ x, x ∈ D ↔ ∀ θ, risk θ x ≠ ⊤)
    (hconvex : ∀ θ, ConvexOn ℝ D (fun x ↦ (risk θ x).toReal))
    (hcap : ∀ θ, 0 ≤ cap θ) (anchor : Θ)
    (hcompact : IsCompact {x | risk anchor x ≤ ENNReal.ofReal (cap anchor + 1)})
    (hclosed : ∀ θ c, IsClosed {x | risk θ x ≤ ENNReal.ofReal c})
    (hno : ¬ ∃ x, ∀ θ, risk θ x ≤ ENNReal.ofReal (cap θ)) :
    ∃ (F : Finset Θ) (w : Θ → ℝ) (a : ℝ),
      (∀ θ ∈ F, 0 ≤ w θ) ∧
      (∀ x ∈ D, a ≤ ∑ θ ∈ F, w θ * (risk θ x).toReal) ∧
      ∑ θ ∈ F, w θ * cap θ < a := by
  have h := (_root_.GD.N0230.N0626.d003530 risk cap D hD hne
    hfiniteDomain hconvex hcap anchor hcompact hclosed).not.mp hno
  push Not at h
  obtain ⟨F, w, hw, a, ha, hb⟩ := h
  exact ⟨F, w, a, hw, ha, hb⟩

end

end GD.N0230.N0626

#print axioms _root_.GD.N0230.N0626.d003527
#print axioms _root_.GD.N0230.N0626.d003526
#print axioms _root_.GD.N0230.N0626.d003528
#print axioms _root_.GD.N0230.N0626.d003529
#print axioms _root_.GD.N0230.N0626.d003530
#print axioms _root_.GD.N0230.N0626.d003531
