import GD.Module0232
import GD.Module0293















open Set
open scoped BigOperators

namespace GD.N0238


def d004321
    {X I : Type*} (u : Finset I)
    (obs : I → X → ℝ) (target : I → ℝ) (x : X) : ℝ :=
  ∑ i ∈ u, (obs i x - target i) ^ 2

theorem d004322
    {X I : Type*} (u : Finset I)
    (obs : I → X → ℝ) (target : I → ℝ) (x : X) :
    0 ≤ _root_.GD.N0238.d004321 u obs target x := by
  classical
  unfold _root_.GD.N0238.d004321
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem d004323
    {X I : Type*} [TopologicalSpace X]
    (u : Finset I) (obs : I → X → ℝ) (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i)) :
    Continuous (_root_.GD.N0238.d004321 u obs target) := by
  classical
  unfold _root_.GD.N0238.d004321
  exact continuous_finsetSum u fun i _hi ↦
    ((hobs i).sub continuous_const).pow 2








theorem d004324
    {X I : Type*} [TopologicalSpace X]
    (base : Set X) (hbase : IsCompact base)
    (obs : I → X → ℝ) (target : I → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (hno : ¬ ∃ x, x ∈ base ∧ ∀ i, obs i x = target i) :
    ∃ u : Finset I, ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ base, ε ≤ _root_.GD.N0238.d004321 u obs target x := by
  classical
  obtain ⟨u, hu⟩ :=
    _root_.GD.N0238.d004299
      base hbase obs target hobs hno
  have hpositive :
      ∀ x ∈ base, 0 < _root_.GD.N0238.d004321 u obs target x := by
    intro x hx
    have hne : _root_.GD.N0238.d004321 u obs target x ≠ 0 := by
      intro hzero
      apply hu
      refine ⟨x, hx, ?_⟩
      intro i hi
      have hterm : (obs i x - target i) ^ 2 = 0 := by
        have hsum :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun j (_hj : j ∈ u) ↦ sq_nonneg (obs j x - target j))).1
            hzero
        exact hsum i hi
      nlinarith
    exact lt_of_le_of_ne
      (_root_.GD.N0238.d004322 u obs target x) (Ne.symm hne)
  obtain ⟨ε, hε, hmargin⟩ :=
    hbase.exists_forall_le'
      (_root_.GD.N0238.d004323 u obs target hobs).continuousOn
      hpositive
  exact ⟨u, ε, hε, hmargin⟩


theorem d004325
    {X I : Type*} [TopologicalSpace X]
    (base : Set X) (hbase : IsCompact base)
    (obs : I → X → ℝ) (hobs : ∀ i, Continuous (obs i))
    (hno : ¬ ∃ x, x ∈ base ∧ ∀ i, obs i x = 0) :
    ∃ u : Finset I, ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ base, ε ≤
        ∑ i ∈ u, (obs i x) ^ 2 := by
  obtain ⟨u, ε, hε, hmargin⟩ :=
    _root_.GD.N0238.d004324
      base hbase obs (fun _ ↦ 0) hobs hno
  refine ⟨u, ε, hε, ?_⟩
  intro x hx
  simpa only [_root_.GD.N0238.d004321, sub_zero] using hmargin x hx










theorem d004326
    {X Y I : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (base : Set X) (hbase : IsCompact base)
    (targets : Set Y) (htargets : IsCompact targets)
    (obs : I → X → ℝ) (targetObs : I → Y → ℝ)
    (hobs : ∀ i, Continuous (obs i))
    (htargetObs : ∀ i, Continuous (targetObs i))
    (hno : ¬ ∃ x, x ∈ base ∧ ∃ y, y ∈ targets ∧
      ∀ i, obs i x = targetObs i y) :
    ∃ u : Finset I, ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ base, ∀ y ∈ targets,
        ε ≤ ∑ i ∈ u, (obs i x - targetObs i y) ^ 2 := by
  have hnoProduct :
      ¬ ∃ p : X × Y, p ∈ base ×ˢ targets ∧
        ∀ i, obs i p.1 = targetObs i p.2 := by
    rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩
    exact hno ⟨x, hx, y, hy, hxy⟩
  obtain ⟨u, ε, hε, hmargin⟩ :=
    _root_.GD.N0238.d004324
      (base ×ˢ targets) (hbase.prod htargets)
      (fun i p ↦ obs i p.1 - targetObs i p.2) (fun _ ↦ 0)
      (fun i ↦
        ((hobs i).comp continuous_fst).sub
          ((htargetObs i).comp continuous_snd))
      (by
        intro hcommon
        apply hnoProduct
        obtain ⟨p, hp, hzero⟩ := hcommon
        exact ⟨p, hp, fun i ↦ sub_eq_zero.mp (hzero i)⟩)
  refine ⟨u, ε, hε, ?_⟩
  intro x hx y hy
  simpa only [_root_.GD.N0238.d004321, sub_zero] using
    hmargin (x, y) ⟨hx, hy⟩

end GD.N0238
