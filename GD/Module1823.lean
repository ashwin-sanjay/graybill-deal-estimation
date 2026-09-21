import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace GD.N0236.N0745

variable {X : Type*}

noncomputable def d030145 (A : ℝ → Set X) (q : ℚ) (x : X) : ℝ := by
  classical
  exact if (0 : ℝ) < q ∧ (q : ℝ) < 1 ∧ x ∈ A q then q else 0

noncomputable def d030146 (A : ℝ → Set X) (x : X) : ℝ :=
  ⨆ q : ℚ, _root_.GD.N0236.N0745.d030145 A q x

def d030147 (A : ℝ → Set X) : Prop :=
  ∀ a ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
    a ≤ b → A b ⊆ A a

theorem d030148 (A : ℝ → Set X) (q : ℚ) (x : X) :
    _root_.GD.N0236.N0745.d030145 A q x ∈ Icc (0 : ℝ) 1 := by
  classical
  unfold _root_.GD.N0236.N0745.d030145
  split_ifs with h
  · exact ⟨h.1.le, h.2.1.le⟩
  · norm_num

theorem d030149 (A : ℝ → Set X) (x : X) :
    BddAbove (range (fun q : ℚ => _root_.GD.N0236.N0745.d030145 A q x)) :=
  ⟨1, by rintro _ ⟨q, rfl⟩; exact (_root_.GD.N0236.N0745.d030148 A q x).2⟩

theorem d030150 (A : ℝ → Set X) (x : X) :
    _root_.GD.N0236.N0745.d030146 A x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact (_root_.GD.N0236.N0745.d030148 A 0 x).1.trans
      (le_ciSup (_root_.GD.N0236.N0745.d030149 A x) (0 : ℚ))
  · exact ciSup_le fun q => (_root_.GD.N0236.N0745.d030148 A q x).2

theorem d030151 [MeasurableSpace X]
    (A : ℝ → Set X) (hA : ∀ q : ℚ, MeasurableSet (A q)) :
    Measurable (_root_.GD.N0236.N0745.d030146 A) := by
  classical
  apply Measurable.iSup
  intro q
  unfold _root_.GD.N0236.N0745.d030145
  exact Measurable.ite
    ((MeasurableSet.const _).inter
      ((MeasurableSet.const _).inter (hA q))) measurable_const measurable_const

theorem d030152 {A : ℝ → Set X} (hA : _root_.GD.N0236.N0745.d030147 A)
    {x : X} {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hx : a < _root_.GD.N0236.N0745.d030146 A x) : x ∈ A a := by
  classical
  obtain ⟨q, hq⟩ := (lt_ciSup_iff (_root_.GD.N0236.N0745.d030149 A x)).mp hx
  unfold _root_.GD.N0236.N0745.d030145 at hq
  split_ifs at hq with h
  · exact hA a ha q ⟨h.1, h.2.1⟩ hq.le h.2.2
  · linarith [ha.1]

theorem d030153 {A : ℝ → Set X} (hA : _root_.GD.N0236.N0745.d030147 A)
    {x : X} {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hx : x ∈ A a) : a ≤ _root_.GD.N0236.N0745.d030146 A x := by
  classical
  by_contra h
  have hlt : _root_.GD.N0236.N0745.d030146 A x < a := lt_of_not_ge h
  obtain ⟨q, hpq, hqa⟩ := exists_rat_btwn hlt
  have hq0 : (0 : ℝ) < q :=
    (_root_.GD.N0236.N0745.d030150 A x).1.trans_lt hpq
  have hq1 : (q : ℝ) < 1 := hqa.trans ha.2
  have hxq : x ∈ A q := hA q ⟨hq0, hq1⟩ a ha hqa.le hx
  have hqle := le_ciSup (_root_.GD.N0236.N0745.d030149 A x) q
  have hv : _root_.GD.N0236.N0745.d030145 A q x = q := if_pos ⟨hq0, hq1, hxq⟩
  rw [hv] at hqle
  exact (not_le_of_gt hpq) hqle

theorem d030154 {A : ℝ → Set X} (hA : _root_.GD.N0236.N0745.d030147 A)
    {x : X} {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    a ≤ _root_.GD.N0236.N0745.d030146 A x ↔ ∀ b ∈ Ioo (0 : ℝ) a, x ∈ A b := by
  constructor
  · intro hx b hb
    exact _root_.GD.N0236.N0745.d030152 hA ⟨hb.1, hb.2.trans ha.2⟩
      (hb.2.trans_le hx)
  · intro hx
    by_contra hn
    have hl : _root_.GD.N0236.N0745.d030146 A x < a := lt_of_not_ge hn
    let b := (_root_.GD.N0236.N0745.d030146 A x + a) / 2
    have hb : b ∈ Ioo (0 : ℝ) a := by
      dsimp [b]; constructor <;> linarith [(_root_.GD.N0236.N0745.d030150 A x).1]
    have := _root_.GD.N0236.N0745.d030153 hA ⟨hb.1, hb.2.trans ha.2⟩ (hx b hb)
    dsimp [b] at this
    linarith

theorem d030155
    [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {A : ℝ → Set X} (hA : _root_.GD.N0236.N0745.d030147 A)
    (hcal : ∀ a ∈ Ioo (0 : ℝ) 1, μ.real (A a) = 1 - a)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    μ.real {x | a ≤ _root_.GD.N0236.N0745.d030146 A x} = 1 - a := by
  let m := μ.real {x | a ≤ _root_.GD.N0236.N0745.d030146 A x}
  change m = 1 - a
  apply le_antisymm
  · by_contra h
    have hm : 1 - a < m := lt_of_not_ge h
    let b := (max 0 (1 - m) + a) / 2
    have hmax : max 0 (1 - m) < a := max_lt ha0 (by linarith)
    have hb0 : 0 < b := by dsimp [b]; linarith [le_max_left (0 : ℝ) (1-m)]
    have hba : b < a := by dsimp [b]; linarith
    have hbm : 1 - m < b := by dsimp [b]; linarith [le_max_right (0 : ℝ) (1-m)]
    have hsub : {x | a ≤ _root_.GD.N0236.N0745.d030146 A x} ⊆ A b := by
      intro x hx
      exact _root_.GD.N0236.N0745.d030152 hA ⟨hb0, hba.trans_le ha1⟩ (hba.trans_le hx)
    have hle := measureReal_mono (μ := μ) hsub
    rw [hcal b ⟨hb0, hba.trans_le ha1⟩] at hle
    change m ≤ 1 - b at hle
    linarith
  · by_contra h
    have hm : m < 1 - a := lt_of_not_ge h
    have hm0 : 0 ≤ m := measureReal_nonneg
    let b := (a + min 1 (1 - m)) / 2
    have hmin : a < min 1 (1 - m) := lt_min (by linarith) (by linarith)
    have hab : a < b := by dsimp [b]; linarith
    have hb1 : b < 1 := by dsimp [b]; linarith [min_le_left (1 : ℝ) (1-m)]
    have hbm : b < 1 - m := by dsimp [b]; linarith [min_le_right (1 : ℝ) (1-m)]
    have hsub : A b ⊆ {x | a ≤ _root_.GD.N0236.N0745.d030146 A x} := by
      intro x hx
      exact hab.le.trans (_root_.GD.N0236.N0745.d030153 hA ⟨ha0.trans hab, hb1⟩ hx)
    have hle := measureReal_mono (μ := μ) hsub
    rw [hcal b ⟨ha0.trans hab, hb1⟩] at hle
    change 1 - b ≤ m at hle
    linarith

theorem d030156
    [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {A : ℝ → Set X} (hA : _root_.GD.N0236.N0745.d030147 A)
    (hAm : ∀ q : ℚ, MeasurableSet (A q))
    (hcal : ∀ a ∈ Ioo (0 : ℝ) 1, μ.real (A a) = 1 - a) :
    μ.map (_root_.GD.N0236.N0745.d030146 A) = volume.restrict (Icc (0 : ℝ) 1) := by
  have hm := _root_.GD.N0236.N0745.d030151 A hAm
  apply Measure.ext_of_Ici
  intro a
  rw [Measure.map_apply hm measurableSet_Ici, Measure.restrict_apply measurableSet_Ici]
  by_cases ha0 : a ≤ 0
  · have hs : _root_.GD.N0236.N0745.d030146 A ⁻¹' Ici a = univ := by
      ext x
      simp only [mem_preimage, mem_Ici, mem_univ, iff_true]
      exact ha0.trans (_root_.GD.N0236.N0745.d030150 A x).1
    rw [hs, measure_univ]
    have hi : Ici a ∩ Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
      ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc]; constructor
      · exact fun h => h.2
      · exact fun h => ⟨ha0.trans h.1, h⟩
    rw [hi, Real.volume_Icc]; norm_num
  · have ha0' : 0 < a := lt_of_not_ge ha0
    by_cases ha1 : a ≤ 1
    · have hs : Ici a ∩ Icc (0 : ℝ) 1 = Icc a 1 := by
        ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc]; constructor
        · exact fun h => ⟨h.1, h.2.2⟩
        · exact fun h => ⟨h.1, ha0'.le.trans h.1, h.2⟩
      rw [hs, Real.volume_Icc]
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) ENNReal.ofReal_ne_top).mp
      rw [ENNReal.toReal_ofReal (sub_nonneg.mpr ha1)]
      exact _root_.GD.N0236.N0745.d030155 μ hA hcal ha0' ha1
    · have h1a : 1 < a := lt_of_not_ge ha1
      have hs : _root_.GD.N0236.N0745.d030146 A ⁻¹' Ici a = ∅ := by
        ext x; simp only [mem_preimage, mem_Ici, mem_empty_iff_false, iff_false]
        exact not_le.mpr ((_root_.GD.N0236.N0745.d030150 A x).2.trans_lt h1a)
      have hi : Ici a ∩ Icc (0 : ℝ) 1 = ∅ := by
        ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc, mem_empty_iff_false, iff_false]
        intro h; linarith [h.1, h.2.2]
      simp [hs, hi]

#print axioms _root_.GD.N0236.N0745.d030154
#print axioms _root_.GD.N0236.N0745.d030155
#print axioms _root_.GD.N0236.N0745.d030156

end GD.N0236.N0745
