import GD.Module1823
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace GD.N0236.N0745

variable {S : Type*}

noncomputable def d030164 (a : ℝ) (n : ℕ) : ℝ := a * (1 - (1 / 2 : ℝ) ^ (n + 1))

theorem d030165 (a : ℝ) (ha : 0 < a) (n : ℕ) :
    _root_.GD.N0236.N0745.d030164 a n ∈ Ioo (0 : ℝ) a := by
  have hp : 0 < (1 / 2 : ℝ) ^ (n + 1) := by positivity
  have hp1 : (1 / 2 : ℝ) ^ (n + 1) < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  unfold _root_.GD.N0236.N0745.d030164
  constructor
  · positivity
  · nlinarith

theorem d030166 (a : ℝ) : Tendsto (_root_.GD.N0236.N0745.d030164 a) atTop (𝓝 a) := by
  change Tendsto (fun n : ℕ => a * (1 - (1 / 2 : ℝ) ^ (n + 1))) atTop (𝓝 a)
  have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).comp (tendsto_add_atTop_nat 1)
  simpa only [sub_zero, mul_one] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hp).const_mul a

def d030167 (L U : ℝ × S → ℝ) (a : ℝ) : Set (S × ℝ) :=
  {x | x.2 ∈ Icc (L (a, x.1)) (U (a, x.1))}

noncomputable def d030168 (L : ℝ × S → ℝ) (z : ℝ × S) : ℝ :=
  ⨆ n : ℕ, L (_root_.GD.N0236.N0745.d030164 z.1 n, z.2)

noncomputable def d030169 (U : ℝ × S → ℝ) (z : ℝ × S) : ℝ :=
  ⨅ n : ℕ, U (_root_.GD.N0236.N0745.d030164 z.1 n, z.2)

theorem d030170 [MeasurableSpace S]
    {L : ℝ × S → ℝ} (hL : Measurable L) : Measurable (_root_.GD.N0236.N0745.d030168 L) := by
  apply Measurable.iSup
  intro n
  exact hL.comp ((measurable_fst.mul_const _).prodMk measurable_snd)

theorem d030171 [MeasurableSpace S]
    {U : ℝ × S → ℝ} (hU : Measurable U) : Measurable (_root_.GD.N0236.N0745.d030169 U) := by
  apply Measurable.iInf
  intro n
  exact hU.comp ((measurable_fst.mul_const _).prodMk measurable_snd)

theorem d030172 [MeasurableSpace S]
    {L U : ℝ × S → ℝ} (hL : Measurable L) (hU : Measurable U) (a : ℝ) :
    MeasurableSet (_root_.GD.N0236.N0745.d030167 L U a) := by
  exact (measurableSet_le (hL.comp (measurable_const.prodMk measurable_fst))
    measurable_snd).inter
    (measurableSet_le measurable_snd (hU.comp (measurable_const.prodMk measurable_fst)))

theorem d030173 {L U : ℝ × S → ℝ}
    (hnest : _root_.GD.N0236.N0745.d030147 (_root_.GD.N0236.N0745.d030167 L U))
    (horder : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ s, L (a,s) ≤ U (a,s))
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (s : S) :
    (∀ n, L (_root_.GD.N0236.N0745.d030164 a n, s) ≤ L (a,s)) ∧
      (∀ n, L (a,s) ≤ U (_root_.GD.N0236.N0745.d030164 a n, s)) := by
  have hpoint : (s, L (a,s)) ∈ _root_.GD.N0236.N0745.d030167 L U a := ⟨le_rfl, horder a ha s⟩
  have hpointn : ∀ n, (s, L (a,s)) ∈ _root_.GD.N0236.N0745.d030167 L U (_root_.GD.N0236.N0745.d030164 a n) := by
    intro n
    have hn := _root_.GD.N0236.N0745.d030165 a ha.1 n
    exact hnest _ ⟨hn.1, hn.2.trans ha.2⟩ a ha hn.2.le hpoint
  exact ⟨fun n => (hpointn n).1, fun n => (hpointn n).2⟩

theorem d030174 {L U : ℝ × S → ℝ}
    (hnest : _root_.GD.N0236.N0745.d030147 (_root_.GD.N0236.N0745.d030167 L U))
    (horder : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ s, L (a,s) ≤ U (a,s))
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (s : S) :
    _root_.GD.N0236.N0745.d030168 L (a,s) ≤ _root_.GD.N0236.N0745.d030169 U (a,s) := by
  obtain ⟨hl, hu⟩ := _root_.GD.N0236.N0745.d030173 hnest horder ha s
  exact (ciSup_le hl).trans (le_ciInf hu)

theorem d030175 {L U : ℝ × S → ℝ}
    (hnest : _root_.GD.N0236.N0745.d030147 (_root_.GD.N0236.N0745.d030167 L U))
    (horder : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ s, L (a,s) ≤ U (a,s))
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (s : S) (d : ℝ) :
    d ∈ Icc (_root_.GD.N0236.N0745.d030168 L (a,s)) (_root_.GD.N0236.N0745.d030169 U (a,s)) ↔
      ∀ n, (s,d) ∈ _root_.GD.N0236.N0745.d030167 L U (_root_.GD.N0236.N0745.d030164 a n) := by
  obtain ⟨hl, hu⟩ := _root_.GD.N0236.N0745.d030173 hnest horder ha s
  have hLb : BddAbove (range (fun n => L (_root_.GD.N0236.N0745.d030164 a n,s))) :=
    ⟨L (a,s), by rintro _ ⟨n,rfl⟩; exact hl n⟩
  have hUb : BddBelow (range (fun n => U (_root_.GD.N0236.N0745.d030164 a n,s))) :=
    ⟨L (a,s), by rintro _ ⟨n,rfl⟩; exact hu n⟩
  constructor
  · intro hd n
    exact ⟨(le_ciSup hLb n).trans hd.1, hd.2.trans (ciInf_le hUb n)⟩
  · intro hd
    exact ⟨ciSup_le fun n => (hd n).1, le_ciInf fun n => (hd n).2⟩

theorem d030176 {L U : ℝ × S → ℝ}
    (hnest : _root_.GD.N0236.N0745.d030147 (_root_.GD.N0236.N0745.d030167 L U))
    (horder : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ s, L (a,s) ≤ U (a,s))
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (s : S) (d : ℝ) :
    a ≤ _root_.GD.N0236.N0745.d030146 (_root_.GD.N0236.N0745.d030167 L U) (s,d) ↔
      d ∈ Icc (_root_.GD.N0236.N0745.d030168 L (a,s)) (_root_.GD.N0236.N0745.d030169 U (a,s)) := by
  rw [_root_.GD.N0236.N0745.d030154 hnest ha, _root_.GD.N0236.N0745.d030175 hnest horder ha]
  constructor
  · intro hd n
    exact hd _ (_root_.GD.N0236.N0745.d030165 a ha.1 n)
  · intro hd b hb
    have he : ∀ᶠ n in atTop, b < _root_.GD.N0236.N0745.d030164 a n :=
      (tendsto_order.mp (_root_.GD.N0236.N0745.d030166 a)).1 b hb.2
    obtain ⟨n, hn⟩ := he.exists
    have hna := _root_.GD.N0236.N0745.d030165 a ha.1 n
    exact hnest b ⟨hb.1, hb.2.trans ha.2⟩ _
      ⟨hna.1, hna.2.trans ha.2⟩ hn.le (hd n)

theorem d030177
    [MeasurableSpace S] {L U : ℝ × S → ℝ}
    (hL : Measurable L) (hU : Measurable U)
    (hnest : _root_.GD.N0236.N0745.d030147 (_root_.GD.N0236.N0745.d030167 L U))
    (horder : ∀ a ∈ Ioo (0 : ℝ) 1, ∀ s, L (a,s) ≤ U (a,s)) :
    ∃ P : S × ℝ → ℝ, ∃ L' U' : ℝ × S → ℝ,
      Measurable P ∧ Measurable L' ∧ Measurable U' ∧
      (∀ x, P x ∈ Icc (0 : ℝ) 1) ∧
      (∀ a ∈ Ioo (0 : ℝ) 1, ∀ s, L' (a,s) ≤ U' (a,s)) ∧
      (∀ a ∈ Ioo (0 : ℝ) 1, ∀ s d,
        a ≤ P (s,d) ↔ d ∈ Icc (L' (a,s)) (U' (a,s))) ∧
      (∀ (μ : Measure (S × ℝ)), IsProbabilityMeasure μ →
        (∀ a ∈ Ioo (0 : ℝ) 1, μ.real (_root_.GD.N0236.N0745.d030167 L U a) = 1-a) →
        μ.map P = volume.restrict (Icc (0 : ℝ) 1)) := by
  refine ⟨_root_.GD.N0236.N0745.d030146 (_root_.GD.N0236.N0745.d030167 L U), _root_.GD.N0236.N0745.d030168 L, _root_.GD.N0236.N0745.d030169 U,
    _root_.GD.N0236.N0745.d030151 _ (fun q => _root_.GD.N0236.N0745.d030172 hL hU q),
    _root_.GD.N0236.N0745.d030170 hL, _root_.GD.N0236.N0745.d030171 hU,
    _root_.GD.N0236.N0745.d030150 _, ?_, ?_, ?_⟩
  · exact fun a ha s => _root_.GD.N0236.N0745.d030174 hnest horder ha s
  · exact fun a ha s d => _root_.GD.N0236.N0745.d030176 hnest horder ha s d
  · intro μ hμ hcal
    letI := hμ
    exact _root_.GD.N0236.N0745.d030156 μ hnest
      (fun q => _root_.GD.N0236.N0745.d030172 hL hU q) hcal

#print axioms _root_.GD.N0236.N0745.d030170
#print axioms _root_.GD.N0236.N0745.d030176
#print axioms _root_.GD.N0236.N0745.d030177

end GD.N0236.N0745
