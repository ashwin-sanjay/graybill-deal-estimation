import GD.Module0348
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace GD.N0024.N0277

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

abbrev d007878 := Ioo (0 : ℝ) 1

def d007879 (t : _root_.GD.N0024.N0277.d007878) : ℝ := t.1 * (1 - t.1)

theorem d007880 (t : _root_.GD.N0024.N0277.d007878) : 0 < _root_.GD.N0024.N0277.d007879 t :=
  mul_pos t.2.1 (sub_pos.mpr t.2.2)

def d007881 (ν : Measure Ω) (g : Ω → ℝ) (t : ℝ) : ℝ :=
  ∫ z, (g z - t) ^ 2 ∂ν

def d007882 (Q : _root_.GD.N0024.N0277.d007878 → Measure Ω) (g : Ω → ℝ) (t : _root_.GD.N0024.N0277.d007878) : ℝ :=
  _root_.GD.N0024.N0277.d007881 (Q t) g t.1 / _root_.GD.N0024.N0277.d007879 t

def d007883 (E : Set Ω) (g : Ω → ℝ) (η : ℝ) : Ω → ℝ :=
  fun z => g z + η * E.indicator (fun _ => (1 : ℝ)) z

theorem d007884 (E : Set Ω) (hE : MeasurableSet E)
    (g : Ω → ℝ) (hg : Measurable g) (η : ℝ) : Measurable (_root_.GD.N0024.N0277.d007883 E g η) :=
  hg.add ((measurable_const.indicator hE).const_mul η)

omit [MeasurableSpace Ω] in
theorem d007885 (E : Set Ω) (g : Ω → ℝ) (d η : ℝ)
    (hg : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (hlow : ∀ z ∈ E, g z ≤ d / 2)
    (hd : d ≤ 1) (hη : 0 ≤ η) (hηd : η ≤ d / 2) :
    ∀ z, _root_.GD.N0024.N0277.d007883 E g η z ∈ Icc (0 : ℝ) 1 := by
  classical
  intro z
  by_cases hz : z ∈ E
  · simp only [_root_.GD.N0024.N0277.d007883, Set.indicator_of_mem hz, mul_one]
    have hgz := hg z
    have he := hlow z hz
    constructor <;> linarith [hgz.1, hgz.2]
  · simpa [_root_.GD.N0024.N0277.d007883, hz] using hg z

theorem d007886 (ν : Measure Ω) [IsFiniteMeasure ν]
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (t : _root_.GD.N0024.N0277.d007878) : Integrable (fun z => g z - t.1) ν := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    ((hg.sub measurable_const).aestronglyMeasurable)
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_le]
  have hz := hb z
  constructor <;> linarith [t.2.1, t.2.2, hz.1, hz.2]

theorem d007887 (ν : Measure Ω) [IsFiniteMeasure ν]
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (t : _root_.GD.N0024.N0277.d007878) : Integrable (fun z => (g z - t.1) ^ 2) ν := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (((hg.sub measurable_const).pow_const 2).aestronglyMeasurable)
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hz := hb z
  have h1 : -1 ≤ g z - t.1 := by linarith [t.2.2, hz.1]
  have h2 : g z - t.1 ≤ 1 := by linarith [t.2.1, hz.2]
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - (g z - t.1))
    (by linarith : 0 ≤ 1 + (g z - t.1))]

theorem d007888 (ν : Measure Ω) [IsFiniteMeasure ν]
    (E : Set Ω) (hE : MeasurableSet E)
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (t : _root_.GD.N0024.N0277.d007878) (a : ℝ) (ha : ∀ z ∈ E, g z - t.1 ≤ a) :
    (∫ z in E, g z - t.1 ∂ν) ≤ ν.real E * a := by
  have hi := setIntegral_mono_on (_root_.GD.N0024.N0277.d007886 ν g hg hb t).integrableOn
    (integrable_const a).integrableOn hE ha
  simpa only [integral_const, measureReal_def, Measure.restrict_apply_univ,
    smul_eq_mul] using hi

theorem d007889 (ν : Measure Ω) [IsFiniteMeasure ν]
    (E : Set Ω) (hE : MeasurableSet E)
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (t : _root_.GD.N0024.N0277.d007878) (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    _root_.GD.N0024.N0277.d007881 ν (_root_.GD.N0024.N0277.d007883 E g η) t.1 ≤ _root_.GD.N0024.N0277.d007881 ν g t.1 + 3 * η * ν.real E := by
  have hid := _root_.GD.N0024.N0267.d005162 ν E hE g t.1 η
    (_root_.GD.N0024.N0277.d007887 ν g hg hb t) (_root_.GD.N0024.N0277.d007886 ν g hg hb t).integrableOn
  have hi := _root_.GD.N0024.N0277.d007888 ν E hE g hg hb t 1
    (fun z _ => by linarith [(hb z).2, t.2.1])
  have hm : 0 ≤ ν.real E := ENNReal.toReal_nonneg
  have hlin := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2 * η)
  have hs : η ^ 2 ≤ η := by nlinarith
  have hquad := mul_le_mul_of_nonneg_right hs hm
  change _ ≤ (∫ z, (g z - t.1) ^ 2 ∂ν) + _
  change (∫ z, (g z + η * E.indicator (fun _ => (1 : ℝ)) z - t.1) ^ 2 ∂ν) ≤ _
  rw [hid]
  nlinarith

theorem d007890 (ν : Measure Ω) [IsFiniteMeasure ν]
    (E : Set Ω) (hE : MeasurableSet E)
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (t : _root_.GD.N0024.N0277.d007878) (d η : ℝ) (hη : 0 ≤ η) (hηd : η ≤ d / 2)
    (ht : d ≤ t.1) (hlow : ∀ z ∈ E, g z ≤ d / 2) :
    _root_.GD.N0024.N0277.d007881 ν (_root_.GD.N0024.N0277.d007883 E g η) t.1 ≤ _root_.GD.N0024.N0277.d007881 ν g t.1 - η * (d / 2) * ν.real E := by
  have hid := _root_.GD.N0024.N0267.d005162 ν E hE g t.1 η
    (_root_.GD.N0024.N0277.d007887 ν g hg hb t) (_root_.GD.N0024.N0277.d007886 ν g hg hb t).integrableOn
  have hi := _root_.GD.N0024.N0277.d007888 ν E hE g hg hb t (-d / 2)
    (fun z hz => by linarith [hlow z hz])
  have hm : 0 ≤ ν.real E := ENNReal.toReal_nonneg
  have hlin := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2 * η)
  have hs : η ^ 2 ≤ η * (d / 2) := by nlinarith
  have hquad := mul_le_mul_of_nonneg_right hs hm
  change _ ≤ (∫ z, (g z - t.1) ^ 2 ∂ν) - _
  change (∫ z, (g z + η * E.indicator (fun _ => (1 : ℝ)) z - t.1) ^ 2 ∂ν) ≤ _
  rw [hid]
  nlinarith

theorem d007891
    (Q : _root_.GD.N0024.N0277.d007878 → Measure Ω) [∀ t, IsFiniteMeasure (Q t)]
    (E : Set Ω) (hE : MeasurableSet E)
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (t : _root_.GD.N0024.N0277.d007878) (η M : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hmass : (Q t).real E / _root_.GD.N0024.N0277.d007879 t ≤ M) :
    _root_.GD.N0024.N0277.d007882 Q (_root_.GD.N0024.N0277.d007883 E g η) t ≤ _root_.GD.N0024.N0277.d007882 Q g t + η * (3 * M) := by
  have hi := div_le_div_of_nonneg_right
    (_root_.GD.N0024.N0277.d007889 (Q t) E hE g hg hb t η hη hη1) (_root_.GD.N0024.N0277.d007880 t).le
  have hm := mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 3 * η)
  simp only [add_div, mul_div_assoc] at hi
  unfold _root_.GD.N0024.N0277.d007882
  nlinarith

theorem d007892
    (Q : _root_.GD.N0024.N0277.d007878 → Measure Ω) [∀ t, IsFiniteMeasure (Q t)]
    (E : Set Ω) (hE : MeasurableSet E)
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (t : _root_.GD.N0024.N0277.d007878) (d η k : ℝ) (hη : 0 ≤ η) (hηd : η ≤ d / 2)
    (ht : d ≤ t.1) (hlow : ∀ z ∈ E, g z ≤ d / 2)
    (hmass : k ≤ (Q t).real E / _root_.GD.N0024.N0277.d007879 t) :
    _root_.GD.N0024.N0277.d007882 Q (_root_.GD.N0024.N0277.d007883 E g η) t ≤ _root_.GD.N0024.N0277.d007882 Q g t - η * (d / 2 * k) := by
  have hi := div_le_div_of_nonneg_right
    (_root_.GD.N0024.N0277.d007890 (Q t) E hE g hg hb t d η hη hηd ht hlow) (_root_.GD.N0024.N0277.d007880 t).le
  have hd : 0 ≤ d / 2 := hη.trans hηd
  have hm := mul_le_mul_of_nonneg_left hmass (mul_nonneg hη hd)
  simp only [sub_div, mul_div_assoc] at hi
  unfold _root_.GD.N0024.N0277.d007882
  nlinarith

theorem d007893
    (Q : _root_.GD.N0024.N0277.d007878 → Measure Ω) [∀ t, IsProbabilityMeasure (Q t)]
    (μ : Measure Ω) (hQ : ∀ t, Q t ≪ μ)
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (d V : ℝ) (hd : 0 < d)
    (hcap : ∀ t, _root_.GD.N0024.N0277.d007882 Q g t ≤ V)
    (hfloor : ∀ᵐ z ∂μ, d ≤ g z) : False := by
  let s := min (d / 2) (min (d ^ 2 / (8 * (|V| + 1))) (1 / 2))
  have hs : 0 < s := by dsimp [s]; positivity
  have hsHalf : s ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hsD : s ≤ d / 2 := min_le_left _ _
  have hsBound : s ≤ d ^ 2 / (8 * (|V| + 1)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  let t : _root_.GD.N0024.N0277.d007878 := ⟨s, hs, by linarith⟩
  have hpoint : ∀ᵐ z ∂Q t, d ^ 2 / 4 ≤ (g z - t.1) ^ 2 := by
    filter_upwards [(hQ t).ae_le hfloor] with z hz
    change _ ≤ (g z - s) ^ 2
    nlinarith [sq_nonneg (g z - s - d / 2)]
  have hlower := integral_mono_ae (integrable_const (d ^ 2 / 4))
    (_root_.GD.N0024.N0277.d007887 (Q t) g hg hb t) hpoint
  have hlower' : d ^ 2 / 4 ≤ _root_.GD.N0024.N0277.d007881 (Q t) g t.1 := by
    simpa only [_root_.GD.N0024.N0277.d007881, integral_const, probReal_univ, one_smul] using hlower
  have hupper : _root_.GD.N0024.N0277.d007881 (Q t) g t.1 ≤ V * _root_.GD.N0024.N0277.d007879 t :=
    (div_le_iff₀ (_root_.GD.N0024.N0277.d007880 t)).mp (hcap t)
  have hweight : V * _root_.GD.N0024.N0277.d007879 t ≤ |V| * s := by
    calc
      _ ≤ |V| * _root_.GD.N0024.N0277.d007879 t := mul_le_mul_of_nonneg_right (le_abs_self V) (_root_.GD.N0024.N0277.d007880 t).le
      _ ≤ |V| * s := by
        unfold _root_.GD.N0024.N0277.d007879
        change |V| * (s * (1 - s)) ≤ |V| * s
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg V)
        nlinarith
  have hden : 0 < 8 * (|V| + 1) := by positivity
  have hsmall := (le_div_iff₀ hden).mp hsBound
  have hstrict : |V| * s < d ^ 2 / 4 := by
    nlinarith [abs_nonneg V, sq_pos_of_pos hd]
  exact (not_lt.mpr (hlower'.trans (hupper.trans hweight))) hstrict

theorem d007894
    (Q : _root_.GD.N0024.N0277.d007878 → Measure Ω) [∀ t, IsProbabilityMeasure (Q t)]
    (μ : Measure Ω) (hQ : ∀ t, Q t ≪ μ)
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (d V : ℝ) (hd : 0 < d)
    (hcap : ∀ t, _root_.GD.N0024.N0277.d007882 Q g t ≤ V) :
    0 < μ {z | g z < d} := by
  by_contra hnot
  have hzero : μ {z | g z < d} = 0 := le_antisymm (not_lt.mp hnot) bot_le
  have hfloor : ∀ᵐ z ∂μ, d ≤ g z := by
    rw [ae_iff]
    simpa only [not_le] using hzero
  exact _root_.GD.N0024.N0277.d007893 Q μ hQ g hg hb d V hd hcap hfloor

theorem d007895
    (μ : Measure Ω) (g : Ω → ℝ) (d : ℝ) (K : ℕ → Set Ω)
    (hcover : ∀ z, ∃ n, z ∈ K n) (hpos : 0 < μ {z | g z < d}) :
    ∃ n, 0 < μ ({z | g z < d} ∩ K n) := by
  by_contra hnot
  push Not at hnot
  have hzero : ∀ n, μ ({z | g z < d} ∩ K n) = 0 :=
    fun n => le_antisymm (hnot n) bot_le
  have hcover' : {z | g z < d} = ⋃ n, ({z | g z < d} ∩ K n) := by
    ext z
    simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := hcover z
      exact ⟨n, hz, hn⟩
    · rintro ⟨n, hz, _⟩
      exact hz
  rw [hcover', measure_iUnion_null hzero] at hpos
  exact lt_irrefl _ hpos

theorem d007896
    (Q : _root_.GD.N0024.N0277.d007878 → Measure Ω) [∀ t, IsFiniteMeasure (Q t)]
    (E : Set Ω) (hE : MeasurableSet E)
    (g : Ω → ℝ) (hg : Measurable g) (hb : ∀ z, g z ∈ Icc (0 : ℝ) 1)
    (d V h k M : ℝ) (hd : 0 < d) (hd1 : d ≤ 1)
    (hh : 0 < h) (hk : 0 < k) (hM : 0 ≤ M)
    (hlow : ∀ z ∈ E, g z ≤ d / 2)
    (hcap : ∀ t, _root_.GD.N0024.N0277.d007882 Q g t ≤ V)
    (hslack : ∀ t : _root_.GD.N0024.N0277.d007878, t.1 < d ∨ 1 - d < t.1 → _root_.GD.N0024.N0277.d007882 Q g t ≤ V - h)
    (hmassUpper : ∀ t, (Q t).real E / _root_.GD.N0024.N0277.d007879 t ≤ M)
    (hmassLower : ∀ t : _root_.GD.N0024.N0277.d007878, d ≤ t.1 → t.1 ≤ 1 - d →
      k ≤ (Q t).real E / _root_.GD.N0024.N0277.d007879 t)
    (hminimax : ∀ f : Ω → ℝ, Measurable f → (∀ z, f z ∈ Icc (0 : ℝ) 1) →
      ∀ ε : ℝ, 0 < ε → ∃ t, V - ε < _root_.GD.N0024.N0277.d007882 Q f t) : False := by
  classical
  obtain ⟨η₀, hη₀, hη₀1, hstep₀⟩ :=
    _root_.GD.N0024.N0267.d005156 h (3 * M) hh (by positivity)
  let η := min η₀ (d / 2)
  have hη : 0 < η := lt_min hη₀ (by positivity)
  have hη1 : η ≤ 1 := (min_le_left _ _).trans hη₀1
  have hηd : η ≤ d / 2 := min_le_right _ _
  have hstep : η * (3 * M) < h :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans_lt hstep₀
  let L : Set _root_.GD.N0024.N0277.d007878 := {t | t.1 < d ∨ 1 - d < t.1}
  refine _root_.GD.N0024.N0267.d005154
    L (_root_.GD.N0024.N0277.d007882 Q g) (_root_.GD.N0024.N0277.d007882 Q (_root_.GD.N0024.N0277.d007883 E g η)) V h (d / 2 * k) (3 * M) η
    hcap ?_ ?_ ?_ (by positivity) hη hstep ?_
  · intro t ht
    exact hslack t ht
  · intro t _
    exact _root_.GD.N0024.N0277.d007891 Q E hE g hg hb t η M hη.le hη1 (hmassUpper t)
  · intro t ht
    have htd : d ≤ t.1 := by
      by_contra hnot
      exact ht (Or.inl (lt_of_not_ge hnot))
    have ht1 : t.1 ≤ 1 - d := by
      by_contra hnot
      exact ht (Or.inr (lt_of_not_ge hnot))
    exact _root_.GD.N0024.N0277.d007892 Q E hE g hg hb t d η k hη.le hηd htd hlow
      (hmassLower t htd ht1)
  · exact hminimax (_root_.GD.N0024.N0277.d007883 E g η) (_root_.GD.N0024.N0277.d007884 E hE g hg η)
      (_root_.GD.N0024.N0277.d007885 E g d η hb hlow hd1 hη.le hηd)

#print axioms _root_.GD.N0024.N0277.d007880
#print axioms _root_.GD.N0024.N0277.d007884
#print axioms _root_.GD.N0024.N0277.d007885
#print axioms _root_.GD.N0024.N0277.d007886
#print axioms _root_.GD.N0024.N0277.d007887
#print axioms _root_.GD.N0024.N0277.d007888
#print axioms _root_.GD.N0024.N0277.d007889
#print axioms _root_.GD.N0024.N0277.d007890
#print axioms _root_.GD.N0024.N0277.d007891
#print axioms _root_.GD.N0024.N0277.d007892
#print axioms _root_.GD.N0024.N0277.d007893
#print axioms _root_.GD.N0024.N0277.d007894
#print axioms _root_.GD.N0024.N0277.d007895
#print axioms _root_.GD.N0024.N0277.d007896

end
end GD.N0024.N0277
