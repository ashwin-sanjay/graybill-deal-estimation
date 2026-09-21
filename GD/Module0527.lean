import GD.Module0525

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
open MeasureTheory Set

namespace GD.N0065
noncomputable section

open _root_.GD.N0024 _root_.GD.N0024.N0277

variable {Ω : Type*} [MeasurableSpace Ω]

def d007898 (g f : Ω → ℝ) (a : ℝ) : Ω → ℝ := fun z => (1 - a) * g z + a * f z

omit [MeasurableSpace Ω] in
theorem d007899 (g f : Ω → ℝ) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hg : ∀ z, g z ∈ Icc (0 : ℝ) 1) (hf : ∀ z, f z ∈ Icc (0 : ℝ) 1) :
    ∀ z, _root_.GD.N0065.d007898 g f a z ∈ Icc (0 : ℝ) 1 := by
  intro z
  have hga := mul_le_mul_of_nonneg_left (hg z).2 (sub_nonneg.mpr ha.2)
  have hfa := mul_le_mul_of_nonneg_left (hf z).2 ha.1
  dsimp [_root_.GD.N0065.d007898]
  constructor
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ha.2) (hg z).1)
      (mul_nonneg ha.1 (hf z).1)
  · nlinarith

theorem d007900 (Q : _root_.GD.N0024.N0277.d007878 → Measure Ω) [∀ t, IsFiniteMeasure (Q t)]
    (g f : Ω → ℝ) (hg : Measurable g) (hf : Measurable f)
    (hgb : ∀ z, g z ∈ Icc (0 : ℝ) 1) (hfb : ∀ z, f z ∈ Icc (0 : ℝ) 1)
    (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (t : _root_.GD.N0024.N0277.d007878) :
    _root_.GD.N0024.N0277.d007882 Q (_root_.GD.N0065.d007898 g f a) t ≤
      (1 - a) * _root_.GD.N0024.N0277.d007882 Q g t + a * _root_.GD.N0024.N0277.d007882 Q f t := by
  have hm : Measurable (_root_.GD.N0065.d007898 g f a) := by unfold _root_.GD.N0065.d007898; fun_prop
  have hi := integral_mono
    (_root_.GD.N0024.N0277.d007887 (Q t) (_root_.GD.N0065.d007898 g f a) hm (_root_.GD.N0065.d007899 g f a ha hgb hfb) t)
    (((_root_.GD.N0024.N0277.d007887 (Q t) g hg hgb t).const_mul (1 - a)).add
      ((_root_.GD.N0024.N0277.d007887 (Q t) f hf hfb t).const_mul a))
    (fun z => show (_root_.GD.N0065.d007898 g f a z - t.1) ^ 2 ≤
      (1 - a) * (g z - t.1) ^ 2 + a * (f z - t.1) ^ 2 by
        dsimp [_root_.GD.N0065.d007898]
        nlinarith [mul_nonneg (mul_nonneg ha.1 (sub_nonneg.mpr ha.2))
          (sq_nonneg (g z - f z))])
  change (∫ z, (_root_.GD.N0065.d007898 g f a z - t.1) ^ 2 ∂Q t) ≤
    ∫ z, (1 - a) * (g z - t.1) ^ 2 + a * (f z - t.1) ^ 2 ∂Q t at hi
  rw [integral_add ((_root_.GD.N0024.N0277.d007887 (Q t) g hg hgb t).const_mul (1 - a))
    ((_root_.GD.N0024.N0277.d007887 (Q t) f hf hfb t).const_mul a), integral_const_mul,
    integral_const_mul] at hi
  have hh := div_le_div_of_nonneg_right hi (_root_.GD.N0024.N0277.d007880 t).le
  simpa only [_root_.GD.N0024.N0277.d007882, _root_.GD.N0024.N0277.d007881, add_div, mul_div_assoc] using hh



theorem d007901
    (Q : _root_.GD.N0024.N0277.d007878 → Measure Ω) [∀ t, IsFiniteMeasure (Q t)]
    (E : Set Ω) (hE : MeasurableSet E)
    (g f : Ω → ℝ) (hg : Measurable g) (hf : Measurable f)
    (hgb : ∀ z, g z ∈ Icc (0 : ℝ) 1) (hfb : ∀ z, f z ∈ Icc (0 : ℝ) 1)
    (d V h H k M C : ℝ) (hd : 0 < d) (hd1 : d ≤ 1)
    (hh : 0 < h) (hH : 0 < H) (hk : 0 < k) (hM : 0 ≤ M)
    (hlow : ∀ z ∈ E, g z ≤ d / 2)
    (hcap : ∀ t, _root_.GD.N0024.N0277.d007882 Q g t ≤ V)
    (hleft : ∀ t : _root_.GD.N0024.N0277.d007878, t.1 < d → _root_.GD.N0024.N0277.d007882 Q g t ≤ V - h)
    (hfcap : ∀ t, _root_.GD.N0024.N0277.d007882 Q f t ≤ C)
    (hfright : ∀ t : _root_.GD.N0024.N0277.d007878, 1 - d < t.1 → _root_.GD.N0024.N0277.d007882 Q f t ≤ V - H)
    (hmassUpper : ∀ t, (Q t).real E / _root_.GD.N0024.N0277.d007879 t ≤ M)
    (hmassLower : ∀ t : _root_.GD.N0024.N0277.d007878, d ≤ t.1 → t.1 ≤ 1 - d →
      k ≤ (Q t).real E / _root_.GD.N0024.N0277.d007879 t)
    (hminimax : ∀ u : Ω → ℝ, Measurable u → (∀ z, u z ∈ Icc (0 : ℝ) 1) →
      ∀ ε : ℝ, 0 < ε → ∃ t, V - ε < _root_.GD.N0024.N0277.d007882 Q u t) : False := by
  obtain ⟨η₀, hη₀, hη₀1, hstep₀⟩ :=
    _root_.GD.N0024.N0267.d005156 h (3 * M) hh (by positivity)
  let η := min η₀ (d / 2)
  have hη : 0 < η := lt_min hη₀ (by positivity)
  have hη1 : η ≤ 1 := (min_le_left _ _).trans hη₀1
  have hηd : η ≤ d / 2 := min_le_right _ _
  have hstep : η * (3 * M) < h :=
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans_lt hstep₀
  let G := _root_.GD.N0024.N0277.d007883 E g η
  have hG : Measurable G := _root_.GD.N0024.N0277.d007884 E hE g hg η
  have hGb : ∀ z, G z ∈ Icc (0 : ℝ) 1 :=
    _root_.GD.N0024.N0277.d007885 E g d η hgb hlow hd1 hη.le hηd
  let e := min (h - η * (3 * M)) (η * (d / 2 * k))
  have he : 0 < e := lt_min (sub_pos.mpr hstep) (by positivity)
  have hGleft : ∀ t : _root_.GD.N0024.N0277.d007878, t.1 ≤ 1 - d → _root_.GD.N0024.N0277.d007882 Q G t ≤ V - e := by
    intro t ht
    by_cases htd : t.1 < d
    · have hu := _root_.GD.N0024.N0277.d007891 Q E hE g hg hgb t η M hη.le hη1 (hmassUpper t)
      have hs := hleft t htd
      have heh : e ≤ h - η * (3 * M) := min_le_left _ _
      dsimp only [G]
      linarith
    · have hu := _root_.GD.N0024.N0277.d007892 Q E hE g hg hgb t d η k hη.le hηd
        (le_of_not_gt htd) hlow (hmassLower t (le_of_not_gt htd) ht)
      have hes : e ≤ η * (d / 2 * k) := min_le_right _ _
      have hc := hcap t
      dsimp only [G]
      linarith
  have hGcap : ∀ t, _root_.GD.N0024.N0277.d007882 Q G t ≤ V := by
    intro t
    by_cases ht : t.1 < d
    · have hu := _root_.GD.N0024.N0277.d007891 Q E hE g hg hgb t η M hη.le hη1 (hmassUpper t)
      have hs := hleft t ht
      dsimp only [G]
      linarith
    · have hm0 : 0 ≤ (Q t).real E / _root_.GD.N0024.N0277.d007879 t :=
        div_nonneg ENNReal.toReal_nonneg (_root_.GD.N0024.N0277.d007880 t).le
      have hu := _root_.GD.N0024.N0277.d007892 Q E hE g hg hgb t d η 0 hη.le hηd
        (le_of_not_gt ht) hlow hm0
      simp only [mul_zero, sub_zero] at hu
      exact hu.trans (hcap t)
  let A := |C| + |V| + e
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨a, ha, ha1, hasmall⟩ := _root_.GD.N0024.N0267.d005156 e A he hA
  let ε := min (e - a * A) (a * H)
  have hε : 0 < ε := lt_min (sub_pos.mpr hasmall) (mul_pos ha hH)
  have hmix : Measurable (_root_.GD.N0065.d007898 G f a) := by unfold _root_.GD.N0065.d007898; fun_prop
  have hmixb := _root_.GD.N0065.d007899 G f a ⟨ha.le, ha1⟩ hGb hfb
  obtain ⟨t, ht⟩ := hminimax (_root_.GD.N0065.d007898 G f a) hmix hmixb ε hε
  have hu := _root_.GD.N0065.d007900 Q G f hG hf hGb hfb a ⟨ha.le, ha1⟩ t
  have hbound : _root_.GD.N0024.N0277.d007882 Q (_root_.GD.N0065.d007898 G f a) t ≤ V - ε := by
    by_cases htd : t.1 ≤ 1 - d
    · have h1 := mul_le_mul_of_nonneg_left (hGleft t htd) (sub_nonneg.mpr ha1)
      have h2 := mul_le_mul_of_nonneg_left (hfcap t) ha.le
      have h3 : a * (C - V + e) ≤ a * A :=
        mul_le_mul_of_nonneg_left (by dsimp [A]; linarith [le_abs_self C, neg_le_abs V]) ha.le
      have hep : ε ≤ e - a * A := min_le_left _ _
      nlinarith
    · have h1 := mul_le_mul_of_nonneg_left (hGcap t) (sub_nonneg.mpr ha1)
      have h2 := mul_le_mul_of_nonneg_left (hfright t (lt_of_not_ge htd)) ha.le
      have hep : ε ≤ a * H := min_le_right _ _
      nlinarith
  exact (not_lt.mpr hbound) ht

end
end GD.N0065

#print axioms _root_.GD.N0065.d007899
#print axioms _root_.GD.N0065.d007900
#print axioms _root_.GD.N0065.d007901
