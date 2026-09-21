import GD.Module0244
import GD.Module0806











open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0232.N0719.N0967

noncomputable section

open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0843
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0632
open _root_.GD.N0230.N0611

variable (k : ℕ) (sizes : Fin k → ℕ)

theorem d012298 (θ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (a • p + b • q) ≤
      ENNReal.ofReal a * _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p + ENNReal.ofReal b * _root_.GD.N0232.N0719.N0859.d010821 k sizes θ q :=
  _root_.GD.N0230.N0602.d000121 (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ)
    θ.location p q ha hb hab

theorem d012299 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (c : ℝ) :
    IsClosed {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) |
      _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p ≤ ENNReal.ofReal c} := by
  simpa [_root_.GD.N0230.N0602.d000118, _root_.GD.N0232.N0719.N0859.d010821] using
    _root_.GD.N0230.N0602.d000122 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      (fun _ : Unit ↦ _root_.GD.N0232.N0719.N0859.d010812 k sizes θ) (fun _ ↦ θ.location)
      (fun _ ↦ ENNReal.ofReal c) (fun _ ↦ _root_.GD.N0232.N0719.N0859.d010814 k sizes θ)

theorem d012300 (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) :
    (_root_.GD.N0230.N0632.d003532 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)).Nonempty := by
  refine ⟨_root_.GD.N0232.N0719.N0859.d010820 k sizes hk hsizes, fun θ ↦ ?_⟩
  rw [_root_.GD.N0232.N0719.N0859.d010824 k sizes hk hsizes θ]
  exact ENNReal.ofReal_ne_top

theorem d012301
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (γ : _root_.GD.N0232.N0719.N0843.d012215 k) (C : ℝ) (hC : 0 ≤ C) :
    (_root_.GD.N0232.N0719.N0843.d012216 k sizes γ C).Nonempty ↔
      ∀ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ),
        (∀ θ ∈ F, 0 ≤ w θ) → ∀ a : ℝ,
        (∀ p ∈ _root_.GD.N0230.N0632.d003532 (_root_.GD.N0232.N0719.N0859.d010821 k sizes),
          a ≤ ∑ θ ∈ F, w θ * (_root_.GD.N0232.N0719.N0859.d010821 k sizes θ p).toReal) →
          a ≤ ∑ θ ∈ F, w θ * (C * γ.value θ) := by
  exact _root_.GD.N0230.N0632.d003536
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes) (_root_.GD.N0232.N0719.N0967.d012298 k sizes) (_root_.GD.N0232.N0719.N0967.d012299 k sizes)
    (_root_.GD.N0232.N0719.N0859.d010810 k)
    (fun p ↦ by simpa only [zero_sub, norm_neg] using _root_.GD.N0232.N0719.N0859.d010829 k sizes p)
    (_root_.GD.N0232.N0719.N0967.d012300 k sizes hk hsizes)
    (fun θ ↦ C * γ.value θ) (fun θ ↦ mul_nonneg hC (γ.positive θ).le)

def d012302 (γ : _root_.GD.N0232.N0719.N0843.d012215 k)
    (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ) : ℝ :=
  ∑ θ ∈ F, w θ * γ.value θ

def d012303
    (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ) (a : ℝ) : Prop :=
  (∀ θ ∈ F, 0 ≤ w θ) ∧
    ∀ p ∈ _root_.GD.N0230.N0632.d003532 (_root_.GD.N0232.N0719.N0859.d010821 k sizes),
      a ≤ ∑ θ ∈ F, w θ * (_root_.GD.N0232.N0719.N0859.d010821 k sizes θ p).toReal

def d012304 (γ : _root_.GD.N0232.N0719.N0843.d012215 k) : Set ℝ≥0∞ :=
  {v | ∃ F w a, _root_.GD.N0232.N0719.N0967.d012303 k sizes F w a ∧
    0 < _root_.GD.N0232.N0719.N0967.d012302 k γ F w ∧
    v = ENNReal.ofReal (a / _root_.GD.N0232.N0719.N0967.d012302 k γ F w)}

def d012305 (γ : _root_.GD.N0232.N0719.N0843.d012215 k) : ℝ≥0∞ :=
  sSup (_root_.GD.N0232.N0719.N0967.d012304 k sizes γ)

theorem d012306 (γ : _root_.GD.N0232.N0719.N0843.d012215 k) (C : ℝ)
    (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ) :
    (∑ θ ∈ F, w θ * (C * γ.value θ)) = C * _root_.GD.N0232.N0719.N0967.d012302 k γ F w := by
  simp only [_root_.GD.N0232.N0719.N0967.d012302, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro θ hθ
  ring

theorem d012307
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (γ : _root_.GD.N0232.N0719.N0843.d012215 k) (C : ℝ) (hC : 0 ≤ C) :
    (_root_.GD.N0232.N0719.N0843.d012216 k sizes γ C).Nonempty ↔ _root_.GD.N0232.N0719.N0967.d012305 k sizes γ ≤ ENNReal.ofReal C := by
  classical
  constructor
  · intro hcap
    apply sSup_le
    rintro v ⟨F, w, a, ha, hB, rfl⟩
    apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ hB).mpr
    have h := (_root_.GD.N0232.N0719.N0967.d012301 k sizes hk hsizes γ C hC).mp
      hcap F w ha.1 a ha.2
    rwa [_root_.GD.N0232.N0719.N0967.d012306 k γ C F w] at h
  · intro hdual
    apply (_root_.GD.N0232.N0719.N0967.d012301 k sizes hk hsizes γ C hC).mpr
    intro F w hw a ha
    rw [_root_.GD.N0232.N0719.N0967.d012306 k γ C F w]
    have hB : 0 ≤ _root_.GD.N0232.N0719.N0967.d012302 k γ F w :=
      Finset.sum_nonneg fun θ hθ ↦ mul_nonneg (hw θ hθ) (γ.positive θ).le
    rcases eq_or_lt_of_le hB with hzero | hpos
    · have hweights : ∀ θ ∈ F, w θ = 0 := by
        intro θ hθ
        have hb : w θ * γ.value θ ≤ _root_.GD.N0232.N0719.N0967.d012302 k γ F w :=
          Finset.single_le_sum (fun η hη ↦ mul_nonneg (hw η hη) (γ.positive η).le) hθ
        have hz : _root_.GD.N0232.N0719.N0967.d012302 k γ F w = 0 := hzero.symm
        rw [hz] at hb
        have hle : w θ ≤ 0 := by
          by_contra h
          exact (not_lt_of_ge hb) (mul_pos (lt_of_not_ge h) (γ.positive θ))
        exact le_antisymm hle (hw θ hθ)
      obtain ⟨p, hp⟩ := _root_.GD.N0232.N0719.N0967.d012300 k sizes hk hsizes
      have hb := ha p hp
      have hs : (∑ θ ∈ F, w θ * (_root_.GD.N0232.N0719.N0859.d010821 k sizes θ p).toReal) = 0 := by
        apply Finset.sum_eq_zero
        intro θ hθ
        rw [hweights θ hθ, zero_mul]
      rw [hs] at hb
      simpa [hzero.symm] using hb
    · have hmem : ENNReal.ofReal (a / _root_.GD.N0232.N0719.N0967.d012302 k γ F w) ∈ _root_.GD.N0232.N0719.N0967.d012304 k sizes γ :=
        ⟨F, w, a, ⟨hw, ha⟩, hpos, rfl⟩
      have hr : a / _root_.GD.N0232.N0719.N0967.d012302 k γ F w ≤ C :=
        (ENNReal.ofReal_le_ofReal_iff hC).mp ((le_sSup hmem).trans hdual)
      exact (div_le_iff₀ hpos).mp hr



theorem d012308
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (γ : _root_.GD.N0232.N0719.N0843.d012215 k) :
    _root_.GD.N0232.N0719.N0844.d012248 k sizes γ = _root_.GD.N0232.N0719.N0967.d012305 k sizes γ := by
  apply le_antisymm
  · by_cases htop : _root_.GD.N0232.N0719.N0967.d012305 k sizes γ = ⊤
    · rw [htop]
      exact le_top
    · let C := (_root_.GD.N0232.N0719.N0967.d012305 k sizes γ).toReal
      have hC : 0 ≤ C := ENNReal.toReal_nonneg
      have hval : ENNReal.ofReal C = _root_.GD.N0232.N0719.N0967.d012305 k sizes γ :=
        ENNReal.ofReal_toReal htop
      obtain ⟨p, hp⟩ := (_root_.GD.N0232.N0719.N0967.d012307
        k sizes hk hsizes γ C hC).mpr hval.ge
      have hm := _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0844.d012246 k sizes γ)
        (show _root_.GD.N0232.N0719.N0896.d011088 k sizes p ∈ _root_.GD.N0232.N0719.N0962.d012184 k sizes from
          _root_.GD.N0232.N0719.N0896.d011089 k sizes p)
      refine hm.trans ?_
      rw [← hval]
      apply iSup_le
      intro θ
      apply (_root_.GD.N0232.N0719.N0844.d012250 k sizes γ
        (by omega) (fun i ↦ by have := hsizes i; omega) C hC θ _).mpr
      rw [_root_.GD.N0232.N0719.N0896.d011093]
      exact hp θ
  · by_cases htop : _root_.GD.N0232.N0719.N0844.d012248 k sizes γ = ⊤
    · rw [htop]
      exact le_top
    · have hcap := _root_.GD.N0232.N0719.N0844.d012261 k sizes γ hk hsizes htop
      have hb := (_root_.GD.N0232.N0719.N0967.d012307 k sizes hk hsizes γ
        (_root_.GD.N0232.N0719.N0844.d012248 k sizes γ).toReal ENNReal.toReal_nonneg).mp hcap
      rwa [ENNReal.ofReal_toReal htop] at hb

end

end GD.N0232.N0719.N0967

#print axioms _root_.GD.N0232.N0719.N0967.d012301
#print axioms _root_.GD.N0232.N0719.N0967.d012307
#print axioms _root_.GD.N0232.N0719.N0967.d012308
