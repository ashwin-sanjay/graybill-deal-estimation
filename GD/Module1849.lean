import GD.Module1848

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0022.N0256

noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1126 _root_.GD.N0232.N0720.N1125
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1220
open _root_.GD.N0034.N0289
open _root_.GD.N0046.N0305
open _root_.GD.N0024 _root_.GD.N0024.N0274

local instance : DecidableEq _root_.GD.N0232.N0720.N1080.d014168 := Classical.decEq _


theorem d030385
    (m n : ℕ) (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w : _root_.GD.N0232.N0720.N1080.d014168 → ℝ)
    (hw : ∀ θ ∈ F, 0 ≤ w θ) (p : _root_.GD.N0046.N0305.d030201 m n)
    (hp : ∀ θ ∈ F, _root_.GD.N0232.N0720.N1080.d014182 m n θ p ≠ ⊤) :
    _root_.GD.N0232.N0720.N1220.d017301 m n F w ≤ _root_.GD.N0024.N0274.d030344 (fun θ => (_root_.GD.N0232.N0720.N1080.d014182 m n θ p).toReal) F w := by
  have h := _root_.GD.N0232.N0720.N1125.d017255
    (m := m) (n := n) (fun θ : F => θ.val) (fun θ => w θ.val)
    (fun θ => hw θ.val θ.property) p (fun θ => hp θ.val θ.property)
  have hnonneg : 0 ≤ ∫ ω,
      _root_.GD.N0232.N0720.N1126.d016415 (fun θ : F => θ.val) (fun θ => w θ.val) ω *
        (p ω - _root_.GD.N0232.N0720.N1126.d016416 (fun θ : F => θ.val)
          (fun θ => w θ.val) ω) ^ 2 ∂_root_.GD.N0232.N0720.N1080.d014172 m n := by
    apply integral_nonneg
    intro ω
    apply mul_nonneg _ (sq_nonneg _)
    exact (_root_.GD.N0230.N0617.d000169
      (fun θ : F => w θ.val) (_root_.GD.N0232.N0720.N1126.d016413 (fun θ : F => θ.val))
      (fun θ => hw θ.val θ.property) (_root_.GD.N0232.N0720.N1126.d016419 _) ω).le
  simp only [_root_.GD.N0232.N0720.N1125.d017249] at h
  rw [Finset.sum_coe_sort F (fun θ => w θ * (_root_.GD.N0232.N0720.N1080.d014182 m n θ p).toReal)] at h
  change _ = _ + _root_.GD.N0232.N0720.N1220.d017301 m n F w at h
  have href : (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 p).toReal = ‖p‖ ^ 2 := by
    simpa only [zero_sub, norm_neg, ENNReal.toReal_ofReal (sq_nonneg ‖p‖)] using
      congrArg ENNReal.toReal (_root_.GD.N0232.N0720.N1080.d014190 m n p)
  change _root_.GD.N0232.N0720.N1220.d017301 m n F w ≤
    (_root_.GD.N0232.N0720.N1080.d014182 m n _root_.GD.N0232.N0720.N1080.d014169 p).toReal + ∑ θ ∈ F, w θ * (_root_.GD.N0232.N0720.N1080.d014182 m n θ p).toReal
  rw [href]
  linarith

theorem d030386 (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w a b : _root_.GD.N0232.N0720.N1080.d014168 → ℝ)
    (hw : ∀ θ ∈ F, 0 ≤ w θ)
    (hab : ∀ θ ∈ insert _root_.GD.N0232.N0720.N1080.d014169 F, a θ ≤ b θ) :
    _root_.GD.N0024.N0274.d030344 a F w ≤ _root_.GD.N0024.N0274.d030344 b F w := by
  apply add_le_add (hab _ (Finset.mem_insert_self _ _))
  exact Finset.sum_le_sum fun θ hθ =>
    mul_le_mul_of_nonneg_left (hab θ (Finset.mem_insert_of_mem hθ)) (hw θ hθ)



theorem d030387
    (m n : ℕ) (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (w c : _root_.GD.N0232.N0720.N1080.d014168 → ℝ)
    (hw : ∀ θ ∈ F, 0 ≤ w θ)
    (hc : ∀ θ ∈ insert _root_.GD.N0232.N0720.N1080.d014169 F, 0 ≤ c θ)
    (hgap : _root_.GD.N0024.N0274.d030344 c F w < _root_.GD.N0232.N0720.N1220.d017301 m n F w)
    (f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hf : Measurable f) :
    ∃ θ ∈ insert _root_.GD.N0232.N0720.N1080.d014169 F, ENNReal.ofReal (c θ) < _root_.GD.N0232.N0720.N1080.d014197 m n θ f := by
  by_contra hnot
  push Not at hnot
  have hfinite : _root_.GD.N0232.N0720.N1080.d014197 m n _root_.GD.N0232.N0720.N1080.d014169 f ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hnot _ (Finset.mem_insert_self _ _))
  let hmem := _root_.GD.N0232.N0720.N1215.d014285 m n f hf hfinite
  let p : _root_.GD.N0046.N0305.d030201 m n := hmem.toLp f
  have hcap : ∀ θ ∈ insert _root_.GD.N0232.N0720.N1080.d014169 F,
      _root_.GD.N0232.N0720.N1080.d014182 m n θ p ≤ ENNReal.ofReal (c θ) := by
    intro θ hθ
    rw [← _root_.GD.N0232.N0720.N1080.d014198 m n θ f hmem]
    exact hnot θ hθ
  have hbound := _root_.GD.N0022.N0256.d030385 m n F w hw p
    (fun θ hθ => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hcap θ (Finset.mem_insert_of_mem hθ)))
  have hmono : _root_.GD.N0024.N0274.d030344 (fun θ => (_root_.GD.N0232.N0720.N1080.d014182 m n θ p).toReal) F w ≤
      _root_.GD.N0024.N0274.d030344 c F w := by
    apply _root_.GD.N0022.N0256.d030386 F w _ _ hw
    intro θ hθ
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hcap θ hθ)).trans_eq
      (ENNReal.toReal_ofReal (hc θ hθ))
  exact (not_le.mpr hgap) (hbound.trans hmono)

theorem d030388 (m n : ℕ) (F : Finset _root_.GD.N0232.N0720.N1080.d014168)
    (w c : _root_.GD.N0232.N0720.N1080.d014168 → ℝ) (ε : ℝ) :
    _root_.GD.N0024.N0274.d030344 (fun θ => c θ + ε * _root_.GD.N0232.N0720.N1257.d015508 m n θ) F w =
      _root_.GD.N0024.N0274.d030344 c F w + ε * _root_.GD.N0232.N0720.N1220.d017307 m n F w := by
  simp only [_root_.GD.N0024.N0274.d030344, _root_.GD.N0232.N0720.N1220.d017307, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, mul_left_comm ε]
  ring



theorem d030389
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (c : _root_.GD.N0232.N0720.N1080.d014168 → ℝ)
    (hc : ∀ θ, 0 ≤ c θ)
    (hempty : ¬ ∃ p : _root_.GD.N0046.N0305.d030201 m n, ∀ θ, _root_.GD.N0232.N0720.N1080.d014182 m n θ p ≤ ENNReal.ofReal (c θ)) :
    ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (ε : ℝ), 0 < ε ∧
      ∀ f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable f →
        ∃ θ ∈ insert _root_.GD.N0232.N0720.N1080.d014169 F,
          ENNReal.ofReal (c θ + ε * _root_.GD.N0232.N0720.N1257.d015508 m n θ) < _root_.GD.N0232.N0720.N1080.d014197 m n θ f := by
  have htests := mt (_root_.GD.N0232.N0720.N1220.d017305 m n hm hn c hc).mpr hempty
  push Not at htests
  obtain ⟨F, w, hw, hgap⟩ := htests
  change _root_.GD.N0024.N0274.d030344 c F w < _root_.GD.N0232.N0720.N1220.d017301 m n F w at hgap
  let D := _root_.GD.N0232.N0720.N1220.d017301 m n F w - _root_.GD.N0024.N0274.d030344 c F w
  let T := _root_.GD.N0232.N0720.N1220.d017307 m n F w
  have hD : 0 < D := sub_pos.mpr hgap
  have hT : 0 < T := _root_.GD.N0232.N0720.N1220.d017308 m n hm F w hw
  let ε := D / (2 * T)
  have hε : 0 < ε := div_pos hD (by positivity)
  have hεT : ε * T = D / 2 := by
    dsimp only [ε]
    field_simp
  refine ⟨F, ε, hε, fun f hf => _root_.GD.N0022.N0256.d030387 m n F w
    (fun θ => c θ + ε * _root_.GD.N0232.N0720.N1257.d015508 m n θ) hw
    (fun θ _ => add_nonneg (hc θ) (mul_nonneg hε.le (_root_.GD.N0232.N0720.N1257.d015509 m n θ)))
    ?_ f hf⟩
  rw [_root_.GD.N0022.N0256.d030388]
  change _root_.GD.N0024.N0274.d030344 c F w + ε * T < _root_.GD.N0232.N0720.N1220.d017301 m n F w
  rw [hεT]
  dsimp only [D]
  linarith



theorem d030390
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hempty : _root_.GD.N0046.N0305.d030202 m n hm hn = ∅) :
    ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (ε : ℝ), 0 < ε ∧
      ∀ f : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable f →
        ∃ θ ∈ insert _root_.GD.N0232.N0720.N1080.d014169 F,
          ENNReal.ofReal (_root_.GD.N0034.N0289.d030220 m n hm hn θ + ε * _root_.GD.N0232.N0720.N1257.d015508 m n θ) <
            _root_.GD.N0232.N0720.N1080.d014197 m n θ f := by
  apply _root_.GD.N0022.N0256.d030389 m n hm hn _
    (_root_.GD.N0034.N0289.d030221 m n hm hn)
  rintro ⟨p, hp⟩
  have hmem := (_root_.GD.N0034.N0289.d030223 m n hm hn p).mp hp
  rw [hempty] at hmem
  exact hmem

theorem d030391 :
    ∃ (F : Finset _root_.GD.N0232.N0720.N1080.d014168) (ε : ℝ), 0 < ε ∧
      ∀ f : _root_.GD.N0232.N0720.N1080.d014170 6 6 → ℝ, Measurable f →
        ∃ θ ∈ insert _root_.GD.N0232.N0720.N1080.d014169 F,
          ENNReal.ofReal (_root_.GD.N0034.N0289.d030220 6 6 (by norm_num) (by norm_num) θ +
            ε * _root_.GD.N0232.N0720.N1257.d015508 6 6 θ) < _root_.GD.N0232.N0720.N1080.d014197 6 6 θ f :=
  _root_.GD.N0022.N0256.d030390 6 6 (by norm_num) (by norm_num)
    _root_.GD.N0024.N0268.d030374

end
end GD.N0022.N0256

#print axioms _root_.GD.N0022.N0256.d030385
#print axioms _root_.GD.N0022.N0256.d030386
#print axioms _root_.GD.N0022.N0256.d030387
#print axioms _root_.GD.N0022.N0256.d030388
#print axioms _root_.GD.N0022.N0256.d030389
#print axioms _root_.GD.N0022.N0256.d030390
#print axioms _root_.GD.N0022.N0256.d030391
