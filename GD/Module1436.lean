import GD.Module1435
import GD.Module0812

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace GD.N0066.N0307
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0963 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0232.N0719.N0965 _root_.GD.N0232.N0719.N0966
open _root_.GD.N0230.N0602

local instance (k : ℕ) : DecidableEq (_root_.GD.N0232.N0719.N0859.d010809 k) := Classical.decEq _

def d022837 (k : ℕ) (c : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ)
    (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ) : ℝ :=
  c (_root_.GD.N0232.N0719.N0859.d010810 k) + ∑ θ ∈ F, w θ * c θ


theorem d022838
    (k : ℕ) (sizes : Fin k → ℕ) (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ)
    (hw : ∀ θ ∈ F, 0 ≤ w θ) (p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hp : ∀ θ ∈ F, _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p ≠ ⊤) :
    _root_.GD.N0232.N0719.N0966.d012351 k sizes F w ≤ _root_.GD.N0066.N0307.d022837 k (fun θ => (_root_.GD.N0232.N0719.N0859.d010821 k sizes θ p).toReal) F w := by
  have h := _root_.GD.N0232.N0719.N0965.d012295
    (k := k) (sizes := sizes) (fun θ : F => θ.val) (fun θ => w θ.val)
    (fun θ => hw θ.val θ.property) p (fun θ => hp θ.val θ.property)
  have hnonneg : 0 ≤ ∫ ω,
      _root_.GD.N0232.N0719.N0965.d012275 (fun θ : F => θ.val) (fun θ => w θ.val) ω *
        (p ω - _root_.GD.N0232.N0719.N0965.d012276 (fun θ : F => θ.val)
          (fun θ => w θ.val) ω) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes := by
    apply integral_nonneg
    intro ω
    apply mul_nonneg _ (sq_nonneg _)
    exact (_root_.GD.N0230.N0617.d000169
      (fun θ : F => w θ.val) (_root_.GD.N0232.N0719.N0965.d012273 (fun θ : F => θ.val))
      (fun θ => hw θ.val θ.property) (_root_.GD.N0232.N0719.N0965.d012279 _) ω).le
  simp only [_root_.GD.N0232.N0719.N0965.d012291] at h
  rw [Finset.sum_coe_sort F (fun θ => w θ * (_root_.GD.N0232.N0719.N0859.d010821 k sizes θ p).toReal)] at h
  change _ = _ + _root_.GD.N0232.N0719.N0966.d012351 k sizes F w at h
  have href : (_root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) p).toReal = ‖p‖ ^ 2 := by
    simpa only [zero_sub, norm_neg, ENNReal.toReal_ofReal (sq_nonneg ‖p‖)] using
      congrArg ENNReal.toReal (_root_.GD.N0232.N0719.N0859.d010829 k sizes p)
  change _root_.GD.N0232.N0719.N0966.d012351 k sizes F w ≤
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) p).toReal + ∑ θ ∈ F, w θ * (_root_.GD.N0232.N0719.N0859.d010821 k sizes θ p).toReal
  rw [href]
  linarith

theorem d022839 (k : ℕ) (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w a b : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ)
    (hw : ∀ θ ∈ F, 0 ≤ w θ)
    (hab : ∀ θ ∈ insert (_root_.GD.N0232.N0719.N0859.d010810 k) F, a θ ≤ b θ) :
    _root_.GD.N0066.N0307.d022837 k a F w ≤ _root_.GD.N0066.N0307.d022837 k b F w := by
  apply add_le_add (hab _ (Finset.mem_insert_self _ _))
  exact Finset.sum_le_sum fun θ hθ =>
    mul_le_mul_of_nonneg_left (hab θ (Finset.mem_insert_of_mem hθ)) (hw θ hθ)



theorem d022840
    (k : ℕ) (sizes : Fin k → ℕ) (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w c : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ)
    (hw : ∀ θ ∈ F, 0 ≤ w θ)
    (hc : ∀ θ ∈ insert (_root_.GD.N0232.N0719.N0859.d010810 k) F, 0 ≤ c θ)
    (hgap : _root_.GD.N0066.N0307.d022837 k c F w < _root_.GD.N0232.N0719.N0966.d012351 k sizes F w)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hf : Measurable f) :
    ∃ θ ∈ insert (_root_.GD.N0232.N0719.N0859.d010810 k) F, ENNReal.ofReal (c θ) < _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f := by
  by_contra hnot
  push Not at hnot
  have hfinite : _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) f ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hnot _ (Finset.mem_insert_self _ _))
  let hmem := _root_.GD.N0232.N0719.N0896.d011095 k sizes f hf hfinite
  let p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) := hmem.toLp f
  have hcap : ∀ θ ∈ insert (_root_.GD.N0232.N0719.N0859.d010810 k) F,
      _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p ≤ ENNReal.ofReal (c θ) := by
    intro θ hθ
    rw [← _root_.GD.N0232.N0719.N0859.d010841 k sizes θ f hmem]
    exact hnot θ hθ
  have hbound := _root_.GD.N0066.N0307.d022838 k sizes F w hw p
    (fun θ hθ => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hcap θ (Finset.mem_insert_of_mem hθ)))
  have hmono : _root_.GD.N0066.N0307.d022837 k (fun θ => (_root_.GD.N0232.N0719.N0859.d010821 k sizes θ p).toReal) F w ≤
      _root_.GD.N0066.N0307.d022837 k c F w := by
    apply _root_.GD.N0066.N0307.d022839 k F w _ _ hw
    intro θ hθ
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hcap θ hθ)).trans_eq
      (ENNReal.toReal_ofReal (hc θ hθ))
  exact (not_le.mpr hgap) (hbound.trans hmono)




theorem d022841 (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    ∃ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (w : _root_.GD.N0232.N0719.N0859.d010809 k → ℝ),
      (∀ θ ∈ F, 0 ≤ w θ) ∧
      _root_.GD.N0232.N0719.N0966.d012370 k sizes F w < _root_.GD.N0232.N0719.N0966.d012351 k sizes F w := by
  have h := (_root_.GD.N0232.N0719.N0966.d012372 k sizes hk hn 1 (by norm_num)).mp
    (by simpa only [ENNReal.ofReal_one] using _root_.GD.N0066.d022835 sizes hk hn)
  simpa only [one_mul] using h



theorem d022842 (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    ∃ (F : Finset (_root_.GD.N0232.N0719.N0859.d010809 k)) (ε : ℝ), 0 < ε ∧
      ∀ f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ, Measurable f →
        ∃ θ ∈ insert (_root_.GD.N0232.N0719.N0859.d010810 k) F,
          ENNReal.ofReal ((1 + ε) * _root_.GD.N0232.N0719.N0963.d012141 k sizes θ) <
            _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f := by
  obtain ⟨F, w, hw, hgap⟩ := _root_.GD.N0066.N0307.d022841 k sizes hk hn
  let T := _root_.GD.N0232.N0719.N0966.d012370 k sizes F w
  have hT : 0 < T := by
    exact _root_.GD.N0232.N0719.N0966.d012357 k
      (_root_.GD.N0232.N0719.N0972.d012344 k sizes (by omega)
        (fun i => by have := hn i; omega)) F w hw
  let D := _root_.GD.N0232.N0719.N0966.d012351 k sizes F w - T
  have hD : 0 < D := sub_pos.mpr hgap
  let ε := D / (2 * T)
  have hε : 0 < ε := div_pos hD (by positivity)
  have hεT : ε * T = D / 2 := by
    dsimp only [ε]
    field_simp
  refine ⟨F, ε, hε, fun f hf => _root_.GD.N0066.N0307.d022840 k sizes F w
    (fun θ => (1 + ε) * _root_.GD.N0232.N0719.N0963.d012141 k sizes θ) hw
    (fun θ _ => mul_nonneg (by linarith) (_root_.GD.N0232.N0719.N0963.d012142 k sizes θ)) ?_ f hf⟩
  have hid : _root_.GD.N0066.N0307.d022837 k (fun θ => (1 + ε) * _root_.GD.N0232.N0719.N0963.d012141 k sizes θ) F w =
      (1 + ε) * T := by
    dsimp only [_root_.GD.N0066.N0307.d022837, T, _root_.GD.N0232.N0719.N0966.d012370]
    simp only [mul_add, Finset.mul_sum, mul_left_comm (1 + ε)]
  rw [hid, add_mul, one_mul, hεT]
  dsimp only [D]
  linarith

end
end GD.N0066.N0307

#print axioms _root_.GD.N0066.N0307.d022838
#print axioms _root_.GD.N0066.N0307.d022840
#print axioms _root_.GD.N0066.N0307.d022841
#print axioms _root_.GD.N0066.N0307.d022842
