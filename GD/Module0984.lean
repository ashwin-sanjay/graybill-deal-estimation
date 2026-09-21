import GD.Module0247
import GD.Module0980










set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0232.N0720.N1227

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0611
open _root_.GD.N0230.N0707

variable (m n : ℕ)



theorem d015587
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (C : ℝ) (hC : 0 ≤ C) :
    ¬ ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤ ENNReal.ofReal C := by
  intro hbound
  let θ₁ : _root_.GD.N0232.N0720.N1080.d014168 := { _root_.GD.N0232.N0720.N1080.d014169 with location := 1 }
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014171 m n θ₁) := by
    unfold _root_.GD.N0232.N0720.N1080.d014171
    infer_instance
  apply _root_.GD.N0230.N0707.d003550
    (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n)
    _root_.GD.N0232.N0720.N1080.d014168.location (_root_.GD.N0232.N0720.N1080.d014173 m n)
    (_root_.GD.N0232.N0720.N1080.d014169) θ₁ (by rfl) (by rfl) (by rfl)
  intro c hc
  let a := Real.sqrt (c / (C + 1))
  have hC1 : 0 < C + 1 := by linarith
  have ha : 0 < a := Real.sqrt_pos.mpr (div_pos hc hC1)
  have ha2 : a ^ 2 = c / (C + 1) := Real.sq_sqrt (div_nonneg hc.le hC1.le)
  have hac : a ^ 2 * C ≤ c := by
    have heq : a ^ 2 * (C + 1) = c := by
      rw [ha2]
      exact div_mul_cancel₀ c hC1.ne'
    nlinarith [sq_nonneg a]
  let g : _root_.GD.N0232.N0719.N0946.d009229 := ⟨0, Real.log a⟩
  have hga : g.d009239 = a := Real.exp_log ha
  let e := _root_.GD.N0232.N0720.N1214.d014261 m n g d
  have he : Measurable e := _root_.GD.N0232.N0720.N1214.d014262 m n g d hd
  have heb (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0232.N0720.N1080.d014197 m n θ e ≤ ENNReal.ofReal c := by
    let η := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ θ
    have hη : _root_.GD.N0232.N0720.N1215.d014272 g η = θ := _root_.GD.N0232.N0720.N1215.d014279 g θ
    rw [← hη, _root_.GD.N0232.N0720.N1215.d014284 m n g η d hd, hga]
    calc
      ENNReal.ofReal (a ^ 2) * _root_.GD.N0232.N0720.N1080.d014197 m n η d ≤
          ENNReal.ofReal (a ^ 2) * ENNReal.ofReal C := mul_le_mul' le_rfl (hbound η)
      _ = ENNReal.ofReal (a ^ 2 * C) := (ENNReal.ofReal_mul (sq_nonneg a)).symm
      _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal hac
  have heLp : MemLp e 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014285 m n e he
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (heb (_root_.GD.N0232.N0720.N1080.d014169)))
  refine ⟨heLp.toLp e, fun θ => ?_⟩
  change _root_.GD.N0232.N0720.N1080.d014182 m n θ (heLp.toLp e) ≤ ENNReal.ofReal c
  rw [← _root_.GD.N0232.N0720.N1080.d014198 m n θ e heLp]
  exact heb θ


theorem d015588
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d) :
    _root_.GD.N0230.N0611.d003516 (_root_.GD.N0232.N0720.N1080.d014197 m n) d = ⊤ := by
  by_contra hfinite
  apply _root_.GD.N0232.N0720.N1227.d015587 m n d hd
    (_root_.GD.N0230.N0611.d003516 (_root_.GD.N0232.N0720.N1080.d014197 m n) d).toReal ENNReal.toReal_nonneg
  intro θ
  rw [ENNReal.ofReal_toReal hfinite]
  exact le_iSup (fun θ => _root_.GD.N0232.N0720.N1080.d014197 m n θ d) θ




theorem d015589
    (S : Set (_root_.GD.N0232.N0720.N1080.d014170 m n → ℝ)) (hS : ∀ d ∈ S, Measurable d) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1080.d014197 m n) S = ⊤ := by
  apply top_unique
  apply le_iInf
  intro d
  apply le_iInf
  intro hd
  exact le_of_eq (_root_.GD.N0232.N0720.N1227.d015588 m n d (hS d hd)).symm

theorem d015590 :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1080.d014197 m n)
      (_root_.GD.N0232.N0720.N1256.d015545 m n) = ⊤ :=
  _root_.GD.N0232.N0720.N1227.d015589 m n _ (fun _ hd => hd)

theorem d015591 :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1080.d014197 m n)
      (_root_.GD.N0232.N0720.N1256.d015551 m n) = ⊤ :=
  _root_.GD.N0232.N0720.N1227.d015589 m n _ (fun _ hd => hd.1)

theorem d015592 :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0720.N1080.d014197 m n)
      (_root_.GD.N0232.N0720.N1256.d015552 m n) = ⊤ :=
  _root_.GD.N0232.N0720.N1227.d015589 m n _ (fun _ hd => hd.1.1)

end
end GD.N0232.N0720.N1227

#print axioms _root_.GD.N0232.N0720.N1227.d015588
#print axioms _root_.GD.N0232.N0720.N1227.d015589
#print axioms _root_.GD.N0232.N0720.N1227.d015591
#print axioms _root_.GD.N0232.N0720.N1227.d015592
