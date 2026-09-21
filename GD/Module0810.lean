import GD.Module0247
import GD.Module0802










set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0232.N0719.N0971

noncomputable section

open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0842
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0611
open _root_.GD.N0230.N0707

variable (k : ℕ) (sizes : Fin k → ℕ)



theorem d012334
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d)
    (C : ℝ) (hC : 0 ≤ C) :
    ¬ ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d ≤ ENNReal.ofReal C := by
  intro hbound
  let θ₁ : _root_.GD.N0232.N0719.N0859.d010809 k := { _root_.GD.N0232.N0719.N0859.d010810 k with location := 1 }
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ₁) := by
    unfold _root_.GD.N0232.N0719.N0859.d010812
    infer_instance
  apply _root_.GD.N0230.N0707.d003550
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes) (_root_.GD.N0232.N0719.N0859.d010812 k sizes)
    (_root_.GD.N0232.N0719.N0859.d010809.location (k := k)) (_root_.GD.N0232.N0719.N0859.d010814 k sizes)
    (_root_.GD.N0232.N0719.N0859.d010810 k) θ₁ (by rfl) (by rfl) (by rfl)
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
  let e := _root_.GD.N0232.N0719.N0842.d010911 k sizes 0 a d
  have he : Measurable e := _root_.GD.N0232.N0719.N0842.d010912 k sizes 0 a d hd
  have heb (θ : _root_.GD.N0232.N0719.N0859.d010809 k) : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ e ≤ ENNReal.ofReal c := by
    let η := _root_.GD.N0232.N0719.N0845.d010881
      (_root_.GD.N0232.N0719.N0842.d010906 0 a) a⁻¹ (inv_pos.mpr ha) θ
    have hη : _root_.GD.N0232.N0719.N0845.d010881 0 a ha η = θ :=
      _root_.GD.N0232.N0719.N0842.d010919 0 a ha θ
    rw [← hη, _root_.GD.N0232.N0719.N0842.d010920 k sizes 0 a ha η d hd]
    calc
      ENNReal.ofReal (a ^ 2) * _root_.GD.N0232.N0719.N0859.d010840 k sizes η d ≤
          ENNReal.ofReal (a ^ 2) * ENNReal.ofReal C := mul_le_mul' le_rfl (hbound η)
      _ = ENNReal.ofReal (a ^ 2 * C) := (ENNReal.ofReal_mul (sq_nonneg a)).symm
      _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal hac
  have heLp : MemLp e 2 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) :=
    _root_.GD.N0232.N0719.N0896.d011095 k sizes e he
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (heb (_root_.GD.N0232.N0719.N0859.d010810 k)))
  refine ⟨heLp.toLp e, fun θ => ?_⟩
  change _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (heLp.toLp e) ≤ ENNReal.ofReal c
  rw [← _root_.GD.N0232.N0719.N0859.d010841 k sizes θ e heLp]
  exact heb θ


theorem d012335
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d) :
    _root_.GD.N0230.N0611.d003516 (_root_.GD.N0232.N0719.N0859.d010840 k sizes) d = ⊤ := by
  by_contra hfinite
  apply _root_.GD.N0232.N0719.N0971.d012334 k sizes d hd
    (_root_.GD.N0230.N0611.d003516 (_root_.GD.N0232.N0719.N0859.d010840 k sizes) d).toReal ENNReal.toReal_nonneg
  intro θ
  rw [ENNReal.ofReal_toReal hfinite]
  exact le_iSup (fun θ => _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d) θ




theorem d012336
    (S : Set (_root_.GD.N0232.N0719.d009173 k sizes → ℝ)) (hS : ∀ d ∈ S, Measurable d) :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0859.d010840 k sizes) S = ⊤ := by
  apply top_unique
  apply le_iInf
  intro d
  apply le_iInf
  intro hd
  exact le_of_eq (_root_.GD.N0232.N0719.N0971.d012335 k sizes d (hS d hd)).symm

theorem d012337 :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0859.d010840 k sizes)
      (_root_.GD.N0232.N0719.N0962.d012184 k sizes) = ⊤ :=
  _root_.GD.N0232.N0719.N0971.d012336 k sizes _ (fun _ hd => hd)

theorem d012338 :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0859.d010840 k sizes)
      (_root_.GD.N0232.N0719.N0962.d012190 k sizes) = ⊤ :=
  _root_.GD.N0232.N0719.N0971.d012336 k sizes _ (fun _ hd => hd.1)

theorem d012339 :
    _root_.GD.N0230.N0611.d003517 (_root_.GD.N0232.N0719.N0859.d010840 k sizes)
      (_root_.GD.N0232.N0719.N0962.d012191 k sizes) = ⊤ :=
  _root_.GD.N0232.N0719.N0971.d012336 k sizes _ (fun _ hd => hd.1.1)

end
end GD.N0232.N0719.N0971

#print axioms _root_.GD.N0232.N0719.N0971.d012335
#print axioms _root_.GD.N0232.N0719.N0971.d012336
#print axioms _root_.GD.N0232.N0719.N0971.d012338
#print axioms _root_.GD.N0232.N0719.N0971.d012339
