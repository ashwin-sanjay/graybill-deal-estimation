import GD.Module1764
import GD.Module1422
import GD.Module1421
import GD.Module1761
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals




set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter Topology
namespace GD.N0106.N0428.N0765.N1602
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1587 _root_.GD.N0106.N0428.N0765.N1538 _root_.GD.N0106.N0428.N0765.N1537 _root_.GD.N0106.N0428.N0765.N1675

def d029271 : Set (ℝ × ℝ) := {p | ((21 : ℝ)/2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 p.1 p.2 < Real.pi}

theorem d029272 {p : ℝ × ℝ} (hp : p ∈ _root_.GD.N0106.N0428.N0765.N1602.d029271) :
    ContinuousAt (fun q : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1587.d029259 q.1 q.2) p := by
  have hw : ((21 : ℝ)/2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 p.1 p.2 < Real.pi := hp
  have hs := _root_.GD.N0106.N0428.N0765.N1537.d021535 hw
  have hA : ContinuousAt (fun q : ℝ × ℝ => Real.cos (q.1 / 2)) p := by fun_prop
  have hB : ContinuousAt (fun q : ℝ × ℝ => Real.cos (q.2 / 2)) p := by fun_prop
  have hW : ContinuousAt (fun q : ℝ × ℝ => Real.cos (_root_.GD.N0106.N0428.N0765.N1538.d021192 q.1 q.2 / 2)) p := by
    unfold _root_.GD.N0106.N0428.N0765.N1538.d021192; fun_prop
  have hS : ContinuousAt (fun q : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1538.d021231 q.1 q.2) p := by
    unfold _root_.GD.N0106.N0428.N0765.N1538.d021231 _root_.GD.N0106.N0428.N0765.N1538.d021192; fun_prop
  have hDa := hA.rpow_const (p := -((23 : ℝ)/2)) (Or.inl (_root_.GD.N0106.N0428.N0765.N1585.d005527 hs.1).ne')
  have hDb := hB.rpow_const (p := -(10 : ℝ)) (Or.inl (_root_.GD.N0106.N0428.N0765.N1585.d005527 hs.2).ne')
  have hg := hB.inv₀ (_root_.GD.N0106.N0428.N0765.N1585.d005527 hs.2).ne'
  have hc := ((hW.rpow_const (p := -((21 : ℝ)/2))
    (Or.inl (_root_.GD.N0106.N0428.N0765.N1538.d021219 (_root_.GD.N0106.N0428.N0765.N1538.d021233 hw)).ne')).const_mul (3/2 : ℝ)).mul
    (hS.inv₀ (_root_.GD.N0106.N0428.N0765.N1538.d021232 hw).ne')
  exact (((hDa.mul hDb).mul (((hg.add_const 1).pow 2).add
    ((hc.add_const 1).pow 2))).mul_const _).mul_const _



theorem d029273 {S : Set (ℝ × ℝ)} (hS : IsCompact S)
    (hsub : S ⊆ _root_.GD.N0106.N0428.N0765.N1602.d029271) :
    ∃ K : ℝ, 0 < K ∧ ∀ e : ℝ, 0 ≤ e → ∀ p ∈ S, ∀ x y : ℝ,
      ‖_root_.GD.N0106.N0428.N0765.N1537.d021532 e p.1 p.2 (x,y)‖ ≤ K * _root_.GD.N0106.N0428.N0765.N1587.d029254 ((3 : ℝ)/2) 10 x * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 y := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => _root_.GD.N0106.N0428.N0765.N1587.d029259 p.1 p.2) S :=
    fun p hp => (_root_.GD.N0106.N0428.N0765.N1602.d029272 (hsub hp)).continuousWithinAt
  obtain ⟨K, hK⟩ := hS.exists_bound_of_continuousOn hc
  refine ⟨max K 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro e he p hp x y
  have hn : |_root_.GD.N0106.N0428.N0765.N1587.d029259 p.1 p.2| ≤ K := by
    simpa only [Real.norm_eq_abs] using hK p hp
  have hcoef : _root_.GD.N0106.N0428.N0765.N1587.d029259 p.1 p.2 ≤ max K 1 :=
    (le_abs_self _).trans (hn.trans (le_max_left _ _))
  exact (_root_.GD.N0106.N0428.N0765.N1587.d029262 he (hsub hp) x y).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (_root_.GD.N0106.N0428.N0765.N1587.d029255 _ _ _).le)
      (_root_.GD.N0106.N0428.N0765.N1587.d029255 _ _ _).le)


theorem d029274 {dA dB : ℝ} (hdA : 0 ≤ dA) (hdB : 0 ≤ dB)
    (hd : ((21 : ℝ)/2) * (dA+dB) < Real.pi) :
    ∃ K : ℝ, 0 < K ∧ ∀ e : ℝ, 0 ≤ e → ∀ α β : ℝ, |α| ≤ dA → |β| ≤ dB →
      ∀ x y : ℝ, ‖_root_.GD.N0106.N0428.N0765.N1537.d021532 e α β (x,y)‖ ≤
        K * _root_.GD.N0106.N0428.N0765.N1587.d029254 ((3 : ℝ)/2) 10 x * _root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 y := by
  have hsub : Icc (-dA) dA ×ˢ Icc (-dB) dB ⊆ _root_.GD.N0106.N0428.N0765.N1602.d029271 := by
    intro p hp
    have ha := abs_le.mpr hp.1
    have hb := abs_le.mpr hp.2
    change ((21 : ℝ)/2) * (|p.1|+|p.2|) < Real.pi
    nlinarith
  obtain ⟨K, hK, h⟩ := _root_.GD.N0106.N0428.N0765.N1602.d029273 (isCompact_Icc.prod isCompact_Icc) hsub
  refine ⟨K,hK,?_⟩
  intro e he α β hα hβ x y
  exact h e he (α,β) ⟨abs_le.mp hα, abs_le.mp hβ⟩ x y

theorem d029275 (a b : ℝ) : Measurable (_root_.GD.N0106.N0428.N0765.N1587.d029254 a b) := by
  exact Measurable.ite measurableSet_Iic (by fun_prop) (by fun_prop)

theorem d029276 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1587.d029254 a b) := by
  have hL : IntegrableOn (_root_.GD.N0106.N0428.N0765.N1587.d029254 a b) (Iic (0 : ℝ)) := by
    refine (integrableOn_exp_mul_Iic ha 0).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    change x ≤ 0 at hx
    simp only [_root_.GD.N0106.N0428.N0765.N1587.d029254, if_pos hx]
  have hR : IntegrableOn (_root_.GD.N0106.N0428.N0765.N1587.d029254 a b) (Ioi (0 : ℝ)) := by
    refine (integrableOn_exp_mul_Ioi (a := -b) (by linarith) 0).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 0 < x at hx
    simp only [_root_.GD.N0106.N0428.N0765.N1587.d029254, if_neg (not_le.mpr hx)]
  simpa only [Iic_union_Ioi, integrableOn_univ] using integrableOn_union.mpr ⟨hL,hR⟩


theorem d029277 {e α β : ℝ} (he : 0 ≤ e)
    (hw : ((21 : ℝ)/2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (y : ℝ) :
    Integrable (fun x : ℝ => _root_.GD.N0106.N0428.N0765.N1537.d021532 e α β (x,y)) := by
  have hm : Measurable (fun x : ℝ => _root_.GD.N0106.N0428.N0765.N1537.d021532 e α β (x,y)) :=
    (_root_.GD.N0106.N0428.N0765.N1537.d021549 e α β).comp (measurable_id.prodMk measurable_const)
  apply Integrable.mono' (((_root_.GD.N0106.N0428.N0765.N1602.d029276 (by norm_num : (0 : ℝ) < 3/2)
    (by norm_num : (0 : ℝ) < 10)).const_mul (_root_.GD.N0106.N0428.N0765.N1587.d029259 α β)).mul_const
    (_root_.GD.N0106.N0428.N0765.N1587.d029254 5 3 y)) hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => _root_.GD.N0106.N0428.N0765.N1587.d029262 he hw x y


theorem d029278 {e α β : ℝ} (he : 0 ≤ e)
    (hw : ((21 : ℝ)/2) * _root_.GD.N0106.N0428.N0765.N1538.d021192 α β < Real.pi) (x : ℝ) :
    Integrable (fun y : ℝ => _root_.GD.N0106.N0428.N0765.N1537.d021532 e α β (x,y)) := by
  have hm : Measurable (fun y : ℝ => _root_.GD.N0106.N0428.N0765.N1537.d021532 e α β (x,y)) :=
    (_root_.GD.N0106.N0428.N0765.N1537.d021549 e α β).comp (measurable_const.prodMk measurable_id)
  apply Integrable.mono' ((_root_.GD.N0106.N0428.N0765.N1602.d029276 (by norm_num : (0 : ℝ) < 5)
    (by norm_num : (0 : ℝ) < 3)).const_mul
      (_root_.GD.N0106.N0428.N0765.N1587.d029259 α β * _root_.GD.N0106.N0428.N0765.N1587.d029254 ((3 : ℝ)/2) 10 x)) hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => _root_.GD.N0106.N0428.N0765.N1587.d029262 he hw x y

end
end GD.N0106.N0428.N0765.N1602
#print axioms _root_.GD.N0106.N0428.N0765.N1602.d029274
#print axioms _root_.GD.N0106.N0428.N0765.N1602.d029277
#print axioms _root_.GD.N0106.N0428.N0765.N1602.d029278
