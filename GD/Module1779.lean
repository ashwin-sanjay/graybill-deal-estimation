import GD.Module1739
import GD.Module1765
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Normed.Group.Tannery



set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
open MeasureTheory Set Filter Topology
namespace GD.N0106.N0428.N0765.N1665
noncomputable section
open _root_.GD.N0106.N0428.N0765.N1670 _root_.GD.N0106.N0428.N0765.N1587 _root_.GD.N0106.N0428.N0765.N1590

def d029611 (a p v w c : ℝ) : ℝ :=
  max (v^(-p)) (w^(-p)) * _root_.GD.N0106.N0428.N0765.N1587.d029254 a (p-a) c

theorem d029612 (a p : ℝ) (n : ℕ) {e u v w : ℝ}
    (he : 0 ≤ e) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 ≤ w) :
    Continuous (_root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w) := by
  have hb : Continuous (_root_.GD.N0106.N0428.N0765.N1670.d028854 e u v w) := by unfold _root_.GD.N0106.N0428.N0765.N1670.d028854; fun_prop
  have hp := hb.rpow_const (p := -p) (fun c => Or.inl (_root_.GD.N0106.N0428.N0765.N1670.d028860 he hu hv hw c).ne')
  exact (show Continuous (fun c : ℝ => Real.exp (a*c)*(1+e*Real.exp c)^n) by
    fun_prop).mul hp

theorem d029613 {a p e u v w : ℝ} {n : ℕ}
    (hn : (n : ℝ) ≤ p) (he : 0 ≤ e) (hu : 0 ≤ u)
    (hv : 0 < v) (hw : 0 < w) (c : ℝ) :
    ‖_root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w c‖ ≤ _root_.GD.N0106.N0428.N0765.N1665.d029611 a p v w c := by
  rw [Real.norm_eq_abs, abs_of_nonneg (_root_.GD.N0106.N0428.N0765.N1670.d028862 a p n he hu hv hw.le c)]
  by_cases hc : c ≤ 0
  · exact (_root_.GD.N0106.N0428.N0765.N1670.d028863 a hn he hu hv hw.le c).trans (by
      unfold _root_.GD.N0106.N0428.N0765.N1665.d029611 _root_.GD.N0106.N0428.N0765.N1587.d029254; rw [if_pos hc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · exact (_root_.GD.N0106.N0428.N0765.N1670.d028864 a hn he hu hv.le hw c).trans (by
      unfold _root_.GD.N0106.N0428.N0765.N1665.d029611 _root_.GD.N0106.N0428.N0765.N1587.d029254; rw [if_neg hc]
      rw [show (a-p)*c = -(p-a)*c by ring]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)

theorem d029614 {a p : ℝ} (ha : 0 < a) (hap : a < p) (v w : ℝ) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1665.d029611 a p v w) := by
  have hl : IntegrableOn (_root_.GD.N0106.N0428.N0765.N1665.d029611 a p v w) (Iic (0 : ℝ)) := by
    have h := (integrableOn_exp_mul_Iic ha 0).const_mul (max (v^(-p)) (w^(-p)))
    refine h.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with c hc
    change c ≤ 0 at hc
    simp only [_root_.GD.N0106.N0428.N0765.N1665.d029611, _root_.GD.N0106.N0428.N0765.N1587.d029254, if_pos hc]
  have hr : IntegrableOn (_root_.GD.N0106.N0428.N0765.N1665.d029611 a p v w) (Ioi (0 : ℝ)) := by
    have h := (integrableOn_exp_mul_Ioi (show -(p-a)<0 by linarith) 0).const_mul
      (max (v^(-p)) (w^(-p)))
    refine h.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with c hc
    change 0 < c at hc
    simp only [_root_.GD.N0106.N0428.N0765.N1665.d029611, _root_.GD.N0106.N0428.N0765.N1587.d029254, if_neg (not_le.mpr hc)]
  simpa only [Iic_union_Ioi, integrableOn_univ] using integrableOn_union.mpr ⟨hl,hr⟩

theorem d029615 {a p e u v w : ℝ} {n : ℕ}
    (ha : 0 < a) (hap : a < p) (hn : (n : ℝ) ≤ p)
    (he : 0 ≤ e) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    Integrable (_root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w) :=
  (_root_.GD.N0106.N0428.N0765.N1665.d029614 ha hap v w).mono'
    (_root_.GD.N0106.N0428.N0765.N1665.d029612 a p n he hu hv hw.le).aestronglyMeasurable
    (Eventually.of_forall (_root_.GD.N0106.N0428.N0765.N1665.d029613 hn he hu hv hw))


theorem d029616 {a p e u v w : ℝ} {n : ℕ}
    (ha : 0 < a) (hap : a < p) (hn : (n : ℝ) ≤ p)
    (he : 0 ≤ e) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    0 < ∫ c, _root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w c := by
  apply integral_pos_of_integrable_nonneg_nonzero
    (_root_.GD.N0106.N0428.N0765.N1665.d029612 a p n he hu hv hw.le)
    (_root_.GD.N0106.N0428.N0765.N1665.d029615 ha hap hn he hu hv hw)
    (_root_.GD.N0106.N0428.N0765.N1670.d028862 a p n he hu hv hw.le) (x := 0)
  have hb := _root_.GD.N0106.N0428.N0765.N1670.d028860 he hu hv hw.le 0
  have hp : 0 < _root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w 0 := by unfold _root_.GD.N0106.N0428.N0765.N1670.d028855; positivity
  exact hp.ne'

theorem d029617 {a p h : ℝ} (ha : 0 < a) (hap : a < p)
    (hh : 0 < h) (v w offset : ℝ) :
    Summable (fun k : ℤ => _root_.GD.N0106.N0428.N0765.N1665.d029611 a p v w (offset+h*k)) :=
  (_root_.GD.N0106.N0428.N0765.N1590.d029266 ha (sub_pos.mpr hap) hh offset).mul_left _

theorem d029618 {a p e u v w h : ℝ} {n : ℕ}
    (ha : 0 < a) (hap : a < p) (hn : (n : ℝ) ≤ p)
    (he : 0 ≤ e) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w)
    (hh : 0 < h) (offset : ℝ) :
    Summable (fun k : ℤ => _root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w (offset+h*k)) :=
  (_root_.GD.N0106.N0428.N0765.N1665.d029617 ha hap hh v w offset).of_norm_bounded
    (fun k => _root_.GD.N0106.N0428.N0765.N1665.d029613 hn he hu hv hw _)

theorem d029619 (a p : ℝ) (n : ℕ) {u v w : ℝ}
    (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 ≤ w) (c : ℝ) :
    Tendsto (fun e : ℝ => _root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w c) (𝓝[>] 0)
      (𝓝 (_root_.GD.N0106.N0428.N0765.N1670.d028855 a p n 0 u v w c)) := by
  have hb : ContinuousAt (fun e : ℝ => _root_.GD.N0106.N0428.N0765.N1670.d028854 e u v w c) 0 := by unfold _root_.GD.N0106.N0428.N0765.N1670.d028854; fun_prop
  have hp := hb.rpow_const (p := -p) (Or.inl (_root_.GD.N0106.N0428.N0765.N1670.d028860 (e := 0) le_rfl hu hv hw c).ne')
  have hc : ContinuousAt (fun e : ℝ => _root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w c) 0 :=
    (show ContinuousAt (fun e : ℝ => Real.exp (a*c)*(1+e*Real.exp c)^n) 0 by
      fun_prop).mul hp
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

theorem d029620 {a p u v w : ℝ} {n : ℕ}
    (ha : 0 < a) (hap : a < p) (hn : (n : ℝ) ≤ p)
    (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) :
    Tendsto (fun e : ℝ => ∫ c, _root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w c) (𝓝[>] 0)
      (𝓝 (∫ c, _root_.GD.N0106.N0428.N0765.N1670.d028855 a p n 0 u v w c)) := by
  refine tendsto_integral_filter_of_dominated_convergence (_root_.GD.N0106.N0428.N0765.N1665.d029611 a p v w) ?_ ?_
    (_root_.GD.N0106.N0428.N0765.N1665.d029614 ha hap v w) ?_
  · filter_upwards [self_mem_nhdsWithin] with e he
    exact (_root_.GD.N0106.N0428.N0765.N1665.d029612 a p n he.le hu hv hw.le).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with e he
    exact Eventually.of_forall (_root_.GD.N0106.N0428.N0765.N1665.d029613 hn he.le hu hv hw)
  · exact Eventually.of_forall (_root_.GD.N0106.N0428.N0765.N1665.d029619 a p n hu hv hw.le)

theorem d029621 {a p u v w h : ℝ} {n : ℕ}
    (ha : 0 < a) (hap : a < p) (hn : (n : ℝ) ≤ p)
    (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 < w) (hh : 0 < h) (offset : ℝ) :
    Tendsto (fun e : ℝ => ∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1670.d028855 a p n e u v w (offset+h*k)) (𝓝[>] 0)
      (𝓝 (∑' k : ℤ, _root_.GD.N0106.N0428.N0765.N1670.d028855 a p n 0 u v w (offset+h*k))) := by
  refine tendsto_tsum_of_dominated_convergence (_root_.GD.N0106.N0428.N0765.N1665.d029617 ha hap hh v w offset)
    (fun k => _root_.GD.N0106.N0428.N0765.N1665.d029619 a p n hu hv hw.le _) ?_
  filter_upwards [self_mem_nhdsWithin] with e he k
  exact _root_.GD.N0106.N0428.N0765.N1665.d029613 hn he.le hu hv hw _

end
end GD.N0106.N0428.N0765.N1665
#print axioms _root_.GD.N0106.N0428.N0765.N1665.d029620
#print axioms _root_.GD.N0106.N0428.N0765.N1665.d029621
