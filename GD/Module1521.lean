import GD.Module1520

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
open MeasureTheory Set
open scoped BigOperators

namespace GD.N0062
noncomputable section
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1441

def d023638 : Set _root_.GD.N0232.N0720.N1436.d013217 := Ioc (0:ℝ) 1 ×ˢ Ioi (0:ℝ)

theorem d023639 : MeasurableSet _root_.GD.N0062.d023638 :=
  measurableSet_Ioc.prod measurableSet_Ioi

theorem d023640 :
    (volume.prod volume).restrict _root_.GD.N0062.d023638 = _root_.GD.N0232.N0720.N1436.d013288 := by
  change (volume.prod volume).restrict (Ioc (0:ℝ) 1 ×ˢ Ioi (0:ℝ)) =
    (volume.prod volume).restrict (Ioo (0:ℝ) 1 ×ˢ Ioi (0:ℝ))
  exact Measure.restrict_congr_set
    (Measure.set_prod_ae_eq Ioo_ae_eq_Ioc (Filter.EventuallyEq.rfl)).symm

def d023641 (t : _root_.GD.N0232.N0720.N1441.d013676) : _root_.GD.N0232.N0720.N1436.d013217 → ℝ :=
  _root_.GD.N0062.d023638.indicator (fun p => _root_.GD.N0062.d023633 t p / ((t:ℝ)*(1-t)))

theorem d023642 (t : _root_.GD.N0232.N0720.N1441.d013676)
    (p : _root_.GD.N0232.N0720.N1436.d013217) : 0≤_root_.GD.N0062.d023641 t p := by
  by_cases hp : p∈_root_.GD.N0062.d023638
  · rw [_root_.GD.N0062.d023641, indicator_of_mem hp]
    change p.1∈Ioc (0:ℝ) 1 ∧ 0<p.2 at hp
    have hoff : 0<_root_.GD.N0062.d022142 t p.1 := add_pos_of_nonneg_of_pos
      (div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hp.1.2))
        (sub_pos.mpr t.property.2).le)
      (div_pos (mul_pos (by norm_num) hp.1.1) t.property.1)
    have hq : 0<p.2^2+_root_.GD.N0062.d022142 t p.1 := add_pos (sq_pos_of_pos hp.2) hoff
    have ht0 := t.property.1
    have ht1 := sub_pos.mpr t.property.2
    unfold _root_.GD.N0062.d023633
    positivity
  · simp [_root_.GD.N0062.d023641, hp]

private theorem d023643 (t : _root_.GD.N0232.N0720.N1441.d013676)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (a : ℝ) :
    (fun p => _root_.GD.N0062.d023641 t p * (g (_root_.GD.N0062.d023632 p)-a)^2) =
      _root_.GD.N0062.d023638.indicator
        (fun p => (_root_.GD.N0062.d023633 t p * (g (_root_.GD.N0062.d023632 p)-a)^2)/((t:ℝ)*(1-t))) := by
  funext p
  by_cases hp : p∈_root_.GD.N0062.d023638
  · simp [_root_.GD.N0062.d023641, hp]
    ring
  · simp [_root_.GD.N0062.d023641, hp]


theorem d023644 (t : _root_.GD.N0232.N0720.N1441.d013676)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ p, |g p|≤B) (a : ℝ) :
    Integrable (fun p => _root_.GD.N0062.d023641 t p * (g (_root_.GD.N0062.d023632 p)-a)^2)
      (volume.prod volume) := by
  rw [_root_.GD.N0062.d023643]
  have hi := (_root_.GD.N0062.d023636 t g hg hB a).div_const ((t:ℝ)*(1-t))
  apply (integrable_indicator_iff _root_.GD.N0062.d023639).mpr
  change Integrable _ ((volume.prod volume).restrict _root_.GD.N0062.d023638)
  rw [_root_.GD.N0062.d023640]
  exact hi



theorem d023645 (t : _root_.GD.N0232.N0720.N1441.d013676)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ p, |g p|≤B) (a : ℝ) :
    ((∫ p, (g p-a)^2 ∂_root_.GD.N0232.N0720.N1441.d013678 3 3 t)/((t:ℝ)*(1-t))) =
      ∫ p, _root_.GD.N0062.d023641 t p * (g (_root_.GD.N0062.d023632 p)-a)^2
        ∂volume.prod volume := by
  rw [_root_.GD.N0062.d023643, integral_indicator _root_.GD.N0062.d023639,
    integral_div, _root_.GD.N0062.d023640, _root_.GD.N0062.d023637 t g hg hB a]

theorem d023646 {ι : Type*} [Fintype ι]
    (t : ι→_root_.GD.N0232.N0720.N1441.d013676) (w : ι→ℝ)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ p, |g p|≤B) :
    Integrable (fun p => ∑ i, (w i*_root_.GD.N0062.d023641 (t i) p)*
      (g (_root_.GD.N0062.d023632 p)-(t i:ℝ))^2) (volume.prod volume) := by
  apply integrable_finsetSum
  intro i _
  apply ((_root_.GD.N0062.d023644 (t i) g hg hB (t i)).const_mul (w i)).congr
  exact ae_of_all _ (fun p => by ring)



theorem d023647 {ι : Type*} [Fintype ι]
    (t : ι→_root_.GD.N0232.N0720.N1441.d013676) (w : ι→ℝ)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    {B : ℝ} (hB : ∀ p, |g p|≤B) :
    (∑ i, w i * ((∫ p, (g p-(t i:ℝ))^2 ∂_root_.GD.N0232.N0720.N1441.d013678 3 3 (t i))/
      ((t i:ℝ)*(1-t i)))) =
      ∫ p, ∑ i, (w i*_root_.GD.N0062.d023641 (t i) p)*
        (g (_root_.GD.N0062.d023632 p)-(t i:ℝ))^2 ∂volume.prod volume := by
  have hi (i : ι) : Integrable (fun p => (w i*_root_.GD.N0062.d023641 (t i) p)*
      (g (_root_.GD.N0062.d023632 p)-(t i:ℝ))^2) (volume.prod volume) := by
    apply ((_root_.GD.N0062.d023644 (t i) g hg hB (t i)).const_mul (w i)).congr
    exact ae_of_all _ (fun p => by ring)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [_root_.GD.N0062.d023645 (t i) g hg hB (t i), ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun p => by ring)

end
end GD.N0062

#print axioms _root_.GD.N0062.d023640
#print axioms _root_.GD.N0062.d023642
#print axioms _root_.GD.N0062.d023644
#print axioms _root_.GD.N0062.d023645
#print axioms _root_.GD.N0062.d023646
#print axioms _root_.GD.N0062.d023647
