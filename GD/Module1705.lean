import GD.Module1482
import GD.Module1502
import GD.Module1704
import GD.Module1703







set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace GD.N0101.N0409
noncomputable section

open _root_.GD.N0232.N0719 _root_.GD.N0232.N0719.N0859
open _root_.GD.N0072 _root_.GD.N0021 _root_.GD.N0101.N0357
open _root_.GD.N0101.N0411 _root_.GD.N0101.N0413
open _root_.GD.N0225.N0538
open _root_.GD.N0225.N0537

variable {k : ℕ}



def d028614 (sizes : Fin k → ℕ)
    (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) : Prop :=
  ¬ ∃ w : (Fin k → ℝ) → Fin k → ℝ,
    Measurable w ∧ (∀ t, ∑ i, w t i = 1) ∧
    (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d) ∧
    ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) <
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d

theorem d028615 (hk : 0 < k) :
    ContinuousOn (_root_.GD.N0021.d023313 (k := k)) _root_.GD.N0101.N0357.d023158 := by
  letI : NeZero k := ⟨hk.ne'⟩
  have hi (i : Fin k) : ContinuousOn (fun t : Fin k → ℝ => (t i)⁻¹) _root_.GD.N0101.N0357.d023158 :=
    (continuous_apply i).continuousOn.inv₀ (fun t ht => (ht i).ne')
  have hs : ContinuousOn (fun t : Fin k → ℝ => ∑ i, (t i)⁻¹) _root_.GD.N0101.N0357.d023158 :=
    continuousOn_finsetSum _ (fun i _ => hi i)
  have hc : ContinuousOn (_root_.GD.N0230.N0665.d000407 (I := Fin k))
      _root_.GD.N0101.N0357.d023158 := by
    apply continuousOn_pi.mpr
    intro i
    exact (hi i).div hs (fun t ht =>
      (_root_.GD.N0230.N0665.d000408 ht).ne')
  exact hc.congr _root_.GD.N0101.N0411.d028562



theorem d028616
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (p w : (Fin k → ℝ) → Fin k → ℝ) (hp : Measurable p) (hw : Measurable w)
    (hpunit : ∀ t, ∑ i, p t i = 1) (hwunit : ∀ t, ∑ i, w t i = 1)
    (hpfinite : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p) ≠ ⊤)
    (hadm : _root_.GD.N0101.N0409.d028614 sizes (_root_.GD.N0072.d023291 sizes p))
    (hpcont : ContinuousOn p _root_.GD.N0101.N0357.d023158) (hwcont : ContinuousOn w _root_.GD.N0101.N0357.d023158)
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p)) :
    EqOn w p _root_.GD.N0101.N0357.d023158 := by
  have hae := _root_.GD.N0225.N0537.d023471 sizes hn p w hp hw
    hpunit hwunit hpfinite hadm hweak (_root_.GD.N0232.N0719.N0859.d010810 k)
  exact _root_.GD.N0216.d023275
    sizes hn (_root_.GD.N0232.N0719.N0859.d010810 k).scale (_root_.GD.N0232.N0719.N0859.d010810 k).scale_pos hae hwcont hpcont




theorem d028617 (hk : 0 < k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hadm : _root_.GD.N0101.N0409.d028614 sizes (_root_.GD.N0232.N0719.N0900.d009111 k sizes))
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hwcont : ContinuousOn w _root_.GD.N0101.N0357.d023158) (hunit : ∀ t ∈ _root_.GD.N0101.N0357.d023158, ∑ i, w t i = 1)
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes)) :
    EqOn w _root_.GD.N0021.d023313 _root_.GD.N0101.N0357.d023158 := by
  have hext : EqOn (_root_.GD.N0101.N0413.d028605 w) w _root_.GD.N0101.N0357.d023158 := by
    intro t ht
    exact if_pos ht
  rw [_root_.GD.N0021.d023315] at hadm hweak
  have hwe (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes (_root_.GD.N0101.N0413.d028605 w)) ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes _root_.GD.N0021.d023313) := by
    rw [_root_.GD.N0101.N0413.d028610 sizes hn w θ]
    exact hweak θ
  have heq := _root_.GD.N0101.N0409.d028616 sizes hn _root_.GD.N0021.d023313 (_root_.GD.N0101.N0413.d028605 w)
    _root_.GD.N0021.d023314 (_root_.GD.N0101.N0413.d028606 w hw)
    (_root_.GD.N0101.N0411.d028560 hk) (_root_.GD.N0101.N0413.d028607 hk w hunit)
    (_root_.GD.N0225.N0538.d023463 sizes hn _root_.GD.N0021.d023313 _root_.GD.N0021.d023314
      (_root_.GD.N0101.N0411.d028560 hk) (_root_.GD.N0101.N0411.d028561 hk)).2 hadm
    (_root_.GD.N0101.N0409.d028615 hk) (hwcont.congr hext) hwe
  exact hext.symm.trans heq



theorem d028618 (hk : 0 < k)
    (sizes : Fin k → ℕ) (hn : ∀ i, 2 ≤ sizes i)
    (hadm : _root_.GD.N0101.N0409.d028614 sizes (_root_.GD.N0232.N0719.N0900.d009111 k sizes))
    (w : (Fin k → ℝ) → Fin k → ℝ) (hw : Measurable w)
    (hwcont : ContinuousOn w _root_.GD.N0101.N0357.d023158) (hunit : ∀ t ∈ _root_.GD.N0101.N0357.d023158, ∑ i, w t i = 1)
    (t : Fin k → ℝ) (ht : t ∈ _root_.GD.N0101.N0357.d023158) (hdiff : w t ≠ _root_.GD.N0021.d023313 t) :
    ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes) <
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) := by
  classical
  by_contra hnone
  have hweak (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0900.d009111 k sizes) :=
    le_of_not_gt (fun h => hnone ⟨θ, h⟩)
  exact hdiff (_root_.GD.N0101.N0409.d028617 hk sizes hn hadm w hw hwcont hunit hweak ht)

theorem d028619 {n : ℕ} (s : ℕ) (hs : 3 ≤ s)
    (w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) (hw : Measurable w)
    (hwcont : ContinuousOn w _root_.GD.N0101.N0357.d023158) (hunit : ∀ t ∈ _root_.GD.N0101.N0357.d023158, ∑ i, w t i = 1)
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) (fun _ => s) θ (_root_.GD.N0072.d023291 (fun _ => s) w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 (n + 1) (fun _ => s) θ (_root_.GD.N0232.N0719.N0900.d009111 (n + 1) (fun _ => s))) :
    EqOn w _root_.GD.N0021.d023313 _root_.GD.N0101.N0357.d023158 :=
  _root_.GD.N0101.N0409.d028617 (Nat.succ_pos _) (fun _ => s) (fun _ => by omega)
    (_root_.GD.N0101.N0410.d028604 n s hs)
    w hw hwcont hunit hweak

theorem d028620 {n : ℕ} (s : ℕ) (hs : 3 ≤ s)
    (w : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) (hw : Measurable w)
    (hwcont : ContinuousOn w _root_.GD.N0101.N0357.d023158) (hunit : ∀ t ∈ _root_.GD.N0101.N0357.d023158, ∑ i, w t i = 1)
    (t : Fin (n + 1) → ℝ) (ht : t ∈ _root_.GD.N0101.N0357.d023158) (hdiff : w t ≠ _root_.GD.N0021.d023313 t) :
    ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 (n + 1) (fun _ => s) θ (_root_.GD.N0232.N0719.N0900.d009111 (n + 1) (fun _ => s)) <
      _root_.GD.N0232.N0719.N0859.d010840 (n + 1) (fun _ => s) θ (_root_.GD.N0072.d023291 (fun _ => s) w) :=
  _root_.GD.N0101.N0409.d028618 (Nat.succ_pos _) (fun _ => s) (fun _ => by omega)
    (_root_.GD.N0101.N0410.d028604 n s hs)
    w hw hwcont hunit t ht hdiff

end
end GD.N0101.N0409

#print axioms _root_.GD.N0101.N0409.d028615
#print axioms _root_.GD.N0101.N0409.d028616
#print axioms _root_.GD.N0101.N0409.d028617
#print axioms _root_.GD.N0101.N0409.d028618
#print axioms _root_.GD.N0101.N0409.d028619
#print axioms _root_.GD.N0101.N0409.d028620
