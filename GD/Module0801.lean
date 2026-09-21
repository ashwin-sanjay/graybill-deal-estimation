import GD.Module0096
import GD.Module0800
import GD.Module0799

set_option autoImplicit false
set_option warningAsError true












open MeasureTheory Set

namespace GD.N0232.N0719.N0964

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0963 _root_.GD.N0232.N0719.N0961
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0709
open _root_.GD.N0230.N0710
open _root_.GD.N0230.N0664
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (k : ℕ) (sizes : Fin k → ℕ)



def d012171 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (x : WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))) :
    WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) := by
  classical
  exact if hx : x ∈ _root_.GD.N0232.N0719.N0963.d012152 k sizes C then
    (_root_.GD.N0232.N0719.N0963.d012165 k sizes C hC g ⟨x, hx⟩).1 else x

theorem d012172 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p : _root_.GD.N0232.N0719.N0963.d012152 k sizes C) :
    _root_.GD.N0232.N0719.N0964.d012171 k sizes C hC g p.1 = (_root_.GD.N0232.N0719.N0963.d012165 k sizes C hC g p).1 := by
  simp [_root_.GD.N0232.N0719.N0964.d012171, p.2]

theorem d012173 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (x : WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)))
    (hx : x ∈ _root_.GD.N0232.N0719.N0963.d012152 k sizes C) :
    _root_.GD.N0232.N0719.N0964.d012171 k sizes C hC g x = toWeakSpace ℝ _
      (_root_.GD.N0232.N0719.N0896.d011109 k sizes g ((toWeakSpace ℝ _).symm x)
        (_root_.GD.N0232.N0719.N0963.d012149 k sizes ((_root_.GD.N0232.N0719.N0963.d012155 k sizes C x).mp hx))) := by
  simp [_root_.GD.N0232.N0719.N0964.d012171, hx, _root_.GD.N0232.N0719.N0963.d012165, _root_.GD.N0232.N0719.N0963.d012164, _root_.GD.N0232.N0719.N0963.d012161]

theorem d012174 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    MapsTo (_root_.GD.N0232.N0719.N0964.d012171 k sizes C hC g) (_root_.GD.N0232.N0719.N0963.d012152 k sizes C) (_root_.GD.N0232.N0719.N0963.d012152 k sizes C) := by
  intro x hx
  rw [show _root_.GD.N0232.N0719.N0964.d012171 k sizes C hC g x =
      (_root_.GD.N0232.N0719.N0963.d012165 k sizes C hC g ⟨x, hx⟩).1 from
        _root_.GD.N0232.N0719.N0964.d012172 k sizes C hC g ⟨x, hx⟩]
  exact (_root_.GD.N0232.N0719.N0963.d012165 k sizes C hC g ⟨x, hx⟩).2

theorem d012175 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    Continuous (_root_.GD.N0232.N0719.N0963.d012165 k sizes C hC g) := by
  apply _root_.GD.N0232.N0719.N0961.d012140 k sizes (_root_.GD.N0232.N0719.N0963.d012152 k sizes C) (_root_.GD.N0232.N0719.N0963.d012153 k sizes hC)
    (fun x hx ↦ _root_.GD.N0232.N0719.N0963.d012149 k sizes ((_root_.GD.N0232.N0719.N0963.d012155 k sizes C x).mp hx)) g
  intro p
  rfl

theorem d012176 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    ContinuousOn (_root_.GD.N0232.N0719.N0964.d012171 k sizes C hC g) (_root_.GD.N0232.N0719.N0963.d012152 k sizes C) := by
  apply continuousOn_iff_continuous_restrict.mpr
  have hc := continuous_subtype_val.comp (_root_.GD.N0232.N0719.N0964.d012175 k sizes C hC g)
  convert hc using 1
  funext p
  exact _root_.GD.N0232.N0719.N0964.d012172 k sizes C hC g p

theorem d012177 (C : ℝ) (hC : 0 ≤ C) (g h : _root_.GD.N0232.N0719.N0946.d009229)
    (p : _root_.GD.N0232.N0719.N0963.d012152 k sizes C) :
    _root_.GD.N0232.N0719.N0963.d012165 k sizes C hC g (_root_.GD.N0232.N0719.N0963.d012165 k sizes C hC h p) =
      _root_.GD.N0232.N0719.N0963.d012165 k sizes C hC (g * h) p := by
  simp only [_root_.GD.N0232.N0719.N0963.d012165, Equiv.symm_apply_apply, _root_.GD.N0232.N0719.N0963.d012163]

theorem d012178 (C : ℝ) (hC : 0 ≤ C) (g h : _root_.GD.N0232.N0719.N0946.d009229)
    (x : WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)))
    (hx : x ∈ _root_.GD.N0232.N0719.N0963.d012152 k sizes C) :
    _root_.GD.N0232.N0719.N0964.d012171 k sizes C hC g (_root_.GD.N0232.N0719.N0964.d012171 k sizes C hC h x) =
      _root_.GD.N0232.N0719.N0964.d012171 k sizes C hC (g * h) x := by
  let p : _root_.GD.N0232.N0719.N0963.d012152 k sizes C := ⟨x, hx⟩
  change _root_.GD.N0232.N0719.N0964.d012171 k sizes C hC g (_root_.GD.N0232.N0719.N0964.d012171 k sizes C hC h p.1) =
    _root_.GD.N0232.N0719.N0964.d012171 k sizes C hC (g * h) p.1
  simp only [_root_.GD.N0232.N0719.N0964.d012172]
  exact congrArg Subtype.val (_root_.GD.N0232.N0719.N0964.d012177 k sizes C hC g h p)

theorem d012179
    (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0230.N0710.d001232 (_root_.GD.N0232.N0719.N0964.d012171 k sizes C hC g) (_root_.GD.N0232.N0719.N0963.d012152 k sizes C) := by
  intro x hx y hy a b ha hb hab
  have hxy := _root_.GD.N0232.N0719.N0963.d012154 k sizes C hx hy ha hb hab
  rw [_root_.GD.N0232.N0719.N0964.d012173 k sizes C hC g _ hxy,
    _root_.GD.N0232.N0719.N0964.d012173 k sizes C hC g x hx,
    _root_.GD.N0232.N0719.N0964.d012173 k sizes C hC g y hy]
  have h := _root_.GD.N0232.N0719.N0963.d012168 k sizes g
    ((toWeakSpace ℝ _).symm x) ((toWeakSpace ℝ _).symm y)
    (_root_.GD.N0232.N0719.N0963.d012149 k sizes ((_root_.GD.N0232.N0719.N0963.d012155 k sizes C x).mp hx))
    (_root_.GD.N0232.N0719.N0963.d012149 k sizes ((_root_.GD.N0232.N0719.N0963.d012155 k sizes C y).mp hy)) hab
    (_root_.GD.N0232.N0719.N0963.d012149 k sizes (_root_.GD.N0232.N0719.N0963.d012148 k sizes C
      ((_root_.GD.N0232.N0719.N0963.d012155 k sizes C x).mp hx)
      ((_root_.GD.N0232.N0719.N0963.d012155 k sizes C y).mp hy) ha hb hab))
  simpa only [map_add, map_smul] using congrArg (toWeakSpace ℝ _) h

theorem d012180 (C : ℝ) (hC : 0 ≤ C) :
    _root_.GD.N0230.N0709.d001221 (_root_.GD.N0232.N0719.N0963.d012152 k sizes C) := by
  apply (Metric.isBounded_closedBall (x := (0 : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)))
    (r := Real.sqrt (C * _root_.GD.N0232.N0719.N0963.d012141 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)))).subset
  rintro p ⟨x, hx, rfl⟩
  have hb := _root_.GD.N0232.N0719.N0963.d012151 k sizes hC ((_root_.GD.N0232.N0719.N0963.d012155 k sizes C x).mp hx)
  simpa only [Metric.mem_closedBall, dist_zero_right] using hb


theorem d012181
    (C : ℝ) (hC : 0 ≤ C)
    (hne : (_root_.GD.N0232.N0719.N0963.d012146 k sizes C).Nonempty) :
    ∃ p, ∃ hp : p ∈ _root_.GD.N0232.N0719.N0963.d012146 k sizes C,
      ∀ g : _root_.GD.N0232.N0719.N0946.d009229,
        _root_.GD.N0232.N0719.N0896.d011109 k sizes g p (_root_.GD.N0232.N0719.N0963.d012149 k sizes hp) = p := by
  obtain ⟨x, hx, hfix⟩ := _root_.GD.N0230.N0664.d001257
    (fun b r ↦ _root_.GD.N0232.N0719.N0964.d012171 k sizes C hC ⟨b, r⟩) (_root_.GD.N0232.N0719.N0963.d012152 k sizes C)
    (_root_.GD.N0232.N0719.N0963.d012153 k sizes hC) (_root_.GD.N0232.N0719.N0963.d012154 k sizes C)
    (hne.image (toWeakSpace ℝ _)) (_root_.GD.N0232.N0719.N0964.d012180 k sizes C hC)
    (fun b r ↦ _root_.GD.N0232.N0719.N0964.d012174 k sizes C hC ⟨b, r⟩)
    (fun b r ↦ _root_.GD.N0232.N0719.N0964.d012176 k sizes C hC ⟨b, r⟩)
    (fun b r ↦ _root_.GD.N0232.N0719.N0964.d012179 k sizes C hC ⟨b, r⟩)
    (fun b r c s x hx ↦ _root_.GD.N0232.N0719.N0964.d012178 k sizes C hC ⟨b, r⟩ ⟨c, s⟩ x hx)
  refine ⟨(toWeakSpace ℝ _).symm x, (_root_.GD.N0232.N0719.N0963.d012155 k sizes C x).mp hx, ?_⟩
  intro g
  have hg : _root_.GD.N0232.N0719.N0964.d012171 k sizes C hC g x = x := by
    cases g with
    | mk b r => exact hfix b r
  rw [_root_.GD.N0232.N0719.N0964.d012173 k sizes C hC g x hx] at hg
  exact (toWeakSpace ℝ _).injective (hg.trans (by simp))



theorem d012182
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (C : ℝ) (hC : 0 ≤ C)
    (hne : (_root_.GD.N0232.N0719.N0963.d012146 k sizes C).Nonempty) :
    ∃ e : _root_.GD.N0232.N0719.d009173 k sizes → ℝ,
      Measurable e ∧
      (∀ g : _root_.GD.N0232.N0719.N0946.d009229, ∀ omega, e (g • omega) = g • e omega) ∧
      ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta e ≤
        ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0963.d012141 k sizes theta) := by
  obtain ⟨p, hp, hfix⟩ := _root_.GD.N0232.N0719.N0964.d012181 k sizes C hC hne
  obtain ⟨e, he, heae, hequiv⟩ :=
    _root_.GD.N0232.N0719.N0896.d011125 k sizes hk hsizes p
      (_root_.GD.N0232.N0719.N0963.d012149 k sizes hp) hfix
  refine ⟨e, he, hequiv, ?_⟩
  intro theta
  rw [_root_.GD.N0232.N0719.N0896.d011094 k sizes theta (heae theta), _root_.GD.N0232.N0719.N0896.d011093]
  exact hp theta



theorem d012183
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i) (C : ℝ) (hC : 0 ≤ C)
    (d : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hd : Measurable d)
    (hbound : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0963.d012141 k sizes theta)) :
    ∃ e : _root_.GD.N0232.N0719.d009173 k sizes → ℝ,
      Measurable e ∧
      (∀ g : _root_.GD.N0232.N0719.N0946.d009229, ∀ omega, e (g • omega) = g • e omega) ∧
      ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta e ≤
        ENNReal.ofReal (C * _root_.GD.N0232.N0719.N0963.d012141 k sizes theta) := by
  obtain ⟨p, hp, _⟩ := _root_.GD.N0232.N0719.N0963.d012170 k sizes C d hd hbound
  exact _root_.GD.N0232.N0719.N0964.d012182 k sizes hk hsizes C hC ⟨p, hp⟩

end

end GD.N0232.N0719.N0964

#print axioms _root_.GD.N0232.N0719.N0964.d012181
#print axioms _root_.GD.N0232.N0719.N0964.d012183
