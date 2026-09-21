import GD.Module1865
import GD.Module1834
import GD.Module1461






set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0101.N0384
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1159 _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1255
open _root_.GD.N0232.N0720.N1441
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0709
open _root_.GD.N0230.N0710
open _root_.GD.N0230.N0664
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0076.N0313

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

private def d030630 (c : ℝ) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0076.N0313.d030580 m n hm hn c → _root_.GD.N0076.N0313.d030580 m n hm hn c := fun p =>
  ⟨toWeakSpace ℝ _ (_root_.GD.N0232.N0720.N1159.d014642 m n g ((toWeakSpace ℝ _).symm p.1)
    (_root_.GD.N0076.N0313.d030576 m n hm hn ((_root_.GD.N0076.N0313.d030583 m n hm hn c p.1).mp p.2))),
    ⟨_, _root_.GD.N0076.N0313.d030588 m n hm hn g
      ((_root_.GD.N0076.N0313.d030583 m n hm hn c p.1).mp p.2), rfl⟩⟩

private def d030631 (c : ℝ) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (x : WeakSpace ℝ (_root_.GD.N0076.N0313.d030564 m n)) : WeakSpace ℝ (_root_.GD.N0076.N0313.d030564 m n) := by
  classical
  exact if hx : x ∈ _root_.GD.N0076.N0313.d030580 m n hm hn c then
    (_root_.GD.N0101.N0384.d030630 m n hm hn c g ⟨x, hx⟩).1 else x

private theorem d030632 (c : ℝ) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (x : WeakSpace ℝ (_root_.GD.N0076.N0313.d030564 m n)) (hx : x ∈ _root_.GD.N0076.N0313.d030580 m n hm hn c) :
    _root_.GD.N0101.N0384.d030631 m n hm hn c g x =
      toWeakSpace ℝ _ (_root_.GD.N0232.N0720.N1159.d014642 m n g ((toWeakSpace ℝ _).symm x)
        (_root_.GD.N0076.N0313.d030576 m n hm hn ((_root_.GD.N0076.N0313.d030583 m n hm hn c x).mp hx))) := by
  simp only [_root_.GD.N0101.N0384.d030631, dif_pos hx, _root_.GD.N0101.N0384.d030630]

private theorem d030633 (c : ℝ) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    MapsTo (_root_.GD.N0101.N0384.d030631 m n hm hn c g) (_root_.GD.N0076.N0313.d030580 m n hm hn c)
      (_root_.GD.N0076.N0313.d030580 m n hm hn c) := by
  intro x hx
  rw [_root_.GD.N0101.N0384.d030632 m n hm hn c g x hx]
  exact ⟨_, _root_.GD.N0076.N0313.d030588 m n hm hn g
    ((_root_.GD.N0076.N0313.d030583 m n hm hn c x).mp hx), rfl⟩

private theorem d030634 (c : ℝ) (hc : 0 ≤ c)
    (g : _root_.GD.N0232.N0719.N0946.d009229) :
    ContinuousOn (_root_.GD.N0101.N0384.d030631 m n hm hn c g) (_root_.GD.N0076.N0313.d030580 m n hm hn c) := by
  have hcont : Continuous (_root_.GD.N0101.N0384.d030630 m n hm hn c g) := by
    apply _root_.GD.N0232.N0720.N1255.d014925 m n (_root_.GD.N0076.N0313.d030580 m n hm hn c)
      (_root_.GD.N0076.N0313.d030581 m n hm hn hc)
      (fun p hp => _root_.GD.N0076.N0313.d030576 m n hm hn
        ((_root_.GD.N0076.N0313.d030583 m n hm hn c p).mp hp)) g
    intro p
    rfl
  apply continuousOn_iff_continuous_restrict.mpr
  convert continuous_subtype_val.comp hcont using 1
  funext p
  exact _root_.GD.N0101.N0384.d030632 m n hm hn c g p.1 p.2

private theorem d030635 (c : ℝ) (g h : _root_.GD.N0232.N0719.N0946.d009229)
    (x : WeakSpace ℝ (_root_.GD.N0076.N0313.d030564 m n)) (hx : x ∈ _root_.GD.N0076.N0313.d030580 m n hm hn c) :
    _root_.GD.N0101.N0384.d030631 m n hm hn c g (_root_.GD.N0101.N0384.d030631 m n hm hn c h x) =
      _root_.GD.N0101.N0384.d030631 m n hm hn c (g * h) x := by
  rw [_root_.GD.N0101.N0384.d030632 m n hm hn c g _
    (_root_.GD.N0101.N0384.d030633 m n hm hn c h hx)]
  simp only [_root_.GD.N0101.N0384.d030632 m n hm hn c h x hx,
    LinearEquiv.symm_apply_apply,
    _root_.GD.N0101.N0384.d030632 m n hm hn c (g * h) x hx]
  congr 1
  exact _root_.GD.N0232.N0720.N1482.d015161 g h _ _

private theorem d030636 (c : ℝ) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0230.N0710.d001232 (_root_.GD.N0101.N0384.d030631 m n hm hn c g)
      (_root_.GD.N0076.N0313.d030580 m n hm hn c) := by
  have hconv : Convex ℝ (_root_.GD.N0076.N0313.d030580 m n hm hn c) :=
    (_root_.GD.N0076.N0313.d030578 m n hm hn c).linear_image (toWeakSpace ℝ _).toLinearMap
  intro x hx y hy a b ha hb hab
  have hxy := hconv hx hy ha hb hab
  rw [_root_.GD.N0101.N0384.d030632 m n hm hn c g _ hxy,
    _root_.GD.N0101.N0384.d030632 m n hm hn c g x hx,
    _root_.GD.N0101.N0384.d030632 m n hm hn c g y hy]
  have h := _root_.GD.N0232.N0720.N1257.d015529 m n hm hn g
    ((toWeakSpace ℝ _).symm x) ((toWeakSpace ℝ _).symm y)
    (_root_.GD.N0076.N0313.d030576 m n hm hn ((_root_.GD.N0076.N0313.d030583 m n hm hn c x).mp hx))
    (_root_.GD.N0076.N0313.d030576 m n hm hn ((_root_.GD.N0076.N0313.d030583 m n hm hn c y).mp hy)) hab
    (_root_.GD.N0076.N0313.d030576 m n hm hn (_root_.GD.N0076.N0313.d030578 m n hm hn c
      ((_root_.GD.N0076.N0313.d030583 m n hm hn c x).mp hx)
      ((_root_.GD.N0076.N0313.d030583 m n hm hn c y).mp hy) ha hb hab))
  simpa only [map_add, map_smul] using congrArg (toWeakSpace ℝ _) h



theorem d030637
    (c : ℝ) (hc : 0 ≤ c) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (hbound : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤
      ENNReal.ofReal (c * _root_.GD.N0076.N0313.d030565 m n hm hn θ)) :
    ∃ e : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ, Measurable e ∧
      (∀ g : _root_.GD.N0232.N0719.N0946.d009229, ∀ ω, e (g • ω) = g • e ω) ∧
      ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ e ≤ ENNReal.ofReal (c * _root_.GD.N0076.N0313.d030565 m n hm hn θ) := by
  have hmem := _root_.GD.N0232.N0720.N1215.d014285 m n d hd
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound _root_.GD.N0232.N0720.N1080.d014169))
  have hp : hmem.toLp d ∈ _root_.GD.N0076.N0313.d030570 m n hm hn c := by
    intro θ
    rw [← _root_.GD.N0232.N0720.N1080.d014198 m n θ d hmem]
    exact hbound θ
  have hconv : Convex ℝ (_root_.GD.N0076.N0313.d030580 m n hm hn c) :=
    (_root_.GD.N0076.N0313.d030578 m n hm hn c).linear_image (toWeakSpace ℝ _).toLinearMap
  have hb : _root_.GD.N0230.N0709.d001221 (_root_.GD.N0076.N0313.d030580 m n hm hn c) := by
    apply (Metric.isBounded_closedBall (x := (0 : _root_.GD.N0076.N0313.d030564 m n))
      (r := Real.sqrt (c * _root_.GD.N0076.N0313.d030565 m n hm hn _root_.GD.N0232.N0720.N1080.d014169))).subset
    rintro p ⟨q, hq, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right,
      LinearEquiv.symm_apply_apply] using _root_.GD.N0076.N0313.d030579 m n hm hn hc
        ((_root_.GD.N0076.N0313.d030583 m n hm hn c q).mp hq)
  obtain ⟨x, hx, hfix⟩ := _root_.GD.N0230.N0664.d001257
    (fun b r => _root_.GD.N0101.N0384.d030631 m n hm hn c ⟨b, r⟩) (_root_.GD.N0076.N0313.d030580 m n hm hn c)
    (_root_.GD.N0076.N0313.d030581 m n hm hn hc) hconv
    (Set.Nonempty.image (toWeakSpace ℝ _) ⟨hmem.toLp d, hp⟩) hb
    (fun b r => _root_.GD.N0101.N0384.d030633 m n hm hn c ⟨b, r⟩)
    (fun b r => _root_.GD.N0101.N0384.d030634 m n hm hn c hc ⟨b, r⟩)
    (fun b r => _root_.GD.N0101.N0384.d030636 m n hm hn c ⟨b, r⟩)
    (fun b r a s x hx => _root_.GD.N0101.N0384.d030635 m n hm hn c ⟨b, r⟩ ⟨a, s⟩ x hx)
  let p := (toWeakSpace ℝ (_root_.GD.N0076.N0313.d030564 m n)).symm x
  have hpcap : p ∈ _root_.GD.N0076.N0313.d030570 m n hm hn c := (_root_.GD.N0076.N0313.d030583 m n hm hn c x).mp hx
  have hpfin := _root_.GD.N0076.N0313.d030576 m n hm hn hpcap
  have hfixed (g : _root_.GD.N0232.N0719.N0946.d009229) : _root_.GD.N0232.N0720.N1159.d014642 m n g p hpfin = p := by
    have hg : _root_.GD.N0101.N0384.d030631 m n hm hn c g x = x := by
      cases g with
      | mk b r => exact hfix b r
    rw [_root_.GD.N0101.N0384.d030632 m n hm hn c g x hx] at hg
    exact (toWeakSpace ℝ _).injective (hg.trans (by simp [p]))
  obtain ⟨e, he, hae, heq⟩ :=
    _root_.GD.N0232.N0720.N1214.d014271 m n hm hn p
      (fun g => _root_.GD.N0232.N0720.N1159.d014641 m n g p hpfin) hfixed
  refine ⟨e, he, heq, fun θ => ?_⟩
  rw [_root_.GD.N0232.N0720.N1159.d014662 m n θ (hae θ), _root_.GD.N0232.N0720.N1215.d014286]
  exact hpcap θ



theorem d030638
    (c : ℝ) (hc : 0 ≤ c) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (hbound : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤
      ENNReal.ofReal (c * _root_.GD.N0076.N0313.d030565 m n hm hn θ)) :
    ∃ g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ,
      Measurable g ∧ (∀ z, g z ∈ Icc (0 : ℝ) 1) ∧
      ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ (_root_.GD.N0232.N0720.N1425.d014719 m n g) ≤
        ENNReal.ofReal (c * _root_.GD.N0076.N0313.d030565 m n hm hn θ) := by
  obtain ⟨e, he, heq, heb⟩ := _root_.GD.N0101.N0384.d030637 m n hm hn c hc d hd hbound
  apply _root_.GD.N0024.N0271.d028029
    m n hm hn e ⟨he, fun θ => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (heb θ)⟩
    ((_root_.GD.N0232.N0720.N1295.d019240 m n e).mpr heq)
    (fun θ => ENNReal.ofReal (c * _root_.GD.N0076.N0313.d030565 m n hm hn θ))
    (fun _ => ENNReal.ofReal_ne_top) _ heb
  intro θ
  unfold _root_.GD.N0076.N0313.d030565 _root_.GD.N0232.N0720.N1066.d014320
  rw [← _root_.GD.N0232.N0720.N1080.d014199 m n hm hn,
    _root_.GD.N0024.N0270.d030251 m n hm hn,
    _root_.GD.N0232.N0720.N1080.d014199 m n hm hn]



theorem d030639
    (c : ℝ) (hc : 0 ≤ c) (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (hbound : ∀ θ, _root_.GD.N0232.N0720.N1080.d014197 m n θ d ≤
      ENNReal.ofReal (c * _root_.GD.N0076.N0313.d030565 m n hm hn θ)) :
    ∃ g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ,
      Measurable g ∧ (∀ z, g z ∈ Icc (0 : ℝ) 1) ∧
      ∀ t : _root_.GD.N0232.N0720.N1441.d013676,
        (∫ z, (g z - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 m n t) ≤
          c * _root_.GD.N0076.N0313.d030565 m n hm hn (_root_.GD.N0045.d023064 m n hm hn t) -
            t.1 * (1 - t.1) := by
  obtain ⟨g, hg, hgb, hcap⟩ := _root_.GD.N0101.N0384.d030638 m n hm hn c hc d hd hbound
  refine ⟨g, hg, hgb, fun t => ?_⟩
  have hb := hcap (_root_.GD.N0045.d023064 m n hm hn t)
  rw [_root_.GD.N0232.N0720.N1335.d020089
    m n hm hn _ hg hgb] at hb
  have ho := _root_.GD.N0232.N0720.N1396.d014795 m n hm hn
    (_root_.GD.N0045.d023064 m n hm hn t)
  unfold _root_.GD.N0232.N0720.N1396.d014778 at ho
  rw [ho] at hb
  simp only [_root_.GD.N0045.d023065,
    _root_.GD.N0045.d023066, one_mul] at hb
  have hb' := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hc (_root_.GD.N0076.N0313.d030566 m n hm hn _).le)).mp hb
  change _ + (∫ z, (g z - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1441.d013678 m n t) ≤ _ at hb'
  linarith

end
end GD.N0101.N0384

#print axioms _root_.GD.N0101.N0384.d030637
#print axioms _root_.GD.N0101.N0384.d030638
#print axioms _root_.GD.N0101.N0384.d030639
