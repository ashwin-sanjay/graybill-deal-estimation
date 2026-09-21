import GD.Module0471
import GD.Module1379
import GD.Module0486














set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set intervalIntegral

namespace GD.N0205
noncomputable section

open _root_.GD.N0179 _root_.GD.N0203
open _root_.GD.N0232.N0720.N1436

def d022322 (a b : ℝ) (v : ℝ → ℝ) (u : ℝ) : ℝ :=
  _root_.GD.N0203.d007246 a b u * v u ^ 2 + _root_.GD.N0203.d007246 a b (1 - u) * (1 - v u) ^ 2

def d022323 (d a b : ℝ) (v : ℝ → ℝ) (u : ℝ) : ℝ :=
  _root_.GD.N0205.d022322 a b v u - 2 * d * (_root_.GD.N0203.d007246 a b u + _root_.GD.N0203.d007246 a b (1 - u))

def d022324 (eta d a b : ℝ) (v : ℝ → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ u in eta..(1 - eta), _root_.GD.N0205.d022323 d a b v u


theorem d022325 {a b u : ℝ} (hu : 0 < u) (ha : 0 < a) (hab : a < b) :
    0 < _root_.GD.N0203.d007246 a b u := by
  have hc : ContinuousOn (_root_.GD.N0179.d006018 u) (Icc a b) :=
    (_root_.GD.N0179.d006037 hu).mono (fun x hx => (ha.trans_le hx.1).le)
  unfold _root_.GD.N0203.d007246
  apply intervalIntegral.integral_pos hab hc
  · intro x hx
    have hx0 : 0 < x := ha.trans hx.1
    unfold _root_.GD.N0179.d006018
    positivity
  · refine ⟨a, ⟨le_rfl, hab.le⟩, ?_⟩
    unfold _root_.GD.N0179.d006018
    positivity

private theorem d022326 {eta a b : ℝ} (heta : 0 < eta)
    (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (_root_.GD.N0203.d007246 a b) (Icc eta (1 - eta)) ∧
      ContinuousOn (fun u => _root_.GD.N0203.d007246 a b (1 - u)) (Icc eta (1 - eta)) := by
  constructor
  · exact (_root_.GD.N0203.d007255 ha hab).mono (fun _ hu => heta.trans_le hu.1)
  · apply (_root_.GD.N0203.d007255 ha hab).comp (by fun_prop)
    intro u hu
    show 0 < 1 - u
    linarith [hu.2]

private theorem d022327 {eta a b : ℝ} (heta : 0 < eta)
    (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (_root_.GD.N0203.d007246 a b) volume eta (1 - eta) ∧
      IntervalIntegrable (fun u => _root_.GD.N0203.d007246 a b (1 - u)) volume eta (1 - eta) := by
  have hc := _root_.GD.N0205.d022326 heta ha hab
  have hwin : eta ≤ 1 - eta := by linarith
  exact ⟨ContinuousOn.intervalIntegrable_of_Icc hwin hc.1,
    ContinuousOn.intervalIntegrable_of_Icc hwin hc.2⟩


theorem d022328 {eta a b : ℝ} (heta : 0 < eta)
    (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a < b) :
    IntervalIntegrable (fun u => _root_.GD.N0203.d007247 (_root_.GD.N0203.d007246 a b u) (_root_.GD.N0203.d007246 a b (1 - u)))
      volume eta (1 - eta) := by
  have hc := _root_.GD.N0205.d022326 heta ha hab.le
  have hn : ∀ u ∈ Icc eta (1 - eta), _root_.GD.N0203.d007246 a b u + _root_.GD.N0203.d007246 a b (1 - u) ≠ 0 := by
    intro u hu
    have hp := _root_.GD.N0205.d022325 (heta.trans_le hu.1) ha hab
    have hp' := _root_.GD.N0205.d022325 (show 0 < 1 - u by linarith [hu.2]) ha hab
    exact (add_pos hp hp').ne'
  have hh : ContinuousOn (fun u => _root_.GD.N0203.d007247 (_root_.GD.N0203.d007246 a b u) (_root_.GD.N0203.d007246 a b (1 - u)))
      (Icc eta (1 - eta)) := (hc.1.mul hc.2).div (hc.1.add hc.2) hn
  exact ContinuousOn.intervalIntegrable_of_Icc (by linarith) hh

private theorem d022329 {l r B : ℝ} {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume l r) (hg : Measurable g)
    (hB : ∀ x, ‖g x‖ ≤ B) : IntervalIntegrable (fun x => f x * g x) volume l r :=
  ⟨Integrable.mul_bdd hf.1 hg.aestronglyMeasurable (ae_of_all _ hB),
    Integrable.mul_bdd hf.2 hg.aestronglyMeasurable (ae_of_all _ hB)⟩

private theorem d022330 {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) : ‖v ^ 2‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg v)]
  simpa only [one_pow] using pow_le_pow_left₀ hv.1 hv.2 2

theorem d022331 {eta a b : ℝ} (heta : 0 < eta)
    (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a ≤ b)
    (v : ℝ → ℝ) (hv : Measurable v) (h01 : ∀ u, v u ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (_root_.GD.N0205.d022322 a b v) volume eta (1 - eta) := by
  obtain ⟨hl, hr⟩ := _root_.GD.N0205.d022327 heta hhalf ha hab
  have hl' : IntervalIntegrable (fun u => _root_.GD.N0203.d007246 a b u * v u ^ 2) volume eta (1 - eta) :=
    _root_.GD.N0205.d022329 hl (by fun_prop) (fun u => _root_.GD.N0205.d022330 (h01 u))
  have hr' : IntervalIntegrable (fun u => _root_.GD.N0203.d007246 a b (1 - u) * (1 - v u) ^ 2)
      volume eta (1 - eta) :=
    _root_.GD.N0205.d022329 hr (by fun_prop) (fun u =>
      _root_.GD.N0205.d022330 ⟨by linarith [(h01 u).2], by linarith [(h01 u).1]⟩)
  exact hl'.add hr'

theorem d022332 {eta a b : ℝ} (heta : 0 < eta)
    (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a ≤ b) (d : ℝ)
    (v : ℝ → ℝ) (hv : Measurable v) (h01 : ∀ u, v u ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (_root_.GD.N0205.d022323 d a b v) volume eta (1 - eta) := by
  have hp := _root_.GD.N0205.d022327 heta hhalf ha hab
  exact (_root_.GD.N0205.d022331 heta hhalf ha hab v hv h01).sub
    ((hp.1.add hp.2).const_mul (2 * d))


theorem d022333 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (v : ℝ) :
    _root_.GD.N0203.d007247 x y ≤ x * v ^ 2 + y * (1 - v) ^ 2 := by
  have h := _root_.GD.N0209.d007518 x y v (add_pos hx hy).ne'
  have hn := mul_nonneg (add_pos hx hy).le (sq_nonneg (v - y / (x + y)))
  unfold _root_.GD.N0209.d007517 at h
  unfold _root_.GD.N0203.d007247
  linarith


theorem d022334 {eta a b : ℝ} (heta : 0 < eta)
    (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a < b) (d : ℝ)
    (v : ℝ → ℝ) (hv : Measurable v) (h01 : ∀ u, v u ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0203.d007249 eta a b - d * _root_.GD.N0203.d007250 eta a b ≤ _root_.GD.N0205.d022324 eta d a b v := by
  have hh := _root_.GD.N0205.d022328 heta hhalf ha hab
  have hp := _root_.GD.N0205.d022327 heta hhalf ha hab.le
  have hm := hp.1.add hp.2
  have he := hm.const_mul (2 * d)
  have hq := _root_.GD.N0205.d022332 heta hhalf ha hab.le d v hv h01
  have h := intervalIntegral.integral_mono_on (show eta ≤ 1 - eta by linarith)
    (hh.sub he) hq (fun u hu => by
      have hl := _root_.GD.N0205.d022333
        (_root_.GD.N0205.d022325 (heta.trans_le hu.1) ha hab)
        (_root_.GD.N0205.d022325 (show 0 < 1 - u by linarith [hu.2]) ha hab) (v u)
      exact sub_le_sub_right hl (2 * d * (_root_.GD.N0203.d007246 a b u + _root_.GD.N0203.d007246 a b (1 - u))))
  rw [intervalIntegral.integral_sub hh he, intervalIntegral.integral_const_mul] at h
  unfold _root_.GD.N0203.d007249 _root_.GD.N0203.d007250 _root_.GD.N0205.d022324
  linarith


theorem d022335 {eta a b : ℝ} (heta : 0 < eta)
    (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a < b) (d y : ℝ)
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (hg : Measurable g)
    (h01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0203.d007249 eta a b - d * _root_.GD.N0203.d007250 eta a b ≤
      _root_.GD.N0205.d022324 eta d a b (fun u => g (u, Real.exp y)) := by
  apply _root_.GD.N0205.d022334 heta hhalf ha hab d
  · exact hg.comp (measurable_id.prodMk measurable_const)
  · intro u
    exact h01 (u, Real.exp y)


theorem d022336 {eta u : ℝ} (heta : 0 < eta)
    (hu : u ∈ Icc eta (1 - eta)) (y : ℝ) (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) :
    _root_.GD.N0163.d022211 g (u, Real.exp y) =
      g ⟨(u, Real.exp y), ⟨⟨heta.trans_le hu.1, by linarith [hu.2]⟩, Real.exp_pos y⟩⟩ :=
  _root_.GD.N0163.d022212 g
    ⟨(u, Real.exp y), ⟨⟨heta.trans_le hu.1, by linarith [hu.2]⟩, Real.exp_pos y⟩⟩


theorem d022337 {eta a b : ℝ} (heta : 0 < eta)
    (hhalf : eta ≤ 1 / 2) (ha : 0 < a) (hab : a < b) (d y : ℝ)
    (g : _root_.GD.N0232.N0720.N1436.d013218 → ℝ) (hg : Measurable g)
    (h01 : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0203.d007249 eta a b - d * _root_.GD.N0203.d007250 eta a b ≤
      _root_.GD.N0205.d022324 eta d a b (fun u => _root_.GD.N0163.d022211 g (u, Real.exp y)) :=
  _root_.GD.N0205.d022335 heta hhalf ha hab d y (_root_.GD.N0163.d022211 g)
    (_root_.GD.N0163.d022213 g hg)
    (_root_.GD.N0163.d022214 g h01)

end
end GD.N0205

#print axioms _root_.GD.N0205.d022325
#print axioms _root_.GD.N0205.d022328
#print axioms _root_.GD.N0205.d022331
#print axioms _root_.GD.N0205.d022332
#print axioms _root_.GD.N0205.d022334
#print axioms _root_.GD.N0205.d022337
