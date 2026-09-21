import GD.Module0559
import GD.Module1888

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace GD.N0149.N0432
noncomputable section
open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1089
open _root_.GD.N0082.N0334
open _root_.GD.N0082.N0335
open _root_.GD.N0082.N0336
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0076.N0313
open _root_.GD.N0149.N0433

def d030808 : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ := _root_.GD.N0082.N0335.d030724 3 3 _root_.GD.N0232.N0720.N1089.d003092

theorem d030809 : _root_.GD.N0149.N0432.d030808 ∈ _root_.GD.N0232.N0720.N1256.d015551 3 3 :=
  _root_.GD.N0082.N0335.d030729 3 3 (by omega) (by omega)
    _root_.GD.N0232.N0720.N1089.d003092 _root_.GD.N0149.N0432.d008282 _root_.GD.N0149.N0432.d008281

theorem d030810 (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0076.N0313.d030568 3 3 (by omega) (by omega) θ _root_.GD.N0149.N0432.d030808 =
      ENNReal.ofReal (_root_.GD.N0149.N0432.d008286 (_root_.GD.N0082.N0336.d030741 θ)) := by
  unfold _root_.GD.N0076.N0313.d030568 _root_.GD.N0149.N0432.d030808
  rw [_root_.GD.N0082.N0336.d030746 _root_.GD.N0232.N0720.N1089.d003092 _root_.GD.N0149.N0432.d008282
    _root_.GD.N0149.N0432.d008281 θ, _root_.GD.N0082.N0336.d030750]
  have hbase : 0 < _root_.GD.N0082.N0336.d030743 θ * (1 + _root_.GD.N0082.N0334.d008258 id (_root_.GD.N0082.N0336.d030741 θ)) :=
    mul_pos (_root_.GD.N0082.N0336.d030744 θ) (by linarith [_root_.GD.N0082.N0334.d008268 id (_root_.GD.N0082.N0336.d030741 θ)])
  rw [← ENNReal.ofReal_div_of_pos hbase]
  congr 1
  exact mul_div_mul_left _ _ (_root_.GD.N0082.N0336.d030744 θ).ne'

theorem d030811 {A : Type*} {F : Filter A}
    (θ : A → _root_.GD.N0232.N0720.N1080.d014168) {b : ℝ} (hb : b=0 ∨ b=1)
    (hθ : Tendsto (fun x => _root_.GD.N0082.N0336.d030741 (θ x)) F (𝓝 b)) :
    Tendsto (fun x => _root_.GD.N0076.N0313.d030568 3 3 (by omega) (by omega) (θ x) _root_.GD.N0149.N0432.d030808)
      F (𝓝 (ENNReal.ofReal (1/2+Real.pi/8))) := by
  have hbI : b ∈ Icc (0 : ℝ) 1 := by rcases hb with rfl | rfl <;> norm_num
  have hm : ∀ᶠ x in F, _root_.GD.N0082.N0336.d030741 (θ x) ∈ Icc (0 : ℝ) 1 :=
    Eventually.of_forall fun x => ⟨(_root_.GD.N0082.N0336.d030742 (θ x)).1.le, (_root_.GD.N0082.N0336.d030742 (θ x)).2.le⟩
  have h := (_root_.GD.N0149.N0432.d008287 b hbI).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hθ,hm⟩)
  have hbv : _root_.GD.N0149.N0432.d008286 b=1/2+Real.pi/8 := by
    rcases hb with rfl | rfl
    · exact _root_.GD.N0149.N0432.d008288
    · exact _root_.GD.N0149.N0432.d008289
  rw [hbv] at h
  simpa only [_root_.GD.N0149.N0432.d030810, Function.comp_def] using ENNReal.tendsto_ofReal h

def d030812 (H : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1+_root_.GD.N0082.N0334.d008258 H t)/(1+_root_.GD.N0082.N0334.d008258 id t)

theorem d030813 (H : ℝ → ℝ) (hH : _root_.GD.N0149.N0433.d008323 H) :
    ContinuousOn (_root_.GD.N0149.N0432.d030812 H) (Icc (0 : ℝ) 1) := by
  apply ContinuousOn.div
  · exact continuousOn_const.add (_root_.GD.N0149.N0433.d008324 H hH)
  · exact continuousOn_const.add (_root_.GD.N0082.N0334.d008267 measurable_id _root_.GD.N0082.N0334.d008266)
  · intro t _
    have := _root_.GD.N0082.N0334.d008268 id t
    linarith

theorem d030814 (H : ℝ → ℝ) (hHm : Measurable H)
    (hHI : ∀ u, H u ∈ Icc (0 : ℝ) 1) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0076.N0313.d030568 3 3 (by omega) (by omega) θ (_root_.GD.N0082.N0335.d030724 3 3 H)=
      ENNReal.ofReal (_root_.GD.N0149.N0432.d030812 H (_root_.GD.N0082.N0336.d030741 θ)) := by
  unfold _root_.GD.N0076.N0313.d030568
  rw [_root_.GD.N0082.N0336.d030746 H hHm hHI θ, _root_.GD.N0082.N0336.d030750]
  have hbase : 0 < _root_.GD.N0082.N0336.d030743 θ*(1+_root_.GD.N0082.N0334.d008258 id (_root_.GD.N0082.N0336.d030741 θ)) :=
    mul_pos (_root_.GD.N0082.N0336.d030744 θ) (by linarith [_root_.GD.N0082.N0334.d008268 id (_root_.GD.N0082.N0336.d030741 θ)])
  rw [← ENNReal.ofReal_div_of_pos hbase]
  congr 1
  exact mul_div_mul_left _ _ (_root_.GD.N0082.N0336.d030744 θ).ne'

theorem d030815 {A : Type*} {F : Filter A}
    (H : ℝ → ℝ) (hH : _root_.GD.N0149.N0433.d008323 H)
    (hHI : ∀ u, H u ∈ Icc (0 : ℝ) 1)
    (θ : A → _root_.GD.N0232.N0720.N1080.d014168) {b : ℝ} (hb : b=0 ∨ b=1)
    (hθ : Tendsto (fun x => _root_.GD.N0082.N0336.d030741 (θ x)) F (𝓝 b)) :
    Tendsto (fun x => _root_.GD.N0076.N0313.d030568 3 3 (by omega) (by omega) (θ x) (_root_.GD.N0082.N0335.d030724 3 3 H))
      F (𝓝 (ENNReal.ofReal ((1+_root_.GD.N0082.N0334.d008258 H b)/2))) := by
  have hbI : b ∈ Icc (0 : ℝ) 1 := by rcases hb with rfl | rfl <;> norm_num
  have hm : ∀ᶠ x in F, _root_.GD.N0082.N0336.d030741 (θ x) ∈ Icc (0 : ℝ) 1 :=
    Eventually.of_forall fun x => ⟨(_root_.GD.N0082.N0336.d030742 (θ x)).1.le, (_root_.GD.N0082.N0336.d030742 (θ x)).2.le⟩
  have h := (_root_.GD.N0149.N0432.d030813 H hH b hbI).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hθ,hm⟩)
  have hid : _root_.GD.N0082.N0334.d008258 id b=1 := by
    rcases hb with rfl | rfl
    · exact _root_.GD.N0082.N0334.d008273
    · simpa using (_root_.GD.N0082.N0334.d008276 (H := id) (fun _ => rfl) 0).trans _root_.GD.N0082.N0334.d008273
  have hv : _root_.GD.N0149.N0432.d030812 H b=(1+_root_.GD.N0082.N0334.d008258 H b)/2 := by norm_num [_root_.GD.N0149.N0432.d030812,hid]
  rw [hv] at h
  simpa only [_root_.GD.N0149.N0432.d030814 H hH.1 hHI, Function.comp_def] using ENNReal.tendsto_ofReal h

theorem d030816 (H : ℝ → ℝ)
    (hH : _root_.GD.N0149.N0433.d008323 H) (hHI : ∀ u, H u ∈ Icc (0 : ℝ) 1)
    {c : ℝ} (hc : 0 ≤ c)
    (hcap : ∀ θ : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0076.N0313.d030568 3 3 (by omega) (by omega) θ (_root_.GD.N0082.N0335.d030724 3 3 H) ≤ ENNReal.ofReal c) :
    1/2+Real.pi/8 ≤ c := by
  have hi : ∀ t ∈ Ioo (0 : ℝ) 1, _root_.GD.N0149.N0432.d030812 H t ≤ c := by
    intro t ht
    let θ := _root_.GD.N0232.N0720.N1219.d017942 3 3 (by omega) (by omega) t ht
    have htθ : _root_.GD.N0082.N0336.d030741 θ=t :=
      _root_.GD.N0232.N0720.N1219.d017949 3 3
        (by omega) (by omega) t ht
    have h := hcap θ
    rw [_root_.GD.N0149.N0432.d030814 H hH.1 hHI, htθ] at h
    exact (ENNReal.ofReal_le_ofReal_iff hc).mp h
  have he : ∀ t ∈ Icc (0 : ℝ) 1, _root_.GD.N0149.N0432.d030812 H t ≤ c := by
    intro t ht
    exact le_on_closure hi
      (by simpa only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using _root_.GD.N0149.N0432.d030813 H hH)
      continuousOn_const (by simpa only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using ht)
  have h0 := he 0 (by norm_num)
  have h1 := he 1 (by norm_num)
  have hid1 : _root_.GD.N0082.N0334.d008258 id 1=1 := by
    simpa using (_root_.GD.N0082.N0334.d008276 (H := id) (fun _ => rfl) 0).trans _root_.GD.N0082.N0334.d008273
  simp only [_root_.GD.N0149.N0432.d030812,_root_.GD.N0082.N0334.d008273,hid1] at h0 h1
  norm_num at h0 h1
  have hmin := _root_.GD.N0149.N0433.d008330.2 ⟨H,hH,rfl⟩
  exact hmin.trans (max_le h0 h1)

end
end GD.N0149.N0432

#print axioms _root_.GD.N0149.N0432.d030809
#print axioms _root_.GD.N0149.N0432.d030810
#print axioms _root_.GD.N0149.N0432.d030811
#print axioms _root_.GD.N0149.N0432.d030813
#print axioms _root_.GD.N0149.N0432.d030814
#print axioms _root_.GD.N0149.N0432.d030815
#print axioms _root_.GD.N0149.N0432.d030816
