import GD.Module1897

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace GD.N0011
noncomputable section

open _root_.GD.N0232.N0720 _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1089
open _root_.GD.N0082.N0334
open _root_.GD.N0082.N0335
open _root_.GD.N0082.N0336
open _root_.GD.N0149.N0432 _root_.GD.N0149.N0433



theorem d030817 (θ : _root_.GD.N0232.N0720.N1080.d014168) : _root_.GD.N0082.N0336.d030743 θ = _root_.GD.N0232.N0720.N1257.d015508 3 3 θ := by
  have hs : θ.scale₁ ≠ 0 := θ.scale₁_pos.ne'
  have ht : θ.scale₂ ≠ 0 := θ.scale₂_pos.ne'
  have hsum : θ.scale₁ ^ 2 + θ.scale₂ ^ 2 ≠ 0 := by positivity
  unfold _root_.GD.N0082.N0336.d030743 _root_.GD.N0082.N0336.d030741
    _root_.GD.N0232.N0720.N1067.d014408
    _root_.GD.N0107.d009046 _root_.GD.N0107.d009045
    _root_.GD.N0107.d009043 _root_.GD.N0107.d009044
    _root_.GD.N0232.N0720.N1257.d015508
  norm_num
  field_simp
  ring


theorem d030818 (H : ℝ → ℝ) (hHm : Measurable H)
    (hHI : ∀ u, H u ∈ Icc (0 : ℝ) 1) (θ : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1256.d015547 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H) =
      ENNReal.ofReal (1 + _root_.GD.N0082.N0334.d008258 H (_root_.GD.N0082.N0336.d030741 θ)) := by
  unfold _root_.GD.N0232.N0720.N1256.d015547
  rw [_root_.GD.N0082.N0336.d030746 H hHm hHI θ, ← _root_.GD.N0011.d030817]
  rw [← ENNReal.ofReal_div_of_pos (_root_.GD.N0082.N0336.d030744 θ)]
  congr 1
  exact mul_div_cancel_left₀ _ (_root_.GD.N0082.N0336.d030744 θ).ne'



theorem d030819 (H : ℝ → ℝ) (hHm : Measurable H)
    (hHI : ∀ u, H u ∈ Icc (0 : ℝ) 1) (C : ℝ) (hC : 0 ≤ C) :
    (∀ θ, _root_.GD.N0232.N0720.N1256.d015547 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H) ≤ ENNReal.ofReal C) ↔
      ∀ t ∈ Ioo (0 : ℝ) 1, 1 + _root_.GD.N0082.N0334.d008258 H t ≤ C := by
  constructor
  · intro hcap t ht
    let θ := _root_.GD.N0232.N0720.N1219.d017942 3 3 (by omega) (by omega) t ht
    have htθ : _root_.GD.N0082.N0336.d030741 θ = t :=
      _root_.GD.N0232.N0720.N1219.d017949 3 3
        (by omega) (by omega) t ht
    have h := hcap θ
    rw [_root_.GD.N0011.d030818 H hHm hHI, htθ] at h
    exact (ENNReal.ofReal_le_ofReal_iff hC).mp h
  · intro hcap θ
    rw [_root_.GD.N0011.d030818 H hHm hHI]
    exact ENNReal.ofReal_le_ofReal (hcap (_root_.GD.N0082.N0336.d030741 θ) (_root_.GD.N0082.N0336.d030742 θ))



theorem d030820 (H : ℝ → ℝ) (hH : _root_.GD.N0149.N0433.d008323 H)
    (hHI : ∀ u, H u ∈ Icc (0 : ℝ) 1) (C : ℝ) (hC : 0 ≤ C)
    (hcap : ∀ θ, _root_.GD.N0232.N0720.N1256.d015547 3 3 θ (_root_.GD.N0082.N0335.d030724 3 3 H) ≤ ENNReal.ofReal C) :
    1 + Real.pi / 4 ≤ C := by
  have hi := (_root_.GD.N0011.d030819 H hH.1 hHI C hC).mp hcap
  have he : ∀ t ∈ Icc (0 : ℝ) 1, 1 + _root_.GD.N0082.N0334.d008258 H t ≤ C := by
    intro t ht
    exact le_on_closure hi
      (by simpa only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using
        (_root_.GD.N0149.N0433.d008324 H hH).const_add 1)
      continuousOn_const
      (by simpa only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using ht)
  have h0 := he 0 (by norm_num)
  have h1 := he 1 (by norm_num)
  have hp := _root_.GD.N0149.N0433.d008329 H hH
  have hn : 0 ≤ ∫ u in Ioo (0 : ℝ) 1, _root_.GD.N0149.N0432.d008292 H u :=
    integral_nonneg (fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  linarith

theorem d030821 {A : Type*} {F : Filter A}
    (θ : A → _root_.GD.N0232.N0720.N1080.d014168) {b : ℝ} (hb : b = 0 ∨ b = 1)
    (hθ : Tendsto (fun x => _root_.GD.N0082.N0336.d030741 (θ x)) F (𝓝 b)) :
    Tendsto (fun x => _root_.GD.N0232.N0720.N1256.d015547 3 3 (θ x) _root_.GD.N0149.N0432.d030808)
      F (𝓝 (ENNReal.ofReal (1 + Real.pi / 4))) := by
  have hbI : b ∈ Icc (0 : ℝ) 1 := by rcases hb with rfl | rfl <;> norm_num
  have hm : ∀ᶠ x in F, _root_.GD.N0082.N0336.d030741 (θ x) ∈ Icc (0 : ℝ) 1 :=
    Eventually.of_forall fun x => ⟨(_root_.GD.N0082.N0336.d030742 (θ x)).1.le, (_root_.GD.N0082.N0336.d030742 (θ x)).2.le⟩
  have hc : ContinuousOn (fun t : ℝ => 1 + _root_.GD.N0082.N0334.d008258 _root_.GD.N0232.N0720.N1089.d003092 t)
      (Icc (0 : ℝ) 1) :=
    (_root_.GD.N0149.N0433.d008324 _root_.GD.N0232.N0720.N1089.d003092 _root_.GD.N0149.N0433.d008326).const_add 1
  have h := (hc b hbI).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hθ, hm⟩)
  have hbv : _root_.GD.N0082.N0334.d008258 _root_.GD.N0232.N0720.N1089.d003092 b = Real.pi / 4 := by
    rcases hb with rfl | rfl
    · exact _root_.GD.N0149.N0432.d008285
    · simpa using (_root_.GD.N0082.N0334.d008276 _root_.GD.N0149.N0432.d008283 0).trans _root_.GD.N0149.N0432.d008285
  rw [hbv] at h
  simpa only [_root_.GD.N0149.N0432.d030808, _root_.GD.N0011.d030818 _root_.GD.N0232.N0720.N1089.d003092 _root_.GD.N0149.N0432.d008282
    _root_.GD.N0149.N0432.d008281, Function.comp_def] using ENNReal.tendsto_ofReal h

end
end GD.N0011

#print axioms _root_.GD.N0011.d030817
#print axioms _root_.GD.N0011.d030818
#print axioms _root_.GD.N0011.d030819
#print axioms _root_.GD.N0011.d030820
#print axioms _root_.GD.N0011.d030821
