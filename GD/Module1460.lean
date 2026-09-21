import GD.Module0809
import GD.Module0149

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped ENNReal

namespace GD.N0213.N0515
noncomputable section
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0675
open _root_.GD.N0230.N0718

variable (k : ℕ) (sizes : Fin k → ℕ)

theorem d023049
    {f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) (ht : ¬ _root_.GD.N0232.N0719.N0970.d012309 k sizes f) :
    ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes,
      ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ e < _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f := by
  classical
  unfold _root_.GD.N0232.N0719.N0970.d012309 at ht
  push Not at ht
  obtain ⟨g, hgm, hweak, θ₀, hne⟩ := ht
  have hg : g ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes :=
    ⟨hgm, fun θ => ne_top_of_le_ne_top (hf.2 θ) (hweak θ)⟩
  let p := _root_.GD.N0232.N0719.N0970.d012312 k sizes f hf
  let q := _root_.GD.N0232.N0719.N0970.d012312 k sizes g hg
  have hp (θ) : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p = _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f :=
    _root_.GD.N0232.N0719.N0970.d012313 k sizes f hf θ
  have hq (θ) : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ q = _root_.GD.N0232.N0719.N0859.d010840 k sizes θ g :=
    _root_.GD.N0232.N0719.N0970.d012313 k sizes g hg θ
  have hpAE : (p : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010813 k sizes] f :=
    (_root_.GD.N0232.N0719.N0896.d011095 k sizes f hf.1
      (hf.2 (_root_.GD.N0232.N0719.N0859.d010810 k))).coeFn_toLp
  have hqAE : (q : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) =ᵐ[
      _root_.GD.N0232.N0719.N0859.d010813 k sizes] g :=
    (_root_.GD.N0232.N0719.N0896.d011095 k sizes g hg.1
      (hg.2 (_root_.GD.N0232.N0719.N0859.d010810 k))).coeFn_toLp
  have hpq : p ≠ q := by
    intro heq
    apply hne
    exact (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ₀).ae_le
      (hqAE.symm.trans (by simpa only [heq] using hpAE))
  have hfiniteP (θ) : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p ≠ ⊤ := by rw [hp]; exact hf.2 θ
  have hfiniteQ (θ) : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ q ≠ ⊤ := by rw [hq]; exact hg.2 θ
  have hweakPQ (θ) : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ q ≤ _root_.GD.N0232.N0719.N0859.d010821 k sizes θ p := by
    rw [hp, hq]
    exact hweak θ
  have hmid : _root_.GD.N0230.N0718.d001528 p q ∈ _root_.GD.N0232.N0719.N0896.d011096 k sizes p := by
    apply _root_.GD.N0232.N0719.N0896.d011098 k sizes p (fun _ => le_rfl) hweakPQ
    all_goals norm_num
  have hfiniteMid (θ) : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (_root_.GD.N0230.N0718.d001528 p q) ≠ ⊤ :=
    ne_top_of_le_ne_top (hfiniteP θ) (hmid θ)
  have hstrict := _root_.GD.N0230.N0675.d001657
    (_root_.GD.N0232.N0719.N0859.d010812 k sizes) (_root_.GD.N0232.N0719.N0859.d010809.location (k := k))
    (_root_.GD.N0232.N0719.N0859.d010814 k sizes)
    (fun θ => (_root_.GD.N0232.N0719.d009183
      k sizes θ.location θ.scale θ.scale_pos).2)
    hfiniteP hfiniteQ
    (fun θ => ENNReal.toReal_mono (hfiniteP θ) (hweakPQ θ)) hpq
  refine ⟨_root_.GD.N0232.N0719.N0896.d011088 k sizes (_root_.GD.N0230.N0718.d001528 p q),
    ⟨_root_.GD.N0232.N0719.N0896.d011089 k sizes _, fun θ => ?_⟩, fun θ => ?_⟩
  · rw [_root_.GD.N0232.N0719.N0896.d011093]
    exact hfiniteMid θ
  · rw [_root_.GD.N0232.N0719.N0896.d011093, ← hp]
    exact (ENNReal.toReal_lt_toReal (hfiniteMid θ) (hfiniteP θ)).mp (hstrict θ)

theorem d023050
    {f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) :
    ¬ _root_.GD.N0232.N0719.N0970.d012309 k sizes f ↔
      ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes, _root_.GD.N0232.N0719.N0970.d012309 k sizes e ∧
        ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ e < _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f := by
  constructor
  · intro ht
    obtain ⟨g, hg, hstrict⟩ := _root_.GD.N0213.N0515.d023049 k sizes hf ht
    exact ⟨_root_.GD.N0232.N0719.N0970.d012314 k sizes g hg, _root_.GD.N0232.N0719.N0970.d012316 k sizes g hg,
      _root_.GD.N0232.N0719.N0970.d012317 k sizes g hg,
      fun θ => (_root_.GD.N0232.N0719.N0970.d012315 k sizes g hg θ).trans_lt (hstrict θ)⟩
  · rintro ⟨g, hg, _, hstrict⟩ ht
    have heq := ht g hg.1 (fun θ => (hstrict θ).le) (_root_.GD.N0232.N0719.N0859.d010810 k)
    have hr := _root_.GD.N0232.N0719.N0896.d011094 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) heq
    exact (hstrict (_root_.GD.N0232.N0719.N0859.d010810 k)).ne hr

end
end GD.N0213.N0515

#print axioms _root_.GD.N0213.N0515.d023049
#print axioms _root_.GD.N0213.N0515.d023050
