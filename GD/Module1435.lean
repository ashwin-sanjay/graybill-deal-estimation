import GD.Module1341
import GD.Module1280
import GD.Module0804

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace GD.N0066
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0981
open _root_.GD.N0232.N0719.N0885 _root_.GD.N0232.N0719.N0980
open _root_.GD.N0232.N0719.N0997 _root_.GD.N0232.N0719.N0932
open _root_.GD.N0156.N0444
open _root_.GD.N0232.N0719.N0963 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0232.N0719.N0969
open _root_.GD.N0230.N0611

variable {k : ℕ} [NeZero k] (sizes : Fin k → ℕ)

def d022826 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) : _root_.GD.N0232.N0719.N0981.d020643 sizes → ℝ≥0 :=
  _root_.GD.N0232.N0719.N0981.d020658 sizes (fun i => _root_.GD.N0232.N0719.N0932.d009193 (θ.scale i))

omit [NeZero k] in
theorem d022827 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (i : _root_.GD.N0232.N0719.N0981.d020643 sizes) :
    0 < _root_.GD.N0066.d022826 sizes θ i :=
  pos_iff_ne_zero.mpr (_root_.GD.N0232.N0719.N0932.d009196 (θ.scale_pos i.1).ne')

omit [NeZero k] in
theorem d022828 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    MeasurePreserving (_root_.GD.N0232.N0719.N0981.d020645 sizes) (_root_.GD.N0232.N0719.N0980.d009697 θ.location (_root_.GD.N0066.d022826 sizes θ))
      (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) := by
  rw [_root_.GD.N0156.N0444.d020668 sizes θ]
  simpa [_root_.GD.N0232.N0719.N0981.d020645, _root_.GD.N0232.N0719.N0980.d009697, _root_.GD.N0066.d022826, _root_.GD.N0232.N0719.N0981.d020658] using
    (_root_.GD.N0232.N0719.N0997.d019803
      (fun (i : Fin k) (_ : Fin (sizes i)) => gaussianReal θ.location (_root_.GD.N0232.N0719.N0932.d009193 (θ.scale i)))).symm

omit [NeZero k] in
theorem d022829 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    (_root_.GD.N0232.N0719.N0885.d009322 (_root_.GD.N0066.d022826 sizes θ))⁻¹ = _root_.GD.N0232.N0719.N0963.d012141 k sizes θ := by
  change (∑ i : _root_.GD.N0232.N0719.N0981.d020643 sizes, (θ.scale i.1 ^ 2)⁻¹)⁻¹ = _
  simp [Fintype.sum_sigma, _root_.GD.N0232.N0719.N0963.d012141,
    _root_.GD.N0232.N0719.N0838.d012097,
    _root_.GD.N0232.N0719.N0838.d012096, div_eq_mul_inv]

def d022830 (θ : _root_.GD.N0232.N0719.N0859.d010809 k) (z : _root_.GD.N0232.N0719.N0859.d010811 k sizes) : ℝ :=
  _root_.GD.N0232.N0719.N0980.d009698 (_root_.GD.N0066.d022826 sizes θ) ((_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z)




theorem d022831
    (hn : ∀ i, 0 < sizes i) (θ : _root_.GD.N0232.N0719.N0859.d010809 k)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hf : Measurable f)
    (he : ∀ c : ℝ, ∀ z, f (fun i j => c + z i j) = c + f z)
    (hfinite : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≠ ⊤)
    (hcap : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤ ENNReal.ofReal (_root_.GD.N0232.N0719.N0963.d012141 k sizes θ)) :
    f =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] _root_.GD.N0066.d022830 sizes θ := by
  letI : Nonempty (_root_.GD.N0232.N0719.N0981.d020643 sizes) := ⟨⟨0, ⟨0, hn 0⟩⟩⟩
  have h2 := _root_.GD.N0156.N0444.d020670 sizes f hf θ hfinite
  have hmp := _root_.GD.N0066.d022828 sizes θ
  have h2flat : MemLp (f ∘ _root_.GD.N0232.N0719.N0981.d020645 sizes) 2 (_root_.GD.N0232.N0719.N0980.d009697 θ.location (_root_.GD.N0066.d022826 sizes θ)) := by
    apply (_root_.GD.N0232.N0719.N0981.d020645 sizes).memLp_map_measure_iff.mp
    rw [hmp.map_eq]
    exact h2
  rw [_root_.GD.N0156.N0444.d020671 sizes f θ h2] at hcap
  have hcapReal : (∫ z, (f z - θ.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes θ) ≤ _root_.GD.N0232.N0719.N0963.d012141 k sizes θ :=
    (ENNReal.ofReal_le_ofReal_iff (_root_.GD.N0232.N0719.N0963.d012142 k sizes θ)).mp hcap
  have hflatCap : (∫ x, ((f ∘ _root_.GD.N0232.N0719.N0981.d020645 sizes) x - θ.location) ^ 2
      ∂_root_.GD.N0232.N0719.N0980.d009697 θ.location (_root_.GD.N0066.d022826 sizes θ)) ≤
      (_root_.GD.N0232.N0719.N0885.d009322 (_root_.GD.N0066.d022826 sizes θ))⁻¹ := by
    rw [_root_.GD.N0066.d022829]
    exact (hmp.integral_comp' (fun z => (f z - θ.location) ^ 2)).trans_le hcapReal
  have hae := _root_.GD.N0066.d021734 θ.location (_root_.GD.N0066.d022826 sizes θ)
    (_root_.GD.N0066.d022827 sizes θ) (f ∘ _root_.GD.N0232.N0719.N0981.d020645 sizes) (hf.comp (_root_.GD.N0232.N0719.N0981.d020645 sizes).measurable)
    (fun c x => he c (_root_.GD.N0232.N0719.N0981.d020645 sizes x)) h2flat hflatCap
  have hraw := hmp.symm.quasiMeasurePreserving.ae hae
  filter_upwards [hraw] with z hz
  change f z = _root_.GD.N0232.N0719.N0980.d009698 (_root_.GD.N0066.d022826 sizes θ) ((_root_.GD.N0232.N0719.N0981.d020645 sizes).symm z)
  simpa only [Function.comp_def, MeasurableEquiv.apply_symm_apply] using hz

def d022832 : _root_.GD.N0232.N0719.N0859.d010809 k where
  location := 0
  scale i := if i = 0 then 2 else 1
  scale_pos i := by split_ifs <;> norm_num




theorem d022833
    (hk : 2 ≤ k) (hn : ∀ i, 0 < sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) (hf : Measurable f)
    (he : ∀ c : ℝ, ∀ z, f (fun i j => c + z i j) = c + f z)
    (hcap0 : _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) f ≤
      ENNReal.ofReal (_root_.GD.N0232.N0719.N0963.d012141 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k)))
    (hcap1 : _root_.GD.N0232.N0719.N0859.d010840 k sizes (_root_.GD.N0066.d022832 (k := k)) f ≤
      ENNReal.ofReal (_root_.GD.N0232.N0719.N0963.d012141 k sizes (_root_.GD.N0066.d022832 (k := k)))) : False := by
  letI : Nonempty (_root_.GD.N0232.N0719.N0981.d020643 sizes) := ⟨⟨0, ⟨0, hn 0⟩⟩⟩
  let θ₀ := _root_.GD.N0232.N0719.N0859.d010810 k
  let θ₁ := _root_.GD.N0066.d022832 (k := k)
  have h0 := _root_.GD.N0066.d022831 sizes hn θ₀ f hf he
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcap0) hcap0
  have h1 := _root_.GD.N0066.d022831 sizes hn θ₁ f hf he
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcap1) hcap1
  have hac : _root_.GD.N0232.N0719.N0859.d010812 k sizes θ₀ ≪ _root_.GD.N0232.N0719.N0859.d010812 k sizes θ₁ :=
    (_root_.GD.N0232.N0719.d009183 k sizes
      θ₁.location θ₁.scale θ₁.scale_pos).2
  have horaw := h0.symm.trans (hac.ae_le h1)
  have hoflat := (_root_.GD.N0066.d022828 sizes θ₀).quasiMeasurePreserving.ae horaw
  have hoeq : _root_.GD.N0232.N0719.N0980.d009698 (_root_.GD.N0066.d022826 sizes θ₀) =ᵐ[_root_.GD.N0232.N0719.N0980.d009697 0 (_root_.GD.N0066.d022826 sizes θ₀)]
      _root_.GD.N0232.N0719.N0980.d009698 (_root_.GD.N0066.d022826 sizes θ₁) := by
    filter_upwards [hoflat] with x hx
    simpa only [_root_.GD.N0066.d022830, MeasurableEquiv.symm_apply_apply] using hx
  obtain ⟨c, _, hprop⟩ := (_root_.GD.N0066.d021737 0
    (_root_.GD.N0066.d022826 sizes θ₀) (_root_.GD.N0066.d022826 sizes θ₀) (_root_.GD.N0066.d022826 sizes θ₁)
    (_root_.GD.N0066.d022827 sizes θ₀) (_root_.GD.N0066.d022827 sizes θ₀) (_root_.GD.N0066.d022827 sizes θ₁)).mp hoeq
  let a : Fin k := ⟨1, by omega⟩
  have ha : a ≠ 0 := by intro h; have := congrArg Fin.val h; simp [a] at this
  have hp0 := hprop ⟨0, ⟨0, hn 0⟩⟩
  have hp1 := hprop ⟨a, ⟨0, hn a⟩⟩
  change ((if (0 : Fin k) = 0 then 2 else 1) : ℝ) ^ 2 = c * 1 ^ 2 at hp0
  change ((if a = 0 then 2 else 1) : ℝ) ^ 2 = c * 1 ^ 2 at hp1
  norm_num [ha] at hp0 hp1
  linarith



theorem d022834
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012185 k sizes)
    (hcap : _root_.GD.N0232.N0719.N0962.d012187 k sizes f ≤ 1) : False := by
  have hraw (θ : _root_.GD.N0232.N0719.N0859.d010809 k) : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤
      ENNReal.ofReal (_root_.GD.N0232.N0719.N0963.d012141 k sizes θ) := by
    have hbound : _root_.GD.N0232.N0719.N0962.d012186 k sizes θ f ≤ 1 :=
      (le_iSup (fun θ => _root_.GD.N0232.N0719.N0962.d012186 k sizes θ f) θ).trans hcap
    have h := (_root_.GD.N0232.N0719.N0962.d012192 k sizes (by omega)
      (fun i => by have := hn i; omega) 1 (by norm_num) θ f).mp
      (by simpa only [ENNReal.ofReal_one] using hbound)
    simpa only [one_mul] using h
  have he : ∀ c : ℝ, ∀ z, f (fun i j => c + z i j) = c + f z := by
    intro c z
    have h := hf.2 c 1 (by norm_num) z
    change f (fun i j => c + 1 * z i j) = c + 1 * f z at h
    simpa only [one_mul] using h
  exact _root_.GD.N0066.d022833 sizes (by omega)
    (fun i => by have := hn i; omega) f hf.1 he (hraw _) (hraw _)

omit [NeZero k] in



theorem d022835
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) : 1 < _root_.GD.N0232.N0719.N0962.d012188 k sizes := by
  letI : NeZero k := ⟨by omega⟩
  by_contra hnot
  have hle : _root_.GD.N0232.N0719.N0962.d012188 k sizes ≤ 1 := le_of_not_gt hnot
  obtain ⟨f, hf, hval⟩ := _root_.GD.N0232.N0719.N0969.d012209 k sizes hk hn
  exact _root_.GD.N0066.d022834 sizes hk hn f hf.1 (by rw [hval]; exact hle)

omit [NeZero k] in


theorem d022836
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    ¬ ∃ f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ, Measurable f ∧
      ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤ ENNReal.ofReal (_root_.GD.N0232.N0719.N0963.d012141 k sizes θ) := by
  letI : NeZero k := ⟨by omega⟩
  rintro ⟨f, hf, hcap⟩
  have hw : _root_.GD.N0232.N0719.N0962.d012187 k sizes f ≤ 1 := by
    apply iSup_le
    intro θ
    rw [← ENNReal.ofReal_one]
    apply (_root_.GD.N0232.N0719.N0962.d012192 k sizes (by omega)
      (fun i => by have := hn i; omega) 1 (by norm_num) θ f).mpr
    simpa only [one_mul] using hcap θ
  have hv := _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes)
    (show f ∈ _root_.GD.N0232.N0719.N0962.d012184 k sizes from hf)
  exact (not_le_of_gt (_root_.GD.N0066.d022835 sizes hk hn)) (hv.trans hw)

end
end GD.N0066

#print axioms _root_.GD.N0066.d022831
#print axioms _root_.GD.N0066.d022833
#print axioms _root_.GD.N0066.d022835
#print axioms _root_.GD.N0066.d022836
