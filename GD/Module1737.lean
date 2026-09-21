import GD.Module1460
import GD.Module1732
import GD.Module1369
import GD.Module0247

set_option autoImplicit false
set_option warningAsError true
open MeasureTheory Set
open scoped ENNReal

namespace GD.N0213.N0524
noncomputable section
open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0963 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0232.N0719.N0970 _root_.GD.N0232.N0719.N0972
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0611
open _root_.GD.N0230.N0707
open _root_.GD.N0213.N0502 _root_.GD.N0213.N0515 _root_.GD.N0213.N0492

variable (k : ℕ) (sizes : Fin k → ℕ)

theorem d028846
    (hk : 0 < k) (hn : ∀ i, 0 < sizes i)
    {f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) :
    _root_.GD.N0232.N0719.N0962.d012187 k sizes f ≠ 0 := by
  intro hzero
  let θ₁ : _root_.GD.N0232.N0719.N0859.d010809 k := ⟨1, fun _ => 1, fun _ => zero_lt_one⟩
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010812 k sizes θ₁) := by
    unfold _root_.GD.N0232.N0719.N0859.d010812
    infer_instance
  apply _root_.GD.N0230.N0707.d003550
    (_root_.GD.N0232.N0719.N0859.d010813 k sizes) (_root_.GD.N0232.N0719.N0859.d010812 k sizes)
    (_root_.GD.N0232.N0719.N0859.d010809.location (k := k)) (_root_.GD.N0232.N0719.N0859.d010814 k sizes)
    (_root_.GD.N0232.N0719.N0859.d010810 k) θ₁ rfl rfl rfl
  intro c _hc
  refine ⟨_root_.GD.N0232.N0719.N0970.d012312 k sizes f hf, fun θ => ?_⟩
  change _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (_root_.GD.N0232.N0719.N0970.d012312 k sizes f hf) ≤ ENNReal.ofReal c
  rw [_root_.GD.N0232.N0719.N0970.d012313]
  have hz : _root_.GD.N0232.N0719.N0962.d012186 k sizes θ f ≤ ENNReal.ofReal 0 := by
    rw [ENNReal.ofReal_zero, ← hzero]
    exact le_iSup (fun θ => _root_.GD.N0232.N0719.N0962.d012186 k sizes θ f) θ
  have hr := (_root_.GD.N0232.N0719.N0962.d012192 k sizes hk hn 0 le_rfl θ f).mp hz
  simp only [zero_mul, ENNReal.ofReal_zero] at hr
  exact hr.trans bot_le

theorem d028847
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)
    (γ : _root_.GD.N0232.N0719.N0843.d012215 k) (C : ℝ) (hC : 0 < C)
    {f : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hf : f ∈ _root_.GD.N0213.N0502.d022050 k sizes)
    (hcap : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤ ENNReal.ofReal (C * γ.value θ)) :
    ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes, _root_.GD.N0232.N0719.N0970.d012309 k sizes e ∧
      _root_.GD.N0232.N0719.N0970.d012310 k sizes e ∧
      ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ e ≤ ENNReal.ofReal (C * γ.value θ) := by
  let η := _root_.GD.N0232.N0719.N0972.d012345 k (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hn) γ 1 C zero_lt_one hC
  have hbound : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤ ENNReal.ofReal (1 * η.value θ) := by
    intro θ
    simp only [η, _root_.GD.N0232.N0719.N0972.d012345, _root_.GD.N0232.N0719.N0972.d012343, one_mul, ENNReal.ofReal_min, le_min_iff]
    exact ⟨by simpa only [_root_.GD.N0232.N0719.N0972.d012341 k sizes hk hn] using hf.2 θ, hcap θ⟩
  obtain ⟨a, ham, hae, hab⟩ := _root_.GD.N0232.N0719.N0843.d012245
    k sizes η hk hn 1 zero_le_one f hf.1 hbound
  have haboth (θ) : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ a ≤ _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0232.N0719.N0859.d010815 k sizes) ∧
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ a ≤ ENNReal.ofReal (C * γ.value θ) := by
    have h := hab θ
    simpa only [η, _root_.GD.N0232.N0719.N0972.d012345, _root_.GD.N0232.N0719.N0972.d012343, one_mul, ENNReal.ofReal_min,
      le_min_iff, _root_.GD.N0232.N0719.N0972.d012341 k sizes hk hn] using h
  have haf : a ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes := _root_.GD.N0213.N0502.d022053 k sizes hk hn
    ⟨ham, fun θ => (haboth θ).1⟩
  have hant : ¬ _root_.GD.N0232.N0719.N0970.d012309 k sizes a := by
    intro ht
    exact _root_.GD.N0213.N0492.d028822 sizes hk hn
      ⟨ham, hae, haf.2, ht⟩ (fun θ => (haboth θ).1)
  obtain ⟨e, he, het, hes⟩ := (_root_.GD.N0213.N0515.d023050 k sizes haf).mp hant
  exact ⟨e, he, het, fun θ => (hes θ).trans_le (haboth θ).1,
    fun θ => (hes θ).le.trans (haboth θ).2⟩

theorem d028848
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0213.N0502.d022051 k sizes ≠ 0 := by
  obtain ⟨f, hf, hv⟩ := _root_.GD.N0213.N0502.d022060 k sizes hk hn
  rw [← hv]
  exact _root_.GD.N0213.N0524.d028846 k sizes (by omega)
    (fun i => by have := hn i; omega) (_root_.GD.N0213.N0502.d022053 k sizes hk hn hf)

theorem d028849
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes, _root_.GD.N0232.N0719.N0970.d012309 k sizes e ∧
      _root_.GD.N0232.N0719.N0970.d012310 k sizes e ∧
      _root_.GD.N0232.N0719.N0962.d012187 k sizes e = _root_.GD.N0213.N0502.d022051 k sizes := by
  by_cases htop : _root_.GD.N0213.N0502.d022051 k sizes = ⊤
  · let d := _root_.GD.N0232.N0719.N0859.d010816 k sizes hk hn
    have hd : d ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes := by
      have h := _root_.GD.N0232.N0719.N0968.d012201 k sizes hk hn
      exact ⟨h.1.1, h.2⟩
    let e := _root_.GD.N0232.N0719.N0970.d012314 k sizes d hd
    have he := _root_.GD.N0232.N0719.N0970.d012316 k sizes d hd
    have hs := _root_.GD.N0232.N0719.N0970.d012321 k sizes d hd (_root_.GD.N0232.N0719.N0970.d012329 k sizes hk hn)
    refine ⟨e, he, _root_.GD.N0232.N0719.N0970.d012317 k sizes d hd, hs, le_antisymm ?_ ?_⟩
    · rw [htop]; exact le_top
    · exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes)
        (show e ∈ _root_.GD.N0213.N0502.d022050 k sizes from ⟨he.1, fun θ => (hs θ).le⟩)
  · let v := (_root_.GD.N0213.N0502.d022051 k sizes).toReal
    have hv : 0 < v := ENNReal.toReal_pos (_root_.GD.N0213.N0524.d028848 k sizes hk hn) htop
    have hvEq : ENNReal.ofReal v = _root_.GD.N0213.N0502.d022051 k sizes := ENNReal.ofReal_toReal htop
    obtain ⟨f, hf, hvalue⟩ := _root_.GD.N0213.N0502.d022060 k sizes hk hn
    have hcap (θ) : _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f ≤ ENNReal.ofReal (v * _root_.GD.N0232.N0719.N0963.d012141 k sizes θ) := by
      apply (_root_.GD.N0232.N0719.N0962.d012192 k sizes (by omega)
        (fun i => by have := hn i; omega) v hv.le θ f).mp
      rw [hvEq, ← hvalue]
      exact le_iSup (fun θ => _root_.GD.N0232.N0719.N0962.d012186 k sizes θ f) θ
    obtain ⟨e, he, het, hes, hecap⟩ := _root_.GD.N0213.N0524.d028847 k sizes hk hn
      (_root_.GD.N0232.N0719.N0972.d012344 k sizes (by omega) (fun i => by have := hn i; omega)) v hv hf hcap
    refine ⟨e, he, het, hes, le_antisymm ?_ ?_⟩
    · rw [← hvEq]
      exact iSup_le (fun θ => (_root_.GD.N0232.N0719.N0962.d012192 k sizes (by omega)
        (fun i => by have := hn i; omega) v hv.le θ e).mpr (hecap θ))
    · exact _root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes)
        (show e ∈ _root_.GD.N0213.N0502.d022050 k sizes from ⟨he.1, fun θ => (hes θ).le⟩)

theorem d028850
    (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i) :
    _root_.GD.N0213.N0502.d022051 k sizes = _root_.GD.N0232.N0719.N0962.d012188 k sizes ↔
      ∃ e ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes, _root_.GD.N0232.N0719.N0970.d012309 k sizes e ∧
        _root_.GD.N0232.N0719.N0970.d012310 k sizes e ∧
        _root_.GD.N0232.N0719.N0962.d012187 k sizes e = _root_.GD.N0232.N0719.N0962.d012188 k sizes := by
  constructor
  · intro h
    simpa only [h] using _root_.GD.N0213.N0524.d028849 k sizes hk hn
  · rintro ⟨e, he, _, hes, hev⟩
    apply le_antisymm
    · exact (_root_.GD.N0230.N0611.d003520 (_root_.GD.N0232.N0719.N0962.d012186 k sizes)
        (show e ∈ _root_.GD.N0213.N0502.d022050 k sizes from ⟨he.1, fun θ => (hes θ).le⟩)).trans_eq hev
    · exact _root_.GD.N0213.N0502.d022062 k sizes

end
end GD.N0213.N0524

#print axioms _root_.GD.N0213.N0524.d028846
#print axioms _root_.GD.N0213.N0524.d028847
#print axioms _root_.GD.N0213.N0524.d028848
#print axioms _root_.GD.N0213.N0524.d028849
#print axioms _root_.GD.N0213.N0524.d028850
