import GD.Module1501

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace GD.N0225.N0537
noncomputable section

open _root_.GD.N0232.N0719
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0962 _root_.GD.N0232.N0719.N0970
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0675
open _root_.GD.N0230.N0718
open _root_.GD.N0072 _root_.GD.N0225.N0538

variable {k : ℕ} (sizes : Fin k → ℕ)



theorem d023466
    {f g : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) (hg : g ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ g ≤ _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f)
    (hno : ¬ ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (fun z => (f z + g z) / 2) <
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f) :
    ∀ θ, g =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] f := by
  classical
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
  have hpq : p = q := by
    by_contra hpq
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
    have hmidAE : ((_root_.GD.N0230.N0718.d001528 p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
        _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ) =ᵐ[
        _root_.GD.N0232.N0719.N0859.d010813 k sizes] (fun z => (f z + g z) / 2) := by
      filter_upwards [Lp.coeFn_add ((1 / 2 : ℝ) • p) ((1 / 2 : ℝ) • q),
        Lp.coeFn_smul (1 / 2 : ℝ) p, Lp.coeFn_smul (1 / 2 : ℝ) q,
        hpAE, hqAE] with z hadd hps hqs hpf hqg
      simp only [_root_.GD.N0230.N0718.d001528, hadd, hps, hqs, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, hpf, hqg]
      ring
    apply hno
    intro θ
    have hrmid : _root_.GD.N0232.N0719.N0859.d010821 k sizes θ (_root_.GD.N0230.N0718.d001528 p q) =
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (fun z => (f z + g z) / 2) :=
      _root_.GD.N0232.N0719.N0896.d011094 k sizes θ
        ((_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le hmidAE)
    rw [← hrmid, ← hp]
    exact (ENNReal.toReal_lt_toReal (hfiniteMid θ) (hfiniteP θ)).mp (hstrict θ)
  intro θ
  apply (_root_.GD.N0232.N0719.N0859.d010814 k sizes θ).ae_le
  exact hqAE.symm.trans ((Filter.EventuallyEq.of_eq (congrArg
    (fun d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) =>
      (d : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ)) hpq.symm)).trans hpAE)



theorem d023467
    (C : Set (_root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ))
    {f g : _root_.GD.N0232.N0719.N0859.d010811 k sizes → ℝ}
    (hf : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes) (hg : g ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes)
    (hmid : (fun z => (f z + g z) / 2) ∈ C)
    (hadm : ¬ ∃ d ∈ C,
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d ≤ _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ d < _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f)
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ g ≤ _root_.GD.N0232.N0719.N0859.d010840 k sizes θ f) :
    ∀ θ, g =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] f := by
  apply _root_.GD.N0225.N0537.d023466 sizes hf hg hweak
  intro hstrict
  exact hadm ⟨_, hmid, fun θ => (hstrict θ).le,
    _root_.GD.N0232.N0719.N0859.d010810 k, hstrict (_root_.GD.N0232.N0719.N0859.d010810 k)⟩



theorem d023468
    (p w : (Fin k → ℝ) → Fin k → ℝ)
    (hp : Measurable p) (hw : Measurable w)
    (hpunit : ∀ t, ∑ i, p t i = 1) (hwunit : ∀ t, ∑ i, w t i = 1)
    (hpfinite : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p) ≠ ⊤)
    (hadm : ¬ ∃ v : (Fin k → ℝ) → Fin k → ℝ,
      Measurable v ∧ (∀ t, ∑ i, v t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes v) ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p)) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes v) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p))
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p)) :
    ∀ θ, _root_.GD.N0072.d023291 sizes w =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] _root_.GD.N0072.d023291 sizes p := by
  apply _root_.GD.N0225.N0537.d023466 sizes
    ⟨_root_.GD.N0072.d023295 sizes p hp, hpfinite⟩
    ⟨_root_.GD.N0072.d023295 sizes w hw,
      fun θ => ne_top_of_le_ne_top (hpfinite θ) (hweak θ)⟩ hweak
  intro hstrict
  have hm : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ
      (_root_.GD.N0072.d023291 sizes (_root_.GD.N0225.N0538.d023458 p w)) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p) := by
    rw [_root_.GD.N0225.N0538.d023462]
    exact hstrict
  exact hadm ⟨_root_.GD.N0225.N0538.d023458 p w, _root_.GD.N0225.N0538.d023459 p w hp hw,
    _root_.GD.N0225.N0538.d023460 p w hpunit hwunit, fun θ => (hm θ).le,
    _root_.GD.N0232.N0719.N0859.d010810 k, hm (_root_.GD.N0232.N0719.N0859.d010810 k)⟩

open _root_.GD.N0232.N0719.N0885 _root_.GD.N0232.N0719.N0933 _root_.GD.N0232.N0719.N0910
open _root_.GD.N0232.N0719.N0980 _root_.GD.N0232.N0719.N0900

private theorem d023469
    (m : ℝ) (v : Fin k → ℝ≥0) (hv : ∀ i, 0 < (v i : ℝ))
    (p w : Fin k → ℝ)
    (h : _root_.GD.N0232.N0719.N0885.d009311 p =ᵐ[_root_.GD.N0232.N0719.N0980.d009697 m v] _root_.GD.N0232.N0719.N0885.d009311 w) : p = w := by
  have he := integral_congr_ae h
  funext i
  have hc : cov[_root_.GD.N0232.N0719.N0885.d009311 p, fun y => y i; _root_.GD.N0232.N0719.N0980.d009697 m v] =
      cov[_root_.GD.N0232.N0719.N0885.d009311 w, fun y => y i; _root_.GD.N0232.N0719.N0980.d009697 m v] := by
    unfold covariance
    rw [he]
    apply integral_congr_ae
    filter_upwards [h] with y hy
    rw [hy]
  rw [_root_.GD.N0232.N0719.N0885.d009319, _root_.GD.N0232.N0719.N0885.d009319] at hc
  exact (mul_right_cancel₀ (hv i).ne') hc



theorem d023470
    (hn : ∀ i, 2 ≤ sizes i)
    (p w : (Fin k → ℝ) → Fin k → ℝ) (hp : Measurable p) (hw : Measurable w)
    (θ : _root_.GD.N0232.N0719.N0859.d010809 k) :
    p =ᵐ[_root_.GD.N0232.N0719.N0933.d009301 k sizes θ.scale] w ↔
      _root_.GD.N0072.d023291 sizes p =ᵐ[_root_.GD.N0232.N0719.N0859.d010812 k sizes θ] _root_.GD.N0072.d023291 sizes w := by
  constructor
  · intro h
    have hmap : p =ᵐ[(_root_.GD.N0232.N0719.N0859.d010812 k sizes θ).map (_root_.GD.N0232.N0719.N0900.d009103 k sizes)] w := by
      rw [_root_.GD.N0072.d023301 sizes hn θ]
      exact h
    have hraw := ae_of_ae_map (by fun_prop : Measurable (_root_.GD.N0232.N0719.N0900.d009103 k sizes)).aemeasurable hmap
    filter_upwards [hraw] with z hz
    simp only [_root_.GD.N0072.d023291, hz]
  · intro h
    let F : ((Fin k → ℝ) × (Fin k → ℝ)) → ℝ := fun z => _root_.GD.N0232.N0719.N0885.d009311 (p z.2) z.1
    let G : ((Fin k → ℝ) × (Fin k → ℝ)) → ℝ := fun z => _root_.GD.N0232.N0719.N0885.d009311 (w z.2) z.1
    have hF : Measurable F := by unfold F _root_.GD.N0232.N0719.N0885.d009311; fun_prop
    have hG : Measurable G := by unfold G _root_.GD.N0232.N0719.N0885.d009311; fun_prop
    have heqset : MeasurableSet {z | F z = G z} := measurableSet_eq_fun hF hG
    have hmap : F =ᵐ[(_root_.GD.N0232.N0719.N0859.d010812 k sizes θ).map (_root_.GD.N0232.N0719.N0933.d009304 k sizes)] G := by
      apply (ae_map_iff (_root_.GD.N0232.N0719.N0933.d009308 k sizes).aemeasurable heqset).mpr
      exact h
    change F =ᵐ[(_root_.GD.N0232.N0719.d009176 k sizes θ.location θ.scale).map
      (_root_.GD.N0232.N0719.N0933.d009304 k sizes)] G at hmap
    rw [_root_.GD.N0232.N0719.N0933.d009309 k sizes hn] at hmap
    letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009300 k sizes θ.location θ.scale) := by
      unfold _root_.GD.N0232.N0719.N0933.d009300
      infer_instance
    letI : IsProbabilityMeasure (_root_.GD.N0232.N0719.N0933.d009301 k sizes θ.scale) :=
      _root_.GD.N0232.N0719.N0910.d010289 sizes hn θ.scale
    have hcond := (Measure.ae_ae_comm heqset).mp (Measure.ae_ae_of_ae_prod hmap)
    filter_upwards [hcond] with t ht
    rw [_root_.GD.N0232.N0719.N0933.d009302 k sizes hn] at ht
    apply _root_.GD.N0225.N0537.d023469 θ.location
      (_root_.GD.N0232.N0719.N0885.d009329 sizes θ.scale) _ (p t) (w t) ht
    intro i
    change 0 < θ.scale i ^ 2 / (sizes i : ℝ)
    exact div_pos (sq_pos_of_pos (θ.scale_pos i))
      (by exact_mod_cast (show 0 < sizes i by have := hn i; omega))



theorem d023471
    (hn : ∀ i, 2 ≤ sizes i)
    (p w : (Fin k → ℝ) → Fin k → ℝ)
    (hp : Measurable p) (hw : Measurable w)
    (hpunit : ∀ t, ∑ i, p t i = 1) (hwunit : ∀ t, ∑ i, w t i = 1)
    (hpfinite : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p) ≠ ⊤)
    (hadm : ¬ ∃ v : (Fin k → ℝ) → Fin k → ℝ,
      Measurable v ∧ (∀ t, ∑ i, v t i = 1) ∧
      (∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes v) ≤
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p)) ∧
      ∃ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes v) <
        _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p))
    (hweak : ∀ θ, _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes w) ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes θ (_root_.GD.N0072.d023291 sizes p)) :
    ∀ θ : _root_.GD.N0232.N0719.N0859.d010809 k, w =ᵐ[_root_.GD.N0232.N0719.N0933.d009301 k sizes θ.scale] p := by
  intro θ
  apply (_root_.GD.N0225.N0537.d023470 sizes hn w p hw hp θ).mpr
  exact _root_.GD.N0225.N0537.d023468 sizes p w hp hw hpunit hwunit hpfinite
    hadm hweak θ

end
end GD.N0225.N0537

#print axioms _root_.GD.N0225.N0537.d023466
#print axioms _root_.GD.N0225.N0537.d023467
#print axioms _root_.GD.N0225.N0537.d023468
#print axioms _root_.GD.N0225.N0537.d023470
#print axioms _root_.GD.N0225.N0537.d023471
