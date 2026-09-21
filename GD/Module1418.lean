import GD.Module1224








set_option autoImplicit false
set_option warningAsError true
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace GD.N0232.N0719.N0941
noncomputable section
open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0972 _root_.GD.N0232.N0719.N0973
open _root_.GD.N0232.N0719.N0844 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0230.N0611
open _root_.GD.N0232.N0719.N0974

variable (k : ℕ) (sizes : Fin k → ℕ) (hk : 3 ≤ k) (hn : ∀ i, 2 ≤ sizes i)

def d020687 (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : ℝ :=
  (∑ i, (sizes i : ℝ) / theta.scale i ^ 2)⁻¹ / _root_.GD.N0232.N0719.N0972.d012340 k sizes theta

include hk hn



theorem d020688
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hf : Measurable f)
    (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta f ≤
      ENNReal.ofReal (c * _root_.GD.N0232.N0719.N0972.d012340 k sizes theta)) :
    ∀ theta, _root_.GD.N0232.N0719.N0941.d020687 k sizes theta ≤ c := by
  obtain ⟨e, hem, heq, heb⟩ := _root_.GD.N0232.N0719.N0843.d012245
    k sizes (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hn) hk hn c hc f hf hb
  have he : ∀ b : ℝ, ∀ x, e (fun i j => b + x i j) = b + e x := by
    intro b x
    let g : _root_.GD.N0232.N0719.N0946.d009229 := ⟨b, 0⟩
    have h := heq g x
    have h' : e (_root_.GD.N0232.N0719.N0900.d009095 k sizes b 1 x) = b + e x := by
      simpa [g, _root_.GD.N0232.N0719.N0946.d009258,
        _root_.GD.N0232.N0719.N0946.d009229.d009244,
        _root_.GD.N0232.N0719.N0946.d009229.d009239,
        _root_.GD.N0232.N0719.N0946.d009229.shift] using h
    have hfun : _root_.GD.N0232.N0719.N0900.d009095 k sizes b 1 x = (fun i j => b + x i j) := by
      funext i j
      change b + 1 * x i j = b + x i j
      ring
    rw [hfun] at h'
    exact h'
  intro theta
  have hpos := _root_.GD.N0232.N0719.N0972.d012342 k sizes hk hn theta
  have hr := _root_.GD.N0232.N0719.N0974.d019823 sizes theta e hem
    (c * _root_.GD.N0232.N0719.N0972.d012340 k sizes theta) (mul_nonneg hc hpos.le) (heb theta)
  have ho := _root_.GD.N0232.N0719.N0974.d019819 sizes (by omega)
    (fun i => by have := hn i; omega) theta e hem he hr.1
  exact (div_le_iff₀ hpos).mpr (by simpa [mul_comm] using ho.trans hr.2)



theorem d020689
    (theta : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (hsat : Tendsto (fun n => _root_.GD.N0232.N0719.N0941.d020687 k sizes (theta n)) atTop (𝓝 1))
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hf : Measurable f)
    (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta f ≤
      ENNReal.ofReal (c * _root_.GD.N0232.N0719.N0972.d012340 k sizes theta)) : 1 ≤ c := by
  exact le_of_tendsto hsat (Eventually.of_forall fun n =>
    _root_.GD.N0232.N0719.N0941.d020688 k sizes hk hn f hf c hc hb (theta n))



theorem d020690
    (theta : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (hsat : Tendsto (fun n => _root_.GD.N0232.N0719.N0941.d020687 k sizes (theta n)) atTop (𝓝 1)) :
    _root_.GD.N0232.N0719.N0973.d012377 k sizes hk hn = 1 := by
  obtain ⟨e, _, heD, hvD, _, hv1⟩ :=
    _root_.GD.N0232.N0719.N0972.d012350 k sizes hk hn
  let M := _root_.GD.N0232.N0719.N0844.d012247 k sizes
    (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hn) e
  have hM : M ≠ ⊤ := ne_top_of_le_ne_top (by simp) hv1
  have hcap : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta e ≤
      ENNReal.ofReal (M.toReal * _root_.GD.N0232.N0719.N0972.d012340 k sizes theta) := by
    intro theta
    apply (_root_.GD.N0232.N0719.N0844.d012250 k sizes
      (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hn) (by omega)
      (fun i => by have := hn i; omega)
      M.toReal ENNReal.toReal_nonneg theta e).mp
    rw [ENNReal.ofReal_toReal hM]
    exact le_iSup (fun theta => _root_.GD.N0232.N0719.N0844.d012246 k sizes
      (_root_.GD.N0232.N0719.N0972.d012343 k sizes hk hn) theta e) theta
  have hge := _root_.GD.N0232.N0719.N0941.d020689 k sizes hk hn theta hsat e heD.1
    M.toReal ENNReal.toReal_nonneg hcap
  have hreal : M.toReal = 1 := le_antisymm
    (by simpa using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) hv1) hge
  have hone : M = 1 := by rw [← ENNReal.ofReal_toReal hM, hreal]; norm_num
  exact hvD.symm.trans hone

theorem d020691
    (theta : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (hsat : Tendsto (fun n => _root_.GD.N0232.N0719.N0941.d020687 k sizes (theta n)) atTop (𝓝 1)) :
    _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hn (_root_.GD.N0232.N0719.N0962.d012190 k sizes) = 0 ∧
      _root_.GD.N0232.N0719.N0973.d012376 k sizes hk hn (_root_.GD.N0232.N0719.N0962.d012191 k sizes) = 0 := by
  obtain ⟨_, _, _, hD, hE, _, _⟩ := _root_.GD.N0232.N0719.N0973.d012380 k sizes hk hn
  rw [_root_.GD.N0232.N0719.N0941.d020690 k sizes hk hn theta hsat] at hD hE
  simpa using And.intro hD hE



theorem d020692
    (theta : ℕ → _root_.GD.N0232.N0719.N0859.d010809 k)
    (hsat : Tendsto (fun n => _root_.GD.N0232.N0719.N0941.d020687 k sizes (theta n)) atTop (𝓝 1))
    (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hf : Measurable f)
    (hb : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 k sizes theta f ≤
      _root_.GD.N0232.N0719.N0859.d010840 k sizes theta (_root_.GD.N0232.N0719.N0859.d010815 k sizes)) :
    _root_.GD.N0232.N0719.N0973.d012375 k sizes hk hn f = 0 := by
  let gamma := _root_.GD.N0232.N0719.N0972.d012343 k sizes hk hn
  let r := _root_.GD.N0232.N0719.N0844.d012246 k sizes gamma
  have hfinite : f ∈ _root_.GD.N0232.N0719.N0962.d012190 k sizes := by
    refine ⟨hf, fun theta => ?_⟩
    apply ne_top_of_le_ne_top _ (hb theta)
    rw [_root_.GD.N0232.N0719.N0972.d012341 k sizes hk hn]
    exact ENNReal.ofReal_ne_top
  have hpoint (theta : _root_.GD.N0232.N0719.N0859.d010809 k) : r theta f ≤ 1 := by
    have h := hb theta
    rw [_root_.GD.N0232.N0719.N0972.d012341 k sizes hk hn] at h
    simpa only [ENNReal.ofReal_one, r] using
      (_root_.GD.N0232.N0719.N0844.d012250 k sizes gamma
      (by omega) (fun i => by have := hn i; omega)
      1 (by norm_num) theta f).mpr (by simpa [gamma, _root_.GD.N0232.N0719.N0972.d012343] using h)
  have hle : _root_.GD.N0230.N0611.d003516 r f ≤ 1 := iSup_le hpoint
  have hge : 1 ≤ _root_.GD.N0230.N0611.d003516 r f := by
    rw [← _root_.GD.N0232.N0719.N0941.d020690 k sizes hk hn theta hsat]
    exact _root_.GD.N0230.N0611.d003520 r hfinite
  have heq : _root_.GD.N0230.N0611.d003516 r f = 1 := le_antisymm hle hge
  haveI : Nonempty (_root_.GD.N0232.N0719.N0859.d010809 k) := ⟨_root_.GD.N0232.N0719.N0859.d010810 k⟩
  have h := _root_.GD.N0230.N0686.d003548 r f
    (ne_top_of_le_ne_top (by simp) hle)
  rw [heq] at h
  simpa [_root_.GD.N0232.N0719.N0973.d012375, r, gamma] using h

end
end GD.N0232.N0719.N0941

#print axioms _root_.GD.N0232.N0719.N0941.d020688
#print axioms _root_.GD.N0232.N0719.N0941.d020689
#print axioms _root_.GD.N0232.N0719.N0941.d020690
#print axioms _root_.GD.N0232.N0719.N0941.d020691
#print axioms _root_.GD.N0232.N0719.N0941.d020692
