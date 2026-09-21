import GD.Module0813
import GD.Module0663
import GD.Module1223
import GD.Module0708









set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology

namespace GD.N0232.N0719.N0974

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0972 _root_.GD.N0232.N0719.N0973
open _root_.GD.N0232.N0719.N0844 _root_.GD.N0232.N0719.N0962
open _root_.GD.N0230.N0611
open _root_.GD.N0232.N0719.N0885 _root_.GD.N0232.N0719.N0980
open _root_.GD.N0232.N0719.N0932
open _root_.GD.N0232.N0719.N0924
open _root_.GD.N0232.N0719.N0927
open _root_.GD.N0232.N0719.N0997 (d019803)

local instance d019816 {k : ℕ} (sizes : Fin k → ℕ) (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    IsProbabilityMeasure (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
  dsimp only [_root_.GD.N0232.N0719.N0859.d010812]
  infer_instance

theorem d019817 : ∀ i, 2 ≤ _root_.GD.N0232.N0719.N0927.d009909 i := by
  intro i
  fin_cases i <;> norm_num [_root_.GD.N0232.N0719.N0927.d009909]



theorem d019818 {I : Type*} [Fintype I] [Nonempty I]
    (m : ℝ) (v : I → ℝ≥0) (hv : ∀ i, 0 < v i)
    (f : (I → ℝ) → ℝ) (hf : Measurable f)
    (he : _root_.GD.N0232.N0719.N0980.d009696 f) (h2 : MemLp f 2 (_root_.GD.N0232.N0719.N0980.d009697 m v)) :
    (_root_.GD.N0232.N0719.N0885.d009322 v)⁻¹ ≤ ∫ x, (f x - m) ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 m v := by
  rw [_root_.GD.N0232.N0719.N0980.d009703 m v hv f hf he h2]
  have horacle : (∫ x, (_root_.GD.N0232.N0719.N0980.d009698 v x - m) ^ 2 ∂_root_.GD.N0232.N0719.N0980.d009697 m v) =
      (_root_.GD.N0232.N0719.N0885.d009322 v)⁻¹ := by
    have h := _root_.GD.N0232.N0719.N0885.d009328 m v hv
    change Var[_root_.GD.N0232.N0719.N0980.d009698 v; _root_.GD.N0232.N0719.N0980.d009697 m v] = (_root_.GD.N0232.N0719.N0885.d009322 v)⁻¹ at h
    rw [variance_eq_integral (_root_.GD.N0232.N0719.N0980.d009699 v).aemeasurable, _root_.GD.N0232.N0719.N0980.d009701 m v hv] at h
    exact h
  rw [horacle]
  exact le_add_of_nonneg_right (integral_nonneg fun _ => sq_nonneg _)



theorem d019819 {k : ℕ} (sizes : Fin k → ℕ)
    (hk : 0 < k) (hn : ∀ i, 0 < sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hf : Measurable f)
    (he : ∀ c : ℝ, ∀ x, f (fun i j => c + x i j) = c + f x)
    (h2 : MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)) :
    (∑ i, (sizes i : ℝ) / theta.scale i ^ 2)⁻¹ ≤
      ∫ x, (f x - theta.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta := by
  let I := Sigma fun i : Fin k => Fin (sizes i)
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  letI : ∀ i, Nonempty (Fin (sizes i)) := fun i => Fin.pos_iff_nonempty.mp (hn i)
  letI : Nonempty I := ⟨⟨⟨0, hk⟩, ⟨0, hn ⟨0, hk⟩⟩⟩⟩
  let v : I → ℝ≥0 := fun j => _root_.GD.N0232.N0719.N0932.d009193 (theta.scale j.1)
  let e : (I → ℝ) ≃ᵐ _root_.GD.N0232.N0719.d009173 k sizes :=
    MeasurableEquiv.piCurry (fun (i : Fin k) (_ : Fin (sizes i)) => ℝ)
  have hphys : _root_.GD.N0232.N0719.N0859.d010812 k sizes theta =
      Measure.pi (fun i => Measure.pi (fun _ : Fin (sizes i) =>
        gaussianReal theta.location (_root_.GD.N0232.N0719.N0932.d009193 (theta.scale i)))) := by
    simp only [_root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.d009176, _root_.GD.N0232.N0719.N0932.d009211]
  have hmp : MeasurePreserving e (_root_.GD.N0232.N0719.N0980.d009697 theta.location v) (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
    rw [hphys]
    exact (_root_.GD.N0232.N0719.N0997.d019803
      (fun (i : Fin k) (_ : Fin (sizes i)) =>
        gaussianReal theta.location (_root_.GD.N0232.N0719.N0932.d009193 (theta.scale i)))).symm
  have hv (i : I) : 0 < v i := by
    change (0 : ℝ) < theta.scale i.1 ^ 2
    exact sq_pos_of_pos (theta.scale_pos i.1)
  have hineq := _root_.GD.N0232.N0719.N0974.d019818 theta.location v hv (f ∘ e)
    (hf.comp e.measurable) (fun c x => he c (e x)) (h2.comp_measurePreserving hmp)
  have hprec : _root_.GD.N0232.N0719.N0885.d009322 v = ∑ i, (sizes i : ℝ) / theta.scale i ^ 2 := by
    change (∑ z : Sigma fun i => Fin (sizes i), (theta.scale z.1 ^ 2)⁻¹) = _
    rw [Fintype.sum_sigma]
    simp [div_eq_mul_inv]
  rw [hprec] at hineq
  rw [← hmp.integral_comp' (fun x => (f x - theta.location) ^ 2)]
  exact hineq

def d019820 (epsilon : ℝ) (he : 0 < epsilon) : _root_.GD.N0232.N0719.N0859.d010809 3 where
  location := 0
  scale := _root_.GD.N0232.N0719.N0924.d010486 epsilon
  scale_pos := by
    intro i
    fin_cases i <;> dsimp [_root_.GD.N0232.N0719.N0924.d010486] <;> positivity

theorem d019821 {epsilon : ℝ} (he : 0 < epsilon) :
    (∑ i, (_root_.GD.N0232.N0719.N0927.d009909 i : ℝ) / (_root_.GD.N0232.N0719.N0974.d019820 epsilon he).scale i ^ 2)⁻¹ =
      epsilon / (1 + 2 * epsilon) := by
  rw [Fin.sum_univ_three]
  change (2 / (Real.sqrt 2 * Real.sqrt epsilon) ^ 2 +
    6 / Real.sqrt 6 ^ 2 + 6 / Real.sqrt 6 ^ 2)⁻¹ = _
  rw [mul_pow, Real.sq_sqrt he.le]
  norm_num
  field_simp [he.ne', show 1 + 2 * epsilon ≠ 0 by positivity]
  ring

theorem d019822 {epsilon : ℝ} (he : 0 < epsilon) :
    _root_.GD.N0232.N0719.N0972.d012340 3 _root_.GD.N0232.N0719.N0927.d009909 (_root_.GD.N0232.N0719.N0974.d019820 epsilon he) ≤ epsilon + 50 * epsilon ^ 2 := by
  have h := (_root_.GD.N0232.N0719.N0924.d010510 he.le).trans_le
    (_root_.GD.N0232.N0719.N0924.d010470 he)
  simpa only [_root_.GD.N0232.N0719.N0972.d012340, _root_.GD.N0232.N0719.N0974.d019820, _root_.GD.N0232.N0719.N0859.d010812, _root_.GD.N0232.N0719.N0924.d010506,
    _root_.GD.N0232.N0719.N0924.d010504, _root_.GD.N0232.N0719.N0859.d010815, sub_zero] using h

theorem d019823 {k : ℕ} (sizes : Fin k → ℕ)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (f : _root_.GD.N0232.N0719.d009173 k sizes → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C)
    (hcap : _root_.GD.N0232.N0719.N0859.d010840 k sizes theta f ≤ ENNReal.ofReal C) :
    MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) ∧
      (∫ x, (f x - theta.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) ≤ C := by
  have hlin : (∫⁻ x, ENNReal.ofReal ((f x - theta.location) ^ 2)
      ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcap
  have hint : Integrable (fun x => (f x - theta.location) ^ 2) (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
    have h := integrable_toReal_of_lintegral_ne_top
      (((hf.sub measurable_const).pow_const 2).ennreal_ofReal.aemeasurable) hlin
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using h
  have herr : MemLp (fun x => f x - theta.location) 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) :=
    (memLp_two_iff_integrable_sq (hf.sub measurable_const).aestronglyMeasurable).2 hint
  have h2 : MemLp f 2 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
    have h := herr.add (memLp_const theta.location)
    convert h using 1
    funext x
    exact (sub_add_cancel (f x) theta.location).symm
  refine ⟨h2, ?_⟩
  have heq : _root_.GD.N0232.N0719.N0859.d010840 k sizes theta f =
      ENNReal.ofReal (∫ x, (f x - theta.location) ^ 2 ∂_root_.GD.N0232.N0719.N0859.d010812 k sizes theta) := by
    exact (ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun _ => sq_nonneg _)).symm
  rw [heq] at hcap
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hcap




theorem d019824
    (f : _root_.GD.N0232.N0719.d009173 3 _root_.GD.N0232.N0719.N0927.d009909 → ℝ) (hf : Measurable f)
    (he : ∀ c : ℝ, ∀ x, f (fun i j => c + x i j) = c + f x)
    (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 3 _root_.GD.N0232.N0719.N0927.d009909 theta f ≤
      ENNReal.ofReal (c * _root_.GD.N0232.N0719.N0972.d012340 3 _root_.GD.N0232.N0719.N0927.d009909 theta)) :
    1 ≤ c := by
  have hpoly (epsilon : ℝ) (heps : 0 < epsilon) :
      1 ≤ c * (1 + 50 * epsilon) * (1 + 2 * epsilon) := by
    let theta := _root_.GD.N0232.N0719.N0974.d019820 epsilon heps
    have hbound := _root_.GD.N0232.N0719.N0974.d019823 _root_.GD.N0232.N0719.N0927.d009909 theta f hf
      (c * _root_.GD.N0232.N0719.N0972.d012340 3 _root_.GD.N0232.N0719.N0927.d009909 theta)
      (mul_nonneg hc (_root_.GD.N0232.N0719.N0972.d012342 3 _root_.GD.N0232.N0719.N0927.d009909 (by norm_num) _root_.GD.N0232.N0719.N0974.d019817 theta).le)
      (hb theta)
    have horacle := _root_.GD.N0232.N0719.N0974.d019819 _root_.GD.N0232.N0719.N0927.d009909 (by norm_num)
      (fun i => lt_of_lt_of_le (by norm_num : 0 < 2) (_root_.GD.N0232.N0719.N0974.d019817 i))
      theta f hf he hbound.1
    have hfull : epsilon / (1 + 2 * epsilon) ≤ c * (epsilon + 50 * epsilon ^ 2) := by
      rw [show theta = _root_.GD.N0232.N0719.N0974.d019820 epsilon heps from rfl, _root_.GD.N0232.N0719.N0974.d019821 heps]
        at horacle
      exact (horacle.trans hbound.2).trans
        (mul_le_mul_of_nonneg_left (_root_.GD.N0232.N0719.N0974.d019822 heps) hc)
    have hprod := (div_le_iff₀ (show 0 < 1 + 2 * epsilon by positivity)).mp hfull
    apply (mul_le_mul_iff_right₀ heps).mp
    nlinarith only [hprod]
  let eps : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have heps (n : ℕ) : 0 < eps n := by dsimp [eps]; positivity
  have ht : Tendsto eps atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hlim : Tendsto
      (fun n => c * (1 + 50 * eps n) * (1 + 2 * eps n)) atTop (𝓝 c) := by
    convert ((tendsto_const_nhds.mul (tendsto_const_nhds.add
      (tendsto_const_nhds.mul ht))).mul
      (tendsto_const_nhds.add (tendsto_const_nhds.mul ht))) using 1
    ring
  exact ge_of_tendsto hlim (Eventually.of_forall fun n => hpoly (eps n) (heps n))



theorem d019825
    (f : _root_.GD.N0232.N0719.d009173 3 _root_.GD.N0232.N0719.N0927.d009909 → ℝ) (hf : Measurable f)
    (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 3 _root_.GD.N0232.N0719.N0927.d009909 theta f ≤
      ENNReal.ofReal (c * _root_.GD.N0232.N0719.N0972.d012340 3 _root_.GD.N0232.N0719.N0927.d009909 theta)) :
    1 ≤ c := by
  obtain ⟨e, hem, heq, heb⟩ := _root_.GD.N0232.N0719.N0843.d012245
    3 _root_.GD.N0232.N0719.N0927.d009909 (_root_.GD.N0232.N0719.N0972.d012343 3 _root_.GD.N0232.N0719.N0927.d009909 (by norm_num) _root_.GD.N0232.N0719.N0974.d019817)
    (by norm_num) _root_.GD.N0232.N0719.N0974.d019817 c hc f hf hb
  apply _root_.GD.N0232.N0719.N0974.d019824 e hem _ c hc heb
  intro b x
  let g : _root_.GD.N0232.N0719.N0946.d009229 := ⟨b, 0⟩
  have h := heq g x
  have h' : e (_root_.GD.N0232.N0719.N0900.d009095 3 _root_.GD.N0232.N0719.N0927.d009909 b 1 x) = b + e x := by
    simpa [g, _root_.GD.N0232.N0719.N0946.d009258,
    _root_.GD.N0232.N0719.N0946.d009229.d009244,
    _root_.GD.N0232.N0719.N0946.d009229.d009239,
    _root_.GD.N0232.N0719.N0946.d009229.shift] using h
  have hfun : _root_.GD.N0232.N0719.N0900.d009095 3 _root_.GD.N0232.N0719.N0927.d009909 b 1 x =
      (fun i j => b + x i j) := by
    funext i j
    change b + 1 * x i j = b + x i j
    ring
  rw [hfun] at h'
  exact h'

theorem d019826 :
    _root_.GD.N0232.N0719.N0973.d012377 3 _root_.GD.N0232.N0719.N0927.d009909 (by norm_num) _root_.GD.N0232.N0719.N0974.d019817 = 1 := by
  obtain ⟨e, _, heD, hvD, _, hv1⟩ :=
    _root_.GD.N0232.N0719.N0972.d012350 3 _root_.GD.N0232.N0719.N0927.d009909 (by norm_num) _root_.GD.N0232.N0719.N0974.d019817
  let M := _root_.GD.N0232.N0719.N0844.d012247 3 _root_.GD.N0232.N0719.N0927.d009909
    (_root_.GD.N0232.N0719.N0972.d012343 3 _root_.GD.N0232.N0719.N0927.d009909 (by norm_num) _root_.GD.N0232.N0719.N0974.d019817) e
  have hM : M ≠ ⊤ := ne_top_of_le_ne_top (by simp) hv1
  have hcap : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 3 _root_.GD.N0232.N0719.N0927.d009909 theta e ≤
      ENNReal.ofReal (M.toReal * _root_.GD.N0232.N0719.N0972.d012340 3 _root_.GD.N0232.N0719.N0927.d009909 theta) := by
    intro theta
    apply (_root_.GD.N0232.N0719.N0844.d012250 3 _root_.GD.N0232.N0719.N0927.d009909
      (_root_.GD.N0232.N0719.N0972.d012343 3 _root_.GD.N0232.N0719.N0927.d009909 (by norm_num) _root_.GD.N0232.N0719.N0974.d019817) (by norm_num)
      (fun i => lt_of_lt_of_le (by norm_num : 0 < 2) (_root_.GD.N0232.N0719.N0974.d019817 i))
      M.toReal ENNReal.toReal_nonneg theta e).mp
    rw [ENNReal.ofReal_toReal hM]
    exact le_iSup (fun theta => _root_.GD.N0232.N0719.N0844.d012246 3 _root_.GD.N0232.N0719.N0927.d009909
      (_root_.GD.N0232.N0719.N0972.d012343 3 _root_.GD.N0232.N0719.N0927.d009909 (by norm_num) _root_.GD.N0232.N0719.N0974.d019817) theta e) theta
  have hge := _root_.GD.N0232.N0719.N0974.d019825 e heD.1 M.toReal ENNReal.toReal_nonneg hcap
  have hreal : M.toReal = 1 := le_antisymm
    (by simpa using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ⊤) hv1) hge
  have hone : M = 1 := by rw [← ENNReal.ofReal_toReal hM, hreal]; norm_num
  exact hvD.symm.trans hone



theorem d019827 :
    _root_.GD.N0232.N0719.N0973.d012376 3 _root_.GD.N0232.N0719.N0927.d009909 (by norm_num) _root_.GD.N0232.N0719.N0974.d019817
        (_root_.GD.N0232.N0719.N0962.d012190 3 _root_.GD.N0232.N0719.N0927.d009909) = 0 ∧
      _root_.GD.N0232.N0719.N0973.d012376 3 _root_.GD.N0232.N0719.N0927.d009909 (by norm_num) _root_.GD.N0232.N0719.N0974.d019817
        (_root_.GD.N0232.N0719.N0962.d012191 3 _root_.GD.N0232.N0719.N0927.d009909) = 0 := by
  obtain ⟨_, _, _, hD, hE, _, _⟩ :=
    _root_.GD.N0232.N0719.N0973.d012380 3 _root_.GD.N0232.N0719.N0927.d009909 (by norm_num) _root_.GD.N0232.N0719.N0974.d019817
  rw [_root_.GD.N0232.N0719.N0974.d019826] at hD hE
  simpa using And.intro hD hE

theorem d019828 :
    ¬ ∃ (f : _root_.GD.N0232.N0719.d009173 3 _root_.GD.N0232.N0719.N0927.d009909 → ℝ) (g : ℝ),
      Measurable f ∧ 0 < g ∧ g ≤ 1 ∧
      ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 3 _root_.GD.N0232.N0719.N0927.d009909 theta f ≤
        ENNReal.ofReal ((1 - g) * _root_.GD.N0232.N0719.N0972.d012340 3 _root_.GD.N0232.N0719.N0927.d009909 theta) := by
  rintro ⟨f, g, hf, hg, hg1, hbound⟩
  have h := _root_.GD.N0232.N0719.N0974.d019825 f hf (1-g) (sub_nonneg.mpr hg1) hbound
  linarith



theorem d019829
    (f : _root_.GD.N0232.N0719.d009173 3 _root_.GD.N0232.N0719.N0927.d009909 → ℝ) (hf : Measurable f)
    (hb : ∀ theta, _root_.GD.N0232.N0719.N0859.d010840 3 _root_.GD.N0232.N0719.N0927.d009909 theta f ≤
      _root_.GD.N0232.N0719.N0859.d010840 3 _root_.GD.N0232.N0719.N0927.d009909 theta (_root_.GD.N0232.N0719.N0859.d010815 3 _root_.GD.N0232.N0719.N0927.d009909)) :
    _root_.GD.N0232.N0719.N0973.d012375 3 _root_.GD.N0232.N0719.N0927.d009909 (by norm_num) _root_.GD.N0232.N0719.N0974.d019817 f = 0 := by
  let gamma := _root_.GD.N0232.N0719.N0972.d012343 3 _root_.GD.N0232.N0719.N0927.d009909 (by norm_num) _root_.GD.N0232.N0719.N0974.d019817
  let r := _root_.GD.N0232.N0719.N0844.d012246 3 _root_.GD.N0232.N0719.N0927.d009909 gamma
  have hfinite : f ∈ _root_.GD.N0232.N0719.N0962.d012190 3 _root_.GD.N0232.N0719.N0927.d009909 := by
    refine ⟨hf, fun theta => ?_⟩
    apply ne_top_of_le_ne_top _ (hb theta)
    rw [_root_.GD.N0232.N0719.N0972.d012341 3 _root_.GD.N0232.N0719.N0927.d009909 (by norm_num) _root_.GD.N0232.N0719.N0974.d019817]
    exact ENNReal.ofReal_ne_top
  have hpoint (theta : _root_.GD.N0232.N0719.N0859.d010809 3) : r theta f ≤ 1 := by
    have h := hb theta
    rw [_root_.GD.N0232.N0719.N0972.d012341 3 _root_.GD.N0232.N0719.N0927.d009909 (by norm_num) _root_.GD.N0232.N0719.N0974.d019817] at h
    simpa only [ENNReal.ofReal_one, r] using
      (_root_.GD.N0232.N0719.N0844.d012250 3 _root_.GD.N0232.N0719.N0927.d009909 gamma
      (by norm_num) (fun i => lt_of_lt_of_le (by norm_num : 0 < 2) (_root_.GD.N0232.N0719.N0974.d019817 i))
      1 (by norm_num) theta f).mpr (by simpa [gamma, _root_.GD.N0232.N0719.N0972.d012343] using h)
  have hle : _root_.GD.N0230.N0611.d003516 r f ≤ 1 := iSup_le hpoint
  have hge : 1 ≤ _root_.GD.N0230.N0611.d003516 r f := by
    rw [← _root_.GD.N0232.N0719.N0974.d019826]
    exact _root_.GD.N0230.N0611.d003520 r hfinite
  have heq : _root_.GD.N0230.N0611.d003516 r f = 1 := le_antisymm hle hge
  haveI : Nonempty (_root_.GD.N0232.N0719.N0859.d010809 3) := ⟨_root_.GD.N0232.N0719.N0859.d010810 3⟩
  have h := _root_.GD.N0230.N0686.d003548 r f
    (ne_top_of_le_ne_top (by simp) hle)
  rw [heq] at h
  simpa [_root_.GD.N0232.N0719.N0973.d012375, r, gamma] using h



theorem d019830 :
    ∃ f ∈ _root_.GD.N0232.N0719.N0962.d012191 3 _root_.GD.N0232.N0719.N0927.d009909,
      f ∈ _root_.GD.N0232.N0719.N0962.d012190 3 _root_.GD.N0232.N0719.N0927.d009909 ∧
      _root_.GD.N0232.N0719.N0973.d012375 3 _root_.GD.N0232.N0719.N0927.d009909 (by norm_num) _root_.GD.N0232.N0719.N0974.d019817 f = 0 ∧
      _root_.GD.N0232.N0719.N0973.d012376 3 _root_.GD.N0232.N0719.N0927.d009909 (by norm_num) _root_.GD.N0232.N0719.N0974.d019817
        (_root_.GD.N0232.N0719.N0962.d012190 3 _root_.GD.N0232.N0719.N0927.d009909) = 0 ∧
      _root_.GD.N0232.N0719.N0973.d012376 3 _root_.GD.N0232.N0719.N0927.d009909 (by norm_num) _root_.GD.N0232.N0719.N0974.d019817
        (_root_.GD.N0232.N0719.N0962.d012191 3 _root_.GD.N0232.N0719.N0927.d009909) = 0 := by
  obtain ⟨f, hfE, hfD, _, _, hfd, _⟩ :=
    _root_.GD.N0232.N0719.N0973.d012380 3 _root_.GD.N0232.N0719.N0927.d009909 (by norm_num) _root_.GD.N0232.N0719.N0974.d019817
  obtain ⟨hD, hE⟩ := _root_.GD.N0232.N0719.N0974.d019827
  exact ⟨f, hfE, hfD, hfd.trans hD, hD, hE⟩

end
end GD.N0232.N0719.N0974

#print axioms _root_.GD.N0232.N0719.N0974.d019819
#print axioms _root_.GD.N0232.N0719.N0974.d019825
#print axioms _root_.GD.N0232.N0719.N0974.d019826
#print axioms _root_.GD.N0232.N0719.N0974.d019827
#print axioms _root_.GD.N0232.N0719.N0974.d019828
#print axioms _root_.GD.N0232.N0719.N0974.d019829
#print axioms _root_.GD.N0232.N0719.N0974.d019830
