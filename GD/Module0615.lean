import GD.Module0427
import GD.Module0612




















open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0137

noncomputable section

abbrev d008894 (n : ℕ) := Fin n → ℝ


def d008895 (n : ℕ) : Measure (_root_.GD.N0137.d008894 n) :=
  _root_.GD.N0140.d006650 n

noncomputable instance (n : ℕ) :
    IsProbabilityMeasure (_root_.GD.N0137.d008895 n) := by
  unfold _root_.GD.N0137.d008895 _root_.GD.N0140.d006650
  infer_instance


def d008896 (n : ℕ) (x : _root_.GD.N0137.d008894 n) : ℝ :=
  Real.sqrt n * _root_.GD.N0126.d006420 x


def d008897 (n : ℕ) (x : _root_.GD.N0137.d008894 n) : ℝ :=
  _root_.GD.N0126.d006422 x / (n - 1 : ℕ)

@[fun_prop] theorem d008898 (n : ℕ) :
    Measurable (_root_.GD.N0137.d008896 n) := by
  unfold _root_.GD.N0137.d008896 _root_.GD.N0126.d006420
  fun_prop

@[fun_prop] theorem d008899 (n : ℕ) :
    Measurable (_root_.GD.N0137.d008897 n) := by
  unfold _root_.GD.N0137.d008897 _root_.GD.N0126.d006422
    _root_.GD.N0126.d006421 _root_.GD.N0126.d006420
  fun_prop

theorem d008900 {n : ℕ} (hn : 2 ≤ n) :
    0 < (((n - 1 : ℕ) : ℝ) / 2) := by
  have hn1 : 0 < n - 1 := by omega
  exact div_pos (by exact_mod_cast hn1) (by norm_num)



theorem d008901 (d : ℕ) (hd : 0 < d) :
    (_root_.GD.N0121.d006346 d).map
        (fun x : ℝ => x / d) =
      gammaMeasure ((d : ℝ) / 2) ((d : ℝ) / 2) := by
  let a : ℝ := (d : ℝ) / 2
  have ha : 0 < a := by
    dsimp [a]
    positivity
  letI : IsProbabilityMeasure
      (_root_.GD.N0121.d006346 d) := by
    unfold _root_.GD.N0121.d006346
    exact isProbabilityMeasure_gammaMeasure ha (by norm_num)
  letI : IsProbabilityMeasure (gammaMeasure a a) :=
    isProbabilityMeasure_gammaMeasure ha ha
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let ε : ℝ := a / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  let X : ℝ → ℝ := fun x => x / d
  have hX : Measurable X := by
    dsimp [X]
    fun_prop
  have hXmgf (t : ℝ) :
      mgf X (_root_.GD.N0121.d006346 d) t =
        mgf id (_root_.GD.N0121.d006346 d) (t / d) := by
    unfold mgf X
    congr 1
    funext x
    congr 1
    simp only [id_eq, div_eq_mul_inv]
    ring
  have hsource :
      Ioo (-ε) ε ⊆
        integrableExpSet X
          (_root_.GD.N0121.d006346 d) := by
    intro t ht
    have htRate : t / d < (1 : ℝ) / 2 := by
      rcases ht with ⟨_, ht⟩
      dsimp [ε, a] at ht
      rw [div_lt_iff₀ hdR]
      norm_num [div_eq_mul_inv] at ht ⊢
      nlinarith
    exact mgf_pos_iff.mp (by
      rw [hXmgf]
      unfold _root_.GD.N0121.d006346
      rw [
        _root_.GD.N0121.d006347
          (a := (d : ℝ) / 2) (r := (1 : ℝ) / 2)
          (by positivity) (by norm_num) htRate]
      positivity)
  have htarget :
      Ioo (-ε) ε ⊆ integrableExpSet id (gammaMeasure a a) := by
    intro t ht
    have htRate : t < a := by
      rcases ht with ⟨_, ht⟩
      dsimp [ε] at ht
      nlinarith [ha]
    exact mgf_pos_iff.mp (by
      rw [_root_.GD.N0121.d006347 ha ha htRate]
      positivity)
  have hlocal :
      Set.EqOn
        (mgf X (_root_.GD.N0121.d006346 d))
        (mgf id (gammaMeasure a a))
        (Ioo (-ε) ε) := by
    intro t ht
    have htSource : t / d < (1 : ℝ) / 2 := by
      have htu := ht.2
      dsimp [ε, a] at htu
      rw [div_lt_iff₀ hdR]
      norm_num [div_eq_mul_inv] at htu ⊢
      nlinarith
    have htTarget : t < a := by
      have htu := ht.2
      dsimp [ε] at htu
      nlinarith [ha]
    rw [hXmgf]
    unfold _root_.GD.N0121.d006346
    rw [
      _root_.GD.N0121.d006347
        (a := (d : ℝ) / 2) (r := (1 : ℝ) / 2)
        (by positivity) (by norm_num) htSource,
      _root_.GD.N0121.d006347 ha ha htTarget]
    dsimp [a]
    congr 1
    field_simp
  have hmap :=
    _root_.GD.N0114.d006372
      (μ := _root_.GD.N0121.d006346 d)
      (ν := gammaMeasure a a)
      (X := X) (Y := id) (ε := ε)
      hε hX measurable_id hsource htarget hlocal
  simpa [X, a] using hmap


theorem d008902
    (n : ℕ) (hn : 2 ≤ n) :
    (_root_.GD.N0137.d008895 n).map (_root_.GD.N0137.d008897 n) =
      gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
        (((n - 1 : ℕ) : ℝ) / 2) := by
  have hd : 0 < n - 1 := by omega
  calc
    (_root_.GD.N0137.d008895 n).map (_root_.GD.N0137.d008897 n) =
        ((_root_.GD.N0137.d008895 n).map
          _root_.GD.N0126.d006422).map
            (fun x : ℝ => x / (n - 1 : ℕ)) := by
          rw [Measure.map_map]
          · rfl
          · fun_prop
          · unfold _root_.GD.N0126.d006422
              _root_.GD.N0126.d006421
              _root_.GD.N0126.d006420
            fun_prop
    _ = (_root_.GD.N0121.d006346 (n - 1)).map
          (fun x : ℝ => x / (n - 1 : ℕ)) := by
        unfold _root_.GD.N0137.d008895
        rw [_root_.GD.N0139.d006681
          n hn]
    _ = gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
          (((n - 1 : ℕ) : ℝ) / 2) :=
        _root_.GD.N0137.d008901 (n - 1) hd

private theorem d008903 (n : ℕ) :
    iIndepFun
      (fun i : Fin n => fun x : _root_.GD.N0137.d008894 n => x i)
      (_root_.GD.N0137.d008895 n) := by
  letI : ∀ _ : Fin n, IsProbabilityMeasure (gaussianReal 0 1) :=
    fun _ => inferInstance
  simpa [_root_.GD.N0137.d008895,
    _root_.GD.N0140.d006650] using
    (iIndepFun_pi
      (μ := fun _ : Fin n => gaussianReal 0 1)
      (X := fun _ : Fin n => id)
      (fun _ => measurable_id.aemeasurable))

private theorem d008904 (n : ℕ) (i : Fin n) :
    HasLaw (fun x : _root_.GD.N0137.d008894 n => x i)
      (gaussianReal 0 1) (_root_.GD.N0137.d008895 n) := by
  letI : ∀ _ : Fin n, IsProbabilityMeasure (gaussianReal 0 1) :=
    fun _ => inferInstance
  refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
  simpa [_root_.GD.N0137.d008895,
    _root_.GD.N0140.d006650] using
    (measurePreserving_eval
      (fun _ : Fin n => gaussianReal 0 1) i).map_eq

private theorem d008905 (n : ℕ) :
    HasGaussianLaw
      (fun x : _root_.GD.N0137.d008894 n => fun i => x i)
      (_root_.GD.N0137.d008895 n) := by
  have hInd := _root_.GD.N0137.d008903 n
  exact hInd.hasGaussianLaw fun i =>
    (_root_.GD.N0137.d008904 n i).hasGaussianLaw

private theorem d008906 (n : ℕ) :
    ∀ i j : Fin n,
      cov[(fun x : _root_.GD.N0137.d008894 n => x i),
          (fun x : _root_.GD.N0137.d008894 n => x j);
          _root_.GD.N0137.d008895 n] =
        if i = j then 1 else 0 := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl,
      covariance_self (measurable_pi_apply i).aemeasurable,
      (_root_.GD.N0137.d008904 n i).variance_eq,
      variance_id_gaussianReal]
    norm_num
  · rw [if_neg hij]
    exact (_root_.GD.N0137.d008903 n).indepFun hij
      |>.covariance_eq_zero
        ((_root_.GD.N0137.d008904 n i).hasGaussianLaw.memLp_two)
        ((_root_.GD.N0137.d008904 n j).hasGaussianLaw.memLp_two)


theorem d008907
    (n : ℕ) (hn : 0 < n) :
    (_root_.GD.N0137.d008895 n).map (_root_.GD.N0137.d008896 n) =
      gaussianReal 0 1 := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  letI : DecidableEq (Fin n) := Classical.decEq _
  let P := _root_.GD.N0137.d008895 n
  let X : Fin n → _root_.GD.N0137.d008894 n → ℝ := fun i x => x i
  have hGaussian :
      HasGaussianLaw (fun x : _root_.GD.N0137.d008894 n => fun i => X i x) P := by
    simpa [P, X] using _root_.GD.N0137.d008905 n
  have hMeanGaussian :
      HasGaussianLaw (_root_.GD.N0126.d006435 X) P := by
    have hmap :=
      hGaussian.map_fun
        (_root_.GD.N0126.d006430
          (ι := Fin n)).toContinuousLinearMap
    convert hmap using 1 <;> rfl
  have hMeanMeas :
      Measurable (_root_.GD.N0126.d006435 X) := by
    unfold _root_.GD.N0126.d006435
      _root_.GD.N0126.d006420
    fun_prop
  have hCoord2 : ∀ i, MemLp (X i) 2 P :=
    fun i => (hGaussian.eval i).memLp_two
  have hmean0 : ∫ x, _root_.GD.N0126.d006435 X x ∂P = 0 := by
    unfold _root_.GD.N0126.d006435
      _root_.GD.N0126.d006420
    rw [integral_div]
    rw [integral_finset_sum Finset.univ
      (fun i _ => (hCoord2 i).integrable (by norm_num))]
    have hzero :
        ∀ i, (∫ x, X i x ∂P) = 0 := by
      intro i
      rw [(_root_.GD.N0137.d008904 n i).integral_eq,
        integral_id_gaussianReal]
    simp_rw [hzero]
    simp
  have hvar :
      Var[_root_.GD.N0126.d006435 X; P] = 1 / (n : ℝ) := by
    rw [← covariance_self hMeanGaussian.aemeasurable]
    have h := _root_.GD.N0126.d006438
      (X := X) (v := (1 : ℝ)) hCoord2 (fun i j => by
        by_cases hij : i = j
        · subst j
          rw [if_pos rfl,
            covariance_self (measurable_pi_apply i).aemeasurable,
            (_root_.GD.N0137.d008904 n i).variance_eq,
            variance_id_gaussianReal]
          norm_num
        · rw [if_neg hij]
          exact (_root_.GD.N0137.d008903 n).indepFun hij
            |>.covariance_eq_zero (hCoord2 i) (hCoord2 j))
    simpa [_root_.GD.N0126.d006419] using h
  have hMeanLaw :
      P.map (_root_.GD.N0126.d006435 X) =
        gaussianReal 0 (Real.toNNReal (1 / (n : ℝ))) := by
    rw [hMeanGaussian.map_eq_gaussianReal, hmean0, hvar]
  calc
    (_root_.GD.N0137.d008895 n).map (_root_.GD.N0137.d008896 n) =
        (P.map (_root_.GD.N0126.d006435 X)).map
          (fun z : ℝ => Real.sqrt n * z) := by
            rw [Measure.map_map]
            · rfl
            · fun_prop
            · exact hMeanMeas
    _ = (gaussianReal 0 (Real.toNNReal (1 / (n : ℝ)))).map
          (fun z : ℝ => Real.sqrt n * z) := by rw [hMeanLaw]
    _ = gaussianReal 0 1 := by
      rw [gaussianReal_map_const_mul]
      congr 1
      · norm_num
      · ext
        simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one,
          Real.coe_toNNReal']
        rw [max_eq_left (by positivity : 0 ≤ 1 / (n : ℝ))]
        rw [Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
        field_simp


theorem d008908
    (n : ℕ) (hn : 2 ≤ n) :
    IndepFun (_root_.GD.N0137.d008896 n) (_root_.GD.N0137.d008897 n)
      (_root_.GD.N0137.d008895 n) := by
  have hn0 : 0 < n := by omega
  letI : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  letI : DecidableEq (Fin n) := Classical.decEq _
  let X : Fin n → _root_.GD.N0137.d008894 n → ℝ := fun i x => x i
  have hbase :
      IndepFun
        (_root_.GD.N0126.d006435 X)
        (fun x : _root_.GD.N0137.d008894 n =>
          _root_.GD.N0126.d006422 (fun i => X i x))
        (_root_.GD.N0137.d008895 n) := by
    apply _root_.GD.N0126.d006441
      (_root_.GD.N0137.d008905 n)
    intro i j
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl,
        covariance_self (measurable_pi_apply i).aemeasurable,
        (_root_.GD.N0137.d008904 n i).variance_eq,
        variance_id_gaussianReal]
    · rw [if_neg hij]
      exact (_root_.GD.N0137.d008903 n).indepFun hij
        |>.covariance_eq_zero
          ((_root_.GD.N0137.d008904 n i).hasGaussianLaw.memLp_two)
          ((_root_.GD.N0137.d008904 n j).hasGaussianLaw.memLp_two)
  have hcomp := hbase.comp
    (show Measurable (fun z : ℝ => Real.sqrt n * z) by fun_prop)
    (show Measurable (fun z : ℝ => z / (n - 1 : ℕ)) by fun_prop)
  convert hcomp using 1 <;> rfl



theorem d008909
    (n : ℕ) (hn : 2 ≤ n) :
    (_root_.GD.N0137.d008895 n).map
        (fun x => (_root_.GD.N0137.d008896 n x, _root_.GD.N0137.d008897 n x)) =
      (gaussianReal 0 1).prod
        (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
          (((n - 1 : ℕ) : ℝ) / 2)) := by
  have hm : HasLaw (_root_.GD.N0137.d008896 n) (gaussianReal 0 1)
      (_root_.GD.N0137.d008895 n) := ⟨
    (_root_.GD.N0137.d008898 n).aemeasurable,
    _root_.GD.N0137.d008907 n (by omega)⟩
  have hr : HasLaw (_root_.GD.N0137.d008897 n)
      (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
        (((n - 1 : ℕ) : ℝ) / 2))
      (_root_.GD.N0137.d008895 n) := ⟨
    (_root_.GD.N0137.d008899 n).aemeasurable,
    _root_.GD.N0137.d008902 n hn⟩
  exact (_root_.GD.N0137.d008908 n hn)
    |>.hasLaw_prod hm hr |>.map_eq

section Interchange

variable {A B C D : Type*}
  [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D]


def d008910 : (A × B) × (C × D) → (A × C) × (B × D) :=
  fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2))

@[fun_prop] theorem d008911 :
    Measurable (_root_.GD.N0137.d008910 : (A × B) × (C × D) → (A × C) × (B × D)) := by
  unfold _root_.GD.N0137.d008910
  fun_prop




theorem d008912
    (μA : Measure A) (μB : Measure B)
    (μC : Measure C) (μD : Measure D)
    [SFinite μA] [SFinite μB] [SFinite μC] [SFinite μD] :
    MeasurePreserving _root_.GD.N0137.d008910
      ((μA.prod μB).prod (μC.prod μD))
      ((μA.prod μC).prod (μB.prod μD)) := by
  let h1 :=
    MeasureTheory.measurePreserving_prodAssoc μA μB (μC.prod μD)
  let h2inner :=
    (MeasureTheory.measurePreserving_prodAssoc μB μC μD).symm
      MeasurableEquiv.prodAssoc
  let h2 := (MeasurePreserving.id μA).prod h2inner
  let h3inner :=
    (Measure.measurePreserving_swap (μ := μB) (ν := μC)).prod
      (MeasurePreserving.id μD)
  let h3 := (MeasurePreserving.id μA).prod h3inner
  let h4inner :=
    MeasureTheory.measurePreserving_prodAssoc μC μB μD
  let h4 := (MeasurePreserving.id μA).prod h4inner
  let h5 :=
    (MeasureTheory.measurePreserving_prodAssoc
      μA μC (μB.prod μD)).symm MeasurableEquiv.prodAssoc
  have h := h5.comp (h4.comp (h3.comp (h2.comp h1)))
  convert h using 1
  funext p
  rcases p with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rfl

theorem d008913
    (μA : Measure A) (μB : Measure B)
    (μC : Measure C) (μD : Measure D)
    [SFinite μA] [SFinite μB] [SFinite μC] [SFinite μD] :
    ((μA.prod μB).prod (μC.prod μD)).map _root_.GD.N0137.d008910 =
      (μA.prod μC).prod (μB.prod μD) :=
  (_root_.GD.N0137.d008912 μA μB μC μD).map_eq

end Interchange




def d008914 (m n : ℕ) :
    Measure (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :=
  (_root_.GD.N0137.d008895 m).prod (_root_.GD.N0137.d008895 n)

noncomputable instance (m n : ℕ) :
    IsProbabilityMeasure (_root_.GD.N0137.d008914 m n) := by
  unfold _root_.GD.N0137.d008914
  infer_instance

def d008915 (m n : ℕ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    (ℝ × ℝ) × (ℝ × ℝ) :=
  ((_root_.GD.N0137.d008896 m ω.1, _root_.GD.N0137.d008896 n ω.2),
    (_root_.GD.N0137.d008897 m ω.1, _root_.GD.N0137.d008897 n ω.2))

@[fun_prop] theorem d008916 (m n : ℕ) :
    Measurable (_root_.GD.N0137.d008915 m n) := by
  unfold _root_.GD.N0137.d008915
  fun_prop



theorem d008917
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (_root_.GD.N0137.d008914 m n).map (_root_.GD.N0137.d008915 m n) =
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).prod
        ((gammaMeasure (((m - 1 : ℕ) : ℝ) / 2)
            (((m - 1 : ℕ) : ℝ) / 2)).prod
          (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
            (((n - 1 : ℕ) : ℝ) / 2))) := by
  letI : IsProbabilityMeasure
      (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2)
        (((m - 1 : ℕ) : ℝ) / 2)) :=
    isProbabilityMeasure_gammaMeasure
      (_root_.GD.N0137.d008900 hm) (_root_.GD.N0137.d008900 hm)
  letI : IsProbabilityMeasure
      (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
        (((n - 1 : ℕ) : ℝ) / 2)) :=
    isProbabilityMeasure_gammaMeasure
      (_root_.GD.N0137.d008900 hn) (_root_.GD.N0137.d008900 hn)
  let bm : _root_.GD.N0137.d008894 m → ℝ × ℝ :=
    fun x => (_root_.GD.N0137.d008896 m x, _root_.GD.N0137.d008897 m x)
  let bn : _root_.GD.N0137.d008894 n → ℝ × ℝ :=
    fun y => (_root_.GD.N0137.d008896 n y, _root_.GD.N0137.d008897 n y)
  let μm :=
    (gaussianReal 0 1).prod
      (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2)
        (((m - 1 : ℕ) : ℝ) / 2))
  let μn :=
    (gaussianReal 0 1).prod
      (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
        (((n - 1 : ℕ) : ℝ) / 2))
  have hbm :
      (_root_.GD.N0137.d008895 m).map bm = μm := by
    simpa [bm, μm] using
      _root_.GD.N0137.d008909 m hm
  have hbn :
      (_root_.GD.N0137.d008895 n).map bn = μn := by
    simpa [bn, μn] using
      _root_.GD.N0137.d008909 n hn
  calc
    (_root_.GD.N0137.d008914 m n).map (_root_.GD.N0137.d008915 m n) =
        (((_root_.GD.N0137.d008895 m).prod (_root_.GD.N0137.d008895 n)).map
          (Prod.map bm bn)).map _root_.GD.N0137.d008910 := by
            rw [Measure.map_map]
            · rfl
            · exact _root_.GD.N0137.d008911
            · fun_prop
    _ = (((_root_.GD.N0137.d008895 m).map bm).prod
          ((_root_.GD.N0137.d008895 n).map bn)).map _root_.GD.N0137.d008910 := by
        congr 1
        exact (Measure.map_prod_map
          (_root_.GD.N0137.d008895 m) (_root_.GD.N0137.d008895 n)
          (by unfold bm; fun_prop) (by unfold bn; fun_prop)).symm
    _ = (μm.prod μn).map _root_.GD.N0137.d008910 := by rw [hbm, hbn]
    _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).prod
          ((gammaMeasure (((m - 1 : ℕ) : ℝ) / 2)
              (((m - 1 : ℕ) : ℝ) / 2)).prod
            (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
              (((n - 1 : ℕ) : ℝ) / 2))) := by
        simpa [μm, μn] using
          _root_.GD.N0137.d008913
            (gaussianReal 0 1)
            (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2)
              (((m - 1 : ℕ) : ℝ) / 2))
            (gaussianReal 0 1)
            (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
              (((n - 1 : ℕ) : ℝ) / 2))



def d008918 (e : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.sqrt e * p.1 + Real.sqrt (1 - e) * p.2


def d008919 (e : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.sqrt (1 - e) * p.1 - Real.sqrt e * p.2

def d008920 (e : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (_root_.GD.N0137.d008918 e p, _root_.GD.N0137.d008919 e p)

@[fun_prop] theorem d008921 (e : ℝ) :
    Measurable (_root_.GD.N0137.d008920 e) := by
  unfold _root_.GD.N0137.d008920 _root_.GD.N0137.d008918 _root_.GD.N0137.d008919
  fun_prop

def d008922 (e : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun := _root_.GD.N0137.d008920 e
  map_add' p q := by
    ext <;>
      simp [_root_.GD.N0137.d008920, _root_.GD.N0137.d008918,
        _root_.GD.N0137.d008919] <;>
      ring
  map_smul' c p := by
    ext <;>
      simp [_root_.GD.N0137.d008920, _root_.GD.N0137.d008918,
        _root_.GD.N0137.d008919] <;>
      ring

private theorem d008923
    (c : ℝ) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (fun p : ℝ × ℝ => c * p.1) =
      gaussianReal 0 (Real.toNNReal (c ^ 2)) := by
  calc
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (fun p : ℝ × ℝ => c * p.1) =
      (((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        Prod.fst).map (fun x : ℝ => c * x) := by
          rw [Measure.map_map]
          · rfl
          all_goals fun_prop
    _ = (gaussianReal 0 1).map (fun x : ℝ => c * x) := by
      rw [measurePreserving_fst.map_eq]
    _ = gaussianReal 0 (Real.toNNReal (c ^ 2)) := by
      rw [gaussianReal_map_const_mul]
      congr 1
      · ring
      · ext
        simp [Real.coe_toNNReal', max_eq_left (sq_nonneg c)]

private theorem d008924
    (c : ℝ) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (fun p : ℝ × ℝ => c * p.2) =
      gaussianReal 0 (Real.toNNReal (c ^ 2)) := by
  calc
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (fun p : ℝ × ℝ => c * p.2) =
      (((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        Prod.snd).map (fun x : ℝ => c * x) := by
          rw [Measure.map_map]
          · rfl
          all_goals fun_prop
    _ = (gaussianReal 0 1).map (fun x : ℝ => c * x) := by
      rw [measurePreserving_snd.map_eq]
    _ = gaussianReal 0 (Real.toNNReal (c ^ 2)) := by
      rw [gaussianReal_map_const_mul]
      congr 1
      · ring
      · ext
        simp [Real.coe_toNNReal', max_eq_left (sq_nonneg c)]

private theorem d008925
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (_root_.GD.N0137.d008918 e) =
      gaussianReal 0 1 := by
  let μ := (gaussianReal 0 1).prod (gaussianReal 0 1)
  let X : ℝ × ℝ → ℝ := fun p => Real.sqrt e * p.1
  let Y : ℝ × ℝ → ℝ := fun p => Real.sqrt (1 - e) * p.2
  have hInd : IndepFun X Y μ := by
    exact (indepFun_prod (μ := gaussianReal 0 1)
      (ν := gaussianReal 0 1) measurable_id measurable_id).comp
        (by fun_prop) (by fun_prop)
  have hX :
      μ.map X = gaussianReal 0 (Real.toNNReal e) := by
    rw [show e = (Real.sqrt e) ^ 2 by
      rw [Real.sq_sqrt he0]]
    exact _root_.GD.N0137.d008923 _
  have hY :
      μ.map Y = gaussianReal 0 (Real.toNNReal (1 - e)) := by
    rw [show 1 - e = (Real.sqrt (1 - e)) ^ 2 by
      rw [Real.sq_sqrt (sub_nonneg.mpr he1)]]
    exact _root_.GD.N0137.d008924 _
  have hadd :=
    gaussianReal_add_gaussianReal_of_indepFun hInd hX hY
  have hvar :
      Real.toNNReal e + Real.toNNReal (1 - e) = (1 : ℝ≥0) := by
    ext
    simp [Real.coe_toNNReal', max_eq_left he0,
      max_eq_left (sub_nonneg.mpr he1)]
  rw [hvar] at hadd
  change μ.map (X + Y) = gaussianReal 0 1
  simpa using hadd

private theorem d008926
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (_root_.GD.N0137.d008919 e) =
      gaussianReal 0 1 := by
  let μ := (gaussianReal 0 1).prod (gaussianReal 0 1)
  let X : ℝ × ℝ → ℝ := fun p => Real.sqrt (1 - e) * p.1
  let Y : ℝ × ℝ → ℝ := fun p => -Real.sqrt e * p.2
  have hInd : IndepFun X Y μ := by
    exact (indepFun_prod (μ := gaussianReal 0 1)
      (ν := gaussianReal 0 1) measurable_id measurable_id).comp
        (by fun_prop) (by fun_prop)
  have hX :
      μ.map X = gaussianReal 0 (Real.toNNReal (1 - e)) := by
    rw [show 1 - e = (Real.sqrt (1 - e)) ^ 2 by
      rw [Real.sq_sqrt (sub_nonneg.mpr he1)]]
    exact _root_.GD.N0137.d008923 _
  have hY :
      μ.map Y = gaussianReal 0 (Real.toNNReal e) := by
    rw [show e = (-Real.sqrt e) ^ 2 by
      rw [neg_sq, Real.sq_sqrt he0]]
    exact _root_.GD.N0137.d008924 _
  have hadd :=
    gaussianReal_add_gaussianReal_of_indepFun hInd hX hY
  have hvar :
      Real.toNNReal (1 - e) + Real.toNNReal e = (1 : ℝ≥0) := by
    ext
    simp [Real.coe_toNNReal', max_eq_left he0,
      max_eq_left (sub_nonneg.mpr he1)]
  rw [hvar] at hadd
  have hfun : _root_.GD.N0137.d008919 e = X + Y := by
    funext p
    simp [_root_.GD.N0137.d008919, X, Y]
    ring
  rw [hfun]
  simpa using hadd




theorem d008927
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (_root_.GD.N0137.d008920 e) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  let μ := (gaussianReal 0 1).prod (gaussianReal 0 1)
  let X : ℝ × ℝ → ℝ := Prod.fst
  let Y : ℝ × ℝ → ℝ := Prod.snd
  let O : ℝ × ℝ → ℝ := _root_.GD.N0137.d008918 e
  let Z : ℝ × ℝ → ℝ := _root_.GD.N0137.d008919 e
  have hXY : IndepFun X Y μ := by
    simpa [μ, X, Y] using
      (indepFun_prod (μ := gaussianReal 0 1)
        (ν := gaussianReal 0 1) measurable_id measurable_id)
  have hXlaw : HasLaw X (gaussianReal 0 1) μ := by
    simpa [μ, X] using
      (measurePreserving_fst
        (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)).hasLaw
  have hYlaw : HasLaw Y (gaussianReal 0 1) μ := by
    simpa [μ, Y] using
      (measurePreserving_snd
        (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)).hasLaw
  have hBaseGaussian :
      HasGaussianLaw (fun p => (X p, Y p)) μ :=
    hXY.hasGaussianLaw hXlaw.hasGaussianLaw hYlaw.hasGaussianLaw
  have hOZGaussian :
      HasGaussianLaw (fun p => (O p, Z p)) μ := by
    have h := hBaseGaussian.map_fun
      (_root_.GD.N0137.d008922 e).toContinuousLinearMap
    simpa [O, Z, _root_.GD.N0137.d008922, _root_.GD.N0137.d008920,
      X, Y] using h
  have hX2 : MemLp X 2 μ := hXlaw.hasGaussianLaw.memLp_two
  have hY2 : MemLp Y 2 μ := hYlaw.hasGaussianLaw.memLp_two
  have hXX : cov[X, X; μ] = 1 := by
    rw [covariance_self hXlaw.aemeasurable,
      hXlaw.variance_eq, variance_id_gaussianReal]
    norm_num
  have hYY : cov[Y, Y; μ] = 1 := by
    rw [covariance_self hYlaw.aemeasurable,
      hYlaw.variance_eq, variance_id_gaussianReal]
    norm_num
  have hXY0 : cov[X, Y; μ] = 0 :=
    hXY.covariance_eq_zero hX2 hY2
  have hYX0 : cov[Y, X; μ] = 0 := by
    rw [covariance_comm, hXY0]
  let A : ℝ × ℝ → ℝ := fun p => Real.sqrt e * X p
  let B : ℝ × ℝ → ℝ := fun p => Real.sqrt (1 - e) * Y p
  let C : ℝ × ℝ → ℝ := fun p => Real.sqrt (1 - e) * X p
  let D : ℝ × ℝ → ℝ := fun p => Real.sqrt e * Y p
  have hA : MemLp A 2 μ := hX2.const_mul _
  have hB : MemLp B 2 μ := hY2.const_mul _
  have hC : MemLp C 2 μ := hX2.const_mul _
  have hD : MemLp D 2 μ := hY2.const_mul _
  have hcov : cov[O, Z; μ] = 0 := by
    change cov[A + B, C - D; μ] = 0
    rw [covariance_add_left hA hB (hC.sub hD),
      covariance_sub_right hA hC hD,
      covariance_sub_right hB hC hD]
    simp only [A, B, C, D, covariance_const_mul_left,
      covariance_const_mul_right, hXX, hYY, hXY0, hYX0,
      mul_zero, mul_one, sub_zero, zero_sub]
    ring
  have hIndOZ : IndepFun O Z μ :=
    hOZGaussian.indepFun_of_covariance_eq_zero hcov
  have hOlaw : HasLaw O (gaussianReal 0 1) μ := by
    exact ⟨(_root_.GD.N0137.d008921 e).fst.aemeasurable, by
      simpa [μ, O] using _root_.GD.N0137.d008925 he0 he1⟩
  have hZlaw : HasLaw Z (gaussianReal 0 1) μ := by
    exact ⟨(_root_.GD.N0137.d008921 e).snd.aemeasurable, by
      simpa [μ, Z] using _root_.GD.N0137.d008926 he0 he1⟩
  have hjoint := hIndOZ.hasLaw_prod hOlaw hZlaw
  change μ.map (fun p => (O p, Z p)) =
    (gaussianReal 0 1).prod (gaussianReal 0 1)
  exact hjoint.map_eq


def d008928 (m n : ℕ) (e : ℝ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    (ℝ × ℝ) × (ℝ × ℝ) :=
  (_root_.GD.N0137.d008920 e
      (_root_.GD.N0137.d008896 m ω.1, _root_.GD.N0137.d008896 n ω.2),
    (_root_.GD.N0137.d008897 m ω.1, _root_.GD.N0137.d008897 n ω.2))

@[fun_prop] theorem d008929 (m n : ℕ) (e : ℝ) :
    Measurable (_root_.GD.N0137.d008928 m n e) := by
  unfold _root_.GD.N0137.d008928
  fun_prop



theorem d008930
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    (_root_.GD.N0137.d008914 m n).map (_root_.GD.N0137.d008928 m n e) =
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).prod
        ((gammaMeasure (((m - 1 : ℕ) : ℝ) / 2)
            (((m - 1 : ℕ) : ℝ) / 2)).prod
          (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
            (((n - 1 : ℕ) : ℝ) / 2))) := by
  letI : IsProbabilityMeasure
      (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2)
        (((m - 1 : ℕ) : ℝ) / 2)) :=
    isProbabilityMeasure_gammaMeasure
      (_root_.GD.N0137.d008900 hm) (_root_.GD.N0137.d008900 hm)
  letI : IsProbabilityMeasure
      (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
        (((n - 1 : ℕ) : ℝ) / 2)) :=
    isProbabilityMeasure_gammaMeasure
      (_root_.GD.N0137.d008900 hn) (_root_.GD.N0137.d008900 hn)
  let μR :=
    (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2)
        (((m - 1 : ℕ) : ℝ) / 2)).prod
      (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
        (((n - 1 : ℕ) : ℝ) / 2))
  calc
    (_root_.GD.N0137.d008914 m n).map (_root_.GD.N0137.d008928 m n e) =
        ((_root_.GD.N0137.d008914 m n).map (_root_.GD.N0137.d008915 m n)).map
          (Prod.map (_root_.GD.N0137.d008920 e) id) := by
            rw [Measure.map_map]
            · rfl
            · fun_prop
            · exact _root_.GD.N0137.d008916 m n
    _ = (((gaussianReal 0 1).prod (gaussianReal 0 1)).prod
          μR).map (Prod.map (_root_.GD.N0137.d008920 e) id) := by
        rw [_root_.GD.N0137.d008917 m n hm hn]
    _ = (((gaussianReal 0 1).prod (gaussianReal 0 1)).map
          (_root_.GD.N0137.d008920 e)).prod
          (μR.map id) := by
        exact (Measure.map_prod_map
          ((gaussianReal 0 1).prod (gaussianReal 0 1)) μR
          (_root_.GD.N0137.d008921 e) measurable_id).symm
    _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).prod μR := by
      rw [_root_.GD.N0137.d008927 he0 he1, Measure.map_id]
    _ = _ := rfl

def d008931 (m n : ℕ) (e : ℝ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  _root_.GD.N0137.d008918 e
    (_root_.GD.N0137.d008896 m ω.1, _root_.GD.N0137.d008896 n ω.2)

def d008932 (m n : ℕ) (e : ℝ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  _root_.GD.N0137.d008919 e
    (_root_.GD.N0137.d008896 m ω.1, _root_.GD.N0137.d008896 n ω.2)

def d008933 (m n : ℕ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  _root_.GD.N0137.d008897 m ω.1

def d008934 (m n : ℕ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  _root_.GD.N0137.d008897 n ω.2

def d008935 (m n : ℕ) (e : ℝ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0124.d006387 :=
  (_root_.GD.N0137.d008932 m n e ω, (_root_.GD.N0137.d008933 m n ω, _root_.GD.N0137.d008934 m n ω))

@[fun_prop] theorem d008936 (m n : ℕ) (e : ℝ) :
    Measurable (_root_.GD.N0137.d008931 m n e) := by
  unfold _root_.GD.N0137.d008931 _root_.GD.N0137.d008918
  fun_prop

@[fun_prop] theorem d008937 (m n : ℕ) (e : ℝ) :
    Measurable (_root_.GD.N0137.d008935 m n e) := by
  unfold _root_.GD.N0137.d008935 _root_.GD.N0137.d008932 _root_.GD.N0137.d008919 _root_.GD.N0137.d008933 _root_.GD.N0137.d008934
  fun_prop



theorem d008938
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    _root_.GD.N0125.d008841
      (_root_.GD.N0137.d008914 m n)
      (_root_.GD.N0137.d008932 m n e)
      (_root_.GD.N0137.d008933 m n) (_root_.GD.N0137.d008934 m n)
      (((m - 1 : ℕ) : ℝ) / 2)
      (((n - 1 : ℕ) : ℝ) / 2) := by
  letI : IsProbabilityMeasure
      (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2)
        (((m - 1 : ℕ) : ℝ) / 2)) :=
    isProbabilityMeasure_gammaMeasure
      (_root_.GD.N0137.d008900 hm) (_root_.GD.N0137.d008900 hm)
  letI : IsProbabilityMeasure
      (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
        (((n - 1 : ℕ) : ℝ) / 2)) :=
    isProbabilityMeasure_gammaMeasure
      (_root_.GD.N0137.d008900 hn) (_root_.GD.N0137.d008900 hn)
  let μR :=
    (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2)
        (((m - 1 : ℕ) : ℝ) / 2)).prod
      (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
        (((n - 1 : ℕ) : ℝ) / 2))
  let dropOracle : (ℝ × ℝ) × (ℝ × ℝ) → ℝ × (ℝ × ℝ) :=
    fun p => (p.1.2, p.2)
  change (_root_.GD.N0137.d008914 m n).map (_root_.GD.N0137.d008935 m n e) =
    _root_.GD.N0125.d008840
      (((m - 1 : ℕ) : ℝ) / 2)
      (((n - 1 : ℕ) : ℝ) / 2)
  calc
    (_root_.GD.N0137.d008914 m n).map (_root_.GD.N0137.d008935 m n e) =
        ((_root_.GD.N0137.d008914 m n).map (_root_.GD.N0137.d008928 m n e)).map
          dropOracle := by
            rw [Measure.map_map]
            · rfl
            · dsimp [dropOracle]
              fun_prop
            · exact _root_.GD.N0137.d008929 m n e
    _ = (((gaussianReal 0 1).prod (gaussianReal 0 1)).prod
          μR).map dropOracle := by
        rw [_root_.GD.N0137.d008930 m n hm hn he0 he1]
    _ = (((gaussianReal 0 1).prod (gaussianReal 0 1)).map
          Prod.snd).prod (μR.map id) := by
        exact (Measure.map_prod_map
          ((gaussianReal 0 1).prod (gaussianReal 0 1)) μR
          measurable_snd measurable_id).symm
    _ = (gaussianReal 0 1).prod μR := by
      rw [measurePreserving_snd.map_eq, Measure.map_id]
    _ = _root_.GD.N0125.d008840
          (((m - 1 : ℕ) : ℝ) / 2)
          (((n - 1 : ℕ) : ℝ) / 2) := by
      rfl

theorem d008939
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    (_root_.GD.N0137.d008914 m n).map (_root_.GD.N0137.d008931 m n e) =
      gaussianReal 0 1 := by
  letI : IsProbabilityMeasure
      (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2)
        (((m - 1 : ℕ) : ℝ) / 2)) :=
    isProbabilityMeasure_gammaMeasure
      (_root_.GD.N0137.d008900 hm) (_root_.GD.N0137.d008900 hm)
  letI : IsProbabilityMeasure
      (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
        (((n - 1 : ℕ) : ℝ) / 2)) :=
    isProbabilityMeasure_gammaMeasure
      (_root_.GD.N0137.d008900 hn) (_root_.GD.N0137.d008900 hn)
  let takeOracle : (ℝ × ℝ) × (ℝ × ℝ) → ℝ :=
    fun p => p.1.1
  calc
    (_root_.GD.N0137.d008914 m n).map (_root_.GD.N0137.d008931 m n e) =
        ((_root_.GD.N0137.d008914 m n).map (_root_.GD.N0137.d008928 m n e)).map
          takeOracle := by
            rw [Measure.map_map]
            · rfl
            · dsimp [takeOracle]
              fun_prop
            · exact _root_.GD.N0137.d008929 m n e
    _ = (((gaussianReal 0 1).prod (gaussianReal 0 1)).prod
          ((gammaMeasure (((m - 1 : ℕ) : ℝ) / 2)
              (((m - 1 : ℕ) : ℝ) / 2)).prod
            (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
              (((n - 1 : ℕ) : ℝ) / 2)))).map
          takeOracle := by
        rw [_root_.GD.N0137.d008930 m n hm hn he0 he1]
    _ = ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
          Prod.fst := by
        calc
          _ = ((((gaussianReal 0 1).prod (gaussianReal 0 1)).prod
                ((gammaMeasure (((m - 1 : ℕ) : ℝ) / 2)
                    (((m - 1 : ℕ) : ℝ) / 2)).prod
                  (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
                    (((n - 1 : ℕ) : ℝ) / 2)))).map
                Prod.fst).map Prod.fst := by
              rw [Measure.map_map]
              · rfl
              · exact measurable_fst
              · exact measurable_fst
          _ = _ := by rw [measurePreserving_fst.map_eq]
    _ = gaussianReal 0 1 := by
      rw [measurePreserving_fst.map_eq]




theorem d008940
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    IndepFun (_root_.GD.N0137.d008931 m n e) (_root_.GD.N0137.d008935 m n e)
      (_root_.GD.N0137.d008914 m n) := by
  letI : IsProbabilityMeasure
      (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2)
        (((m - 1 : ℕ) : ℝ) / 2)) :=
    isProbabilityMeasure_gammaMeasure
      (_root_.GD.N0137.d008900 hm) (_root_.GD.N0137.d008900 hm)
  letI : IsProbabilityMeasure
      (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
        (((n - 1 : ℕ) : ℝ) / 2)) :=
    isProbabilityMeasure_gammaMeasure
      (_root_.GD.N0137.d008900 hn) (_root_.GD.N0137.d008900 hn)
  let μR :=
    (gammaMeasure (((m - 1 : ℕ) : ℝ) / 2)
        (((m - 1 : ℕ) : ℝ) / 2)).prod
      (gammaMeasure (((n - 1 : ℕ) : ℝ) / 2)
        (((n - 1 : ℕ) : ℝ) / 2))
  have hjoint :
      (_root_.GD.N0137.d008914 m n).map
          (fun ω => (_root_.GD.N0137.d008931 m n e ω, _root_.GD.N0137.d008935 m n e ω)) =
        (gaussianReal 0 1).prod ((gaussianReal 0 1).prod μR) := by
    calc
      (_root_.GD.N0137.d008914 m n).map
          (fun ω => (_root_.GD.N0137.d008931 m n e ω, _root_.GD.N0137.d008935 m n e ω)) =
        ((_root_.GD.N0137.d008914 m n).map (_root_.GD.N0137.d008928 m n e)).map
          MeasurableEquiv.prodAssoc := by
            rw [Measure.map_map]
            · rfl
            all_goals fun_prop
      _ = (((gaussianReal 0 1).prod (gaussianReal 0 1)).prod
            μR).map MeasurableEquiv.prodAssoc := by
          rw [_root_.GD.N0137.d008930 m n hm hn he0 he1]
      _ = (gaussianReal 0 1).prod
            ((gaussianReal 0 1).prod μR) :=
          Measure.prodAssoc_prod
  rw [indepFun_iff_map_prod_eq_prod_map_map
    (_root_.GD.N0137.d008936 m n e).aemeasurable
    (_root_.GD.N0137.d008937 m n e).aemeasurable]
  rw [hjoint, _root_.GD.N0137.d008939 m n hm hn he0 he1]
  change (gaussianReal 0 1).prod
      ((gaussianReal 0 1).prod μR) =
    (gaussianReal 0 1).prod
      ((_root_.GD.N0137.d008914 m n).map (_root_.GD.N0137.d008935 m n e))
  have hraw :=
    _root_.GD.N0137.d008938 m n hm hn he0 he1
  change (_root_.GD.N0137.d008914 m n).map (_root_.GD.N0137.d008935 m n e) =
    _root_.GD.N0125.d008840
      (((m - 1 : ℕ) : ℝ) / 2)
      (((n - 1 : ℕ) : ℝ) / 2) at hraw
  rw [hraw]
  rfl

theorem d008941
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    ∫ ω, _root_.GD.N0137.d008931 m n e ω ∂_root_.GD.N0137.d008914 m n = 0 := by
  have hLaw : HasLaw (_root_.GD.N0137.d008931 m n e) (gaussianReal 0 1)
      (_root_.GD.N0137.d008914 m n) := ⟨
    (_root_.GD.N0137.d008936 m n e).aemeasurable,
    _root_.GD.N0137.d008939 m n hm hn he0 he1⟩
  rw [hLaw.integral_eq, integral_id_gaussianReal]


def d008942 (m n : ℕ) (e Sigma : ℝ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  Real.sqrt Sigma * _root_.GD.N0137.d008932 m n e ω

def d008943 (m n : ℕ) (e : ℝ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  e * _root_.GD.N0137.d008934 m n ω /
    ((1 - e) * _root_.GD.N0137.d008933 m n ω + e * _root_.GD.N0137.d008934 m n ω)

def d008944 (m n : ℕ) (e : ℝ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  _root_.GD.N0137.d008932 m n e ω ^ 2 /
    ((1 - e) * _root_.GD.N0137.d008933 m n ω + e * _root_.GD.N0137.d008934 m n ω)


def d008945 (m n : ℕ) (e Sigma : ℝ)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  Real.sqrt (Sigma * e * (1 - e)) * _root_.GD.N0137.d008931 m n e ω

@[fun_prop] theorem d008946 (m n : ℕ) (e Sigma : ℝ) :
    Measurable (fun ω =>
      (_root_.GD.N0137.d008942 m n e Sigma ω,
        (_root_.GD.N0137.d008943 m n e ω, _root_.GD.N0137.d008944 m n e ω))) := by
  unfold _root_.GD.N0137.d008942 _root_.GD.N0137.d008943 _root_.GD.N0137.d008944 _root_.GD.N0137.d008932
    _root_.GD.N0137.d008919 _root_.GD.N0137.d008933 _root_.GD.N0137.d008934
  fun_prop

theorem d008947
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e Sigma : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    IndepFun (_root_.GD.N0137.d008945 m n e Sigma)
      (fun ω =>
        (_root_.GD.N0137.d008942 m n e Sigma ω,
          (_root_.GD.N0137.d008943 m n e ω, _root_.GD.N0137.d008944 m n e ω)))
      (_root_.GD.N0137.d008914 m n) := by
  have h :=
    _root_.GD.N0137.d008940 m n hm hn he0 he1
  exact h.comp
    (show Measurable (fun o : ℝ =>
      Real.sqrt (Sigma * e * (1 - e)) * o) by fun_prop)
    (show Measurable
      (fun p : _root_.GD.N0124.d006387 =>
        (Real.sqrt Sigma * p.1,
          (e * p.2.2 /
              ((1 - e) * p.2.1 + e * p.2.2),
            p.1 ^ 2 /
              ((1 - e) * p.2.1 + e * p.2.2)))) by fun_prop)

theorem d008948
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e Sigma : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    ∫ ω, _root_.GD.N0137.d008945 m n e Sigma ω ∂_root_.GD.N0137.d008914 m n = 0 := by
  unfold _root_.GD.N0137.d008945
  rw [integral_const_mul,
    _root_.GD.N0137.d008941 m n hm hn he0 he1, mul_zero]




theorem d008949
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    {e Sigma : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hSigma : 0 ≤ Sigma) :
    _root_.GD.N0125.d008847
      (_root_.GD.N0137.d008914 m n)
      (_root_.GD.N0137.d008942 m n e Sigma)
      (_root_.GD.N0137.d008943 m n e)
      (_root_.GD.N0137.d008944 m n e)
      (((m - 1 : ℕ) : ℝ) / 2)
      (((n - 1 : ℕ) : ℝ) / 2)
      e Sigma := by
  apply _root_.GD.N0125.d008876
  · have hm1 : 0 < m - 1 := by omega
    exact div_pos (by exact_mod_cast hm1) (by norm_num)
  · have hn1 : 0 < n - 1 := by omega
    exact div_pos (by exact_mod_cast hn1) (by norm_num)
  · exact hSigma
  · exact _root_.GD.N0137.d008937 m n e
  · exact _root_.GD.N0137.d008938 m n hm hn he0 he1
  · intro ω
    rfl
  · intro ω
    rfl
  · intro ω
    rfl

end

end GD.N0137
