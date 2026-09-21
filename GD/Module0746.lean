import GD.Module0725
import GD.Module0726
import GD.Module0637
import GD.Module0253
import GD.Module0699

























open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace GD
namespace N0232
namespace N0719
namespace N0934

noncomputable section

open _root_.GD.N0232.N0719.N0859
open _root_.GD.N0232.N0719.N0858
open _root_.GD.N0232.N0719.N0845
open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0232.N0719.N0910
open _root_.GD.N0232.N0719.N1024
open _root_.GD.N0232.N0719.N0933
open _root_.GD.N0232.N0719.N0886


theorem d011154
    (location : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, (x - location) ^ 2 ∂gaussianReal location v) =
      (v : ℝ) := by
  have h := variance_fun_id_gaussianReal (μ := location) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa using h


theorem d011155
    {k : ℕ} (location : ℝ) (y : Fin k → ℝ) :
    _root_.GD.N0232.N0719.N0910.d010278 location y ^ 2 ≤
      (k : ℝ) * ∑ i, (y i - location) ^ 2 := by
  simpa [_root_.GD.N0232.N0719.N0910.d010278, sq_abs] using
    (sq_sum_le_card_mul_sum_sq
      (s := Finset.univ) (f := fun i ↦ |y i - location|))


theorem d011156
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ) :
    (∫ y : Fin k → ℝ, ∑ i, (y i - location) ^ 2
        ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes location scales) =
      ∑ i, scales i ^ 2 / (sizes i : ℝ) := by
  rw [_root_.GD.N0232.N0719.N0933.d009302
    k sizes hsizes location scales]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _hi
    have heval :
        (∫ y : Fin k → ℝ, (y i - location) ^ 2
          ∂Measure.pi (fun j : Fin k ↦
            gaussianReal location
              (.mk (scales j ^ 2 / (sizes j : ℝ))
                (div_nonneg (sq_nonneg (scales j))
                  (Nat.cast_nonneg (sizes j)))))) =
          ∫ x : ℝ, (x - location) ^ 2
            ∂gaussianReal location
              (.mk (scales i ^ 2 / (sizes i : ℝ))
                (div_nonneg (sq_nonneg (scales i))
                  (Nat.cast_nonneg (sizes i)))) := by
      exact integral_comp_eval
        (X := fun _ : Fin k ↦ ℝ)
        (μ := fun j : Fin k ↦
          gaussianReal location
            (.mk (scales j ^ 2 / (sizes j : ℝ))
              (div_nonneg (sq_nonneg (scales j))
                (Nat.cast_nonneg (sizes j)))))
        (i := i) (f := fun x : ℝ ↦ (x - location) ^ 2)
        (((measurable_id.sub measurable_const).pow_const 2).aestronglyMeasurable)
    rw [heval]
    exact _root_.GD.N0232.N0719.N0934.d011154 location
      (.mk (scales i ^ 2 / (sizes i : ℝ))
        (div_nonneg (sq_nonneg (scales i))
          (Nat.cast_nonneg (sizes i))))
  · intro i _hi
    have hi : Integrable
        (fun x : ℝ ↦ (x - location) ^ 2)
        (gaussianReal location
          (.mk (scales i ^ 2 / (sizes i : ℝ))
            (div_nonneg (sq_nonneg (scales i))
              (Nat.cast_nonneg (sizes i))))) := by
      exact ((memLp_id_gaussianReal
        (μ := location)
        (v := .mk (scales i ^ 2 / (sizes i : ℝ))
          (div_nonneg (sq_nonneg (scales i))
            (Nat.cast_nonneg (sizes i)))) 2).sub
          (memLp_const location)).integrable_sq
    exact integrable_comp_eval
      (X := fun _ : Fin k ↦ ℝ)
      (μ := fun j : Fin k ↦
        gaussianReal location
          (.mk (scales j ^ 2 / (sizes j : ℝ))
            (div_nonneg (sq_nonneg (scales j))
              (Nat.cast_nonneg (sizes j)))))
      (i := i) (f := fun x : ℝ ↦ (x - location) ^ 2) hi



theorem d011157
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (location : ℝ) (scales : Fin k → ℝ) :
    (∫ z : (Fin k → ℝ) × (Fin k → ℝ),
        _root_.GD.N0232.N0719.N0910.d010278 location z.1 ^ 2
      ∂((_root_.GD.N0232.N0719.N0933.d009300 k sizes location scales).prod
        (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales))) =
      ∫ y : Fin k → ℝ, _root_.GD.N0232.N0719.N0910.d010278 location y ^ 2
        ∂_root_.GD.N0232.N0719.N0933.d009300 k sizes location scales := by
  letI : IsProbabilityMeasure
      (_root_.GD.N0232.N0719.N0933.d009300 k sizes location scales) := by
    rw [_root_.GD.N0232.N0719.N0933.d009302
      k sizes hsizes location scales]
    infer_instance
  letI : IsProbabilityMeasure
      (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales) :=
    _root_.GD.N0232.N0719.N0910.d010289 sizes hsizes scales
  have hIntegrable : Integrable
      (fun y : Fin k → ℝ ↦ _root_.GD.N0232.N0719.N0910.d010278 location y ^ 2)
      (_root_.GD.N0232.N0719.N0933.d009300 k sizes location scales) :=
    (_root_.GD.N0232.N0719.N0910.d010291
      sizes hsizes location scales).integrable_sq
  rw [integral_prod _ (hIntegrable.comp_fst
    (_root_.GD.N0232.N0719.N0933.d009301 k sizes scales))]
  simp



theorem d011158
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0141.d006684 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
        (fun omega ↦ _root_.GD.N0232.N0719.N0859.d010815
          k sizes omega - theta.location) ≤
      (k : ℝ) * ∑ i, theta.scale i ^ 2 / (sizes i : ℝ) := by
  let μY := _root_.GD.N0232.N0719.N0933.d009300 k sizes theta.location theta.scale
  let μT := _root_.GD.N0232.N0719.N0933.d009301 k sizes theta.scale
  let F : _root_.GD.N0232.N0719.N0900.d009096 k → ℝ :=
    fun s ↦ (_root_.GD.N0232.N0719.N0900.d009110 s - theta.location) ^ 2
  have htransport := _root_.GD.N0232.N0719.N0933.d009310
    k sizes hsizes theta.location theta.scale F
      (((_root_.GD.N0232.N0719.N0900.d009121.sub measurable_const).pow_const 2))
  have hbaseIntegrable : Integrable
      (fun z : (Fin k → ℝ) × (Fin k → ℝ) ↦
        (_root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0933.d009305 k z) -
          theta.location) ^ 2) (μY.prod μT) := by
    exact (_root_.GD.N0232.N0719.N0910.d010292
      (by omega : 0 < k) sizes hsizes theta.location theta.scale).integrable_sq
  have hcenteredIntegrable : Integrable
      (fun z : (Fin k → ℝ) × (Fin k → ℝ) ↦
        _root_.GD.N0232.N0719.N0910.d010278 theta.location z.1 ^ 2) (μY.prod μT) := by
    letI : IsProbabilityMeasure μT := by
      dsimp [μT]
      exact _root_.GD.N0232.N0719.N0910.d010289
        sizes hsizes theta.scale
    exact ((_root_.GD.N0232.N0719.N0910.d010291
      sizes hsizes theta.location theta.scale).integrable_sq).comp_fst μT
  have hsumIntegrable : Integrable
      (fun y : Fin k → ℝ ↦
        (k : ℝ) * ∑ i, (y i - theta.location) ^ 2) μY := by
    exact (integrable_finsetSum Finset.univ fun i _ ↦
      (_root_.GD.N0232.N0719.N0910.d010290
        sizes hsizes theta.location theta.scale i).integrable_sq).const_mul _
  calc
    _root_.GD.N0141.d006684 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
        (fun omega ↦ _root_.GD.N0232.N0719.N0859.d010815
          k sizes omega - theta.location) =
        ∫ z : (Fin k → ℝ) × (Fin k → ℝ),
          (_root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0933.d009305 k z) -
            theta.location) ^ 2 ∂(μY.prod μT) := by
      change
        (∫ omega,
          (_root_.GD.N0232.N0719.N0900.d009111 k sizes omega - theta.location) ^ 2
            ∂_root_.GD.N0232.N0719.d009176
              k sizes theta.location theta.scale) =
          ∫ z : (Fin k → ℝ) × (Fin k → ℝ),
            (_root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0933.d009305 k z) -
              theta.location) ^ 2 ∂(μY.prod μT)
      simpa [_root_.GD.N0232.N0719.N0900.d009111, μY, μT, F] using htransport
    _ ≤ ∫ z : (Fin k → ℝ) × (Fin k → ℝ),
        _root_.GD.N0232.N0719.N0910.d010278 theta.location z.1 ^ 2 ∂(μY.prod μT) := by
      apply integral_mono hbaseIntegrable hcenteredIntegrable
      intro z
      have habs := _root_.GD.N0232.N0719.N0910.d010281
        (by omega : 0 < k) theta.location (_root_.GD.N0232.N0719.N0933.d009305 k z)
      have hnonneg := _root_.GD.N0232.N0719.N0910.d010279 theta.location z.1
      simp only [_root_.GD.N0232.N0719.N0933.d009305] at habs
      simpa only [sq_abs] using
        (sq_le_sq₀
          (abs_nonneg
            (_root_.GD.N0232.N0719.N0900.d009110 (_root_.GD.N0232.N0719.N0933.d009305 k z) -
              theta.location)) hnonneg).2 habs
    _ = ∫ y : Fin k → ℝ, _root_.GD.N0232.N0719.N0910.d010278 theta.location y ^ 2 ∂μY := by
      exact _root_.GD.N0232.N0719.N0934.d011157
        sizes hsizes theta.location theta.scale
    _ ≤ ∫ y : Fin k → ℝ,
        (k : ℝ) * ∑ i, (y i - theta.location) ^ 2 ∂μY := by
      apply integral_mono
        (_root_.GD.N0232.N0719.N0910.d010291
          sizes hsizes theta.location theta.scale).integrable_sq
        hsumIntegrable
      intro y
      exact _root_.GD.N0232.N0719.N0934.d011155 theta.location y
    _ = (k : ℝ) * ∑ i, theta.scale i ^ 2 / (sizes i : ℝ) := by
      rw [integral_const_mul]
      rw [_root_.GD.N0232.N0719.N0934.d011156
        sizes hsizes theta.location theta.scale]



theorem d011159
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (htotal : _root_.GD.N0232.N0719.N0845.d010886 theta = 1) :
    ∑ i, theta.scale i ^ 2 / (sizes i : ℝ) ≤ 1 := by
  calc
    ∑ i, theta.scale i ^ 2 / (sizes i : ℝ) ≤
        ∑ i, theta.scale i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact div_le_self (sq_nonneg (theta.scale i)) (by
        exact_mod_cast (show 1 ≤ sizes i from le_trans (by omega) (hsizes i)))
    _ ≤ (∑ i, theta.scale i) ^ 2 := by
      exact Finset.sum_sq_le_sq_sum_of_nonneg
        (s := Finset.univ) (f := theta.scale)
        (fun i _ ↦ (theta.scale_pos i).le)
    _ = 1 := by
      have hsum : ∑ i, theta.scale i = 1 := by
        simpa only [_root_.GD.N0232.N0719.N0845.d010886] using htotal
      rw [hsum]
      norm_num



theorem d011160
    {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (htotal : _root_.GD.N0232.N0719.N0845.d010886 theta = 1) :
    ∑ i, theta.scale i ^ 2 / (sizes i : ℝ) ≤ (1 : ℝ) / 2 := by
  calc
    ∑ i, theta.scale i ^ 2 / (sizes i : ℝ) ≤
        ∑ i, theta.scale i ^ 2 / 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact div_le_div_of_nonneg_left (sq_nonneg (theta.scale i))
        (by norm_num) (by exact_mod_cast hsizes i)
    _ = (∑ i, theta.scale i ^ 2) / 2 := by
      rw [Finset.sum_div]
    _ ≤ (1 : ℝ) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      calc
        ∑ i, theta.scale i ^ 2 ≤ (∑ i, theta.scale i) ^ 2 := by
          exact Finset.sum_sq_le_sq_sum_of_nonneg
            (s := Finset.univ) (f := theta.scale)
            (fun i _ ↦ (theta.scale_pos i).le)
        _ = 1 := by
          have hsum : ∑ i, theta.scale i = 1 := by
            simpa only [_root_.GD.N0232.N0719.N0845.d010886] using htotal
          rw [hsum]
          norm_num





theorem d011161
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (htotal : _root_.GD.N0232.N0719.N0845.d010886 theta = 1) :
    _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta < (k : ℝ) / 2 := by
  have hcross : _root_.GD.N0232.N0719.N1024.d010712 k sizes hk theta.scale < 0 :=
    _root_.GD.N0232.N0719.N1024.d010804 hk sizes hsizes theta.scale theta.scale_pos
  have hstep : 0 < _root_.GD.N0232.N0719.N1024.d010727 k sizes hk := _root_.GD.N0232.N0719.N1024.d010728 k sizes hk
  have hcapLtBaseline : _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta <
      _root_.GD.N0141.d006684 (_root_.GD.N0232.N0719.N0859.d010812 k sizes theta)
        (fun omega ↦ _root_.GD.N0232.N0719.N0859.d010815
          k sizes omega - theta.location) := by
    unfold _root_.GD.N0232.N0719.N0858.d010851
    nlinarith
  have hbaseline := _root_.GD.N0232.N0719.N0934.d011158
    k sizes hk hsizes theta
  have hvariance := _root_.GD.N0232.N0719.N0934.d011160
    sizes hsizes theta htotal
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  exact hcapLtBaseline.trans_le
    (hbaseline.trans (by nlinarith))





theorem d011162
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (htotal : _root_.GD.N0232.N0719.N0845.d010886 theta = 1) :
    _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes theta < (k : ℝ) := by
  have hhalf := _root_.GD.N0232.N0719.N0934.d011161
    k sizes hk hsizes theta htotal
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  nlinarith



theorem d011163
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes
      (_root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k) theta) < (k : ℝ) := by
  exact _root_.GD.N0232.N0719.N0934.d011162
    k sizes hk hsizes
    (_root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k) theta)
    (_root_.GD.N0232.N0719.N0845.d010893 (by omega : 0 < k) theta)


theorem d011164
    (k : ℕ) (sizes : Fin k → ℕ)
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (theta : _root_.GD.N0232.N0719.N0859.d010809 k) :
    _root_.GD.N0232.N0719.N0858.d010851 k sizes hk hsizes
      (_root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k) theta) < (k : ℝ) / 2 := by
  exact _root_.GD.N0232.N0719.N0934.d011161
    k sizes hk hsizes
    (_root_.GD.N0232.N0719.N0845.d010890 (by omega : 0 < k) theta)
    (_root_.GD.N0232.N0719.N0845.d010893 (by omega : 0 < k) theta)

end

end N0934
end N0719
end N0232
end GD

#print axioms _root_.GD.N0232.N0719.N0934.d011158
#print axioms _root_.GD.N0232.N0719.N0934.d011161
#print axioms _root_.GD.N0232.N0719.N0934.d011162
#print axioms _root_.GD.N0232.N0719.N0934.d011163
