import GD.Module0992

open Filter MeasureTheory Set
open scoped ENNReal

namespace GD.N0232.N0720.N1464

noncomputable section

open _root_.GD.N0137
open _root_.GD.N0107
open _root_.GD.N0141
open _root_.GD.N0120
open _root_.GD.N0145
open _root_.GD.N0108
open _root_.GD.N0134
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1082
open _root_.GD.N0232.N0720.N1466

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)



theorem d015739
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
        (_root_.GD.N0232.N0720.N1082.d015379 m n hm hn U) ≤
      _root_.GD.N0232.N0720.N1466.d015735 m n hm hn U *
        _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau := by
  let e := _root_.GD.N0107.d009046 m n sigma tau
  let Sigma := _root_.GD.N0107.d009045 m n sigma tau
  let alpha : ℝ := (((m - 1 : ℕ) : ℝ) / 2)
  let beta : ℝ := (((n - 1 : ℕ) : ℝ) / 2)
  let q := U.emitted.table.d008659
  have he0 : 0 < e :=
    _root_.GD.N0107.d009050 (by omega) (by omega) hsigma htau
  have he1 : e < 1 :=
    _root_.GD.N0107.d009051 (by omega) (by omega) hsigma htau
  have he : e ∈ Icc (0 : ℝ) 1 := ⟨he0.le, he1.le⟩
  let A := U.realized e he
  have hSigma : 0 < Sigma :=
    _root_.GD.N0107.d009049 (by omega) (by omega) hsigma htau
  have halpha : 0 < alpha := by
    dsimp [alpha]
    have : 0 < (m - 1 : ℕ) := by omega
    positivity
  have hbeta : 0 < beta := by
    dsimp [beta]
    have : 0 < (n - 1 : ℕ) := by omega
    positivity
  have hq : Measurable q := U.emitted.table.d008664
  have hqBound :
      ∀ p, |q p| ≤ _root_.GD.N0108.d008888 U.emitted.table :=
    _root_.GD.N0108.d008891 U.emitted.table
  have hBoundNonneg :
      0 ≤ _root_.GD.N0108.d008888 U.emitted.table := by
    unfold _root_.GD.N0108.d008888
    positivity
  have hL2 :=
    _root_.GD.N0107.d012748
      m n hm hn mu sigma tau hsigma htau q hq hBoundNonneg hqBound
  have hLaw :=
    _root_.GD.N0107.d009052 m n hm hn mu sigma tau hsigma htau
  have hEnergyTarget :=
    _root_.GD.N0108.d008893
      U.emitted.table halpha hbeta he0 he1
  have hEnergyIter :=
    _root_.GD.N0143.d006698 _ hEnergyTarget
  have hEnergyTerm :
      _root_.GD.N0141.d006688 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (_root_.GD.N0107.d009038 m n mu sigma tau e Sigma)
          (fun omega ↦
            q (_root_.GD.N0107.d009039 m n mu sigma tau e omega,
              _root_.GD.N0107.d009040 m n mu sigma tau e omega)) =
        Sigma * _root_.GD.N0120.d008813 alpha beta e *
          _root_.GD.N0120.d008817 alpha beta e q := by
    rw [hLaw.d008878 q hq,
      _root_.GD.N0120.d008826
        halpha hbeta he0 he1 q hEnergyTarget hEnergyIter]
    ring
  have hAemitted : A.emitted = U.emitted := by
    simpa [A] using U.realized_emitted e he
  have halphaDesign :
      ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ) = alpha := by
    simp [_root_.GD.N0134.d006543, _root_.GD.N0134.d006540, alpha]
  have hbetaDesign :
      ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ) = beta := by
    simp [_root_.GD.N0134.d006543, _root_.GD.N0134.d006540, beta]
  have hEnergyBound :
      _root_.GD.N0120.d008817 alpha beta e q ≤
        _root_.GD.N0232.N0720.N1466.d015735 m n hm hn U * (U.M : ℝ) := by
    have h := _root_.GD.N0232.N0720.N1466.d015738 m n hm hn U e he
    simpa only [q, halphaDesign, hbetaDesign] using h
  have hMR : 0 < (U.M : ℝ) := by exact_mod_cast U.M_pos
  have hstep :
      (U.step : ℝ) =
        (((U.emitted.ledger.C / 2 : ℚ) : ℝ)) / (U.M : ℝ) := by
    rw [U.step_eq]
    norm_cast
  have hstepEnergy :
      (U.step : ℝ) ^ 2 * (U.M : ℝ) = _root_.GD.N0232.N0720.d014160 U := by
    rw [hstep]
    unfold _root_.GD.N0232.N0720.d014160 _root_.GD.N0117.d014154
    field_simp [ne_of_gt hMR]
  have hD :
      _root_.GD.N0107.d009038 m n mu sigma tau e Sigma =
        _root_.GD.N0107.d009090 m n := by
    funext omega
    exact _root_.GD.N0107.d012724
      m n hm hn mu sigma tau hsigma htau omega
  have hF :
      _root_.GD.N0107.d009040 m n mu sigma tau e =
        _root_.GD.N0107.d009093 m n := by
    funext omega
    exact _root_.GD.N0107.d012731
      m n hm hn mu sigma tau hsigma htau omega
  have hL :
      _root_.GD.N0107.d009039 m n mu sigma tau e =
        fun omega ↦
          _root_.GD.N0107.d009091 m n
            (_root_.GD.N0107.d009085 omega.1)
            (_root_.GD.N0107.d009085 omega.2) := by
    funext omega
    exact _root_.GD.N0107.d012729
      m n hm hn mu sigma tau hsigma htau omega
  have hObservedQ :
      (fun omega ↦
        q
          (_root_.GD.N0107.d009091 m n
              (_root_.GD.N0107.d009085 omega.1)
              (_root_.GD.N0107.d009085 omega.2),
            _root_.GD.N0107.d009093 m n omega)) =
        _root_.GD.N0232.N0720.d014159 U := by
    rfl
  rw [hD, hL, hF, hObservedQ] at hEnergyTerm
  have hCorrectionRisk :
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (_root_.GD.N0232.N0720.N1082.d015379 m n hm hn U) =
        (U.step : ℝ) ^ 2 *
          (Sigma * _root_.GD.N0120.d008813 alpha beta e *
            _root_.GD.N0120.d008817 alpha beta e q) := by
    calc
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (_root_.GD.N0232.N0720.N1082.d015379 m n hm hn U) =
        (U.step : ℝ) ^ 2 *
          _root_.GD.N0141.d006688 (_root_.GD.N0107.d009030 m n mu sigma tau)
            (_root_.GD.N0107.d009090 m n) (_root_.GD.N0232.N0720.d014159 U) := by
          unfold _root_.GD.N0141.d006684 _root_.GD.N0232.N0720.N1082.d015379 _root_.GD.N0141.d006688
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with omega
          ring
      _ = _ := by rw [hEnergyTerm]
  rw [hCorrectionRisk]
  have hscale0 :
      0 ≤ Sigma * _root_.GD.N0120.d008813 alpha beta e :=
    (mul_pos hSigma
      (_root_.GD.N0120.d008823 halpha hbeta he0 he1)).le
  have hlambda0 :
      0 ≤ _root_.GD.N0232.N0720.N1466.d015735 m n hm hn U :=
    _root_.GD.N0232.N0720.N1466.d015736 m n hm hn U
  calc
    (U.step : ℝ) ^ 2 *
          (Sigma * _root_.GD.N0120.d008813 alpha beta e *
            _root_.GD.N0120.d008817 alpha beta e q) =
        (Sigma * _root_.GD.N0120.d008813 alpha beta e) *
          ((U.step : ℝ) ^ 2 * _root_.GD.N0120.d008817 alpha beta e q) := by ring
    _ ≤ (Sigma * _root_.GD.N0120.d008813 alpha beta e) *
          ((U.step : ℝ) ^ 2 *
            (_root_.GD.N0232.N0720.N1466.d015735 m n hm hn U * (U.M : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hEnergyBound (sq_nonneg _)) hscale0
    _ = _root_.GD.N0232.N0720.N1466.d015735 m n hm hn U *
        _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau := by
      rw [show
        (U.step : ℝ) ^ 2 *
            (_root_.GD.N0232.N0720.N1466.d015735 m n hm hn U * (U.M : ℝ)) =
          _root_.GD.N0232.N0720.N1466.d015735 m n hm hn U * _root_.GD.N0232.N0720.d014160 U by
            rw [← hstepEnergy]
            ring]
      unfold _root_.GD.N0232.N0720.N1082.d015390
      dsimp [Sigma, alpha, beta, e]
      ring

end

end GD.N0232.N0720.N1464
