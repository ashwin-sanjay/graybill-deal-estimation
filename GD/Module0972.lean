import GD.Module0971



















open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1085

noncomputable section

open _root_.GD.N0137
open _root_.GD.N0107
open _root_.GD.N0141
open _root_.GD.N0120
open _root_.GD.N0145
open _root_.GD.N0108
open _root_.GD.N0134
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1201
open _root_.GD.N0232.N0720.N1082
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

noncomputable local instance d015407 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  unfold _root_.GD.N0232.N0720.N1080.d014171
  infer_instance

noncomputable local instance d015408 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance






theorem d015409
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (e : ℝ) (he : e ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0120.d008816
        ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
        ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
        e U.emitted.table.d008659 ≤
      -(5 * ((U.emitted.ledger.C : ℚ) : ℝ) / 8) := by
  let A := U.realized e he
  let C := A.d008724
  have hAemitted : A.emitted = U.emitted := by
    simpa [A] using U.realized_emitted e he
  have hbridge := U.d014131 e he
  change
    _root_.GD.N0120.d008816
          ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
          ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
          e A.emitted.table.d008659 =
        A.emitted.table.d008714 A.rho A.carrier ∧
      _root_.GD.N0120.d008817
          ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
          ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
          e A.emitted.table.d008659 =
        A.emitted.table.d008715 A.rho A.power at hbridge
  have htrace :
      _root_.GD.N0120.d008816
          ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
          ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
          e U.emitted.table.d008659 = C.trace := by
    rw [hAemitted] at hbridge
    calc
      _root_.GD.N0120.d008816
          ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
          ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
          e U.emitted.table.d008659 =
          U.emitted.table.d008714 A.rho A.carrier := hbridge.1
      _ = A.emitted.table.d008714 A.rho A.carrier := by rw [hAemitted]
      _ = C.trace := rfl
  have hCC : C.C = U.emitted.ledger.C := by
    dsimp [C,
      _root_.GD.N0113.d008651.d008723.d008724]
    exact congrArg (fun E ↦ E.ledger.C) hAemitted
  have hsmear : C.smear ≤ (C.C : ℝ) / 16 :=
    (le_abs_self C.smear).trans C.smearing_bound
  have hdensity : C.densityError ≤ (C.C : ℝ) / 16 :=
    (le_abs_self C.densityError).trans C.density_bound
  rw [htrace, C.trace_eq]
  have hatomic := C.atomic_margin
  rw [hCC] at hatomic hsmear hdensity
  linarith



theorem d015410
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (e : ℝ) (he : e ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0120.d008817
        ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
        ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
        e U.emitted.table.d008659 ≤ (U.M : ℝ) := by
  let A := U.realized e he
  let C := A.d008724
  have hAemitted : A.emitted = U.emitted := by
    simpa [A] using U.realized_emitted e he
  have hbridge := U.d014131 e he
  change
    _root_.GD.N0120.d008816
          ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
          ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
          e A.emitted.table.d008659 =
        A.emitted.table.d008714 A.rho A.carrier ∧
      _root_.GD.N0120.d008817
          ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
          ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
          e A.emitted.table.d008659 =
        A.emitted.table.d008715 A.rho A.power at hbridge
  have henergy :
      _root_.GD.N0120.d008817
          ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
          ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
          e U.emitted.table.d008659 = C.energy := by
    rw [hAemitted] at hbridge
    calc
      _root_.GD.N0120.d008817
          ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
          ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
          e U.emitted.table.d008659 =
          U.emitted.table.d008715 A.rho A.power := hbridge.2
      _ = A.emitted.table.d008715 A.rho A.power := by rw [hAemitted]
      _ = C.energy := rfl
  have hCM : C.M = U.M := by
    dsimp [C,
      _root_.GD.N0113.d008651.d008723.d008724]
    calc
      _root_.GD.N0113.d008670
          A.emitted.table A.emitted.ledger.inversePower =
          _root_.GD.N0113.d008670
            U.emitted.table U.emitted.ledger.inversePower := by rw [hAemitted]
      _ = U.M := U.M_eq.symm
  rw [henergy]
  exact C.energy_ceiling.trans_eq (by rw [hCM])



theorem d015411
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (e : ℝ) (he : e ∈ Icc (0 : ℝ) 1) :
    2 * (U.step : ℝ) *
          _root_.GD.N0120.d008816
            ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
            ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
            e U.emitted.table.d008659
        + (U.step : ℝ) ^ 2 *
          _root_.GD.N0120.d008817
            ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
            ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
            e U.emitted.table.d008659 ≤
      -(3 / 2 : ℝ) * _root_.GD.N0232.N0720.d014160 U := by
  let c : ℝ := ((U.emitted.ledger.C : ℚ) : ℝ)
  let eps : ℝ := (U.step : ℝ)
  let M : ℝ := (U.M : ℝ)
  let T := _root_.GD.N0120.d008816
    ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
    ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
    e U.emitted.table.d008659
  let E := _root_.GD.N0120.d008817
    ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ)
    ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ)
    e U.emitted.table.d008659
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast U.emitted.ledger.C_pos
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast U.M_pos
  have heps : 0 < eps := by
    dsimp [eps]
    exact_mod_cast U.step_pos
  have hT : T ≤ -(5 * c / 8) := by
    simpa only [T, c] using _root_.GD.N0232.N0720.N1085.d015409 m n hm hn U e he
  have hE : E ≤ M := by
    simpa only [E, M] using _root_.GD.N0232.N0720.N1085.d015410 m n hm hn U e he
  have hstep : eps = (c / 2) / M := by
    dsimp [eps, c, M]
    rw [U.step_eq]
    norm_cast
  have hstepRaw :
      (U.step : ℝ) =
        (((U.emitted.ledger.C / 2 : ℚ) : ℝ)) / (U.M : ℝ) := by
    rw [U.step_eq]
    norm_cast
  have hc_eq : c = 2 * eps * M := by
    rw [hstep]
    field_simp [ne_of_gt hM]
  have hstepEnergy : eps ^ 2 * M = _root_.GD.N0232.N0720.d014160 U := by
    dsimp only [eps, M]
    rw [hstepRaw]
    unfold _root_.GD.N0232.N0720.d014160 _root_.GD.N0117.d014154
    field_simp [ne_of_gt hM]
  calc
    2 * eps * T + eps ^ 2 * E ≤
        2 * eps * (-(5 * c / 8)) + eps ^ 2 * M := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ 2 * eps))
        (mul_le_mul_of_nonneg_left hE (sq_nonneg eps))
    _ = -(3 / 2 : ℝ) * (eps ^ 2 * M) := by
      rw [hc_eq]
      ring
    _ = -(3 / 2 : ℝ) * _root_.GD.N0232.N0720.d014160 U := by rw [hstepEnergy]





theorem d015412
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦
            _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U 1 omega - mu) -
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦ _root_.GD.N0232.N0720.N1080.d014175 m n omega - mu) =
      _root_.GD.N0107.d009045 m n sigma tau *
        _root_.GD.N0120.d008813
          (((m - 1 : ℕ) : ℝ) / 2)
          (((n - 1 : ℕ) : ℝ) / 2)
          (_root_.GD.N0107.d009046 m n sigma tau) *
        (2 * (U.step : ℝ) *
            _root_.GD.N0120.d008816
              (((m - 1 : ℕ) : ℝ) / 2)
              (((n - 1 : ℕ) : ℝ) / 2)
              (_root_.GD.N0107.d009046 m n sigma tau)
              U.emitted.table.d008659
          + (U.step : ℝ) ^ 2 *
            _root_.GD.N0120.d008817
              (((m - 1 : ℕ) : ℝ) / 2)
              (((n - 1 : ℕ) : ℝ) / 2)
              (_root_.GD.N0107.d009046 m n sigma tau)
              U.emitted.table.d008659) := by
  let e := _root_.GD.N0107.d009046 m n sigma tau
  let Sigma := _root_.GD.N0107.d009045 m n sigma tau
  let alpha : ℝ := (((m - 1 : ℕ) : ℝ) / 2)
  let beta : ℝ := (((n - 1 : ℕ) : ℝ) / 2)
  let q := U.emitted.table.d008659
  have he0 : 0 < e := _root_.GD.N0107.d009050 (by omega) (by omega) hsigma htau
  have he1 : e < 1 := _root_.GD.N0107.d009051 (by omega) (by omega) hsigma htau
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
  have hqBound : ∀ p, |q p| ≤ _root_.GD.N0108.d008888 U.emitted.table :=
    _root_.GD.N0108.d008891 U.emitted.table
  have hBoundNonneg : 0 ≤ _root_.GD.N0108.d008888 U.emitted.table := by
    unfold _root_.GD.N0108.d008888
    positivity
  have hL2 := _root_.GD.N0107.d012748
    m n hm hn mu sigma tau hsigma htau q hq hBoundNonneg hqBound
  have hLaw := _root_.GD.N0107.d009052
    m n hm hn mu sigma tau hsigma htau
  have hTraceTarget := _root_.GD.N0108.d008892
    U.emitted.table halpha hbeta he0 he1
  have hEnergyTarget := _root_.GD.N0108.d008893
    U.emitted.table halpha hbeta he0 he1
  have hTraceIter := _root_.GD.N0143.d006698 _ hTraceTarget
  have hEnergyIter := _root_.GD.N0143.d006698 _ hEnergyTarget
  have hTraceTerm :
      _root_.GD.N0141.d006687 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (_root_.GD.N0107.d009038 m n mu sigma tau e Sigma)
          (_root_.GD.N0107.d009039 m n mu sigma tau e)
          (fun omega ↦ q
            (_root_.GD.N0107.d009039 m n mu sigma tau e omega,
              _root_.GD.N0107.d009040 m n mu sigma tau e omega)) e =
        Sigma * _root_.GD.N0120.d008813 alpha beta e * _root_.GD.N0120.d008816 alpha beta e q := by
    rw [hLaw.d008877 q hq,
      _root_.GD.N0120.d008825
        halpha hbeta he0 he1 q hTraceTarget hTraceIter]
    ring
  have hEnergyTerm :
      _root_.GD.N0141.d006688 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (_root_.GD.N0107.d009038 m n mu sigma tau e Sigma)
          (fun omega ↦ q
            (_root_.GD.N0107.d009039 m n mu sigma tau e omega,
              _root_.GD.N0107.d009040 m n mu sigma tau e omega)) =
        Sigma * _root_.GD.N0120.d008813 alpha beta e * _root_.GD.N0120.d008817 alpha beta e q := by
    rw [hLaw.d008878 q hq,
      _root_.GD.N0120.d008826
        halpha hbeta he0 he1 q hEnergyTarget hEnergyIter]
    ring
  have hRiskIdentity := _root_.GD.N0144.d006723
    (P := _root_.GD.N0107.d009030 m n mu sigma tau)
    (U := _root_.GD.N0107.d012732 m n mu e)
    (D := _root_.GD.N0107.d009038 m n mu sigma tau e Sigma)
    (L := _root_.GD.N0107.d009039 m n mu sigma tau e)
    (Sobs := fun omega ↦
      (_root_.GD.N0107.d009039 m n mu sigma tau e omega,
        _root_.GD.N0107.d009040 m n mu sigma tau e omega))
    (q := fun p : ℝ × (ℝ × ℝ) ↦ q p.2)
    (e := e) (ε := (U.step : ℝ))
    (hq.comp measurable_snd)
    (_root_.GD.N0107.d012747 m n hm hn mu sigma tau hsigma htau)
    hL2.1 hL2.2
    (_root_.GD.N0107.d012745
      m n hm hn mu sigma tau hsigma htau)
    (_root_.GD.N0107.d012746
      m n hm hn mu sigma tau hsigma htau)
  have hCorrectedAbstract :
      (fun omega ↦
        _root_.GD.N0141.d006685
            (_root_.GD.N0107.d012732 m n mu e)
            (_root_.GD.N0107.d009038 m n mu sigma tau e Sigma)
            (_root_.GD.N0107.d009039 m n mu sigma tau e) e omega
          + (U.step : ℝ) *
            _root_.GD.N0144.d006721
              (_root_.GD.N0107.d009038 m n mu sigma tau e Sigma)
              (fun z ↦
                (_root_.GD.N0107.d009039 m n mu sigma tau e z,
                  _root_.GD.N0107.d009040 m n mu sigma tau e z))
              (fun p : ℝ × (ℝ × ℝ) ↦ q p.2) omega) =
        _root_.GD.N0141.d006686
          (_root_.GD.N0107.d012732 m n mu e)
          (_root_.GD.N0107.d009038 m n mu sigma tau e Sigma)
          (_root_.GD.N0107.d009039 m n mu sigma tau e)
          (fun omega ↦ q
            (_root_.GD.N0107.d009039 m n mu sigma tau e omega,
              _root_.GD.N0107.d009040 m n mu sigma tau e omega))
          e (U.step : ℝ) := by
    funext omega
    unfold _root_.GD.N0141.d006686 _root_.GD.N0144.d006721
    ring
  rw [hCorrectedAbstract] at hRiskIdentity
  have hD : _root_.GD.N0107.d009038 m n mu sigma tau e Sigma =
      _root_.GD.N0107.d009090 m n := by
    funext omega
    exact _root_.GD.N0107.d012724
      m n hm hn mu sigma tau hsigma htau omega
  have hL : _root_.GD.N0107.d009039 m n mu sigma tau e =
      fun omega ↦ _root_.GD.N0107.d009091 m n
        (_root_.GD.N0107.d009085 omega.1) (_root_.GD.N0107.d009085 omega.2) := by
    funext omega
    exact _root_.GD.N0107.d012729
      m n hm hn mu sigma tau hsigma htau omega
  have hF : _root_.GD.N0107.d009040 m n mu sigma tau e =
      _root_.GD.N0107.d009093 m n := by
    funext omega
    exact _root_.GD.N0107.d012731
      m n hm hn mu sigma tau hsigma htau omega
  have hObservedQ :
      (fun omega ↦ q
        (_root_.GD.N0107.d009091 m n
            (_root_.GD.N0107.d009085 omega.1)
            (_root_.GD.N0107.d009085 omega.2),
          _root_.GD.N0107.d009093 m n omega)) = _root_.GD.N0232.N0720.d014159 U := by
    rfl
  have hCorrected :
      (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U 1 omega - mu) =
        _root_.GD.N0141.d006686
          (_root_.GD.N0107.d012732 m n mu e)
          (_root_.GD.N0107.d009038 m n mu sigma tau e Sigma)
          (_root_.GD.N0107.d009039 m n mu sigma tau e)
          (fun omega ↦ q
            (_root_.GD.N0107.d009039 m n mu sigma tau e omega,
              _root_.GD.N0107.d009040 m n mu sigma tau e omega))
          e (U.step : ℝ) := by
    funext omega
    rw [hD, hL, hF, hObservedQ]
    unfold _root_.GD.N0232.N0720.N1082.d015380
    simp only [one_mul]
    exact _root_.GD.N0107.d012736
      m n mu e (U.step : ℝ) (_root_.GD.N0232.N0720.d014159 U) omega
  have hBase :
      (fun omega ↦ _root_.GD.N0232.N0720.N1080.d014175 m n omega - mu) =
        _root_.GD.N0141.d006685
          (_root_.GD.N0107.d012732 m n mu e)
          (_root_.GD.N0107.d009038 m n mu sigma tau e Sigma)
          (_root_.GD.N0107.d009039 m n mu sigma tau e) e := by
    funext omega
    rw [hD, hL]
    exact _root_.GD.N0107.d012735 m n mu e omega
  rw [hCorrected, hBase, hRiskIdentity, hTraceTerm, hEnergyTerm]
  simp only [e, Sigma, alpha, beta, q]
  ring



theorem d015413
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U 1 omega - mu) -
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦ _root_.GD.N0232.N0720.N1080.d014175 m n omega - mu) ≤
      -(3 / 2 : ℝ) * _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau := by
  rw [_root_.GD.N0232.N0720.N1085.d015412
    m n hm hn U mu sigma tau hsigma htau]
  let e := _root_.GD.N0107.d009046 m n sigma tau
  have he : e ∈ Icc (0 : ℝ) 1 :=
    ⟨(_root_.GD.N0107.d009050 (by omega) (by omega) hsigma htau).le,
      (_root_.GD.N0107.d009051 (by omega) (by omega) hsigma htau).le⟩
  have hbracket := _root_.GD.N0232.N0720.N1085.d015411
    m n hm hn U e he
  have halpha : ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ) =
      (((m - 1 : ℕ) : ℝ) / 2) := by simp [_root_.GD.N0134.d006543, _root_.GD.N0134.d006540]
  have hbeta : ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ) =
      (((n - 1 : ℕ) : ℝ) / 2) := by simp [_root_.GD.N0134.d006543, _root_.GD.N0134.d006540]
  rw [halpha, hbeta] at hbracket
  have hscale : 0 ≤ _root_.GD.N0107.d009045 m n sigma tau *
      _root_.GD.N0120.d008813
        (((m - 1 : ℕ) : ℝ) / 2)
        (((n - 1 : ℕ) : ℝ) / 2)
        (_root_.GD.N0107.d009046 m n sigma tau) := by
    exact (mul_pos
      (_root_.GD.N0107.d009049 (by omega) (by omega) hsigma htau)
      (_root_.GD.N0120.d008823
      (by
        have hm1 : 0 < (m - 1 : ℕ) := by omega
        exact div_pos (by exact_mod_cast hm1) (by norm_num))
        (by
          have hn1 : 0 < (n - 1 : ℕ) := by omega
          exact div_pos (by exact_mod_cast hn1) (by norm_num))
        (_root_.GD.N0107.d009050 (by omega) (by omega) hsigma htau)
        (_root_.GD.N0107.d009051 (by omega) (by omega) hsigma htau))).le
  have hmul := mul_le_mul_of_nonneg_left hbracket hscale
  unfold _root_.GD.N0232.N0720.N1082.d015390
  dsimp [e] at hmul
  nlinarith





theorem d015414
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (mu sigma tau b : ℝ)
    (hsigma : 0 < sigma) (htau : 0 < tau)
    (hb1 : 1 ≤ b) (hb32 : b ≤ 3 / 2) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U b omega - mu) -
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U 1 omega - mu) ≤
      -((b - 1) * (3 / 2 - b) *
        _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau) := by
  let P := _root_.GD.N0107.d009030 m n mu sigma tau
  let base : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ := fun omega ↦ _root_.GD.N0232.N0720.N1080.d014175 m n omega - mu
  let correction := _root_.GD.N0232.N0720.N1082.d015379 m n hm hn U
  have hbase : MemLp base 2 P := by
    simpa [P, base, _root_.GD.N0232.N0720.N1080.d014171] using _root_.GD.N0232.N0720.N1080.d014177 m n hm hn
      ⟨mu, sigma, tau, hsigma, htau⟩
  have hcorrection : MemLp correction 2 P := by
    simpa [P, correction, _root_.GD.N0232.N0720.N1080.d014171] using _root_.GD.N0232.N0720.N1082.d015385
      m n hm hn ⟨mu, sigma, tau, hsigma, htau⟩ U
  have hquadratic := _root_.GD.N0232.N0720.N1082.d015377
    P base correction hbase hcorrection 1 b
  have henergy0 : 0 ≤ _root_.GD.N0141.d006684 P correction :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have henergy : _root_.GD.N0141.d006684 P correction ≤
      _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau := by
    simpa [P, correction] using
      _root_.GD.N0232.N0720.N1082.d015392
        m n hm hn U mu sigma tau hsigma htau
  have hgap0 : 0 ≤ _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau :=
    (_root_.GD.N0232.N0720.N1082.d015391 m n hm hn U hsigma htau).le
  have herror (c : ℝ) :
      (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U c omega - mu) =
        fun omega ↦ base omega + c * correction omega := by
    funext omega
    rw [_root_.GD.N0232.N0720.N1082.d015381]
    dsimp only [base, correction]
    ring
  have hfull :
      _root_.GD.N0141.d006684 P (fun omega ↦ base omega + correction omega) -
          _root_.GD.N0141.d006684 P base ≤
        -(3 / 2 : ℝ) * _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau := by
    have hfun : (fun omega ↦ base omega + correction omega) =
        (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U 1 omega - mu) := by
      rw [herror 1]
      funext omega
      ring
    rw [hfun]
    simpa only [P, base] using
      _root_.GD.N0232.N0720.N1085.d015413
        m n hm hn U mu sigma tau hsigma htau
  rw [herror b, herror 1]
  have hba : 0 ≤ b - 1 := sub_nonneg.mpr hb1
  calc
    _root_.GD.N0141.d006684 P (fun omega ↦ base omega + b * correction omega) -
        _root_.GD.N0141.d006684 P (fun omega ↦ base omega + 1 * correction omega) =
      (b - 1) *
        (_root_.GD.N0141.d006684 P (fun omega ↦ base omega + correction omega) -
            _root_.GD.N0141.d006684 P base + b * _root_.GD.N0141.d006684 P correction) := by
          rw [hquadratic]
          ring
    _ ≤ (b - 1) *
        (-(3 / 2 : ℝ) * _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau +
          b * _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau) := by
      apply mul_le_mul_of_nonneg_left _ hba
      exact add_le_add hfull
        (mul_le_mul_of_nonneg_left henergy
          ((by norm_num : (0 : ℝ) ≤ 1).trans hb1))
    _ = -((b - 1) * (3 / 2 - b) *
        _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau) := by ring



theorem d015415
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    {b : ℝ} (hb1 : 1 < b) (hb32 : b < 3 / 2) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U b)
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U 1) := by
  intro theta
  have hle := _root_.GD.N0232.N0720.N1085.d015414
    m n hm hn U theta.location theta.scale₁ theta.scale₂ b
    theta.scale₁_pos theta.scale₂_pos hb1.le hb32.le
  have hnegative :
      -((b - 1) * (3 / 2 - b) *
        _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂) < 0 := by
    exact neg_lt_zero.mpr
      (mul_pos (mul_pos (sub_pos.mpr hb1) (sub_pos.mpr hb32))
        (_root_.GD.N0232.N0720.N1082.d015391 m n hm hn U
          theta.scale₁_pos theta.scale₂_pos))
  have hstrict :
      _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
          (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U b omega - theta.location) <
        _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
          (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U 1 omega - theta.location) :=
    sub_neg.mp (hle.trans_lt hnegative)
  have hupperPos : 0 < _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
      (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U 1 omega - theta.location) :=
    lt_of_le_of_lt (integral_nonneg fun _ ↦ sq_nonneg _) hstrict
  rw [_root_.GD.N0232.N0720.N1082.d015389, _root_.GD.N0232.N0720.N1082.d015389]
  exact (ENNReal.ofReal_lt_ofReal_iff hupperPos).2 hstrict



theorem d015416
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U (5 / 4) omega - mu) -
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U 1 omega - mu) ≤
      -(_root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau / 16) := by
  have h := _root_.GD.N0232.N0720.N1085.d015414
    m n hm hn U mu sigma tau (5 / 4) hsigma htau (by norm_num) (by norm_num)
  convert h using 1 <;> ring

theorem d015417
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U (5 / 4))
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U 1) := by
  exact _root_.GD.N0232.N0720.N1085.d015415
    m n hm hn U (by norm_num) (by norm_num)



theorem d015418
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (mu sigma tau a : ℝ)
    (hsigma : 0 < sigma) (htau : 0 < tau)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U (5 / 4) omega - mu) -
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U a omega - mu) ≤
      -((5 / 4 - a) ^ 2 *
        _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau) := by
  let P := _root_.GD.N0107.d009030 m n mu sigma tau
  let base : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ := fun omega ↦ _root_.GD.N0232.N0720.N1080.d014175 m n omega - mu
  let correction := _root_.GD.N0232.N0720.N1082.d015379 m n hm hn U
  have hbase : MemLp base 2 P := by
    simpa [P, base, _root_.GD.N0232.N0720.N1080.d014171] using _root_.GD.N0232.N0720.N1080.d014177 m n hm hn
      ⟨mu, sigma, tau, hsigma, htau⟩
  have hcorrection : MemLp correction 2 P := by
    simpa [P, correction, _root_.GD.N0232.N0720.N1080.d014171] using _root_.GD.N0232.N0720.N1082.d015385
      m n hm hn ⟨mu, sigma, tau, hsigma, htau⟩ U
  have hquadratic := _root_.GD.N0232.N0720.N1082.d015377
    P base correction hbase hcorrection a (5 / 4)
  have henergy : _root_.GD.N0141.d006684 P correction ≤
      _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau := by
    simpa [P, correction] using
      _root_.GD.N0232.N0720.N1082.d015392
        m n hm hn U mu sigma tau hsigma htau
  have herror (c : ℝ) :
      (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U c omega - mu) =
        fun omega ↦ base omega + c * correction omega := by
    funext omega
    rw [_root_.GD.N0232.N0720.N1082.d015381]
    dsimp only [base, correction]
    ring
  have hfull :
      _root_.GD.N0141.d006684 P (fun omega ↦ base omega + correction omega) -
          _root_.GD.N0141.d006684 P base ≤
        -(3 / 2 : ℝ) * _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau := by
    have hfun : (fun omega ↦ base omega + correction omega) =
        (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U 1 omega - mu) := by
      rw [herror 1]
      funext omega
      ring
    rw [hfun]
    simpa only [P, base] using
      _root_.GD.N0232.N0720.N1085.d015413
        m n hm hn U mu sigma tau hsigma htau
  rw [herror (5 / 4), herror a]
  have hba : 0 ≤ 5 / 4 - a := by linarith
  calc
    _root_.GD.N0141.d006684 P (fun omega ↦ base omega + (5 / 4) * correction omega) -
        _root_.GD.N0141.d006684 P (fun omega ↦ base omega + a * correction omega) =
      (5 / 4 - a) *
        (_root_.GD.N0141.d006684 P (fun omega ↦ base omega + correction omega) -
            _root_.GD.N0141.d006684 P base +
          (5 / 4 + a - 1) * _root_.GD.N0141.d006684 P correction) := hquadratic
    _ ≤ (5 / 4 - a) *
        (-(3 / 2 : ℝ) * _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau +
          (5 / 4 + a - 1) *
            _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau) := by
      apply mul_le_mul_of_nonneg_left _ hba
      exact add_le_add hfull
        (mul_le_mul_of_nonneg_left henergy (by linarith))
    _ = -((5 / 4 - a) ^ 2 *
        _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau) := by ring



theorem d015419
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U (5 / 4))
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U a) := by
  intro theta
  have hle := _root_.GD.N0232.N0720.N1085.d015418
    m n hm hn U theta.location theta.scale₁ theta.scale₂ a
    theta.scale₁_pos theta.scale₂_pos ha0 ha1
  have hpositive : 0 < (5 / 4 - a) ^ 2 *
      _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U theta.scale₁ theta.scale₂ := by
    exact mul_pos (sq_pos_of_pos (by linarith))
      (_root_.GD.N0232.N0720.N1082.d015391 m n hm hn U theta.scale₁_pos theta.scale₂_pos)
  have hstrict : _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
          (fun omega ↦
            _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U (5 / 4) omega - theta.location) <
        _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
          (fun omega ↦
            _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U a omega - theta.location) :=
    sub_neg.mp (hle.trans_lt (neg_neg_of_pos hpositive))
  have hupperPos : 0 < _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
      (fun omega ↦ _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U a omega - theta.location) :=
    lt_of_le_of_lt (integral_nonneg fun _ ↦ sq_nonneg _) hstrict
  rw [_root_.GD.N0232.N0720.N1082.d015389, _root_.GD.N0232.N0720.N1082.d015389]
  exact (ENNReal.ofReal_lt_ofReal_iff hupperPos).2 hstrict




noncomputable def d015420
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) : _root_.GD.N0232.N0720.N1159.d014639 m n :=
  _root_.GD.N0232.N0720.N1159.d014657 m n hm hn
    (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U (5 / 4))
    (_root_.GD.N0232.N0720.N1082.d015396
      m n hm hn U (5 / 4))
    (fun theta ↦
      (_root_.GD.N0232.N0720.N1085.d015417 m n hm hn U theta).trans
        ((_root_.GD.N0232.N0720.N1082.d015399 m n hm hn U 1 zero_lt_one le_rfl) theta))

@[simp] theorem d015421
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    (_root_.GD.N0232.N0720.N1085.d015420 m n hm hn U).value =
      _root_.GD.N0232.N0720.N1082.d015387 m n hm hn U (5 / 4) := rfl


theorem d015422
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U 1 1 / 16 ≤
      _root_.GD.N0232.N0720.N1201.d015333 m n
        (_root_.GD.N0232.N0720.N1082.d015397 m n hm hn U 1 zero_lt_one le_rfl) := by
  let s₁ := _root_.GD.N0232.N0720.N1082.d015397 m n hm hn U 1 zero_lt_one le_rfl
  let d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1082.d015387 m n hm hn U (5 / 4)
  have hbelow : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) s₁.value d := by
    intro theta
    exact (_root_.GD.N0232.N0720.N1085.d015417 m n hm hn U theta).le
  have hrisk := _root_.GD.N0232.N0720.N1085.d015416
    m n hm hn U 0 1 1 zero_lt_one zero_lt_one
  have hnormFull := _root_.GD.N0232.N0720.N1082.d015402
    m n hm hn U 1
  have hnormFive := _root_.GD.N0232.N0720.N1082.d015402
    m n hm hn U (5 / 4)
  have hnormGap : _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U 1 1 / 16 ≤
      ‖s₁.value‖ ^ 2 - ‖d‖ ^ 2 := by
    dsimp only [s₁, d]
    rw [_root_.GD.N0232.N0720.N1082.d015398, hnormFull, hnormFive]
    simp only [sub_zero] at hrisk
    nlinarith
  exact hnormGap.trans
    (_root_.GD.N0232.N0720.N1201.d015338
      m n s₁ d hbelow)



theorem d015423
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (5 / 4 - a) ^ 2 * _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U 1 1 ≤
      _root_.GD.N0232.N0720.N1201.d015333 m n
        (_root_.GD.N0232.N0720.N1082.d015397 m n hm hn U a ha ha1) := by
  let sa := _root_.GD.N0232.N0720.N1082.d015397 m n hm hn U a ha ha1
  let d : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1082.d015387 m n hm hn U (5 / 4)
  have hbelow : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) sa.value d := by
    intro theta
    exact (_root_.GD.N0232.N0720.N1085.d015419
      m n hm hn U ha.le ha1 theta).le
  have hrisk := _root_.GD.N0232.N0720.N1085.d015418
    m n hm hn U 0 1 1 a zero_lt_one zero_lt_one ha.le ha1
  have hnormA := _root_.GD.N0232.N0720.N1082.d015402
    m n hm hn U a
  have hnormFive := _root_.GD.N0232.N0720.N1082.d015402
    m n hm hn U (5 / 4)
  have hnormGap :
      (5 / 4 - a) ^ 2 * _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U 1 1 ≤
        ‖sa.value‖ ^ 2 - ‖d‖ ^ 2 := by
    dsimp only [sa, d]
    rw [_root_.GD.N0232.N0720.N1082.d015398, hnormA, hnormFive]
    simp only [sub_zero] at hrisk
    nlinarith
  exact hnormGap.trans
    (_root_.GD.N0232.N0720.N1201.d015338
      m n sa d hbelow)



theorem d015424
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U 1 1 / 16 ≤
      _root_.GD.N0232.N0720.N1201.d015333 m n
        (_root_.GD.N0232.N0720.N1082.d015397 m n hm hn U a ha ha1) := by
  have hsharp := _root_.GD.N0232.N0720.N1085.d015423
    m n hm hn U a ha ha1
  have hgap0 :=
    (_root_.GD.N0232.N0720.N1082.d015391 m n hm hn U zero_lt_one zero_lt_one).le
  have hcoef : (1 / 16 : ℝ) ≤ (5 / 4 - a) ^ 2 := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcoef hgap0
  have hfloor : _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U 1 1 / 16 ≤
      (5 / 4 - a) ^ 2 * _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U 1 1 := by
    nlinarith
  exact hfloor.trans hsharp



theorem d015425
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (a : ℕ → ℝ) (ha : ∀ j, 0 < a j) (ha1 : ∀ j, a j ≤ 1) :
    ¬ Tendsto
      (fun j ↦ _root_.GD.N0232.N0720.N1201.d015333 m n
        (_root_.GD.N0232.N0720.N1082.d015397 m n hm hn U (a j) (ha j) (ha1 j)))
      atTop (nhds 0) := by
  intro hzero
  have hfloor : 0 < _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U 1 1 / 16 :=
    div_pos (_root_.GD.N0232.N0720.N1082.d015391 m n hm hn U zero_lt_one zero_lt_one)
      (by norm_num)
  have heventually : ∀ᶠ j : ℕ in atTop,
      _root_.GD.N0232.N0720.N1201.d015333 m n
          (_root_.GD.N0232.N0720.N1082.d015397 m n hm hn U (a j) (ha j) (ha1 j)) <
        _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U 1 1 / 16 := by
    have hopen : Set.Iio (_root_.GD.N0232.N0720.N1082.d015390 m n hm hn U 1 1 / 16) ∈ nhds (0 : ℝ) := by
      exact Iio_mem_nhds hfloor
    exact hzero.eventually hopen
  have hcontra : ∀ᶠ _j : ℕ in atTop, False := by
    filter_upwards [heventually] with j hj
    exact (not_lt_of_ge
      (_root_.GD.N0232.N0720.N1085.d015424
        m n hm hn U (a j) (ha j) (ha1 j))) hj
  have hbot : (atTop : Filter ℕ) = ⊥ :=
    Filter.eventually_false_iff_eq_bot.mp hcontra
  haveI : (atTop : Filter ℕ).NeBot := inferInstance
  exact (show (atTop : Filter ℕ) ≠ ⊥ from Filter.NeBot.ne inferInstance) hbot

theorem d015426
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    0 < _root_.GD.N0232.N0720.N1201.d015333 m n
      (_root_.GD.N0232.N0720.N1082.d015397 m n hm hn U 1 zero_lt_one le_rfl) := by
  exact lt_of_lt_of_le
    (div_pos (_root_.GD.N0232.N0720.N1082.d015391 m n hm hn U zero_lt_one zero_lt_one)
      (by norm_num))
    (_root_.GD.N0232.N0720.N1085.d015422 m n hm hn U)


theorem d015427
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    ¬ _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1082.d015397 m n hm hn U 1 zero_lt_one le_rfl).value := by
  intro hterminal
  have hzero :=
    (_root_.GD.N0232.N0720.N1082.d015401
      m n (_root_.GD.N0232.N0720.N1082.d015397 m n hm hn U 1 zero_lt_one le_rfl)).2 hterminal
  exact (ne_of_gt (_root_.GD.N0232.N0720.N1085.d015426 m n hm hn U)) hzero

end

end N1085
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1085.d015409
#print axioms _root_.GD.N0232.N0720.N1085.d015411
#print axioms _root_.GD.N0232.N0720.N1085.d015413
#print axioms _root_.GD.N0232.N0720.N1085.d015414
#print axioms _root_.GD.N0232.N0720.N1085.d015415
#print axioms _root_.GD.N0232.N0720.N1085.d015416
#print axioms _root_.GD.N0232.N0720.N1085.d015418
#print axioms _root_.GD.N0232.N0720.N1085.d015419
#print axioms _root_.GD.N0232.N0720.N1085.d015420
#print axioms _root_.GD.N0232.N0720.N1085.d015422
#print axioms _root_.GD.N0232.N0720.N1085.d015424
#print axioms _root_.GD.N0232.N0720.N1085.d015425
#print axioms _root_.GD.N0232.N0720.N1085.d015427
