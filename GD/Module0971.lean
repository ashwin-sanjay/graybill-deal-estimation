import GD.Module0969






























open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1082

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
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

noncomputable local instance d015375 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  unfold _root_.GD.N0232.N0720.N1080.d014171
  infer_instance

noncomputable local instance d015376 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance





theorem d015377
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (base correction : Omega → ℝ)
    (hbase : MemLp base 2 P) (hcorrection : MemLp correction 2 P)
    (a b : ℝ) :
    _root_.GD.N0141.d006684 P (fun omega ↦ base omega + b * correction omega) -
        _root_.GD.N0141.d006684 P (fun omega ↦ base omega + a * correction omega) =
      (b - a) *
        (_root_.GD.N0141.d006684 P (fun omega ↦ base omega + correction omega) -
            _root_.GD.N0141.d006684 P base +
          (b + a - 1) * _root_.GD.N0141.d006684 P correction) := by
  have ha : MemLp (fun omega ↦ base omega + a * correction omega) 2 P := by
    apply (memLp_congr_ae ?_).2
      (hbase.add (hcorrection.const_mul a))
    filter_upwards [] with omega
    rfl
  have hb : MemLp (fun omega ↦ base omega + b * correction omega) 2 P := by
    apply (memLp_congr_ae ?_).2
      (hbase.add (hcorrection.const_mul b))
    filter_upwards [] with omega
    rfl
  have hone : MemLp (fun omega ↦ base omega + correction omega) 2 P := by
    apply (memLp_congr_ae ?_).2 (hbase.add hcorrection)
    filter_upwards [] with omega
    rfl
  unfold _root_.GD.N0141.d006684
  calc
    (∫ omega, (base omega + b * correction omega) ^ 2 ∂P) -
          ∫ omega, (base omega + a * correction omega) ^ 2 ∂P =
        ∫ omega,
          ((base omega + b * correction omega) ^ 2 -
            (base omega + a * correction omega) ^ 2) ∂P := by
      rw [integral_sub hb.integrable_sq ha.integrable_sq]
    _ = ∫ omega,
          (b - a) *
            (((base omega + correction omega) ^ 2 - base omega ^ 2) +
              (b + a - 1) * correction omega ^ 2) ∂P := by
      apply integral_congr_ae
      filter_upwards [] with omega
      ring
    _ = (b - a) *
          ∫ omega,
            (((base omega + correction omega) ^ 2 - base omega ^ 2) +
              (b + a - 1) * correction omega ^ 2) ∂P := by
      rw [integral_const_mul]
    _ = (b - a) *
        ((∫ omega, (base omega + correction omega) ^ 2 ∂P) -
            ∫ omega, base omega ^ 2 ∂P +
          (b + a - 1) * ∫ omega, correction omega ^ 2 ∂P) := by
      congr 1
      rw [← integral_sub hone.integrable_sq hbase.integrable_sq,
        ← integral_const_mul]
      exact integral_add
        (hone.integrable_sq.sub hbase.integrable_sq)
        (hcorrection.integrable_sq.const_mul (b + a - 1))





theorem d015378
    {fullGap energy gap a b : ℝ}
    (hfull : fullGap ≤ -gap)
    (henergy0 : 0 ≤ energy) (henergy : energy ≤ gap)
    (_hgap : 0 ≤ gap) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (b - a) * (fullGap + (b + a - 1) * energy) ≤
      -((b - a) * (1 - a) * gap) := by
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have ha1 : a ≤ 1 := hab.trans hb
  by_cases hcoefficient : b + a - 1 ≤ 0
  · have hterm : (b + a - 1) * energy ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcoefficient henergy0
    have hins : fullGap + (b + a - 1) * energy ≤ -gap := by
      linarith
    have htarget : -gap ≤ -(1 - a) * gap := by
      nlinarith
    have := mul_le_mul_of_nonneg_left (hins.trans htarget) hba
    nlinarith
  · have hcoefficient0 : 0 ≤ b + a - 1 := le_of_not_ge hcoefficient
    have hterm :
        (b + a - 1) * energy ≤ (b + a - 1) * gap :=
      mul_le_mul_of_nonneg_left henergy hcoefficient0
    have hins :
        fullGap + (b + a - 1) * energy ≤
          -(2 - b - a) * gap := by
      nlinarith
    have htarget : -(2 - b - a) * gap ≤ -(1 - a) * gap := by
      nlinarith
    have := mul_le_mul_of_nonneg_left (hins.trans htarget) hba
    nlinarith




def d015379
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  fun omega ↦
    (U.step : ℝ) * _root_.GD.N0107.d009090 m n omega *
      _root_.GD.N0232.N0720.d014159 U omega




def d015380
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) (a : ℝ) :
    _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ :=
  _root_.GD.N0107.d012734 m n (a * (U.step : ℝ)) (_root_.GD.N0232.N0720.d014159 U)

theorem d015381
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) (a : ℝ) :
    _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U a =
      fun omega ↦ _root_.GD.N0232.N0720.N1080.d014175 m n omega +
        a * _root_.GD.N0232.N0720.N1082.d015379 m n hm hn U omega := by
  funext omega
  unfold _root_.GD.N0232.N0720.N1082.d015380 _root_.GD.N0232.N0720.N1082.d015379 _root_.GD.N0232.N0720.N1080.d014175
    _root_.GD.N0107.d012734
  ring

theorem d015382
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    Measurable (_root_.GD.N0232.N0720.N1082.d015379 m n hm hn U) := by
  unfold _root_.GD.N0232.N0720.N1082.d015379
  exact
    ((measurable_const.mul
      (_root_.GD.N0117.d014142 m n)).mul
        (_root_.GD.N0232.N0720.d014161 U))

theorem d015383
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) (a : ℝ) :
    Measurable (_root_.GD.N0232.N0720.N1082.d015380 m n hm hn U a) := by
  rw [_root_.GD.N0232.N0720.N1082.d015381]
  exact
    (_root_.GD.N0117.d014146 m n).add
      (measurable_const.mul (_root_.GD.N0232.N0720.N1082.d015382 m n hm hn U))



theorem d015384
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) (a d : ℝ)
    {c : ℝ} (hc : c ≠ 0) (omega : _root_.GD.N0232.N0720.N1080.d014170 m n) :
    _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U a
        (_root_.GD.N0107.d009024 m n d c c omega) =
      d + c * _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U a omega := by
  have hmy :=
    _root_.GD.N0107.d009086 (by omega : 0 < n) d c omega.2
  have hx :=
    _root_.GD.N0117.d014148
      hm d c omega.1
  have hy :=
    _root_.GD.N0117.d014148
      hn d c omega.2
  have hD :=
    _root_.GD.N0117.d014149
      hm hn d c omega
  have hq := _root_.GD.N0232.N0720.d014163 U d hc omega
  have hD' :
      _root_.GD.N0107.d009090 m n
          (_root_.GD.N0107.d009018 m d c omega.1, _root_.GD.N0107.d009018 n d c omega.2) =
        c * _root_.GD.N0107.d009090 m n omega := by
    simpa [_root_.GD.N0107.d009024] using hD
  have hq' :
      _root_.GD.N0232.N0720.d014159 U
          (_root_.GD.N0107.d009018 m d c omega.1, _root_.GD.N0107.d009018 n d c omega.2) =
        _root_.GD.N0232.N0720.d014159 U omega := by
    simpa [_root_.GD.N0107.d009024] using hq
  unfold _root_.GD.N0232.N0720.N1082.d015380 _root_.GD.N0107.d012734 _root_.GD.N0107.d012733
    _root_.GD.N0107.d009084 _root_.GD.N0107.d009024
  simp only
  rw [hmy, hx, hy,
    _root_.GD.N0117.d014150 hm hn hc,
    hD', hq']
  ring


theorem d015385 (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    MemLp (_root_.GD.N0232.N0720.N1082.d015379 m n hm hn U) 2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  let q := U.emitted.table.d008659
  have hq : Measurable q := U.emitted.table.d008664
  have hB : 0 ≤ _root_.GD.N0108.d008888 U.emitted.table := by
    unfold _root_.GD.N0108.d008888
    positivity
  have hqBound :
      ∀ p, |q p| ≤ _root_.GD.N0108.d008888 U.emitted.table :=
    _root_.GD.N0108.d008891 U.emitted.table
  have hcarrier :=
    (_root_.GD.N0107.d012749
      m n hm hn theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos theta.scale₂_pos q hq hB hqBound).2
  have hcarrier' : MemLp
      (fun omega ↦ _root_.GD.N0107.d009090 m n omega *
        _root_.GD.N0232.N0720.d014159 U omega) 2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
    simpa [_root_.GD.N0232.N0720.d014159, _root_.GD.N0232.N0720.d014159,
      _root_.GD.N0117.d014139, _root_.GD.N0232.N0720.N1080.d014171, q] using hcarrier
  apply (memLp_congr_ae ?_).2 (hcarrier'.const_mul (U.step : ℝ))
  filter_upwards [] with omega
  unfold _root_.GD.N0232.N0720.N1082.d015379
  ring



theorem d015386 (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) (a : ℝ) :
    MemLp
      (fun omega ↦
        _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U a omega - theta.location)
      2 (_root_.GD.N0232.N0720.N1080.d014171 m n theta) := by
  have hbase := _root_.GD.N0232.N0720.N1080.d014177 m n hm hn theta
  have hcorrection :=
    (_root_.GD.N0232.N0720.N1082.d015385 m n hm hn theta U).const_mul a
  apply (memLp_congr_ae ?_).2 (hbase.add hcorrection)
  filter_upwards [] with omega
  rw [_root_.GD.N0232.N0720.N1082.d015381]
  simp only [Pi.add_apply]
  ring


noncomputable def d015387
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) (a : ℝ) :
    _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
  MemLp.toLp (_root_.GD.N0232.N0720.N1082.d015380 m n hm hn U a)
    (by
      simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
        _root_.GD.N0232.N0720.N1082.d015386
          m n hm hn _root_.GD.N0232.N0720.N1080.d014169 U a)

theorem d015388
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) :
    _root_.GD.N0232.N0720.N1082.d015387 m n hm hn U 0 = _root_.GD.N0232.N0720.N1080.d014180 m n hm hn := by
  apply Lp.ext
  have hamp :
      (fun omega ↦ (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U 0) omega) =ᵐ[
        _root_.GD.N0232.N0720.N1080.d014172 m n] _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U 0 := by
    simpa [_root_.GD.N0232.N0720.N1082.d015387, _root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
      (show MemLp (_root_.GD.N0232.N0720.N1082.d015380 m n hm hn U 0) 2
          (_root_.GD.N0232.N0720.N1080.d014172 m n) from by
        simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
          _root_.GD.N0232.N0720.N1082.d015386
            m n hm hn _root_.GD.N0232.N0720.N1080.d014169 U 0).coeFn_toLp
  have hbase :
      (fun omega ↦ (_root_.GD.N0232.N0720.N1080.d014180 m n hm hn) omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1080.d014175 m n := by
    simpa [_root_.GD.N0232.N0720.N1080.d014180, _root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
      (show MemLp (_root_.GD.N0232.N0720.N1080.d014175 m n) 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) from by
        simpa [_root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
          _root_.GD.N0232.N0720.N1080.d014177 m n hm hn _root_.GD.N0232.N0720.N1080.d014169).coeFn_toLp
  filter_upwards [hamp, hbase] with omega ha hb
  rw [ha, hb]
  simp [_root_.GD.N0232.N0720.N1082.d015380, _root_.GD.N0107.d012734, _root_.GD.N0232.N0720.N1080.d014175]


theorem d015389 (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) (a : ℝ) :
    _root_.GD.N0232.N0720.N1080.d014182 m n theta (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U a) =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
          (fun omega ↦
            _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U a omega - theta.location)) := by
  apply _root_.GD.N0232.N0720.N1080.d014183
    m n (_root_.GD.N0232.N0720.N1080.d014173 m n theta)
  exact _root_.GD.N0232.N0720.N1082.d015386 m n hm hn theta U a





def d015390
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (sigma tau : ℝ) : ℝ :=
  _root_.GD.N0107.d009045 m n sigma tau *
    _root_.GD.N0120.d008813
      (((m - 1 : ℕ) : ℝ) / 2)
      (((n - 1 : ℕ) : ℝ) / 2)
      (_root_.GD.N0107.d009046 m n sigma tau) *
    _root_.GD.N0232.N0720.d014160 U

theorem d015391
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    {sigma tau : ℝ} (hsigma : 0 < sigma) (htau : 0 < tau) :
    0 < _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau := by
  have halpha : 0 < (((m - 1 : ℕ) : ℝ) / 2) := by
    have : 0 < (m - 1 : ℕ) := by omega
    positivity
  have hbeta : 0 < (((n - 1 : ℕ) : ℝ) / 2) := by
    have : 0 < (n - 1 : ℕ) := by omega
    positivity
  exact mul_pos
    (mul_pos
      (_root_.GD.N0107.d009049 (by omega) (by omega) hsigma htau)
      (_root_.GD.N0120.d008823 halpha hbeta
        (_root_.GD.N0107.d009050 (by omega) (by omega) hsigma htau)
        (_root_.GD.N0107.d009051 (by omega) (by omega) hsigma htau)))
    (_root_.GD.N0232.N0720.d014165 U)



theorem d015392
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (mu sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
        (_root_.GD.N0232.N0720.N1082.d015379 m n hm hn U) ≤
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
  have hbridge := U.d014131 e he
  have hReducedEnergy :
      _root_.GD.N0120.d008817 alpha beta e q =
        U.emitted.table.d008715 A.rho A.power := by
    dsimp only at hbridge
    rw [hAemitted, halphaDesign, hbetaDesign] at hbridge
    simpa only [q, A] using hbridge.2
  let C := A.d008724
  have hCM : C.M = U.M := by
    dsimp [C,
      _root_.GD.N0113.d008651.d008723.d008724]
    calc
      _root_.GD.N0113.d008670
          A.emitted.table A.emitted.ledger.inversePower =
          _root_.GD.N0113.d008670
            U.emitted.table U.emitted.ledger.inversePower := by
        rw [hAemitted]
      _ = U.M := U.M_eq.symm
  have hEnergyBound : _root_.GD.N0120.d008817 alpha beta e q ≤ (U.M : ℝ) := by
    rw [hReducedEnergy]
    calc
      U.emitted.table.d008715 A.rho A.power =
          A.emitted.table.d008715 A.rho A.power := by rw [hAemitted]
      _ = C.energy := rfl
      _ ≤ (C.M : ℝ) := C.energy_ceiling
      _ = (U.M : ℝ) := by rw [hCM]
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
  calc
    (U.step : ℝ) ^ 2 *
          (Sigma * _root_.GD.N0120.d008813 alpha beta e *
            _root_.GD.N0120.d008817 alpha beta e q) =
        (Sigma * _root_.GD.N0120.d008813 alpha beta e) *
          ((U.step : ℝ) ^ 2 * _root_.GD.N0120.d008817 alpha beta e q) := by ring
    _ ≤ (Sigma * _root_.GD.N0120.d008813 alpha beta e) *
          ((U.step : ℝ) ^ 2 * (U.M : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hEnergyBound (sq_nonneg _)) hscale0
    _ = _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau := by
      rw [hstepEnergy]
      rfl



theorem d015393
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (mu sigma tau a b : ℝ)
    (hsigma : 0 < sigma) (htau : 0 < tau)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦
            _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U b omega - mu) -
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦
            _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U a omega - mu) ≤
      -((b - a) * (1 - a) *
        _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau) := by
  let P := _root_.GD.N0107.d009030 m n mu sigma tau
  let base : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ := fun omega ↦ _root_.GD.N0232.N0720.N1080.d014175 m n omega - mu
  let correction := _root_.GD.N0232.N0720.N1082.d015379 m n hm hn U
  have hbase : MemLp base 2 P := by
    simpa [P, base, _root_.GD.N0232.N0720.N1080.d014171] using
      _root_.GD.N0232.N0720.N1080.d014177 m n hm hn
        ⟨mu, sigma, tau, hsigma, htau⟩
  have hcorrection : MemLp correction 2 P := by
    simpa [P, correction, _root_.GD.N0232.N0720.N1080.d014171] using
      _root_.GD.N0232.N0720.N1082.d015385 m n hm hn
        ⟨mu, sigma, tau, hsigma, htau⟩ U
  have hquadratic := _root_.GD.N0232.N0720.N1082.d015377
    P base correction hbase hcorrection a b
  have hfull :=
    (_root_.GD.N0232.N0720.d014166 U mu sigma tau hsigma htau).1
  have honeError :
      (fun omega ↦ base omega + correction omega) =
        (fun omega ↦
          _root_.GD.N0107.d012734 m n (U.step : ℝ) (_root_.GD.N0232.N0720.d014159 U) omega -
            mu) := by
    funext omega
    dsimp only [base, correction, _root_.GD.N0232.N0720.N1082.d015379]
    unfold _root_.GD.N0107.d012734 _root_.GD.N0232.N0720.N1080.d014175
    ring
  have hzeroError :
      base = fun omega ↦ _root_.GD.N0107.d012733 m n omega - mu := by
    rfl
  have hfull' :
      _root_.GD.N0141.d006684 P (fun omega ↦ base omega + correction omega) -
          _root_.GD.N0141.d006684 P base ≤
        -(_root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau) := by
    rw [honeError, hzeroError]
    simpa only [P, _root_.GD.N0232.N0720.N1082.d015390] using hfull
  have henergy0 : 0 ≤ _root_.GD.N0141.d006684 P correction := by
    exact integral_nonneg fun _ ↦ sq_nonneg _
  have henergy :
      _root_.GD.N0141.d006684 P correction ≤ _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau := by
    simpa [P, correction] using
      _root_.GD.N0232.N0720.N1082.d015392
        m n hm hn U mu sigma tau hsigma htau
  have hgap0 : 0 ≤ _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U sigma tau :=
    (_root_.GD.N0232.N0720.N1082.d015391 m n hm hn U hsigma htau).le
  have hbound := _root_.GD.N0232.N0720.N1082.d015378
    hfull' henergy0 henergy hgap0 ha hab hb
  have herror (c : ℝ) :
      (fun omega ↦
        _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U c omega - mu) =
        fun omega ↦ base omega + c * correction omega := by
    funext omega
    rw [_root_.GD.N0232.N0720.N1082.d015381]
    dsimp only [base, correction]
    ring
  rw [herror b, herror a]
  exact hquadratic.trans_le hbound

theorem d015394
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (mu sigma tau a b : ℝ)
    (hsigma : 0 < sigma) (htau : 0 < tau)
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦
            _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U b omega - mu) <
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
          (fun omega ↦
            _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U a omega - mu) := by
  apply sub_neg.mp
  refine lt_of_le_of_lt
    (_root_.GD.N0232.N0720.N1082.d015393
      m n hm hn U mu sigma tau a b hsigma htau ha hab.le hb) ?_
  have ha1 : a < 1 := hab.trans_le hb
  have hgap := _root_.GD.N0232.N0720.N1082.d015391 m n hm hn U hsigma htau
  exact neg_lt_zero.mpr
    (mul_pos (mul_pos (sub_pos.mpr hab) (sub_pos.mpr ha1)) hgap)



theorem d015395
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U b)
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U a) := by
  intro theta
  have hstrict := _root_.GD.N0232.N0720.N1082.d015394
    m n hm hn U theta.location theta.scale₁ theta.scale₂ a b
    theta.scale₁_pos theta.scale₂_pos ha hab hb
  have hupperPos :
      0 < _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
        (fun omega ↦
          _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U a omega - theta.location) :=
    lt_of_le_of_lt (integral_nonneg fun _ ↦ sq_nonneg _) hstrict
  rw [_root_.GD.N0232.N0720.N1082.d015389, _root_.GD.N0232.N0720.N1082.d015389]
  exact (ENNReal.ofReal_lt_ofReal_iff hupperPos).2 hstrict



theorem d015396
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) (a : ℝ) :
    _root_.GD.N0232.N0720.N1159.d014652 m n
      (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U a) := by
  let raw := _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U a
  let href : MemLp raw 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := by
    simpa [raw, _root_.GD.N0232.N0720.N1080.d014172, _root_.GD.N0232.N0720.N1080.d014169] using
      _root_.GD.N0232.N0720.N1082.d015386
        m n hm hn _root_.GD.N0232.N0720.N1080.d014169 U a
  have hclassReference :
      raw =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n]
        _root_.GD.N0232.N0720.N1214.d014265 m n (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U a) := by
    have hcoe :
        (fun omega ↦ (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U a) omega) =ᵐ[
          _root_.GD.N0232.N0720.N1080.d014172 m n] raw := by
      simpa [_root_.GD.N0232.N0720.N1082.d015387, raw] using href.coeFn_toLp
    exact hcoe.symm.trans
      (_root_.GD.N0232.N0720.N1214.d014267
        m n (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U a)).symm
  refine ⟨raw, _root_.GD.N0232.N0720.N1082.d015383 m n hm hn U a, ?_, ?_⟩
  · intro theta
    exact (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le hclassReference
  · intro g omega
    simpa [raw, _root_.GD.N0232.N0720.N1214.d014259] using
      _root_.GD.N0232.N0720.N1082.d015384
        m n hm hn U a g.shift g.d009241 omega



noncomputable def d015397
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    _root_.GD.N0232.N0720.N1159.d014639 m n :=
  _root_.GD.N0232.N0720.N1159.d014657 m n hm hn
    (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U a)
    (_root_.GD.N0232.N0720.N1082.d015396
      m n hm hn U a)
    (by
      simpa only [_root_.GD.N0232.N0720.N1082.d015388 m n hm hn U] using
        _root_.GD.N0232.N0720.N1082.d015395
          m n hm hn U (a := 0) (b := a) (by norm_num) ha ha1)

theorem d015398
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (_root_.GD.N0232.N0720.N1082.d015397 m n hm hn U a ha ha1).value =
      _root_.GD.N0232.N0720.N1082.d015387 m n hm hn U a := rfl

theorem d015399
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    _root_.GD.N0232.N0720.N1200.d015250 m n hm hn
      (_root_.GD.N0232.N0720.N1082.d015397 m n hm hn U a ha ha1) := by
  dsimp only [_root_.GD.N0232.N0720.N1200.d015250]
  simpa only [_root_.GD.N0232.N0720.N1082.d015398,
    _root_.GD.N0232.N0720.N1082.d015388 m n hm hn U] using
      _root_.GD.N0232.N0720.N1082.d015395
        m n hm hn U (a := 0) (b := a) (by norm_num) ha ha1





theorem d015400
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1201.d015333 m n s = 0 ↔
      _root_.GD.N0232.N0720.N1159.d014633 m n s.value = s.value := by
  constructor
  · intro hgap
    have htax := _root_.GD.N0232.N0720.N1159.d014648
      m n s.value s.value
      (_root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value)
    have hsq :
        ‖s.value - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 ≤ 0 := by
      have hgap' :
          ‖s.value‖ ^ 2 - ‖_root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ ^ 2 = 0 := by
        simpa only [_root_.GD.N0232.N0720.N1201.d015333] using hgap
      exact htax.trans_eq hgap'
    have hnorm :
        ‖s.value - _root_.GD.N0232.N0720.N1159.d014633 m n s.value‖ = 0 := by
      nlinarith [norm_nonneg
        (s.value - _root_.GD.N0232.N0720.N1159.d014633 m n s.value)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm
  · intro hfixed
    unfold _root_.GD.N0232.N0720.N1201.d015333
    rw [hfixed]
    exact sub_self _



theorem d015401
    (s : _root_.GD.N0232.N0720.N1159.d014639 m n) :
    _root_.GD.N0232.N0720.N1201.d015333 m n s = 0 ↔
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) s.value := by
  rw [_root_.GD.N0232.N0720.N1082.d015400]
  exact _root_.GD.N0232.N0720.N1159.d014635 m n s.value





theorem d015402
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn) (a : ℝ) :
    ‖_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U a‖ ^ 2 =
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n 0 1 1)
        (fun omega ↦
          _root_.GD.N0232.N0720.N1082.d015380 m n hm hn U a omega) := by
  have href := _root_.GD.N0232.N0720.N1080.d014190 m n (_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U a)
  have hamp := _root_.GD.N0232.N0720.N1082.d015389
    m n hm hn _root_.GD.N0232.N0720.N1080.d014169 U a
  have heq :
      ENNReal.ofReal (‖_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U a‖ ^ 2) =
        ENNReal.ofReal
          (_root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n 0 1 1)
            (_root_.GD.N0232.N0720.N1082.d015380 m n hm hn U a)) := by
    simpa [_root_.GD.N0232.N0720.N1080.d014171, _root_.GD.N0232.N0720.N1080.d014169] using href.symm.trans hamp
  exact (ENNReal.ofReal_eq_ofReal_iff
    (sq_nonneg ‖_root_.GD.N0232.N0720.N1082.d015387 m n hm hn U a‖)
    (integral_nonneg fun _ ↦ sq_nonneg _)).mp heq




theorem d015403
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    (1 - a) ^ 2 * _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U 1 1 ≤
      _root_.GD.N0232.N0720.N1201.d015333 m n
        (_root_.GD.N0232.N0720.N1082.d015397 m n hm hn U a ha ha1.le) := by
  let sa := _root_.GD.N0232.N0720.N1082.d015397 m n hm hn U a ha ha1.le
  let full : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1082.d015387 m n hm hn U 1
  have hbelow : _root_.GD.N0230.N0608.d000673 (_root_.GD.N0232.N0720.N1080.d014182 m n) sa.value full := by
    intro theta
    exact (_root_.GD.N0232.N0720.N1082.d015395
      m n hm hn U (a := a) (b := 1) ha.le ha1 le_rfl theta).le
  have hrisk := _root_.GD.N0232.N0720.N1082.d015393
    m n hm hn U 0 1 1 a 1 zero_lt_one zero_lt_one ha.le ha1.le le_rfl
  have hnormA := _root_.GD.N0232.N0720.N1082.d015402
    m n hm hn U a
  have hnormFull := _root_.GD.N0232.N0720.N1082.d015402
    m n hm hn U 1
  have hnormGap :
      (1 - a) ^ 2 * _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U 1 1 ≤
        ‖sa.value‖ ^ 2 - ‖full‖ ^ 2 := by
    dsimp only [sa, full]
    rw [_root_.GD.N0232.N0720.N1082.d015398, hnormA, hnormFull]
    simp only [sub_zero] at hrisk
    nlinarith
  exact hnormGap.trans
    (_root_.GD.N0232.N0720.N1201.d015338
      m n sa full hbelow)


theorem d015404
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    0 < _root_.GD.N0232.N0720.N1201.d015333 m n
      (_root_.GD.N0232.N0720.N1082.d015397 m n hm hn U a ha ha1.le) := by
  have hlower := _root_.GD.N0232.N0720.N1082.d015403
    m n hm hn U a ha ha1
  exact lt_of_lt_of_le
    (mul_pos (sq_pos_of_pos (sub_pos.mpr ha1))
      (_root_.GD.N0232.N0720.N1082.d015391 m n hm hn U zero_lt_one zero_lt_one))
    hlower


theorem d015405
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ¬ _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n)
      (_root_.GD.N0232.N0720.N1082.d015397 m n hm hn U a ha ha1.le).value := by
  intro hterminal
  have hzero :=
    (_root_.GD.N0232.N0720.N1082.d015401
      m n (_root_.GD.N0232.N0720.N1082.d015397 m n hm hn U a ha ha1.le)).2 hterminal
  exact (ne_of_gt
    (_root_.GD.N0232.N0720.N1082.d015404
      m n hm hn U a ha ha1)) hzero


theorem d015406
    (U : _root_.GD.N0232.N0720.d014158 m n hm hn)
    {rho a : ℝ} (_hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (ha : 0 < a) (harho : a ≤ rho) :
    (1 - rho) ^ 2 * _root_.GD.N0232.N0720.N1082.d015390 m n hm hn U 1 1 ≤
      _root_.GD.N0232.N0720.N1201.d015333 m n
        (_root_.GD.N0232.N0720.N1082.d015397 m n hm hn U a ha
          (harho.trans hrho1.le)) := by
  have hlower := _root_.GD.N0232.N0720.N1082.d015403
    m n hm hn U a ha (harho.trans_lt hrho1)
  have hgap0 :=
    (_root_.GD.N0232.N0720.N1082.d015391 m n hm hn U zero_lt_one zero_lt_one).le
  have hsquare : (1 - rho) ^ 2 ≤ (1 - a) ^ 2 := by
    nlinarith
  exact (mul_le_mul_of_nonneg_right hsquare hgap0).trans hlower

end

end N1082
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1082.d015378
#print axioms _root_.GD.N0232.N0720.N1082.d015384
#print axioms _root_.GD.N0232.N0720.N1082.d015392
#print axioms _root_.GD.N0232.N0720.N1082.d015394
#print axioms _root_.GD.N0232.N0720.N1082.d015395
#print axioms _root_.GD.N0232.N0720.N1082.d015401
#print axioms _root_.GD.N0232.N0720.N1082.d015403
#print axioms _root_.GD.N0232.N0720.N1082.d015405
