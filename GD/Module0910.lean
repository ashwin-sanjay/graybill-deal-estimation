import GD.Module0835
import GD.Module0614
import GD.Module0908
import GD.Module0909
import GD.Module0429















open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace GD.N0117

noncomputable section

open _root_.GD.N0107
open _root_.GD.N0137
open _root_.GD.N0134
open _root_.GD.N0134.d006518
open _root_.GD.N0113
open _root_.GD.N0113.d008651
open _root_.GD.N0145
open _root_.GD.N0108
open _root_.GD.N0120
open _root_.GD.N0141


def d014139
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0145.d014114 m n hm hn)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) : ℝ :=
  U.emitted.table.d008659
    (_root_.GD.N0107.d009091 m n
        (_root_.GD.N0107.d009085 ω.1)
        (_root_.GD.N0107.d009085 ω.2),
      _root_.GD.N0107.d009093 m n ω)

@[fun_prop] theorem d014140
    (r : ℕ) :
    Measurable (@_root_.GD.N0107.d009084 r) := by
  unfold _root_.GD.N0107.d009084 _root_.GD.N0126.d006420
    _root_.GD.N0126.d006419
  fun_prop

@[fun_prop] theorem d014141
    (r : ℕ) :
    Measurable (@_root_.GD.N0107.d009085 r) := by
  unfold _root_.GD.N0107.d009085 _root_.GD.N0126.d006422
    _root_.GD.N0126.d006421 _root_.GD.N0126.d006420
    _root_.GD.N0126.d006419
  fun_prop

@[fun_prop] theorem d014142
    (m n : ℕ) :
    Measurable (_root_.GD.N0107.d009090 m n) := by
  unfold _root_.GD.N0107.d009090
  fun_prop

@[fun_prop] theorem d014143
    (m n : ℕ) :
    Measurable (fun p : ℝ × ℝ => _root_.GD.N0107.d009091 m n p.1 p.2) := by
  unfold _root_.GD.N0107.d009091
  fun_prop

@[fun_prop] theorem d014144
    (m n : ℕ) :
    Measurable (_root_.GD.N0107.d009093 m n) := by
  unfold _root_.GD.N0107.d009093 _root_.GD.N0107.d009092
  fun_prop

@[fun_prop] theorem d014145
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0145.d014114 m n hm hn) :
    Measurable (_root_.GD.N0117.d014139 U) := by
  unfold _root_.GD.N0117.d014139
  apply U.emitted.table.d008664.comp
  exact
    ((_root_.GD.N0117.d014143 m n).comp
        (((_root_.GD.N0117.d014141 m).comp measurable_fst).prodMk
          ((_root_.GD.N0117.d014141 n).comp measurable_snd))).prodMk
      (_root_.GD.N0117.d014144 m n)

@[fun_prop] theorem d014146
    (m n : ℕ) :
    Measurable (_root_.GD.N0107.d012733 m n) := by
  unfold _root_.GD.N0107.d012733
  exact
    ((_root_.GD.N0117.d014140 n).comp measurable_snd).add
      (((_root_.GD.N0117.d014143 m n).comp
          (((_root_.GD.N0117.d014141 m).comp measurable_fst).prodMk
            ((_root_.GD.N0117.d014141 n).comp measurable_snd))).mul
        (_root_.GD.N0117.d014142 m n))

@[fun_prop] theorem d014147
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0145.d014114 m n hm hn) :
    Measurable
      (_root_.GD.N0107.d012734 m n (U.step : ℝ) (_root_.GD.N0117.d014139 U)) := by
  unfold _root_.GD.N0107.d012734
  exact
    (_root_.GD.N0117.d014146 m n).add
      ((measurable_const.mul (_root_.GD.N0117.d014142 m n)).mul
        (_root_.GD.N0117.d014145 U))


theorem d014148
    {r : ℕ} (hr : 2 ≤ r) (d c : ℝ) (z : _root_.GD.N0137.d008894 r) :
    _root_.GD.N0107.d009085 (_root_.GD.N0107.d009018 r d c z) =
      c ^ 2 * _root_.GD.N0107.d009085 z := by
  unfold _root_.GD.N0107.d009085
  rw [_root_.GD.N0107.d009088 (by omega) d c z]
  ring


theorem d014149
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d c : ℝ) (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d009090 m n (_root_.GD.N0107.d009024 m n d c c ω) =
      c * _root_.GD.N0107.d009090 m n ω := by
  unfold _root_.GD.N0107.d009090 _root_.GD.N0107.d009084 _root_.GD.N0107.d009024
  rw [_root_.GD.N0107.d009086 (by omega) d c ω.1,
    _root_.GD.N0107.d009086 (by omega) d c ω.2]
  ring



theorem d014150
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {c sx2 sy2 : ℝ} (hc : c ≠ 0) :
    _root_.GD.N0107.d009091 m n (c ^ 2 * sx2) (c ^ 2 * sy2) =
      _root_.GD.N0107.d009091 m n sx2 sy2 := by
  unfold _root_.GD.N0107.d009091
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hnum :
      c ^ 2 * sy2 / (n : ℝ) = c ^ 2 * (sy2 / (n : ℝ)) := by
    field_simp [hnR]
  have hden :
      c ^ 2 * sx2 / (m : ℝ) + c ^ 2 * (sy2 / (n : ℝ)) =
        c ^ 2 * (sx2 / (m : ℝ) + sy2 / (n : ℝ)) := by
    field_simp [hmR, hnR]
  rw [hnum, hden, mul_div_mul_left _ _ hc2]



theorem d014151
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (d : ℝ) {c : ℝ} (hc : c ≠ 0)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d009093 m n (_root_.GD.N0107.d009024 m n d c c ω) =
      _root_.GD.N0107.d009093 m n ω := by
  have hD :=
    _root_.GD.N0117.d014149 hm hn d c ω
  have hx :=
    _root_.GD.N0117.d014148 hm d c ω.1
  have hy :=
    _root_.GD.N0117.d014148 hn d c ω.2
  unfold _root_.GD.N0107.d009093 _root_.GD.N0107.d009092
  have hD' :
      _root_.GD.N0107.d009090 m n
          (_root_.GD.N0107.d009018 m d c ω.1, _root_.GD.N0107.d009018 n d c ω.2) =
        c * _root_.GD.N0107.d009090 m n ω := by
    simpa [_root_.GD.N0107.d009024] using hD
  change
    _root_.GD.N0107.d009090 m n
          (_root_.GD.N0107.d009018 m d c ω.1, _root_.GD.N0107.d009018 n d c ω.2) ^ 2 /
        (_root_.GD.N0107.d009085 (_root_.GD.N0107.d009018 m d c ω.1) / (m : ℝ) +
          _root_.GD.N0107.d009085 (_root_.GD.N0107.d009018 n d c ω.2) / (n : ℝ)) =
      _root_.GD.N0107.d009090 m n ω ^ 2 /
        (_root_.GD.N0107.d009085 ω.1 / (m : ℝ) +
          _root_.GD.N0107.d009085 ω.2 / (n : ℝ))
  rw [hD', hx, hy]
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hnum :
      (c * _root_.GD.N0107.d009090 m n ω) ^ 2 =
        c ^ 2 * _root_.GD.N0107.d009090 m n ω ^ 2 := by ring
  have hden :
      c ^ 2 * _root_.GD.N0107.d009085 ω.1 / (m : ℝ) +
          c ^ 2 * _root_.GD.N0107.d009085 ω.2 / (n : ℝ) =
        c ^ 2 *
          (_root_.GD.N0107.d009085 ω.1 / (m : ℝ) +
            _root_.GD.N0107.d009085 ω.2 / (n : ℝ)) := by
    field_simp [hmR, hnR]
  rw [hnum, hden, mul_div_mul_left _ _ hc2]



theorem d014152
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0145.d014114 m n hm hn)
    (d : ℝ) {c : ℝ} (hc : c ≠ 0)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0117.d014139 U (_root_.GD.N0107.d009024 m n d c c ω) =
      _root_.GD.N0117.d014139 U ω := by
  unfold _root_.GD.N0117.d014139
  rw [_root_.GD.N0117.d014151 hm hn d hc ω]
  simp only [_root_.GD.N0107.d009024]
  rw [_root_.GD.N0117.d014148 hm d c ω.1,
    _root_.GD.N0117.d014148 hn d c ω.2,
    _root_.GD.N0117.d014150 hm hn hc]



theorem d014153
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0145.d014114 m n hm hn)
    (d : ℝ) {c : ℝ} (hc : c ≠ 0)
    (ω : _root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) :
    _root_.GD.N0107.d012734 m n (U.step : ℝ) (_root_.GD.N0117.d014139 U)
        (_root_.GD.N0107.d009024 m n d c c ω) =
      d + c *
        _root_.GD.N0107.d012734 m n (U.step : ℝ) (_root_.GD.N0117.d014139 U) ω := by
  have hmy :=
    _root_.GD.N0107.d009086 (by omega : 0 < n) d c ω.2
  have hx :=
    _root_.GD.N0117.d014148 hm d c ω.1
  have hy :=
    _root_.GD.N0117.d014148 hn d c ω.2
  have hD :=
    _root_.GD.N0117.d014149 hm hn d c ω
  have hq := _root_.GD.N0117.d014152 U d hc ω
  have hD' :
      _root_.GD.N0107.d009090 m n
          (_root_.GD.N0107.d009018 m d c ω.1, _root_.GD.N0107.d009018 n d c ω.2) =
        c * _root_.GD.N0107.d009090 m n ω := by
    simpa [_root_.GD.N0107.d009024] using hD
  have hq' :
      _root_.GD.N0117.d014139 U
          (_root_.GD.N0107.d009018 m d c ω.1, _root_.GD.N0107.d009018 n d c ω.2) =
        _root_.GD.N0117.d014139 U ω := by
    simpa [_root_.GD.N0107.d009024] using hq
  unfold _root_.GD.N0107.d012734 _root_.GD.N0107.d012733 _root_.GD.N0107.d009084
    _root_.GD.N0107.d009024
  simp only
  rw [hmy, hx, hy, _root_.GD.N0117.d014150 hm hn hc, hD', hq']
  ring



def d014154
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0145.d014114 m n hm hn) : ℝ :=
  (((U.emitted.ledger.C / 2 : ℚ) : ℝ) ^ 2) / (U.M : ℝ)

theorem d014155
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (U : _root_.GD.N0145.d014114 m n hm hn) :
    0 < _root_.GD.N0117.d014154 U := by
  unfold _root_.GD.N0117.d014154
  have hC : (0 : ℝ) <
      (((U.emitted.ledger.C / 2 : ℚ) : ℝ)) := by
    exact_mod_cast
      (div_pos U.emitted.ledger.C_pos (by norm_num : (0 : ℚ) < 2))
  have hM : (0 : ℝ) < (U.M : ℝ) := by
    exact_mod_cast U.M_pos
  positivity




theorem d014156
    {m n : ℕ} {hm : 2 ≤ m} {hn : 2 ≤ n}
    (Ucert : _root_.GD.N0145.d014114 m n hm hn)
    (μ σ τ : ℝ) (hσ : 0 < σ) (hτ : 0 < τ) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n μ σ τ)
          (fun ω =>
            _root_.GD.N0107.d012734 m n (Ucert.step : ℝ)
                (_root_.GD.N0117.d014139 Ucert) ω - μ)
        -
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n μ σ τ)
          (fun ω => _root_.GD.N0107.d012733 m n ω - μ)
      ≤
        -(_root_.GD.N0107.d009045 m n σ τ *
          _root_.GD.N0120.d008813
            (((m - 1 : ℕ) : ℝ) / 2)
            (((n - 1 : ℕ) : ℝ) / 2)
            (_root_.GD.N0107.d009046 m n σ τ) *
          _root_.GD.N0117.d014154 Ucert)
    ∧
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n μ σ τ)
          (fun ω =>
            _root_.GD.N0107.d012734 m n (Ucert.step : ℝ)
                (_root_.GD.N0117.d014139 Ucert) ω - μ)
      <
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n μ σ τ)
          (fun ω => _root_.GD.N0107.d012733 m n ω - μ) := by
  let e := _root_.GD.N0107.d009046 m n σ τ
  let Sigma := _root_.GD.N0107.d009045 m n σ τ
  let α : ℝ := (((m - 1 : ℕ) : ℝ) / 2)
  let β : ℝ := (((n - 1 : ℕ) : ℝ) / 2)
  let q := Ucert.emitted.table.d008659
  have he0 : 0 < e :=
    _root_.GD.N0107.d009050 (by omega) (by omega) hσ hτ
  have he1 : e < 1 :=
    _root_.GD.N0107.d009051 (by omega) (by omega) hσ hτ
  have he : e ∈ Icc (0 : ℝ) 1 := ⟨he0.le, he1.le⟩
  let A := Ucert.realized e he
  have hSigma : 0 < Sigma :=
    _root_.GD.N0107.d009049 (by omega) (by omega) hσ hτ
  have hα : 0 < α := by
    dsimp [α]
    have hm1 : 0 < (m - 1 : ℕ) := by omega
    positivity
  have hβ : 0 < β := by
    dsimp [β]
    have hn1 : 0 < (n - 1 : ℕ) := by omega
    positivity
  have hq : Measurable q :=
    Ucert.emitted.table.d008664
  have hqBound :
      ∀ p, |q p| ≤ _root_.GD.N0108.d008888 Ucert.emitted.table :=
    _root_.GD.N0108.d008891 Ucert.emitted.table
  have hBoundNonneg :
      0 ≤ _root_.GD.N0108.d008888 Ucert.emitted.table := by
    unfold _root_.GD.N0108.d008888
    positivity
  have hL2 :=
    _root_.GD.N0107.d012748
      m n hm hn μ σ τ hσ hτ q hq hBoundNonneg hqBound
  have hLaw :=
    _root_.GD.N0107.d009052 m n hm hn μ σ τ hσ hτ
  have hTraceTarget :=
    _root_.GD.N0108.d008892
      Ucert.emitted.table hα hβ he0 he1
  have hEnergyTarget :=
    _root_.GD.N0108.d008893
      Ucert.emitted.table hα hβ he0 he1
  have hTraceIter :=
    _root_.GD.N0143.d006698 _ hTraceTarget
  have hEnergyIter :=
    _root_.GD.N0143.d006698 _ hEnergyTarget
  have hAemitted : A.emitted = Ucert.emitted := by
    simpa [A] using Ucert.realized_emitted e he
  have hTraceTerm :
      _root_.GD.N0141.d006687 (_root_.GD.N0107.d009030 m n μ σ τ)
          (_root_.GD.N0107.d009038 m n μ σ τ e Sigma)
          (_root_.GD.N0107.d009039 m n μ σ τ e)
          (fun ω =>
            q (_root_.GD.N0107.d009039 m n μ σ τ e ω,
              _root_.GD.N0107.d009040 m n μ σ τ e ω)) e
        =
      Sigma * _root_.GD.N0120.d008813 α β e *
        _root_.GD.N0120.d008816 α β e q := by
    rw [_root_.GD.N0125.d008847.d008877 hLaw q hq,
      _root_.GD.N0120.d008825
        hα hβ he0 he1 q hTraceTarget hTraceIter]
    ring
  have hEnergyTerm :
      _root_.GD.N0141.d006688 (_root_.GD.N0107.d009030 m n μ σ τ)
          (_root_.GD.N0107.d009038 m n μ σ τ e Sigma)
          (fun ω =>
            q (_root_.GD.N0107.d009039 m n μ σ τ e ω,
              _root_.GD.N0107.d009040 m n μ σ τ e ω))
        =
      Sigma * _root_.GD.N0120.d008813 α β e *
        _root_.GD.N0120.d008817 α β e q := by
    rw [_root_.GD.N0125.d008847.d008878 hLaw q hq,
      _root_.GD.N0120.d008826
        hα hβ he0 he1 q hEnergyTarget hEnergyIter]
    ring
  have hclose :=
    Ucert.d014132 e he
  have hαdesign :
      ((_root_.GD.N0134.d006543 m n hm hn).alpha : ℝ) = α := by
    simp [_root_.GD.N0134.d006543, _root_.GD.N0134.d006540, α]
  have hβdesign :
      ((_root_.GD.N0134.d006543 m n hm hn).beta : ℝ) = β := by
    simp [_root_.GD.N0134.d006543, _root_.GD.N0134.d006540, β]
  have hclose' :
      2 * (Ucert.step : ℝ) * _root_.GD.N0120.d008816 α β e q
            + (Ucert.step : ℝ) ^ 2 * _root_.GD.N0120.d008817 α β e q
          ≤ -_root_.GD.N0117.d014154 Ucert
        ∧
      2 * (Ucert.step : ℝ) * _root_.GD.N0120.d008816 α β e q
            + (Ucert.step : ℝ) ^ 2 * _root_.GD.N0120.d008817 α β e q < 0 := by
    dsimp only at hclose
    rw [hAemitted, hαdesign, hβdesign] at hclose
    simpa only [q, _root_.GD.N0117.d014154] using hclose
  have hbracket :
      2 * (Ucert.step : ℝ) *
            _root_.GD.N0120.d008816 α β e q
        + (Ucert.step : ℝ) ^ 2 *
            _root_.GD.N0120.d008817 α β e q
      ≤ -_root_.GD.N0117.d014154 Ucert := by
    exact hclose'.1
  have hbracketStrict :
      2 * (Ucert.step : ℝ) *
            _root_.GD.N0120.d008816 α β e q
        + (Ucert.step : ℝ) ^ 2 *
            _root_.GD.N0120.d008817 α β e q < 0 := by
    exact hclose'.2
  have hRiskIdentity :=
    _root_.GD.N0144.d006723
      (P := _root_.GD.N0107.d009030 m n μ σ τ)
      (U := _root_.GD.N0107.d012732 m n μ e)
      (D := _root_.GD.N0107.d009038 m n μ σ τ e Sigma)
      (L := _root_.GD.N0107.d009039 m n μ σ τ e)
      (Sobs := fun ω =>
        (_root_.GD.N0107.d009039 m n μ σ τ e ω,
          _root_.GD.N0107.d009040 m n μ σ τ e ω))
      (q := fun p : ℝ × (ℝ × ℝ) => q p.2)
      (e := e) (ε := (Ucert.step : ℝ))
      (hq.comp measurable_snd)
      (_root_.GD.N0107.d012747
        m n hm hn μ σ τ hσ hτ)
      hL2.1 hL2.2
      (_root_.GD.N0107.d012745
        m n hm hn μ σ τ hσ hτ)
      (_root_.GD.N0107.d012746
        m n hm hn μ σ τ hσ hτ)
  have hCorrectedAbstract :
      (fun ω =>
        _root_.GD.N0141.d006685
            (_root_.GD.N0107.d012732 m n μ e)
            (_root_.GD.N0107.d009038 m n μ σ τ e Sigma)
            (_root_.GD.N0107.d009039 m n μ σ τ e) e ω
          + (Ucert.step : ℝ) *
            _root_.GD.N0144.d006721
              (_root_.GD.N0107.d009038 m n μ σ τ e Sigma)
              (fun z =>
                (_root_.GD.N0107.d009039 m n μ σ τ e z,
                  _root_.GD.N0107.d009040 m n μ σ τ e z))
              (fun p : ℝ × (ℝ × ℝ) => q p.2) ω) =
        _root_.GD.N0141.d006686
          (_root_.GD.N0107.d012732 m n μ e)
          (_root_.GD.N0107.d009038 m n μ σ τ e Sigma)
          (_root_.GD.N0107.d009039 m n μ σ τ e)
          (fun ω =>
            q (_root_.GD.N0107.d009039 m n μ σ τ e ω,
              _root_.GD.N0107.d009040 m n μ σ τ e ω))
          e (Ucert.step : ℝ) := by
    funext ω
    unfold _root_.GD.N0141.d006686 _root_.GD.N0144.d006721
    ring
  rw [hCorrectedAbstract] at hRiskIdentity
  have hScalePos :
      0 < Sigma * _root_.GD.N0120.d008813 α β e :=
    mul_pos hSigma (_root_.GD.N0120.d008823 hα hβ he0 he1)
  have hAbstractGap :
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n μ σ τ)
          (_root_.GD.N0141.d006686
            (_root_.GD.N0107.d012732 m n μ e)
            (_root_.GD.N0107.d009038 m n μ σ τ e Sigma)
            (_root_.GD.N0107.d009039 m n μ σ τ e)
            (fun ω =>
              q (_root_.GD.N0107.d009039 m n μ σ τ e ω,
                _root_.GD.N0107.d009040 m n μ σ τ e ω))
            e (Ucert.step : ℝ))
        -
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n μ σ τ)
          (_root_.GD.N0141.d006685
            (_root_.GD.N0107.d012732 m n μ e)
            (_root_.GD.N0107.d009038 m n μ σ τ e Sigma)
            (_root_.GD.N0107.d009039 m n μ σ τ e) e)
      ≤
        -(Sigma * _root_.GD.N0120.d008813 α β e * _root_.GD.N0117.d014154 Ucert) := by
    rw [hRiskIdentity, hTraceTerm, hEnergyTerm]
    have hmul := mul_le_mul_of_nonneg_left hbracket hScalePos.le
    nlinarith
  have hAbstractStrict :
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n μ σ τ)
          (_root_.GD.N0141.d006686
            (_root_.GD.N0107.d012732 m n μ e)
            (_root_.GD.N0107.d009038 m n μ σ τ e Sigma)
            (_root_.GD.N0107.d009039 m n μ σ τ e)
            (fun ω =>
              q (_root_.GD.N0107.d009039 m n μ σ τ e ω,
                _root_.GD.N0107.d009040 m n μ σ τ e ω))
            e (Ucert.step : ℝ))
      <
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n μ σ τ)
          (_root_.GD.N0141.d006685
            (_root_.GD.N0107.d012732 m n μ e)
            (_root_.GD.N0107.d009038 m n μ σ τ e Sigma)
            (_root_.GD.N0107.d009039 m n μ σ τ e) e) := by
    apply sub_neg.mp
    exact lt_of_le_of_lt hAbstractGap
      (neg_neg_of_pos
        (mul_pos hScalePos (_root_.GD.N0117.d014155 Ucert)))
  have hD :
      _root_.GD.N0107.d009038 m n μ σ τ e Sigma =
        _root_.GD.N0107.d009090 m n := by
    funext ω
    exact _root_.GD.N0107.d012724
      m n hm hn μ σ τ hσ hτ ω
  have hL :
      _root_.GD.N0107.d009039 m n μ σ τ e =
        fun ω =>
          _root_.GD.N0107.d009091 m n
            (_root_.GD.N0107.d009085 ω.1)
            (_root_.GD.N0107.d009085 ω.2) := by
    funext ω
    exact _root_.GD.N0107.d012729
      m n hm hn μ σ τ hσ hτ ω
  have hF :
      _root_.GD.N0107.d009040 m n μ σ τ e =
        _root_.GD.N0107.d009093 m n := by
    funext ω
    exact _root_.GD.N0107.d012731
      m n hm hn μ σ τ hσ hτ ω
  have hObservedQ :
      (fun ω =>
        q
          (_root_.GD.N0107.d009091 m n
              (_root_.GD.N0107.d009085 ω.1)
              (_root_.GD.N0107.d009085 ω.2),
            _root_.GD.N0107.d009093 m n ω)) =
        _root_.GD.N0117.d014139 Ucert := by
    rfl
  have hCorrected :
      (fun ω =>
        _root_.GD.N0107.d012734 m n (Ucert.step : ℝ)
            (_root_.GD.N0117.d014139 Ucert) ω - μ) =
      _root_.GD.N0141.d006686
        (_root_.GD.N0107.d012732 m n μ e)
        (_root_.GD.N0107.d009038 m n μ σ τ e Sigma)
        (_root_.GD.N0107.d009039 m n μ σ τ e)
        (fun ω =>
          q (_root_.GD.N0107.d009039 m n μ σ τ e ω,
            _root_.GD.N0107.d009040 m n μ σ τ e ω))
        e (Ucert.step : ℝ) := by
    funext ω
    rw [hD, hL, hF, hObservedQ]
    exact
      _root_.GD.N0107.d012736
        m n μ e (Ucert.step : ℝ)
          (_root_.GD.N0117.d014139 Ucert) ω
  have hBase :
      (fun ω => _root_.GD.N0107.d012733 m n ω - μ) =
      _root_.GD.N0141.d006685
        (_root_.GD.N0107.d012732 m n μ e)
        (_root_.GD.N0107.d009038 m n μ σ τ e Sigma)
        (_root_.GD.N0107.d009039 m n μ σ τ e) e := by
    funext ω
    rw [hD, hL]
    exact _root_.GD.N0107.d012735 m n μ e ω
  rw [hCorrected, hBase]
  constructor
  · simpa [e, Sigma, α, β] using hAbstractGap
  · exact hAbstractStrict







theorem d014157
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    ∃ Ucert : _root_.GD.N0145.d014114 m n hm hn,
      0 < Ucert.step
      ∧ 0 < _root_.GD.N0117.d014154 Ucert
      ∧ ∀ (μ σ τ : ℝ), 0 < σ → 0 < τ →
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n μ σ τ)
              (fun ω =>
                _root_.GD.N0107.d012734 m n (Ucert.step : ℝ)
                    (_root_.GD.N0117.d014139 Ucert) ω - μ)
            -
            _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n μ σ τ)
              (fun ω => _root_.GD.N0107.d012733 m n ω - μ)
          ≤
            -(_root_.GD.N0107.d009045 m n σ τ *
              _root_.GD.N0120.d008813
                (((m - 1 : ℕ) : ℝ) / 2)
                (((n - 1 : ℕ) : ℝ) / 2)
                (_root_.GD.N0107.d009046 m n σ τ) *
              _root_.GD.N0117.d014154 Ucert)
        ∧
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n μ σ τ)
              (fun ω =>
                _root_.GD.N0107.d012734 m n (Ucert.step : ℝ)
                    (_root_.GD.N0117.d014139 Ucert) ω - μ)
          <
            _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n μ σ τ)
              (fun ω => _root_.GD.N0107.d012733 m n ω - μ) := by
  let Ucert : _root_.GD.N0145.d014114 m n hm hn :=
    Classical.choice (_root_.GD.N0145.d014138 m n hm hn)
  refine ⟨Ucert, Ucert.step_pos, ?_, ?_⟩
  · exact _root_.GD.N0117.d014155 Ucert
  · intro μ σ τ hσ hτ
    exact _root_.GD.N0117.d014156 Ucert μ σ τ hσ hτ

end

end GD.N0117
