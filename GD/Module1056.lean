import GD.Module0204
import GD.Module1055
import Mathlib.Tactic










open Filter MeasureTheory Topology

namespace GD.N0232.N0720.N1275

noncomputable section

open _root_.GD.N0232.N0720.N1280
open _root_.GD.N0232.N0720.N1282
open _root_.GD.N0232.N0720.N1285
open _root_.GD.N0232.N0720.N1283
open _root_.GD.N0232.N0720.N1367
open _root_.GD.N0232.N0720.N1276
open _root_.GD.N0232.N0720.N1366
open _root_.GD.N0232.N0720.N1405


def d016918 (n : ℕ) : ℝ := (n : ℝ) + 3

theorem d016919 (n : ℕ) :
    3 ≤ _root_.GD.N0232.N0720.N1275.d016918 n := by
  simp [_root_.GD.N0232.N0720.N1275.d016918]



theorem d016920
    {N : ℝ} (hN : 3 ≤ N)
    (z : _root_.GD.N0232.N0720.N1397.d014798) :
    (N / 3) * _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) z.2 ≤
      _root_.GD.N0232.N0720.N1282.d014823 N z := by
  let B := _root_.GD.N0232.N0720.N1285.d002683 N
  let c := _root_.GD.N0232.N0720.N1285.d002682 N
  have hN0 : 0 < N := by linarith
  have hc4 : 4 ≤ c := _root_.GD.N0232.N0720.N1285.d002692 hN
  have hc0 : 0 ≤ c / N := by positivity
  have hB0 : 0 ≤ B := by
    exact (_root_.GD.N0232.N0720.N1285.d002695 hN).trans' zero_le_one
  have hBscale : B ≤ c ^ 2 / N ^ 2 :=
    _root_.GD.N0232.N0720.N1285.d002696 hN
  have hsqrt : Real.sqrt B ≤ c / N := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hc0).mp
    rw [Real.sq_sqrt hB0]
    simpa [div_pow] using hBscale
  have hgamma : c / 3 ≤ _root_.GD.N0232.N0720.N1285.d002684 N := _root_.GD.N0232.N0720.N1285.d002694 hN
  have hNgamma : (N / 3) * Real.sqrt B ≤ _root_.GD.N0232.N0720.N1285.d002684 N := by
    have hmul := mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ N / 3)
    calc
      (N / 3) * Real.sqrt B ≤ (N / 3) * (c / N) := hmul
      _ = c / 3 := by field_simp [hN0.ne']
      _ ≤ _root_.GD.N0232.N0720.N1285.d002684 N := hgamma
  have hk : 0 ≤ _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) z.2 :=
    (_root_.GD.N0232.N0720.N1280.d003925 (by linarith [_root_.GD.N0232.N0720.N1285.d002687 hN]) z.2).le
  have hbroad : 0 ≤ _root_.GD.N0232.N0720.N1280.d003887 N z.1 :=
    (_root_.GD.N0232.N0720.N1280.d003894 hN z.1).le
  have href : 0 < _root_.GD.N0232.N0720.N1280.d003886 z.1 :=
    _root_.GD.N0232.N0720.N1280.d003893 z.1
  have hreference := _root_.GD.N0232.N0720.N1280.d003944 hN z.1
  have hleft :
      ((N / 3) * _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) z.2) *
          _root_.GD.N0232.N0720.N1280.d003886 z.1 ≤
        _root_.GD.N0232.N0720.N1285.d002684 N * _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) z.2 *
          _root_.GD.N0232.N0720.N1280.d003887 N z.1 := by
    calc
      ((N / 3) * _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) z.2) *
          _root_.GD.N0232.N0720.N1280.d003886 z.1 ≤
        ((N / 3) * _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) z.2) *
          (Real.sqrt B * _root_.GD.N0232.N0720.N1280.d003887 N z.1) := by
            gcongr
      _ = ((N / 3) * Real.sqrt B) *
          _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) z.2 * _root_.GD.N0232.N0720.N1280.d003887 N z.1 := by ring
      _ ≤ _root_.GD.N0232.N0720.N1285.d002684 N * _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 N) z.2 *
          _root_.GD.N0232.N0720.N1280.d003887 N z.1 := by gcongr
  apply (le_div_iff₀ href).2
  exact hleft.trans (_root_.GD.N0232.N0720.N1280.d003948 hN z)

theorem d016921 :
    Tendsto _root_.GD.N0232.N0720.N1275.d016918 atTop atTop := by
  apply Filter.tendsto_atTop_mono (fun n ↦ ?_)
    (tendsto_natCast_atTop_atTop (R := ℝ))
  unfold _root_.GD.N0232.N0720.N1275.d016918
  linarith

theorem d016922 :
    Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1285.d002679 (_root_.GD.N0232.N0720.N1275.d016918 n))
      atTop (𝓝 0) := by
  have hsq : Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1275.d016918 n * _root_.GD.N0232.N0720.N1275.d016918 n)
      atTop atTop :=
    _root_.GD.N0232.N0720.N1275.d016921.atTop_mul_atTop₀
      _root_.GD.N0232.N0720.N1275.d016921
  have hdiv := hsq.const_div_atTop (1 : ℝ)
  simpa [_root_.GD.N0232.N0720.N1285.d002679, pow_two] using hdiv

theorem d016923
    (r : ℝ × (ℝ × ℝ)) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 (_root_.GD.N0232.N0720.N1275.d016918 n)) r)
      atTop (𝓝 1) := by
  have hcont : ContinuousAt (fun e ↦ _root_.GD.N0232.N0720.N1280.d003882 e r) 0 := by
    unfold _root_.GD.N0232.N0720.N1280.d003882 _root_.GD.N0232.N0720.N1283.d003859 _root_.GD.N0232.N0720.N1283.d003854 _root_.GD.N0232.N0720.N1283.d003851
    fun_prop (disch := norm_num)
  have hk0 : _root_.GD.N0232.N0720.N1280.d003882 0 r = 1 := by
    simp [_root_.GD.N0232.N0720.N1280.d003882, _root_.GD.N0232.N0720.N1283.d003859, _root_.GD.N0232.N0720.N1283.d003854, _root_.GD.N0232.N0720.N1283.d003851]
  rw [← hk0]
  simpa only [Function.comp_def] using
    hcont.tendsto.comp _root_.GD.N0232.N0720.N1275.d016922


theorem d016924
    (z : _root_.GD.N0232.N0720.N1397.d014798) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1282.d014823 (_root_.GD.N0232.N0720.N1275.d016918 n) z)
      atTop atTop := by
  have hk := _root_.GD.N0232.N0720.N1275.d016923 z.2
  have hkhalf : ∀ᶠ n in atTop,
      (1 / 2 : ℝ) ≤ _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 (_root_.GD.N0232.N0720.N1275.d016918 n)) z.2 := by
    have hmem := hk.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
    exact hmem.mono fun _ hn ↦ hn.le
  have hbase : Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1275.d016918 n / 6) atTop atTop :=
    _root_.GD.N0232.N0720.N1275.d016921.atTop_div_const (by norm_num)
  have hrhs : Tendsto
      (fun n ↦ (_root_.GD.N0232.N0720.N1275.d016918 n / 3) *
        _root_.GD.N0232.N0720.N1280.d003882 (_root_.GD.N0232.N0720.N1285.d002679 (_root_.GD.N0232.N0720.N1275.d016918 n)) z.2)
      atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hbase
    filter_upwards [hkhalf] with n hn
    have hN0 : 0 ≤ _root_.GD.N0232.N0720.N1275.d016918 n := by
      linarith [_root_.GD.N0232.N0720.N1275.d016919 n]
    nlinarith
  apply tendsto_atTop_mono' atTop _ hrhs
  exact Filter.Eventually.of_forall fun n ↦
    _root_.GD.N0232.N0720.N1275.d016920 (_root_.GD.N0232.N0720.N1275.d016919 n) z


theorem d016925
    (omega : _root_.GD.N0232.N0720.N1282.d014821) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1282.d014826 (_root_.GD.N0232.N0720.N1275.d016918 n) omega)
      atTop atTop := by
  exact _root_.GD.N0232.N0720.N1275.d016924
    (_root_.GD.N0232.N0720.N1397.d014815 omega)



theorem d016926
    (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1276.d016063
      (_root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n)) omega)
      atTop atTop := by
  apply (_root_.GD.N0232.N0720.N1275.d016925 omega).congr'
  exact Filter.Eventually.of_forall fun n ↦
    (_root_.GD.N0232.N0720.N1367.d016882
      (_root_.GD.N0232.N0720.N1275.d016919 n) omega).symm


theorem d016927 :
    Tendsto (fun n ↦ _root_.GD.N0232.N0720.N1276.d016067
      (_root_.GD.N0232.N0720.N1367.d016868 (_root_.GD.N0232.N0720.N1275.d016918 n) (_root_.GD.N0232.N0720.N1275.d016919 n))
      _root_.GD.N0232.N0720.N1405.d016086) atTop (𝓝 0) := by
  have hrate : Tendsto (fun n ↦ 48 / _root_.GD.N0232.N0720.N1275.d016918 n ^ 9)
      atTop (𝓝 0) :=
    ((tendsto_pow_atTop (α := ℝ) (by norm_num : 9 ≠ 0)).comp
      _root_.GD.N0232.N0720.N1275.d016921).const_div_atTop 48
  apply squeeze_zero'
  · apply Filter.Eventually.of_forall
    intro n
    unfold _root_.GD.N0232.N0720.N1276.d016067
    apply integral_nonneg
    intro omega
    apply div_nonneg (sq_nonneg _)
    rw [_root_.GD.N0232.N0720.N1367.d016882
      (_root_.GD.N0232.N0720.N1275.d016919 n)]
    unfold _root_.GD.N0232.N0720.N1282.d014826 _root_.GD.N0232.N0720.N1282.d014823
    exact (div_pos
      (_root_.GD.N0232.N0720.N1282.d014833 (_root_.GD.N0232.N0720.N1275.d016919 n) _)
      (_root_.GD.N0232.N0720.N1280.d003893 _)).le
  · exact Filter.Eventually.of_forall fun n ↦
      _root_.GD.N0232.N0720.N1366.d016917
        (_root_.GD.N0232.N0720.N1275.d016919 n)
  · exact hrate

end

end GD.N0232.N0720.N1275

#print axioms _root_.GD.N0232.N0720.N1275.d016920
#print axioms _root_.GD.N0232.N0720.N1275.d016925
#print axioms _root_.GD.N0232.N0720.N1275.d016926
#print axioms _root_.GD.N0232.N0720.N1275.d016927
