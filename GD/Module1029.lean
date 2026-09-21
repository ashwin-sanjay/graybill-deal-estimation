import GD.Module1028
import GD.Module0928






















open Filter MeasureTheory Set
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1074

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1070
open _root_.GD.N0232.N0720.N1075
open _root_.GD.N0232.N0720.N1069
open _root_.GD.N0232.N0720.N1433
open _root_.GD.N0232.N0720.N1442
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1078
open _root_.GD.N0230.N0553
open _root_.GD.N0230.N0567
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0633

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)



theorem d016382
    (hminimax : _root_.GD.N0232.N0720.N1078.d016380 m n hm hn)
    {d : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (sigma tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau) :
    _root_.GD.N0232.N0720.N1075.d014487 m n
        (_root_.GD.N0232.N0720.N1078.d016372 0 sigma tau hsigma htau) ≤
      _root_.GD.N0232.N0720.N1066.d014332 m n hm hn d := by
  calc
    _root_.GD.N0232.N0720.N1075.d014487 m n
        (_root_.GD.N0232.N0720.N1078.d016372 0 sigma tau hsigma htau) ≤
        ⨆ mu : ℝ,
          _root_.GD.N0232.N0720.N1066.d014327 m n hm hn
            (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau) d :=
      hminimax sigma tau hsigma htau d hd
    _ ≤ _root_.GD.N0232.N0720.N1066.d014332 m n hm hn d := by
      apply ciSup_le
      intro mu
      unfold _root_.GD.N0232.N0720.N1066.d014332 _root_.GD.N0230.N0567.d001636
      exact le_ciSup
        (_root_.GD.N0232.N0720.N1066.d014344 m n hm hn d)
        (_root_.GD.N0232.N0720.N1078.d016372 mu sigma tau hsigma htau)




def d016383 (k : ℕ) : ℝ :=
  1 / ((k : ℝ) + 2)

theorem d016384 (k : ℕ) :
    0 < _root_.GD.N0232.N0720.N1074.d016383 k := by
  unfold _root_.GD.N0232.N0720.N1074.d016383
  positivity

theorem d016385 (k : ℕ) :
    _root_.GD.N0232.N0720.N1074.d016383 k < 1 := by
  unfold _root_.GD.N0232.N0720.N1074.d016383
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk : (1 : ℝ) < (k : ℝ) + 2 := by linarith
  exact (div_lt_one (by positivity)).2 hk

theorem d016386 :
    Tendsto _root_.GD.N0232.N0720.N1074.d016383 atTop (nhds 0) := by
  have hshift : Tendsto (fun k : ℕ => k + 2) atTop atTop :=
    tendsto_add_atTop_nat 2
  have h :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hshift
  apply h.congr'
  exact Filter.Eventually.of_forall fun k => by
    simp [_root_.GD.N0232.N0720.N1074.d016383, Function.comp_apply, Nat.cast_add]


def d016387 (m k : ℕ) : ℝ :=
  Real.sqrt ((m : ℝ) * (1 - _root_.GD.N0232.N0720.N1074.d016383 k))


def d016388 (n k : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) * _root_.GD.N0232.N0720.N1074.d016383 k)

theorem d016389 (hm2 : 2 ≤ m) (k : ℕ) :
    0 < _root_.GD.N0232.N0720.N1074.d016387 m k := by
  unfold _root_.GD.N0232.N0720.N1074.d016387
  apply Real.sqrt_pos.2
  exact mul_pos (by exact_mod_cast (show 0 < m by omega))
    (sub_pos.mpr (_root_.GD.N0232.N0720.N1074.d016385 k))

theorem d016390 (hn2 : 2 ≤ n) (k : ℕ) :
    0 < _root_.GD.N0232.N0720.N1074.d016388 n k := by
  unfold _root_.GD.N0232.N0720.N1074.d016388
  apply Real.sqrt_pos.2
  exact mul_pos (by exact_mod_cast (show 0 < n by omega))
    (_root_.GD.N0232.N0720.N1074.d016384 k)



def d016391 (k : ℕ) : _root_.GD.N0232.N0720.N1080.d014168 :=
  _root_.GD.N0232.N0720.N1078.d016372 0
    (_root_.GD.N0232.N0720.N1074.d016387 m k) (_root_.GD.N0232.N0720.N1074.d016388 n k)
    (_root_.GD.N0232.N0720.N1074.d016389 m hm k)
    (_root_.GD.N0232.N0720.N1074.d016390 n hn k)

theorem d016392 (k : ℕ) :
    _root_.GD.N0232.N0720.N1069.d014352 m n (_root_.GD.N0232.N0720.N1074.d016391 m n hm hn k) =
      _root_.GD.N0232.N0720.N1074.d016383 k := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp0 := _root_.GD.N0232.N0720.N1074.d016384 k
  have hp1 := _root_.GD.N0232.N0720.N1074.d016385 k
  unfold _root_.GD.N0232.N0720.N1069.d014352 _root_.GD.N0232.N0720.N1074.d016391
  simp only [_root_.GD.N0232.N0720.N1078.d016374, _root_.GD.N0232.N0720.N1078.d016375]
  unfold _root_.GD.N0232.N0720.N1074.d016387 _root_.GD.N0232.N0720.N1074.d016388
    _root_.GD.N0107.d009046
    _root_.GD.N0107.d009045
    _root_.GD.N0107.d009043
    _root_.GD.N0107.d009044
  rw [Real.sq_sqrt (mul_nonneg hmR.le (sub_nonneg.mpr hp1.le)),
    Real.sq_sqrt (mul_nonneg hnR.le hp0.le)]
  field_simp [hmR.ne', hnR.ne']
  ring



theorem d016393
    (hm4 : 4 ≤ m) :
    Tendsto
      (fun k => _root_.GD.N0232.N0720.N1075.d014487 m n
        (_root_.GD.N0232.N0720.N1074.d016391 m n hm hn k))
      atTop (nhds 1) := by
  have hbeta : 0 < _root_.GD.N0232.N0720.N1433.d014025 n := _root_.GD.N0232.N0720.N1433.d014027 hn
  have hp := _root_.GD.N0232.N0720.N1074.d016386
  have hp0 : ∀ k, 0 < _root_.GD.N0232.N0720.N1074.d016383 k := _root_.GD.N0232.N0720.N1074.d016384
  have hp1 : ∀ k, _root_.GD.N0232.N0720.N1074.d016383 k < 1 := _root_.GD.N0232.N0720.N1074.d016385
  have hpair : Tendsto
      (fun k =>
        (_root_.GD.N0232.N0720.N1442.d013869
            (_root_.GD.N0232.N0720.N1433.d014024 m) (_root_.GD.N0232.N0720.N1433.d014025 n)
            (_root_.GD.N0232.N0720.N1074.d016383 k),
          _root_.GD.N0232.N0720.N1442.d013868
            (_root_.GD.N0232.N0720.N1433.d014024 m) (_root_.GD.N0232.N0720.N1433.d014025 n)
            (_root_.GD.N0232.N0720.N1074.d016383 k)))
      atTop (nhds (1, 0)) := by
    rcases (show m = 4 ∨ m = 5 ∨ 6 ≤ m by omega) with rfl | rfl | hm6
    · exact _root_.GD.N0232.N0720.N1442.d013882
        (by norm_num [_root_.GD.N0232.N0720.N1433.d014024])
        (by norm_num [_root_.GD.N0232.N0720.N1433.d014024]) hbeta hp hp0 hp1
    · norm_num [_root_.GD.N0232.N0720.N1433.d014024]
      exact _root_.GD.N0232.N0720.N1442.d013883 hbeta hp hp0 hp1
    · exact _root_.GD.N0232.N0720.N1442.d013884
        (_root_.GD.N0232.N0720.N1433.d014033 hm6) hbeta hp hp0 hp1
  have hfirst : Tendsto
      (fun k => _root_.GD.N0232.N0720.N1442.d013869
        (_root_.GD.N0232.N0720.N1433.d014024 m) (_root_.GD.N0232.N0720.N1433.d014025 n)
        (_root_.GD.N0232.N0720.N1074.d016383 k)) atTop (nhds 1) := by
    exact continuous_fst.continuousAt.tendsto.comp hpair
  simpa only [_root_.GD.N0232.N0720.N1075.d014487,
    _root_.GD.N0232.N0720.N1074.d016392] using hfirst





theorem d016394
    {alpha beta p : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hp0 : 0 < p) (hp1 : p < 1) :
    _root_.GD.N0232.N0720.N1442.d013869 alpha beta p =
      _root_.GD.N0232.N0720.N1442.d013869 beta alpha (1 - p) := by
  have hregret := _root_.GD.N0232.N0720.N1438.d013603
    halpha hbeta hp0 hp1
  have horacle : _root_.GD.N0232.N0720.N1442.d013866 p = _root_.GD.N0232.N0720.N1442.d013866 (1 - p) := by
    unfold _root_.GD.N0232.N0720.N1442.d013866
    ring
  unfold _root_.GD.N0232.N0720.N1442.d013869 _root_.GD.N0232.N0720.N1442.d013867
  rw [horacle, hregret]


def d016395 (m k : ℕ) : ℝ :=
  Real.sqrt ((m : ℝ) * _root_.GD.N0232.N0720.N1074.d016383 k)


def d016396 (n k : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) * (1 - _root_.GD.N0232.N0720.N1074.d016383 k))

theorem d016397 (hm2 : 2 ≤ m) (k : ℕ) :
    0 < _root_.GD.N0232.N0720.N1074.d016395 m k := by
  unfold _root_.GD.N0232.N0720.N1074.d016395
  apply Real.sqrt_pos.2
  exact mul_pos (by exact_mod_cast (show 0 < m by omega))
    (_root_.GD.N0232.N0720.N1074.d016384 k)

theorem d016398 (hn2 : 2 ≤ n) (k : ℕ) :
    0 < _root_.GD.N0232.N0720.N1074.d016396 n k := by
  unfold _root_.GD.N0232.N0720.N1074.d016396
  apply Real.sqrt_pos.2
  exact mul_pos (by exact_mod_cast (show 0 < n by omega))
    (sub_pos.mpr (_root_.GD.N0232.N0720.N1074.d016385 k))


def d016399 (k : ℕ) : _root_.GD.N0232.N0720.N1080.d014168 :=
  _root_.GD.N0232.N0720.N1078.d016372 0
    (_root_.GD.N0232.N0720.N1074.d016395 m k) (_root_.GD.N0232.N0720.N1074.d016396 n k)
    (_root_.GD.N0232.N0720.N1074.d016397 m hm k)
    (_root_.GD.N0232.N0720.N1074.d016398 n hn k)

theorem d016400 (k : ℕ) :
    _root_.GD.N0232.N0720.N1069.d014352 m n (_root_.GD.N0232.N0720.N1074.d016399 m n hm hn k) =
      1 - _root_.GD.N0232.N0720.N1074.d016383 k := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp0 := _root_.GD.N0232.N0720.N1074.d016384 k
  have hp1 := _root_.GD.N0232.N0720.N1074.d016385 k
  unfold _root_.GD.N0232.N0720.N1069.d014352 _root_.GD.N0232.N0720.N1074.d016399
  simp only [_root_.GD.N0232.N0720.N1078.d016374, _root_.GD.N0232.N0720.N1078.d016375]
  unfold _root_.GD.N0232.N0720.N1074.d016395 _root_.GD.N0232.N0720.N1074.d016396
    _root_.GD.N0107.d009046
    _root_.GD.N0107.d009045
    _root_.GD.N0107.d009043
    _root_.GD.N0107.d009044
  rw [Real.sq_sqrt (mul_nonneg hmR.le hp0.le),
    Real.sq_sqrt (mul_nonneg hnR.le (sub_nonneg.mpr hp1.le))]
  field_simp [hmR.ne', hnR.ne']
  ring



theorem d016401
    (hn4 : 4 ≤ n) :
    Tendsto
      (fun k => _root_.GD.N0232.N0720.N1075.d014487 m n
        (_root_.GD.N0232.N0720.N1074.d016399 m n hm hn k))
      atTop (nhds 1) := by
  have halpha : 0 < _root_.GD.N0232.N0720.N1433.d014024 m := _root_.GD.N0232.N0720.N1433.d014026 hm
  have hbeta : 0 < _root_.GD.N0232.N0720.N1433.d014025 n := _root_.GD.N0232.N0720.N1433.d014027 hn
  have hp := _root_.GD.N0232.N0720.N1074.d016386
  have hp0 : ∀ k, 0 < _root_.GD.N0232.N0720.N1074.d016383 k := _root_.GD.N0232.N0720.N1074.d016384
  have hp1 : ∀ k, _root_.GD.N0232.N0720.N1074.d016383 k < 1 := _root_.GD.N0232.N0720.N1074.d016385
  have hpair : Tendsto
      (fun k =>
        (_root_.GD.N0232.N0720.N1442.d013869
            (_root_.GD.N0232.N0720.N1433.d014025 n) (_root_.GD.N0232.N0720.N1433.d014024 m)
            (_root_.GD.N0232.N0720.N1074.d016383 k),
          _root_.GD.N0232.N0720.N1442.d013868
            (_root_.GD.N0232.N0720.N1433.d014025 n) (_root_.GD.N0232.N0720.N1433.d014024 m)
            (_root_.GD.N0232.N0720.N1074.d016383 k)))
      atTop (nhds (1, 0)) := by
    rcases (show n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | hn6
    · exact _root_.GD.N0232.N0720.N1442.d013882
        (by norm_num [_root_.GD.N0232.N0720.N1433.d014025])
        (by norm_num [_root_.GD.N0232.N0720.N1433.d014025]) halpha hp hp0 hp1
    · norm_num [_root_.GD.N0232.N0720.N1433.d014025]
      exact _root_.GD.N0232.N0720.N1442.d013883 halpha hp hp0 hp1
    · exact _root_.GD.N0232.N0720.N1442.d013884
        (_root_.GD.N0232.N0720.N1433.d014034 hn6) halpha hp hp0 hp1
  have hreflected : Tendsto
      (fun k => _root_.GD.N0232.N0720.N1442.d013869
        (_root_.GD.N0232.N0720.N1433.d014024 m) (_root_.GD.N0232.N0720.N1433.d014025 n)
        (1 - _root_.GD.N0232.N0720.N1074.d016383 k)) atTop (nhds 1) := by
    have hfirst : Tendsto
        (fun k => _root_.GD.N0232.N0720.N1442.d013869
          (_root_.GD.N0232.N0720.N1433.d014025 n) (_root_.GD.N0232.N0720.N1433.d014024 m)
          (_root_.GD.N0232.N0720.N1074.d016383 k)) atTop (nhds 1) :=
      continuous_fst.continuousAt.tendsto.comp hpair
    apply hfirst.congr'
    exact Filter.Eventually.of_forall fun k => by
      exact _root_.GD.N0232.N0720.N1074.d016394
        (alpha := _root_.GD.N0232.N0720.N1433.d014025 n) (beta := _root_.GD.N0232.N0720.N1433.d014024 m)
        (p := _root_.GD.N0232.N0720.N1074.d016383 k)
        hbeta halpha (_root_.GD.N0232.N0720.N1074.d016384 k) (_root_.GD.N0232.N0720.N1074.d016385 k)
  simpa only [_root_.GD.N0232.N0720.N1075.d014487,
    _root_.GD.N0232.N0720.N1074.d016400] using hreflected





theorem d016402
    (hm4 : 4 ≤ m)
    (hminimax : _root_.GD.N0232.N0720.N1078.d016380 m n hm hn)
    {d : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1066.d014332 m n hm hn d = 1 := by
  apply le_antisymm
  · exact _root_.GD.N0232.N0720.N1066.d014343 m n hm hn d
  · have hlimit := _root_.GD.N0232.N0720.N1074.d016393
      m n hm hn hm4
    apply le_of_tendsto hlimit
    exact Filter.Eventually.of_forall fun k =>
      _root_.GD.N0232.N0720.N1074.d016382
        m n hm hn hminimax hd
        (_root_.GD.N0232.N0720.N1074.d016387 m k) (_root_.GD.N0232.N0720.N1074.d016388 n k)
        (_root_.GD.N0232.N0720.N1074.d016389 m hm k)
        (_root_.GD.N0232.N0720.N1074.d016390 n hn k)



theorem d016403
    (hn4 : 4 ≤ n)
    (hminimax : _root_.GD.N0232.N0720.N1078.d016380 m n hm hn)
    {d : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1066.d014332 m n hm hn d = 1 := by
  apply le_antisymm
  · exact _root_.GD.N0232.N0720.N1066.d014343 m n hm hn d
  · have hlimit := _root_.GD.N0232.N0720.N1074.d016401
      m n hm hn hn4
    apply le_of_tendsto hlimit
    exact Filter.Eventually.of_forall fun k =>
      _root_.GD.N0232.N0720.N1074.d016382
        m n hm hn hminimax hd
        (_root_.GD.N0232.N0720.N1074.d016395 m k) (_root_.GD.N0232.N0720.N1074.d016396 n k)
        (_root_.GD.N0232.N0720.N1074.d016397 m hm k)
        (_root_.GD.N0232.N0720.N1074.d016398 n hn k)



theorem d016404
    (hdesign : 4 ≤ m ∨ 4 ≤ n)
    (hminimax : _root_.GD.N0232.N0720.N1078.d016380 m n hm hn)
    {d : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1066.d014332 m n hm hn d = 1 := by
  rcases hdesign with hm4 | hn4
  · exact _root_.GD.N0232.N0720.N1074.d016402
      m n hm hn hm4 hminimax hd
  · exact _root_.GD.N0232.N0720.N1074.d016403
      m n hm hn hn4 hminimax hd




theorem d016405
    (hdesign : 4 ≤ m ∨ 4 ≤ n)
    {d : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1066.d014332 m n hm hn d = 1 := by
  exact _root_.GD.N0232.N0720.N1074.d016404
    m n hm hn hdesign
      (_root_.GD.N0232.N0720.N1078.d016381 m n hm hn) hd



theorem d016406
    (hdesign : 4 ≤ m ∨ 4 ≤ n)
    (hminimax : _root_.GD.N0232.N0720.N1078.d016380 m n hm hn)
    (d : _root_.GD.N0232.N0720.N1025.d014303 m n) :
    _root_.GD.N0232.N0720.N1066.d014332 m n hm hn d = 1 := by
  by_cases hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn
  · exact _root_.GD.N0232.N0720.N1074.d016404
      m n hm hn hdesign hminimax hd
  · exact _root_.GD.N0232.N0720.N1066.d014345 m n hm hn hd



theorem d016407
    (hdesign : 4 ≤ m ∨ 4 ≤ n)
    (d : _root_.GD.N0232.N0720.N1025.d014303 m n) :
    _root_.GD.N0232.N0720.N1066.d014332 m n hm hn d = 1 := by
  exact _root_.GD.N0232.N0720.N1074.d016406
    m n hm hn hdesign
      (_root_.GD.N0232.N0720.N1078.d016381 m n hm hn) d


theorem d016408
    (hdesign : 4 ≤ m ∨ 4 ≤ n)
    {d : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    IsMinOn (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) d := by
  intro e he
  change _root_.GD.N0232.N0720.N1066.d014332 m n hm hn d ≤
    _root_.GD.N0232.N0720.N1066.d014332 m n hm hn e
  rw [_root_.GD.N0232.N0720.N1074.d016405
      m n hm hn hdesign hd,
    _root_.GD.N0232.N0720.N1074.d016405
      m n hm hn hdesign he]





theorem d016409 :
    (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn).Subsingleton ↔
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) := by
  constructor
  · intro hsub e he
    have heCap : toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n) e ∈
        _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
      ⟨e, he, rfl⟩
    have hdomCap : toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)
        (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn :=
      ⟨_root_.GD.N0232.N0720.N1080.d014181 m n hm hn,
        _root_.GD.N0230.N0608.d000676 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn), rfl⟩
    exact (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).injective
      (hsub heCap hdomCap)
  · intro hterminal p hp q hq
    have hpStrong :
        (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm p =
          _root_.GD.N0232.N0720.N1080.d014181 m n hm hn := by
      exact hterminal _ ((_root_.GD.N0232.N0720.N1025.d014306 m n hm hn p).1 hp)
    have hqStrong :
        (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm q =
          _root_.GD.N0232.N0720.N1080.d014181 m n hm hn := by
      exact hterminal _ ((_root_.GD.N0232.N0720.N1025.d014306 m n hm hn q).1 hq)
    apply (toWeakSpace ℝ (_root_.GD.N0232.N0720.N1025.d014302 m n)).symm.injective
    rw [hpStrong, hqStrong]




theorem d016410
    (hdesign : 4 ≤ m ∨ 4 ≤ n) :
    _root_.GD.N0230.N0553.d001612
        (_root_.GD.N0230.N0567.d001631
          (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
        (_root_.GD.N0230.N0567.d001641
          (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
        (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
        (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) ↔
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn).Subsingleton := by
  constructor
  · intro hfaithful p hp q hq
    have hcollapse := _root_.GD.N0232.N0720.N1070.d014389
      m n hm hn hp hq
      (_root_.GD.N0232.N0720.N1074.d016408
        m n hm hn hdesign hp)
      (_root_.GD.N0232.N0720.N1074.d016408
        m n hm hn hdesign hq)
    exact
      (_root_.GD.N0232.N0720.N1070.d014392
        m n hm hn hfaithful) p q hp hq
        (_root_.GD.N0232.N0720.N1074.d016408
          m n hm hn hdesign hp)
        (_root_.GD.N0232.N0720.N1074.d016408
          m n hm hn hdesign hq) hcollapse
  · intro hsub p q hp hq _hpMin _hqMin _theta _hpActive _hqActive _hzero
    exact hsub hp hq





theorem d016411
    (hdesign : 4 ≤ m ∨ 4 ≤ n) :
    _root_.GD.N0230.N0553.d001612
        (_root_.GD.N0230.N0567.d001631
          (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
        (_root_.GD.N0230.N0567.d001641
          (_root_.GD.N0232.N0720.N1066.d014330 m n hm hn))
        (_root_.GD.N0232.N0720.N1066.d014332 m n hm hn)
        (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) ↔
      _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0720.N1080.d014182 m n) (_root_.GD.N0232.N0720.N1080.d014181 m n hm hn) := by
  exact (_root_.GD.N0232.N0720.N1074.d016410
    m n hm hn hdesign).trans
      (_root_.GD.N0232.N0720.N1074.d016409
        m n hm hn)

end

end N1074
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1074.d016405
#print axioms _root_.GD.N0232.N0720.N1074.d016410
#print axioms _root_.GD.N0232.N0720.N1074.d016411
