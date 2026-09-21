import GD.Module1103
import GD.Module1113
import GD.Module0894
import GD.Module1116
import GD.Module0933
import GD.Module1091
import Mathlib.Tactic











open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal

namespace GD.N0232.N0720.N1346

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1036
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1067
open _root_.GD.N0232.N0720.N1071
open _root_.GD.N0107 _root_.GD.N0141
open _root_.GD.N0232.N0720.N1218
open _root_.GD.N0232.N0720.N1219
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1185
open _root_.GD.N0232.N0720.N1276
open _root_.GD.N0232.N0720.N1361
open _root_.GD.N0232.N0720.N1362
open _root_.GD.N0232.N0720.N1425
open _root_.GD.N0232.N0720.N1433
open _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1442
open _root_.GD.N0232.N0720.N1405
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602

noncomputable local instance d018207 :
    MeasurableSpace _root_.GD.N0232.N0720.N1080.d014168 := borel _root_.GD.N0232.N0720.N1080.d014168

local instance d018208 : BorelSpace _root_.GD.N0232.N0720.N1080.d014168 := ⟨rfl⟩

private local instance d018209 :
    IsProbabilityMeasure (_root_.GD.N0232.N0720.N1080.d014172 2 2) := by
  unfold _root_.GD.N0232.N0720.N1080.d014172 _root_.GD.N0232.N0720.N1080.d014171
  infer_instance



theorem d018210
    (omega : _root_.GD.N0232.N0720.N1276.d016060) :
    _root_.GD.N0232.N0720.N1425.d014719 2 2 (fun _ ↦ (1 / 2 : ℝ)) omega =
      _root_.GD.N0232.N0720.N1405.d016086 omega := by
  rw [_root_.GD.N0232.N0720.N1425.d014720]
  have h := _root_.GD.N0232.N0720.N1362.d017713
    _root_.GD.N0232.N0720.N1080.d014169 omega
  simp only [_root_.GD.N0232.N0720.N1080.d014169] at h
  rw [show _root_.GD.N0232.N0720.N1405.d016086 omega =
      _root_.GD.N0107.d012732 2 2 0 (1 / 2) omega by simpa using h]
  unfold _root_.GD.N0107.d012732
  ring



theorem d018211
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta)
        (fun omega ↦ _root_.GD.N0232.N0720.N1405.d016086 omega - theta.location) =
      _root_.GD.N0107.d009045 2 2 theta.scale₁ theta.scale₂ / 4 := by
  let t := _root_.GD.N0107.d009046 2 2 theta.scale₁ theta.scale₂
  letI : IsProbabilityMeasure (_root_.GD.N0232.N0720.N1436.d013289 2 2 t) :=
    _root_.GD.N0232.N0720.N1434.d013564
      (by omega) (by omega)
      (_root_.GD.N0107.d009050 (by omega) (by omega)
        theta.scale₁_pos theta.scale₂_pos)
      (_root_.GD.N0107.d009051 (by omega) (by omega)
        theta.scale₁_pos theta.scale₂_pos)
  have hbridge :=
    _root_.GD.N0232.N0720.N1425.d014726
      2 2 (by omega) (by omega) theta.location theta.scale₁ theta.scale₂
      theta.scale₁_pos theta.scale₂_pos
      (fun _ ↦ (1 / 2 : ℝ)) measurable_const
      (B := (1 / 2 : ℝ)) (by norm_num) (by intro _; norm_num)
  have horacle := _root_.GD.N0232.N0720.N1071.d014426
    2 2 (by omega) (by omega) theta
  have hconst :
      (∫ _x, ((1 / 2 : ℝ) - t) ^ 2
        ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t) = (1 / 2 - t) ^ 2 := by
    simp
  rw [show (fun omega ↦
      _root_.GD.N0232.N0720.N1425.d014719 2 2 (fun _ ↦ (1 / 2 : ℝ)) omega -
        theta.location) =
      (fun omega ↦ _root_.GD.N0232.N0720.N1405.d016086 omega - theta.location) by
        funext omega
        rw [_root_.GD.N0232.N0720.N1346.d018210]] at hbridge
  change _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta)
      (fun omega ↦ _root_.GD.N0232.N0720.N1405.d016086 omega - theta.location) = _ at hbridge
  have horacle' :
      _root_.GD.N0141.d006684
          (_root_.GD.N0107.d009030 2 2 theta.location theta.scale₁ theta.scale₂)
          (_root_.GD.N0107.d012732 2 2 theta.location
            (_root_.GD.N0107.d009046 2 2 theta.scale₁ theta.scale₂)) =
        _root_.GD.N0107.d009045 2 2 theta.scale₁ theta.scale₂ *
          _root_.GD.N0232.N0720.N1442.d013866
            (_root_.GD.N0107.d009046 2 2 theta.scale₁ theta.scale₂) := by
    simpa [_root_.GD.N0232.N0720.N1080.d014171, t, _root_.GD.N0232.N0720.N1067.d014408] using horacle
  have hconst' :
      (∫ _x, ((1 / 2 : ℝ) -
          _root_.GD.N0107.d009046 2 2 theta.scale₁ theta.scale₂) ^ 2
        ∂_root_.GD.N0232.N0720.N1436.d013289 2 2
          (_root_.GD.N0107.d009046 2 2 theta.scale₁ theta.scale₂)) =
        (1 / 2 - _root_.GD.N0107.d009046 2 2 theta.scale₁ theta.scale₂) ^ 2 := by
    simpa [t] using hconst
  rw [horacle', hconst'] at hbridge
  rw [hbridge]
  unfold _root_.GD.N0232.N0720.N1442.d013866
  ring



theorem d018212
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1080.d014182 2 2 theta _root_.GD.N0232.N0720.N1362.d017715 =
      ENNReal.ofReal
        (_root_.GD.N0107.d009045 2 2 theta.scale₁ theta.scale₂ / 4) := by
  rw [_root_.GD.N0232.N0720.N1362.d017717,
    _root_.GD.N0232.N0720.N1346.d018211]

theorem d018213
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta _root_.GD.N0232.N0720.N1362.d017715).toReal =
      _root_.GD.N0107.d009045 2 2 theta.scale₁ theta.scale₂ / 4 := by
  rw [_root_.GD.N0232.N0720.N1346.d018212,
    ENNReal.toReal_ofReal]
  exact div_nonneg
    (_root_.GD.N0107.d009049 (by omega) (by omega)
      theta.scale₁_pos theta.scale₂_pos).le (by norm_num)

theorem d018214 :
    (_root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1080.d014169 _root_.GD.N0232.N0720.N1362.d017715).toReal =
      1 / 4 := by
  rw [_root_.GD.N0232.N0720.N1346.d018213]
  norm_num [_root_.GD.N0232.N0720.N1080.d014169, _root_.GD.N0107.d009045, _root_.GD.N0107.d009043,
    _root_.GD.N0107.d009044]

theorem d018215 :
    _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1080.d014169 _root_.GD.N0232.N0720.N1362.d017715 =
      ENNReal.ofReal (1 / 4) := by
  rw [_root_.GD.N0232.N0720.N1346.d018212]
  norm_num [_root_.GD.N0232.N0720.N1080.d014169, _root_.GD.N0107.d009045, _root_.GD.N0107.d009043,
    _root_.GD.N0107.d009044]





theorem d018216 :
    _root_.GD.N0232.N0720.N1080.d014182 2 2 _root_.GD.N0232.N0720.N1080.d014169 _root_.GD.N0232.N0720.N1362.d017715 <
      _root_.GD.N0232.N0720.N1066.d014320 2 2 (by omega) (by omega) _root_.GD.N0232.N0720.N1080.d014169 := by
  rw [_root_.GD.N0232.N0720.N1346.d018215,
    _root_.GD.N0232.N0720.N1503.d017913]
  norm_num

private def d018217 (k : ℕ) : ℝ :=
  1 / ((k : ℝ) + 2)

private theorem d018218 (k : ℕ) :
    0 < _root_.GD.N0232.N0720.N1346.d018217 k := by
  unfold _root_.GD.N0232.N0720.N1346.d018217
  positivity

private theorem d018219 (k : ℕ) :
    _root_.GD.N0232.N0720.N1346.d018217 k < 1 := by
  unfold _root_.GD.N0232.N0720.N1346.d018217
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk : (1 : ℝ) < (k : ℝ) + 2 := by linarith
  exact (div_lt_one (by positivity)).2 hk

private theorem d018220 :
    Tendsto _root_.GD.N0232.N0720.N1346.d018217 atTop (nhds 0) := by
  have hshift : Tendsto (fun k : ℕ ↦ k + 2) atTop atTop :=
    tendsto_add_atTop_nat 2
  have h :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hshift
  apply h.congr'
  exact Filter.Eventually.of_forall fun k ↦ by
    simp [_root_.GD.N0232.N0720.N1346.d018217, Function.comp_apply, Nat.cast_add]

private theorem d018221 :
    ∀ᶠ k in atTop,
      _root_.GD.N0232.N0720.N1442.d013867 (1 / 2) (1 / 2) (_root_.GD.N0232.N0720.N1346.d018217 k) <
        1 / 4 := by
  have hregret := _root_.GD.N0232.N0720.N1218.d013894
    (alpha := (1 / 2 : ℝ)) (beta := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1346.d018220
    _root_.GD.N0232.N0720.N1346.d018218 _root_.GD.N0232.N0720.N1346.d018219
  have horacle : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1442.d013866 (_root_.GD.N0232.N0720.N1346.d018217 k)) atTop (nhds 0) := by
    unfold _root_.GD.N0232.N0720.N1442.d013866
    convert _root_.GD.N0232.N0720.N1346.d018220.mul
      (tendsto_const_nhds.sub _root_.GD.N0232.N0720.N1346.d018220) using 1 <;>
      ring
  have htotal : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1442.d013867 (1 / 2) (1 / 2)
        (_root_.GD.N0232.N0720.N1346.d018217 k)) atTop (nhds 0) := by
    simpa [_root_.GD.N0232.N0720.N1442.d013867] using horacle.add hregret
  exact htotal.eventually_lt_const (by norm_num)



theorem d018222 :
    ∃ theta : _root_.GD.N0232.N0720.N1080.d014168,
      _root_.GD.N0232.N0720.N1066.d014320 2 2 (by omega) (by omega) theta <
        _root_.GD.N0232.N0720.N1080.d014182 2 2 theta _root_.GD.N0232.N0720.N1362.d017715 := by
  obtain ⟨k, hk⟩ := _root_.GD.N0232.N0720.N1346.d018221.exists
  let z := _root_.GD.N0232.N0720.N1346.d018217 k
  have hz : z ∈ Ioo (0 : ℝ) 1 :=
    ⟨_root_.GD.N0232.N0720.N1346.d018218 k, _root_.GD.N0232.N0720.N1346.d018219 k⟩
  let theta := _root_.GD.N0232.N0720.N1219.d017942 2 2 (by omega) (by omega) z hz
  refine ⟨theta, (ENNReal.toReal_lt_toReal
    (_root_.GD.N0232.N0720.N1066.d014323 2 2 (by omega) (by omega) theta)
    (_root_.GD.N0232.N0720.N1362.d017718 theta)).1 ?_⟩
  rw [_root_.GD.N0232.N0720.N1071.d014427,
    _root_.GD.N0232.N0720.N1346.d018213]
  rw [_root_.GD.N0232.N0720.N1219.d017948,
    show _root_.GD.N0232.N0720.N1067.d014408 2 2 theta = z by
      simpa [theta, _root_.GD.N0232.N0720.N1067.d014408,
        _root_.GD.N0232.N0720.N1069.d014352] using
        _root_.GD.N0232.N0720.N1219.d017949
          2 2 (by omega) (by omega) z hz]
  have hfirst : _root_.GD.N0232.N0720.N1433.d014024 2 =
      (1 / 2 : ℝ) := by
    norm_num [_root_.GD.N0232.N0720.N1433.d014024]
  have hsecond : _root_.GD.N0232.N0720.N1433.d014025 2 =
      (1 / 2 : ℝ) := by
    norm_num [_root_.GD.N0232.N0720.N1433.d014025]
  rw [hfirst, hsecond]
  simpa [z] using hk

theorem d018223 :
    ¬ _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 2 2) _root_.GD.N0232.N0720.N1362.d017715
      (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by omega) (by omega)) := by
  intro hdom
  obtain ⟨theta, hstrict⟩ :=
    _root_.GD.N0232.N0720.N1346.d018222
  exact (not_lt_of_ge (hdom theta)) (by
    simpa [_root_.GD.N0232.N0720.N1066.d014320] using hstrict)

theorem d018224 :
    ¬ _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 2 2) (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by omega) (by omega))
      _root_.GD.N0232.N0720.N1362.d017715 := by
  intro hdom
  exact (not_lt_of_ge (hdom _root_.GD.N0232.N0720.N1080.d014169)) (by
    simpa [_root_.GD.N0232.N0720.N1066.d014320] using
      _root_.GD.N0232.N0720.N1346.d018216)





theorem d018225
    (hterminal : _root_.GD.N0232.N0720.N1036.d014669 2 2
      _root_.GD.N0232.N0720.N1362.d017715)
    (s : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2) s
      (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by omega) (by omega))) :
    ¬ _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0720.N1080.d014182 2 2) s _root_.GD.N0232.N0720.N1362.d017715 := by
  intro hdom
  obtain ⟨theta, hbase⟩ :=
    _root_.GD.N0232.N0720.N1346.d018222
  have hs := hstrict theta
  rw [hterminal s hdom theta] at hs
  have hs' : _root_.GD.N0232.N0720.N1080.d014182 2 2 theta _root_.GD.N0232.N0720.N1362.d017715 <
      _root_.GD.N0232.N0720.N1066.d014320 2 2 (by omega) (by omega) theta := by
    simpa [_root_.GD.N0232.N0720.N1066.d014320] using hs
  exact (not_lt_of_ge hbase.le) hs'





theorem d018226
    (s : _root_.GD.N0232.N0720.N1159.d014639 2 2)
    (hstrict : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by omega) (by omega)))
    (hterminal : _root_.GD.N0232.N0720.N1036.d014669 2 2 s.value) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  exact _root_.GD.N0232.N0720.N1036.d014672
    2 2 (by omega) (by omega) s hstrict hterminal




theorem d018227 :
    _root_.GD.N0232.N0720.N1185.d017526 ≠ _root_.GD.N0232.N0720.N1362.d017715 := by
  intro heq
  obtain ⟨theta, hbase⟩ :=
    _root_.GD.N0232.N0720.N1346.d018222
  have ht := _root_.GD.N0232.N0720.N1185.d017532 theta
  rw [heq] at ht
  have ht' : _root_.GD.N0232.N0720.N1080.d014182 2 2 theta _root_.GD.N0232.N0720.N1362.d017715 <
      _root_.GD.N0232.N0720.N1066.d014320 2 2 (by omega) (by omega) theta := by
    simpa [_root_.GD.N0232.N0720.N1066.d014320] using ht
  exact (not_lt_of_ge hbase.le) ht'







theorem d018228
    (hterminal : _root_.GD.N0232.N0720.N1036.d014669 2 2 _root_.GD.N0232.N0720.N1185.d017526) :
    _root_.GD.N0232.N0720.N1159.d014661 2 2 := by
  apply _root_.GD.N0232.N0720.N1036.d014672
    2 2 (by omega) (by omega) _root_.GD.N0232.N0720.N1185.d017530
  · simpa only [_root_.GD.N0232.N0720.N1185.d017531] using
      _root_.GD.N0232.N0720.N1185.d017532
  · simpa only [_root_.GD.N0232.N0720.N1185.d017531] using hterminal






theorem d018229
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (candidate shifted : _root_.GD.N0232.N0720.N1276.d016060 → ℝ)
    (omega : _root_.GD.N0232.N0720.N1276.d016060)
    (hlike : Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior)
    (htarget : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      prior) :
    _root_.GD.N0232.N0720.N1276.d016066 prior shifted omega =
      _root_.GD.N0232.N0720.N1276.d016066 prior candidate omega -
        (shifted omega - candidate omega) * _root_.GD.N0232.N0720.N1276.d016063 prior omega := by
  rw [_root_.GD.N0232.N0720.N1276.d016072 prior shifted omega hlike htarget,
    _root_.GD.N0232.N0720.N1276.d016072 prior candidate omega hlike htarget]
  ring




theorem d018230
    {M J h : ℝ} (hM : 1 ≤ M) :
    h ^ 2 / 2 ≤ J ^ 2 / M + (J - h * M) ^ 2 / M := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  rw [← add_div]
  apply (le_div_iff₀ hMpos).2
  have haux : 0 ≤ h ^ 2 * M * (M - 1) :=
    mul_nonneg (mul_nonneg (sq_nonneg h) hMpos.le) (sub_nonneg.mpr hM)
  nlinarith [sq_nonneg (2 * J - h * M)]


theorem d018231
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (candidate shifted : _root_.GD.N0232.N0720.N1276.d016060 → ℝ)
    (omega : _root_.GD.N0232.N0720.N1276.d016060)
    (hlike : Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior)
    (htarget : Integrable
      (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
      prior)
    (hfloor : 1 ≤ _root_.GD.N0232.N0720.N1276.d016063 prior omega) :
    (shifted omega - candidate omega) ^ 2 / 2 ≤
      _root_.GD.N0232.N0720.N1276.d016066 prior candidate omega ^ 2 /
          _root_.GD.N0232.N0720.N1276.d016063 prior omega +
        _root_.GD.N0232.N0720.N1276.d016066 prior shifted omega ^ 2 /
          _root_.GD.N0232.N0720.N1276.d016063 prior omega := by
  rw [_root_.GD.N0232.N0720.N1346.d018229 prior candidate shifted omega
    hlike htarget]
  exact _root_.GD.N0232.N0720.N1346.d018230 hfloor




theorem d018232
    (prior : Measure _root_.GD.N0232.N0720.N1080.d014168)
    (candidate shifted : _root_.GD.N0232.N0720.N1276.d016060 → ℝ)
    (hrows : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) prior ∧
      Integrable
        (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
        prior)
    (hfloor : ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      1 ≤ _root_.GD.N0232.N0720.N1276.d016063 prior omega)
    (hdifference : Integrable
      (fun omega ↦ (shifted omega - candidate omega) ^ 2 / 2)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hcandidate : Integrable
      (fun omega ↦
        _root_.GD.N0232.N0720.N1276.d016066 prior candidate omega ^ 2 /
          _root_.GD.N0232.N0720.N1276.d016063 prior omega) (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hshifted : Integrable
      (fun omega ↦
        _root_.GD.N0232.N0720.N1276.d016066 prior shifted omega ^ 2 /
          _root_.GD.N0232.N0720.N1276.d016063 prior omega) (_root_.GD.N0232.N0720.N1080.d014172 2 2)) :
    (∫ omega, (shifted omega - candidate omega) ^ 2 / 2
        ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) ≤
      _root_.GD.N0232.N0720.N1276.d016067 prior candidate +
        _root_.GD.N0232.N0720.N1276.d016067 prior shifted := by
  unfold _root_.GD.N0232.N0720.N1276.d016067
  rw [← integral_add hcandidate hshifted]
  apply integral_mono_ae hdifference (hcandidate.add hshifted)
  filter_upwards [hrows, hfloor] with omega hrow hM
  exact _root_.GD.N0232.N0720.N1346.d018231
    prior candidate shifted omega hrow.1 hrow.2 hM




theorem d018233
    (prior : ℕ → Measure _root_.GD.N0232.N0720.N1080.d014168)
    (candidate shifted : _root_.GD.N0232.N0720.N1276.d016060 → ℝ)
    (hrows : ∀ k, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      Integrable (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016062 theta omega) (prior k) ∧
      Integrable
        (fun theta ↦ _root_.GD.N0232.N0720.N1276.d016061 theta * _root_.GD.N0232.N0720.N1276.d016062 theta omega)
        (prior k))
    (hfloor : ∀ k, ∀ᵐ omega ∂_root_.GD.N0232.N0720.N1080.d014172 2 2,
      1 ≤ _root_.GD.N0232.N0720.N1276.d016063 (prior k) omega)
    (hdifference : Integrable
      (fun omega ↦ (shifted omega - candidate omega) ^ 2 / 2)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hcandidate : ∀ k, Integrable
      (fun omega ↦
        _root_.GD.N0232.N0720.N1276.d016066 (prior k) candidate omega ^ 2 /
          _root_.GD.N0232.N0720.N1276.d016063 (prior k) omega) (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hshifted : ∀ k, Integrable
      (fun omega ↦
        _root_.GD.N0232.N0720.N1276.d016066 (prior k) shifted omega ^ 2 /
          _root_.GD.N0232.N0720.N1276.d016063 (prior k) omega) (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hcandidateZero : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1276.d016067 (prior k) candidate)
      atTop (nhds 0))
    (hshiftedZero : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1276.d016067 (prior k) shifted)
      atTop (nhds 0)) :
    (∫ omega, (shifted omega - candidate omega) ^ 2 / 2
      ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) = 0 := by
  let D := ∫ omega, (shifted omega - candidate omega) ^ 2 / 2
    ∂_root_.GD.N0232.N0720.N1080.d014172 2 2
  have hDnonneg : 0 ≤ D := by
    exact integral_nonneg fun omega ↦ div_nonneg (sq_nonneg _) (by norm_num)
  apply le_antisymm _ hDnonneg
  by_contra hnot
  have hDpos : 0 < D := lt_of_not_ge hnot
  have hsumZero : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1276.d016067 (prior k) candidate +
        _root_.GD.N0232.N0720.N1276.d016067 (prior k) shifted)
      atTop (nhds 0) := by
    simpa only [add_zero] using hcandidateZero.add hshiftedZero
  have hevent : ∀ᶠ k in atTop,
      _root_.GD.N0232.N0720.N1276.d016067 (prior k) candidate +
        _root_.GD.N0232.N0720.N1276.d016067 (prior k) shifted < D :=
    hsumZero.eventually_lt_const hDpos
  obtain ⟨k, hk⟩ := hevent.exists
  have hbound := _root_.GD.N0232.N0720.N1346.d018232
    (prior k) candidate shifted (hrows k) (hfloor k) hdifference
      (hcandidate k) (hshifted k)
  exact (not_lt_of_ge (by simpa [D] using hbound)) hk

theorem d018234
    (candidate shifted : _root_.GD.N0232.N0720.N1276.d016060 → ℝ)
    (hdifference : Integrable
      (fun omega ↦ (shifted omega - candidate omega) ^ 2 / 2)
      (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hzero : (∫ omega, (shifted omega - candidate omega) ^ 2 / 2
      ∂_root_.GD.N0232.N0720.N1080.d014172 2 2) = 0) :
    shifted =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2] candidate := by
  have hae : (fun omega ↦
      (shifted omega - candidate omega) ^ 2 / 2) =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 2 2] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (ae_of_all _ fun omega ↦
        div_nonneg (sq_nonneg (shifted omega - candidate omega)) (by norm_num))
      hdifference).1 hzero
  filter_upwards [hae] with omega homega
  simp only [Pi.zero_apply] at homega
  have hsquare : (shifted omega - candidate omega) ^ 2 = 0 := by
    nlinarith
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)

#print axioms _root_.GD.N0232.N0720.N1346.d018212
#print axioms _root_.GD.N0232.N0720.N1346.d018216
#print axioms _root_.GD.N0232.N0720.N1346.d018222
#print axioms _root_.GD.N0232.N0720.N1346.d018232
#print axioms _root_.GD.N0232.N0720.N1346.d018233
#print axioms _root_.GD.N0232.N0720.N1346.d018234
#print axioms _root_.GD.N0232.N0720.N1346.d018227
#print axioms _root_.GD.N0232.N0720.N1346.d018228

end

end GD.N0232.N0720.N1346
