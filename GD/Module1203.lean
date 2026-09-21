import GD.Module1110
import GD.Module0894
import GD.Module1023
import GD.Module1171
import GD.Module0923
import GD.Module1163
import GD.Module1164
import GD.Module0932
import GD.Module1116
import GD.Module0940
import GD.Module0860
import GD.Module1202































open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal

namespace GD
namespace N0232
namespace N0720
namespace N1063

noncomputable section

open _root_.GD.N0232.N0720.N1029
open _root_.GD.N0232.N0720.N1047
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1067
open _root_.GD.N0232.N0720.N1071
open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1106
open _root_.GD.N0107 _root_.GD.N0141
open _root_.GD.N0232.N0720.N1218
open _root_.GD.N0232.N0720.N1219
open _root_.GD.N0232.N0720.N1301
open _root_.GD.N0232.N0720.N1369
open _root_.GD.N0232.N0720.N1425
open _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1433
open _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1442
open _root_.GD.N0232.N0720.N1450
open _root_.GD.N0232.N0720.N1471
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0602





theorem d019443
    (kernel : ℝ → ℝ) (_hevidence : kernel 0 ≠ 0) :
    _root_.GD.N0232.N0720.N1218.d013885 (Measure.dirac 0) kernel = 0 := by
  simp [_root_.GD.N0232.N0720.N1218.d013885]



theorem d019444
    (kernel : ℝ → ℝ) (hevidence : kernel 1 ≠ 0) :
    _root_.GD.N0232.N0720.N1218.d013885 (Measure.dirac 1) kernel = 1 := by
  simp [_root_.GD.N0232.N0720.N1218.d013885, hevidence]





theorem d019445
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta)
        (fun omega ↦
          _root_.GD.N0232.N0720.N1425.d014719 2 2 (fun _ ↦ (0 : ℝ)) omega -
            theta.location) =
      _root_.GD.N0107.d009045 2 2 theta.scale₁ theta.scale₂ *
        _root_.GD.N0232.N0720.N1067.d014408 2 2 theta := by
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
      (fun _ ↦ (0 : ℝ)) measurable_const
      (B := (0 : ℝ)) (by norm_num) (by intro _; simp)
  have horacle := _root_.GD.N0232.N0720.N1071.d014426
    2 2 (by omega) (by omega) theta
  have horacle' :
      _root_.GD.N0141.d006684
          (_root_.GD.N0107.d009030 2 2 theta.location theta.scale₁ theta.scale₂)
          (_root_.GD.N0107.d012732 2 2 theta.location t) =
        _root_.GD.N0107.d009045 2 2 theta.scale₁ theta.scale₂ *
          _root_.GD.N0232.N0720.N1442.d013866 t := by
    simpa [_root_.GD.N0232.N0720.N1080.d014171, t, _root_.GD.N0232.N0720.N1067.d014408] using horacle
  have hconst :
      (∫ _x, ((0 : ℝ) - t) ^ 2
          ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t) = t ^ 2 := by
    simp
  rw [horacle', hconst] at hbridge
  change
    _root_.GD.N0141.d006684
        (_root_.GD.N0107.d009030 2 2 theta.location theta.scale₁ theta.scale₂)
        (fun omega ↦
          _root_.GD.N0232.N0720.N1425.d014719 2 2 (fun _ ↦ (0 : ℝ)) omega -
            theta.location) =
      _root_.GD.N0107.d009045 2 2 theta.scale₁ theta.scale₂ *
        _root_.GD.N0107.d009046
          2 2 theta.scale₁ theta.scale₂
  rw [hbridge]
  dsimp [t]
  unfold _root_.GD.N0232.N0720.N1442.d013866
  ring



theorem d019446
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta)
        (fun omega ↦
          _root_.GD.N0232.N0720.N1425.d014719 2 2 (fun _ ↦ (1 : ℝ)) omega -
            theta.location) =
      _root_.GD.N0107.d009045 2 2 theta.scale₁ theta.scale₂ *
        (1 - _root_.GD.N0232.N0720.N1067.d014408 2 2 theta) := by
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
      (fun _ ↦ (1 : ℝ)) measurable_const
      (B := (1 : ℝ)) (by norm_num) (by intro _; simp)
  have horacle := _root_.GD.N0232.N0720.N1071.d014426
    2 2 (by omega) (by omega) theta
  have horacle' :
      _root_.GD.N0141.d006684
          (_root_.GD.N0107.d009030 2 2 theta.location theta.scale₁ theta.scale₂)
          (_root_.GD.N0107.d012732 2 2 theta.location t) =
        _root_.GD.N0107.d009045 2 2 theta.scale₁ theta.scale₂ *
          _root_.GD.N0232.N0720.N1442.d013866 t := by
    simpa [_root_.GD.N0232.N0720.N1080.d014171, t, _root_.GD.N0232.N0720.N1067.d014408] using horacle
  have hconst :
      (∫ _x, ((1 : ℝ) - t) ^ 2
          ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t) = (1 - t) ^ 2 := by
    simp
  rw [horacle', hconst] at hbridge
  change
    _root_.GD.N0141.d006684
        (_root_.GD.N0107.d009030 2 2 theta.location theta.scale₁ theta.scale₂)
        (fun omega ↦
          _root_.GD.N0232.N0720.N1425.d014719 2 2 (fun _ ↦ (1 : ℝ)) omega -
            theta.location) =
      _root_.GD.N0107.d009045 2 2 theta.scale₁ theta.scale₂ *
        (1 - _root_.GD.N0107.d009046
          2 2 theta.scale₁ theta.scale₂)
  rw [hbridge]
  dsimp [t]
  unfold _root_.GD.N0232.N0720.N1442.d013866
  ring




def d019447 (k : ℕ) : ℝ := 1 / ((k : ℝ) + 2)

theorem d019448 (k : ℕ) : 0 < _root_.GD.N0232.N0720.N1063.d019447 k := by
  unfold _root_.GD.N0232.N0720.N1063.d019447
  positivity

theorem d019449 (k : ℕ) : _root_.GD.N0232.N0720.N1063.d019447 k < 1 := by
  unfold _root_.GD.N0232.N0720.N1063.d019447
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  exact (div_lt_one (by positivity)).2 (by linarith)

theorem d019450 :
    Tendsto _root_.GD.N0232.N0720.N1063.d019447 atTop (nhds 0) := by
  have hshift : Tendsto (fun k : ℕ ↦ k + 2) atTop atTop :=
    tendsto_add_atTop_nat 2
  have h :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hshift
  apply h.congr'
  exact Filter.Eventually.of_forall fun k ↦ by
    simp [_root_.GD.N0232.N0720.N1063.d019447, Function.comp_apply, Nat.cast_add]



theorem d019451 :
    ∀ᶠ k in atTop,
      _root_.GD.N0232.N0720.N1442.d013867 (1 / 2) (1 / 2) (_root_.GD.N0232.N0720.N1063.d019447 k) <
        1 - _root_.GD.N0232.N0720.N1063.d019447 k := by
  have hregret := _root_.GD.N0232.N0720.N1218.d013894
    (alpha := (1 / 2 : ℝ)) (beta := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) _root_.GD.N0232.N0720.N1063.d019450
    _root_.GD.N0232.N0720.N1063.d019448 _root_.GD.N0232.N0720.N1063.d019449
  have horacle : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1442.d013866 (_root_.GD.N0232.N0720.N1063.d019447 k)) atTop (nhds 0) := by
    unfold _root_.GD.N0232.N0720.N1442.d013866
    simpa using _root_.GD.N0232.N0720.N1063.d019450.mul
      (tendsto_const_nhds.sub _root_.GD.N0232.N0720.N1063.d019450)
  have htotal : Tendsto
      (fun k ↦ _root_.GD.N0232.N0720.N1442.d013867 (1 / 2) (1 / 2)
        (_root_.GD.N0232.N0720.N1063.d019447 k)) atTop (nhds 0) := by
    simpa [_root_.GD.N0232.N0720.N1442.d013867] using horacle.add hregret
  have htotalSmall := htotal.eventually_lt_const
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hprobeSmall := _root_.GD.N0232.N0720.N1063.d019450.eventually_lt_const
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [htotalSmall, hprobeSmall] with k htotalK hprobeK
  linarith



theorem d019452
    {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    _root_.GD.N0232.N0720.N1442.d013867 (1 / 2) (1 / 2) (1 - z) =
      _root_.GD.N0232.N0720.N1442.d013867 (1 / 2) (1 / 2) z := by
  have hreflect :=
    _root_.GD.N0232.N0720.N1438.d013603
      (alpha := (1 / 2 : ℝ)) (beta := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) hz0 hz1
  unfold _root_.GD.N0232.N0720.N1442.d013867 _root_.GD.N0232.N0720.N1442.d013866
  rw [← hreflect]
  ring





def d019453
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) : Prop :=
  ∀ theta : _root_.GD.N0232.N0720.N1080.d014168,
    (fun omega ↦ q omega) =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 2 2 theta]
      _root_.GD.N0232.N0720.N1425.d014719 2 2 g

theorem d019454
    {q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2)}
    (hq : _root_.GD.N0232.N0720.N1159.d014637 2 2 q)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ}
    (hrep : _root_.GD.N0232.N0720.N1063.d019453 q g)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta q).toReal =
      _root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 2 2 theta)
        (fun omega ↦ _root_.GD.N0232.N0720.N1425.d014719 2 2 g omega - theta.location) := by
  rw [_root_.GD.N0232.N0720.N1128.d017097
    2 2 theta q (hq theta)]
  unfold _root_.GD.N0141.d006684
  apply integral_congr_ae
  filter_upwards [hrep theta] with omega homega
  rw [homega]



theorem d019455
    (s : _root_.GD.N0232.N0720.N1159.d014639 2 2)
    (hstrict : _root_.GD.N0232.N0720.N1471.d019425 2 2 (by omega) (by omega) s) :
    ¬ _root_.GD.N0232.N0720.N1063.d019453 s.value (fun _ ↦ (1 : ℝ)) := by
  intro hrep
  obtain ⟨k, hk⟩ := _root_.GD.N0232.N0720.N1063.d019451.exists
  let z := _root_.GD.N0232.N0720.N1063.d019447 k
  have hz : z ∈ Ioo (0 : ℝ) 1 :=
    ⟨_root_.GD.N0232.N0720.N1063.d019448 k, _root_.GD.N0232.N0720.N1063.d019449 k⟩
  let theta := _root_.GD.N0232.N0720.N1219.d017942 2 2 (by omega) (by omega) z hz
  have hall : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by omega) (by omega)) :=
    (_root_.GD.N0232.N0720.N1106.d018689 2 2 s.value
      (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by omega) (by omega)) s.riskCharacter
      (_root_.GD.N0232.N0720.N1047.d018647 2 2 (by omega) (by omega))).2 hstrict
  have hreal :
      (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta s.value).toReal <
        (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by omega) (by omega))).toReal :=
    (ENNReal.toReal_lt_toReal (s.finiteRisk theta)
      (_root_.GD.N0232.N0720.N1047.d018646
        2 2 (by omega) (by omega) theta)).2
        (hall theta)
  rw [_root_.GD.N0232.N0720.N1063.d019454 s.finiteRisk hrep,
    _root_.GD.N0232.N0720.N1063.d019446,
    show _root_.GD.N0107.d009045 2 2 theta.scale₁ theta.scale₂ = 1 by
      simpa [theta] using _root_.GD.N0232.N0720.N1219.d017948
        2 2 (by omega) (by omega) z hz,
    show _root_.GD.N0232.N0720.N1067.d014408 2 2 theta = z by
      simpa [theta, _root_.GD.N0232.N0720.N1067.d014408,
        _root_.GD.N0232.N0720.N1069.d014352] using
        _root_.GD.N0232.N0720.N1219.d017949
          2 2 (by omega) (by omega) z hz,
    one_mul] at hreal
  have hbase :
      (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by omega) (by omega))).toReal =
        _root_.GD.N0232.N0720.N1442.d013867 (1 / 2) (1 / 2) z := by
    change (_root_.GD.N0232.N0720.N1066.d014320 2 2 (by omega) (by omega) theta).toReal = _
    rw [_root_.GD.N0232.N0720.N1071.d014427]
    rw [show _root_.GD.N0107.d009045 2 2 theta.scale₁ theta.scale₂ = 1 by
        simpa [theta] using _root_.GD.N0232.N0720.N1219.d017948
          2 2 (by omega) (by omega) z hz,
      show _root_.GD.N0232.N0720.N1067.d014408 2 2 theta = z by
        simpa [theta, _root_.GD.N0232.N0720.N1067.d014408,
          _root_.GD.N0232.N0720.N1069.d014352] using
          _root_.GD.N0232.N0720.N1219.d017949
            2 2 (by omega) (by omega) z hz]
    norm_num [_root_.GD.N0232.N0720.N1433.d014024,
      _root_.GD.N0232.N0720.N1433.d014025]
  rw [hbase] at hreal
  exact (not_lt_of_ge hk.le) (by simpa [z] using hreal)



theorem d019456
    (s : _root_.GD.N0232.N0720.N1159.d014639 2 2)
    (hstrict : _root_.GD.N0232.N0720.N1471.d019425 2 2 (by omega) (by omega) s) :
    ¬ _root_.GD.N0232.N0720.N1063.d019453 s.value (fun _ ↦ (0 : ℝ)) := by
  intro hrep
  obtain ⟨k, hk⟩ := _root_.GD.N0232.N0720.N1063.d019451.exists
  let z := _root_.GD.N0232.N0720.N1063.d019447 k
  have hz : z ∈ Ioo (0 : ℝ) 1 :=
    ⟨_root_.GD.N0232.N0720.N1063.d019448 k, _root_.GD.N0232.N0720.N1063.d019449 k⟩
  let w := 1 - z
  have hw : w ∈ Ioo (0 : ℝ) 1 := by
    exact ⟨sub_pos.mpr hz.2, by linarith [hz.1]⟩
  let theta := _root_.GD.N0232.N0720.N1219.d017942 2 2 (by omega) (by omega) w hw
  have hall : _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0720.N1080.d014182 2 2) s.value
      (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by omega) (by omega)) :=
    (_root_.GD.N0232.N0720.N1106.d018689 2 2 s.value
      (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by omega) (by omega)) s.riskCharacter
      (_root_.GD.N0232.N0720.N1047.d018647 2 2 (by omega) (by omega))).2 hstrict
  have hreal :
      (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta s.value).toReal <
        (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by omega) (by omega))).toReal :=
    (ENNReal.toReal_lt_toReal (s.finiteRisk theta)
      (_root_.GD.N0232.N0720.N1047.d018646
        2 2 (by omega) (by omega) theta)).2
        (hall theta)
  rw [_root_.GD.N0232.N0720.N1063.d019454 s.finiteRisk hrep,
    _root_.GD.N0232.N0720.N1063.d019445,
    show _root_.GD.N0107.d009045 2 2 theta.scale₁ theta.scale₂ = 1 by
      simpa [theta] using _root_.GD.N0232.N0720.N1219.d017948
        2 2 (by omega) (by omega) w hw,
    show _root_.GD.N0232.N0720.N1067.d014408 2 2 theta = w by
      simpa [theta, _root_.GD.N0232.N0720.N1067.d014408,
        _root_.GD.N0232.N0720.N1069.d014352] using
        _root_.GD.N0232.N0720.N1219.d017949
          2 2 (by omega) (by omega) w hw,
    one_mul] at hreal
  have hbase :
      (_root_.GD.N0232.N0720.N1080.d014182 2 2 theta (_root_.GD.N0232.N0720.N1080.d014180 2 2 (by omega) (by omega))).toReal =
        _root_.GD.N0232.N0720.N1442.d013867 (1 / 2) (1 / 2) w := by
    change (_root_.GD.N0232.N0720.N1066.d014320 2 2 (by omega) (by omega) theta).toReal = _
    rw [_root_.GD.N0232.N0720.N1071.d014427]
    rw [show _root_.GD.N0107.d009045 2 2 theta.scale₁ theta.scale₂ = 1 by
        simpa [theta] using _root_.GD.N0232.N0720.N1219.d017948
          2 2 (by omega) (by omega) w hw,
      show _root_.GD.N0232.N0720.N1067.d014408 2 2 theta = w by
        simpa [theta, _root_.GD.N0232.N0720.N1067.d014408,
          _root_.GD.N0232.N0720.N1069.d014352] using
          _root_.GD.N0232.N0720.N1219.d017949
            2 2 (by omega) (by omega) w hw]
    norm_num [_root_.GD.N0232.N0720.N1433.d014024,
      _root_.GD.N0232.N0720.N1433.d014025]
  rw [hbase] at hreal
  have hreflect :
      _root_.GD.N0232.N0720.N1442.d013867 (1 / 2) (1 / 2) w =
        _root_.GD.N0232.N0720.N1442.d013867 (1 / 2) (1 / 2) z := by
    simpa [w] using _root_.GD.N0232.N0720.N1063.d019452 hz.1 hz.2
  rw [hreflect] at hreal
  exact (not_lt_of_ge hk.le) (by simpa [w, z] using hreal)



theorem d019457 :
    ¬ _root_.GD.N0232.N0720.N1063.d019453
      (_root_.GD.N0232.N0720.N1029.d015364 2 2 (by omega) (by omega)) (fun _ ↦ (0 : ℝ)) := by
  apply _root_.GD.N0232.N0720.N1063.d019456
    (_root_.GD.N0232.N0720.N1029.d015372 2 2 (by omega) (by omega))
  exact (_root_.GD.N0232.N0720.N1106.d018689 2 2 _ _
    (_root_.GD.N0232.N0720.N1029.d015372 2 2 (by omega) (by omega)).riskCharacter
    (_root_.GD.N0232.N0720.N1047.d018647 2 2 (by omega) (by omega))).1
      (_root_.GD.N0232.N0720.N1029.d015368
        2 2 (by omega) (by omega))

theorem d019458 :
    ¬ _root_.GD.N0232.N0720.N1063.d019453
      (_root_.GD.N0232.N0720.N1029.d015364 2 2 (by omega) (by omega)) (fun _ ↦ (1 : ℝ)) := by
  apply _root_.GD.N0232.N0720.N1063.d019455
    (_root_.GD.N0232.N0720.N1029.d015372 2 2 (by omega) (by omega))
  exact (_root_.GD.N0232.N0720.N1106.d018689 2 2 _ _
    (_root_.GD.N0232.N0720.N1029.d015372 2 2 (by omega) (by omega)).riskCharacter
    (_root_.GD.N0232.N0720.N1047.d018647 2 2 (by omega) (by omega))).1
      (_root_.GD.N0232.N0720.N1029.d015368
        2 2 (by omega) (by omega))

theorem d019459 :
    ¬ _root_.GD.N0232.N0720.N1063.d019453
      (_root_.GD.N0232.N0720.N1450.d017831 2 2 (by omega) (by omega)) (fun _ ↦ (0 : ℝ)) := by
  apply _root_.GD.N0232.N0720.N1063.d019456
    (_root_.GD.N0232.N0720.N1450.d017834 2 2 (by omega) (by omega))
  exact (_root_.GD.N0232.N0720.N1106.d018689 2 2 _ _
    (_root_.GD.N0232.N0720.N1450.d017834 2 2 (by omega) (by omega)).riskCharacter
    (_root_.GD.N0232.N0720.N1047.d018647 2 2 (by omega) (by omega))).1
      (_root_.GD.N0232.N0720.N1450.d017836 2 2 (by omega) (by omega))

theorem d019460 :
    ¬ _root_.GD.N0232.N0720.N1063.d019453
      (_root_.GD.N0232.N0720.N1450.d017831 2 2 (by omega) (by omega)) (fun _ ↦ (1 : ℝ)) := by
  apply _root_.GD.N0232.N0720.N1063.d019455
    (_root_.GD.N0232.N0720.N1450.d017834 2 2 (by omega) (by omega))
  exact (_root_.GD.N0232.N0720.N1106.d018689 2 2 _ _
    (_root_.GD.N0232.N0720.N1450.d017834 2 2 (by omega) (by omega)).riskCharacter
    (_root_.GD.N0232.N0720.N1047.d018647 2 2 (by omega) (by omega))).1
      (_root_.GD.N0232.N0720.N1450.d017836 2 2 (by omega) (by omega))



theorem d019461
    (q : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (b : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hb : _root_.GD.N0232.N0720.N1063.d019453 b (fun _ ↦ (0 : ℝ))) :
    ¬ (Tendsto q atTop
          (nhds (_root_.GD.N0232.N0720.N1450.d017831 2 2 (by omega) (by omega))) ∧
        Tendsto q atTop (nhds b)) := by
  rintro ⟨hday, hboundary⟩
  have heq : b = _root_.GD.N0232.N0720.N1450.d017831 2 2 (by omega) (by omega) :=
    tendsto_nhds_unique hboundary hday
  subst b
  exact _root_.GD.N0232.N0720.N1063.d019459 hb


theorem d019462
    (q : ℕ → _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (b : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 2 2))
    (hb : _root_.GD.N0232.N0720.N1063.d019453 b (fun _ ↦ (1 : ℝ))) :
    ¬ (Tendsto q atTop
          (nhds (_root_.GD.N0232.N0720.N1450.d017831 2 2 (by omega) (by omega))) ∧
        Tendsto q atTop (nhds b)) := by
  rintro ⟨hday, hboundary⟩
  have heq : b = _root_.GD.N0232.N0720.N1450.d017831 2 2 (by omega) (by omega) :=
    tendsto_nhds_unique hboundary hday
  subst b
  exact _root_.GD.N0232.N0720.N1063.d019460 hb






theorem d019463
    {massZero massOne : ℝ}
    (hmassZero : 0 < massZero) (hmassOne : 0 < massOne)
    (hswap : ∀ e ∈ Ioo (0 : ℝ) 1,
      _root_.GD.N0232.N0720.N1301.d016275 massZero massOne (1 - e) =
        1 - _root_.GD.N0232.N0720.N1301.d016275 massZero massOne e) :
    massZero = massOne := by
  have hhalf := hswap (1 / 2 : ℝ) (by norm_num)
  norm_num only at hhalf
  rw [_root_.GD.N0232.N0720.N1301.d016278 hmassZero hmassOne] at hhalf
  have hsum : massZero + massOne ≠ 0 :=
    (add_pos hmassZero hmassOne).ne'
  field_simp [hsum] at hhalf
  linarith




theorem d019464
    {massZero massOne : ℝ}
    (hmassZero : 0 < massZero) (hmassOne : 0 < massOne)
    (hswap : ∀ e ∈ Ioo (0 : ℝ) 1,
      _root_.GD.N0232.N0720.N1301.d016275 massZero massOne (1 - e) =
        1 - _root_.GD.N0232.N0720.N1301.d016275 massZero massOne e) :
    ¬ ∀ e ∈ Ioo (0 : ℝ) 1,
      _root_.GD.N0232.N0720.N1301.d016275 massZero massOne e = e := by
  have hmasses : massZero = massOne :=
    _root_.GD.N0232.N0720.N1063.d019463 hmassZero hmassOne hswap
  subst massOne
  exact _root_.GD.N0232.N0720.N1301.d016280 hmassZero hmassZero

end

end N1063
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1063.d019443
#print axioms _root_.GD.N0232.N0720.N1063.d019445
#print axioms _root_.GD.N0232.N0720.N1063.d019456
#print axioms _root_.GD.N0232.N0720.N1063.d019455
#print axioms _root_.GD.N0232.N0720.N1063.d019459
#print axioms _root_.GD.N0232.N0720.N1063.d019461
#print axioms _root_.GD.N0232.N0720.N1063.d019464
