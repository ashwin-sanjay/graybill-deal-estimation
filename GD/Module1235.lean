import GD.Module1212
import GD.Module0894














open MeasureTheory Filter Set
open scoped Topology

namespace GD.N0232.N0720.N1399

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1398 _root_.GD.N0232.N0720.N1287
open _root_.GD.N0232.N0720.N1424 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1434
open _root_.GD.N0232.N0720.N1423 _root_.GD.N0232.N0720.N1091
open _root_.GD.N0232.N0720.N1218



theorem d020093 (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1398.d019610 _root_.GD.N0232.N0720.N1424.d014839 t.1 = _root_.GD.N0232.N0720.N1091.d012790 (1 / 2) (1 / 2) t.1 := by
  unfold _root_.GD.N0232.N0720.N1398.d019610 _root_.GD.N0232.N0720.N1424.d014839
  rw [← _root_.GD.N0232.N0720.N1425.d014723
    (m := 2) (n := 2) (by omega) (by omega) t.2.1 t.2.2
    (fun x : _root_.GD.N0232.N0720.N1436.d013217 ↦ (x.1 - t.1) ^ 2)
    (by fun_prop)]
  have h := _root_.GD.N0232.N0720.N1423.d014020
    (alpha := _root_.GD.N0232.N0720.N1436.d013207 2) (beta := _root_.GD.N0232.N0720.N1436.d013208 2)
    (by norm_num [_root_.GD.N0232.N0720.N1436.d013207]) (by norm_num [_root_.GD.N0232.N0720.N1436.d013208]) t.2.1 t.2.2
  rw [h]
  simpa only [_root_.GD.N0232.N0720.N1436.d013207, _root_.GD.N0232.N0720.N1436.d013208, Nat.reduceSub, Nat.cast_one] using
    (_root_.GD.N0232.N0720.N1091.d012800
      (alpha := (1 / 2 : ℝ)) (beta := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) t.2.1 t.2.2).symm

theorem d020094 {p : ℕ → _root_.GD.N0232.N0720.N1441.d013676}
    (hp : Tendsto (fun k ↦ (p k).1) atTop (nhds 0)) :
    Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1398.d019610 _root_.GD.N0232.N0720.N1424.d014839 (p k).1) atTop (nhds 0) := by
  have h := _root_.GD.N0232.N0720.N1218.d013894 (alpha := (1 / 2 : ℝ)) (beta := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) hp (fun k ↦ (p k).2.1) (fun k ↦ (p k).2.2)
  exact h.congr' (Filter.Eventually.of_forall fun k ↦
    (_root_.GD.N0232.N0720.N1399.d020093 (p k)).symm)

theorem d020095 {p : ℕ → _root_.GD.N0232.N0720.N1441.d013676}
    (hp : Tendsto (fun k ↦ (p k).1) atTop (nhds 1)) :
    Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1398.d019610 _root_.GD.N0232.N0720.N1424.d014839 (p k).1) atTop (nhds 0) := by
  have h := _root_.GD.N0232.N0720.N1218.d013895 (alpha := (1 / 2 : ℝ)) (beta := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) hp (fun k ↦ (p k).2.1) (fun k ↦ (p k).2.2)
  exact h.congr' (Filter.Eventually.of_forall fun k ↦
    (_root_.GD.N0232.N0720.N1399.d020093 (p k)).symm)


theorem d020096 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) {p : ℕ → _root_.GD.N0232.N0720.N1441.d013676}
    (hp : Tendsto (fun k ↦ (p k).1) atTop (nhds 0)) :
    Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1398.d019610 (_root_.GD.N0232.N0720.N1398.d019601 d) (p k).1)
      atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (_root_.GD.N0232.N0720.N1399.d020094 hp)
    (fun k ↦ _root_.GD.N0232.N0720.N1398.d019611 _ _) (fun k ↦ (_root_.GD.N0232.N0720.N1398.d019617 hd (p k)).le)


theorem d020097 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) {p : ℕ → _root_.GD.N0232.N0720.N1441.d013676}
    (hp : Tendsto (fun k ↦ (p k).1) atTop (nhds 1)) :
    Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1398.d019610 (_root_.GD.N0232.N0720.N1398.d019601 d) (p k).1)
      atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (_root_.GD.N0232.N0720.N1399.d020095 hp)
    (fun k ↦ _root_.GD.N0232.N0720.N1398.d019611 _ _) (fun k ↦ (_root_.GD.N0232.N0720.N1398.d019617 hd (p k)).le)


theorem d020098 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : Measurable d) (t : _root_.GD.N0232.N0720.N1441.d013676) {a : ℝ} (hta : t.1 ≤ a)
    (ha : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2, a ≤ _root_.GD.N0232.N0720.N1398.d019601 d x) :
    (a - t.1) ^ 2 ≤ _root_.GD.N0232.N0720.N1398.d019610 (_root_.GD.N0232.N0720.N1398.d019601 d) t.1 := by
  letI := _root_.GD.N0232.N0720.N1434.d013564 (m := 2) (n := 2)
    (by omega) (by omega) t.2.1 t.2.2
  have hat : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1,
      a ≤ _root_.GD.N0232.N0720.N1398.d019601 d x :=
    (_root_.GD.N0232.N0720.N1441.d013682 (by omega : 2 ≤ 2) (by omega : 2 ≤ 2) t).ae_le ha
  calc
    (a - t.1) ^ 2 = ∫ _x, (a - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1 := by simp
    _ ≤ _root_.GD.N0232.N0720.N1398.d019610 (_root_.GD.N0232.N0720.N1398.d019601 d) t.1 := by
      apply integral_mono_ae (integrable_const _) (_root_.GD.N0232.N0720.N1398.d019609 hd t)
      filter_upwards [hat] with x hx
      exact (sq_le_sq₀ (sub_nonneg.mpr hta) (by linarith)).2 (by linarith)


theorem d020099 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : Measurable d) (t : _root_.GD.N0232.N0720.N1441.d013676) {b : ℝ} (hbt : b ≤ t.1)
    (hb : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2, _root_.GD.N0232.N0720.N1398.d019601 d x ≤ b) :
    (t.1 - b) ^ 2 ≤ _root_.GD.N0232.N0720.N1398.d019610 (_root_.GD.N0232.N0720.N1398.d019601 d) t.1 := by
  letI := _root_.GD.N0232.N0720.N1434.d013564 (m := 2) (n := 2)
    (by omega) (by omega) t.2.1 t.2.2
  have hbt' : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1,
      _root_.GD.N0232.N0720.N1398.d019601 d x ≤ b :=
    (_root_.GD.N0232.N0720.N1441.d013682 (by omega : 2 ≤ 2) (by omega : 2 ≤ 2) t).ae_le hb
  calc
    (t.1 - b) ^ 2 = ∫ _x, (t.1 - b) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 2 2 t.1 := by simp
    _ ≤ _root_.GD.N0232.N0720.N1398.d019610 (_root_.GD.N0232.N0720.N1398.d019601 d) t.1 := by
      apply integral_mono_ae (integrable_const _) (_root_.GD.N0232.N0720.N1398.d019609 hd t)
      filter_upwards [hbt'] with x hx
      have h := (sq_le_sq₀ (sub_nonneg.mpr hbt)
        (show 0 ≤ t.1 - _root_.GD.N0232.N0720.N1398.d019601 d x by linarith)).2
        (show t.1 - b ≤ t.1 - _root_.GD.N0232.N0720.N1398.d019601 d x by linarith)
      nlinarith

def d020100 (k : ℕ) : _root_.GD.N0232.N0720.N1441.d013676 :=
  ⟨1 / ((k : ℝ) + 2), by
    constructor
    · positivity
    · apply (div_lt_one (by positivity)).2
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith⟩

theorem d020101 :
    Tendsto (fun k ↦ (_root_.GD.N0232.N0720.N1399.d020100 k).1) atTop (nhds 0) := by
  have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
  apply h.congr'
  exact Filter.Eventually.of_forall fun k ↦ by simp [_root_.GD.N0232.N0720.N1399.d020100, Function.comp_apply]

def d020102 (k : ℕ) : _root_.GD.N0232.N0720.N1441.d013676 :=
  ⟨1 - (_root_.GD.N0232.N0720.N1399.d020100 k).1, by
    constructor <;> linarith [(_root_.GD.N0232.N0720.N1399.d020100 k).2.1, (_root_.GD.N0232.N0720.N1399.d020100 k).2.2]⟩

theorem d020103 :
    Tendsto (fun k ↦ (_root_.GD.N0232.N0720.N1399.d020102 k).1) atTop (nhds 1) := by
  simpa only [_root_.GD.N0232.N0720.N1399.d020102, sub_zero] using
    (tendsto_const_nhds.sub _root_.GD.N0232.N0720.N1399.d020101)



theorem d020104 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) {a : ℝ} (ha : 0 < a) :
    ¬ (∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2, a ≤ _root_.GD.N0232.N0720.N1398.d019601 d x) := by
  intro hfloor
  have hloss := _root_.GD.N0232.N0720.N1399.d020096 hd _root_.GD.N0232.N0720.N1399.d020101
  have hsmall := hloss.eventually_lt_const (sq_pos_of_pos (half_pos ha))
  have hfrac := _root_.GD.N0232.N0720.N1399.d020101.eventually_lt_const (half_pos ha)
  obtain ⟨k, hk, ht⟩ := (hsmall.and hfrac).exists
  have hbound := _root_.GD.N0232.N0720.N1399.d020098 hd.1 (_root_.GD.N0232.N0720.N1399.d020100 k)
    (a := a) (by linarith) hfloor
  have hgap : a / 2 < a - (_root_.GD.N0232.N0720.N1399.d020100 k).1 := by linarith
  have hsquare := (sq_lt_sq₀ (half_pos ha).le (by linarith)).2 hgap
  linarith



theorem d020105 {d : _root_.GD.N0232.N0720.N1080.d014170 2 2 → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 2 2 d) {b : ℝ} (hb : b < 1) :
    ¬ (∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 2 2, _root_.GD.N0232.N0720.N1398.d019601 d x ≤ b) := by
  intro hceiling
  have hgap : 0 < (1 - b) / 2 := half_pos (sub_pos.mpr hb)
  have hloss := _root_.GD.N0232.N0720.N1399.d020097 hd _root_.GD.N0232.N0720.N1399.d020103
  have hsmall := hloss.eventually_lt_const (sq_pos_of_pos hgap)
  have hfrac := _root_.GD.N0232.N0720.N1399.d020103.eventually_const_lt
    (show (1 + b) / 2 < 1 by linarith)
  obtain ⟨k, hk, ht⟩ := (hsmall.and hfrac).exists
  have hbound := _root_.GD.N0232.N0720.N1399.d020099 hd.1 (_root_.GD.N0232.N0720.N1399.d020102 k)
    (b := b) (by linarith) hceiling
  have hsquare := (sq_lt_sq₀ hgap.le
    (show 0 ≤ (_root_.GD.N0232.N0720.N1399.d020102 k).1 - b by linarith)).2
    (show (1 - b) / 2 < (_root_.GD.N0232.N0720.N1399.d020102 k).1 - b by linarith)
  linarith

end
end GD.N0232.N0720.N1399

#print axioms _root_.GD.N0232.N0720.N1399.d020093
#print axioms _root_.GD.N0232.N0720.N1399.d020096
#print axioms _root_.GD.N0232.N0720.N1399.d020097
#print axioms _root_.GD.N0232.N0720.N1399.d020104
#print axioms _root_.GD.N0232.N0720.N1399.d020105
