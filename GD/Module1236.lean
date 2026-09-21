import GD.Module1235










open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace GD.N0232.N0720.N1332

noncomputable section

open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1159
open _root_.GD.N0232.N0720.N1287 _root_.GD.N0232.N0720.N1396
open _root_.GD.N0232.N0720.N1424 _root_.GD.N0232.N0720.N1441
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1434 _root_.GD.N0232.N0720.N1423
open _root_.GD.N0232.N0720.N1091 _root_.GD.N0232.N0720.N1218
open _root_.GD.N0107 _root_.GD.N0137 _root_.GD.N0141
open _root_.GD.N0232.N0720.N1399 (d020100 d020102
  d020101 d020103)

def d020106 (m n : ℕ) (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (t : ℝ) : ℝ :=
  ∫ x, (g x - t) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 m n t

theorem d020107 (m n : ℕ) (g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ) (t : ℝ) :
    0 ≤ _root_.GD.N0232.N0720.N1332.d020106 m n g t := integral_nonneg (fun _ ↦ sq_nonneg _)

theorem d020108 {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {g h : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (heq : g =ᵐ[_root_.GD.N0232.N0720.N1441.d013679 m n] h)
    (t : _root_.GD.N0232.N0720.N1441.d013676) : _root_.GD.N0232.N0720.N1332.d020106 m n g t.1 = _root_.GD.N0232.N0720.N1332.d020106 m n h t.1 := by
  apply integral_congr_ae
  filter_upwards [(_root_.GD.N0232.N0720.N1441.d013682 hm hn t).ae_le heq] with x hx
  rw [hx]

theorem d020109
    (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1080.d014197 m n theta (_root_.GD.N0232.N0720.N1425.d014719 m n g) =
      ENNReal.ofReal
        (_root_.GD.N0141.d006684 (_root_.GD.N0232.N0720.N1080.d014171 m n theta)
          (_root_.GD.N0107.d012732 m n theta.location
            (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) +
          _root_.GD.N0107.d009045 m n theta.scale₁ theta.scale₂ *
            _root_.GD.N0232.N0720.N1332.d020106 m n g (_root_.GD.N0107.d009046 m n theta.scale₁ theta.scale₂)) := by
  rw [_root_.GD.N0232.N0720.N1396.d014785 m n theta
    (_root_.GD.N0232.N0720.N1287.d019517 m n hm hn theta g hg hb)]
  congr 1
  exact _root_.GD.N0232.N0720.N1425.d014726
    m n hm hn theta.location theta.scale₁ theta.scale₂
    theta.scale₁_pos theta.scale₂_pos g hg (B := 1) zero_le_one
    (fun x ↦ by rw [abs_of_nonneg (hb x).1]; exact (hb x).2)

def d020110 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676) : _root_.GD.N0232.N0720.N1080.d014168 where
  location := 0
  scale₁ := _root_.GD.N0232.N0720.N1424.d014846 m t.1
  scale₂ := _root_.GD.N0232.N0720.N1424.d014847 n t.1
  scale₁_pos := _root_.GD.N0232.N0720.N1424.d014848 hm t.2.2
  scale₂_pos := _root_.GD.N0232.N0720.N1424.d014849 hn t.2.1

theorem d020111 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0107.d009045 m n (_root_.GD.N0232.N0720.N1332.d020110 m n hm hn t).scale₁
      (_root_.GD.N0232.N0720.N1332.d020110 m n hm hn t).scale₂ = 1 :=
  _root_.GD.N0232.N0720.N1424.d014852 hm hn t.2.1 t.2.2

theorem d020112 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0107.d009046 m n (_root_.GD.N0232.N0720.N1332.d020110 m n hm hn t).scale₁
      (_root_.GD.N0232.N0720.N1332.d020110 m n hm hn t).scale₂ = t.1 :=
  _root_.GD.N0232.N0720.N1424.d014853 hm hn t.2.1 t.2.2



theorem d020113
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d) {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ}
    (hg : Measurable g) (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g)
    (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1332.d020106 m n g t.1 < _root_.GD.N0232.N0720.N1332.d020106 m n _root_.GD.N0232.N0720.N1424.d014839 t.1 := by
  have h := hd.2.2.1 (_root_.GD.N0232.N0720.N1332.d020110 m n hm hn t)
  rw [_root_.GD.N0232.N0720.N1159.d014662 m n _ (hrep _),
    _root_.GD.N0232.N0720.N1332.d020109 m n hm hn _ hg hb,
    _root_.GD.N0232.N0720.N1080.d014199 m n hm hn,
    _root_.GD.N0232.N0720.N1287.d019529 m n hm hn] at h
  change ENNReal.ofReal (_ + _ * _root_.GD.N0232.N0720.N1332.d020106 m n g _) <
    ENNReal.ofReal (_ + _ * _root_.GD.N0232.N0720.N1332.d020106 m n _root_.GD.N0232.N0720.N1424.d014839 _) at h
  rw [_root_.GD.N0232.N0720.N1332.d020111, _root_.GD.N0232.N0720.N1332.d020112, one_mul] at h
  have hreal := (ENNReal.ofReal_lt_ofReal_iff').1 h
  linarith [hreal.1]

theorem d020114
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) (t : _root_.GD.N0232.N0720.N1441.d013676) :
    _root_.GD.N0232.N0720.N1332.d020106 m n _root_.GD.N0232.N0720.N1424.d014839 t.1 =
      _root_.GD.N0232.N0720.N1091.d012790 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) t.1 := by
  unfold _root_.GD.N0232.N0720.N1332.d020106 _root_.GD.N0232.N0720.N1424.d014839
  rw [← _root_.GD.N0232.N0720.N1425.d014723 hm hn t.2.1 t.2.2
    (fun x : _root_.GD.N0232.N0720.N1436.d013217 ↦ (x.1 - t.1) ^ 2) (by fun_prop)]
  rw [_root_.GD.N0232.N0720.N1423.d014020
    (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn) t.2.1 t.2.2]
  exact (_root_.GD.N0232.N0720.N1091.d012800
    (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn) t.2.1 t.2.2).symm

theorem d020115
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) {p : ℕ → _root_.GD.N0232.N0720.N1441.d013676}
    (hp : Tendsto (fun k ↦ (p k).1) atTop (nhds 0)) :
    Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1332.d020106 m n _root_.GD.N0232.N0720.N1424.d014839 (p k).1) atTop (nhds 0) := by
  have h := _root_.GD.N0232.N0720.N1218.d013894
    (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn) hp
    (fun k ↦ (p k).2.1) (fun k ↦ (p k).2.2)
  exact h.congr' (Eventually.of_forall fun k ↦
    (_root_.GD.N0232.N0720.N1332.d020114 hm hn (p k)).symm)

theorem d020116
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) {p : ℕ → _root_.GD.N0232.N0720.N1441.d013676}
    (hp : Tendsto (fun k ↦ (p k).1) atTop (nhds 1)) :
    Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1332.d020106 m n _root_.GD.N0232.N0720.N1424.d014839 (p k).1) atTop (nhds 0) := by
  have h := _root_.GD.N0232.N0720.N1218.d013895
    (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn) hp
    (fun k ↦ (p k).2.1) (fun k ↦ (p k).2.2)
  exact h.congr' (Eventually.of_forall fun k ↦
    (_root_.GD.N0232.N0720.N1332.d020114 hm hn (p k)).symm)

theorem d020117 {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1) (t : _root_.GD.N0232.N0720.N1441.d013676) {a : ℝ} (hta : t.1 ≤ a)
    (ha : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, a ≤ g x) :
    (a - t.1) ^ 2 ≤ _root_.GD.N0232.N0720.N1332.d020106 m n g t.1 := by
  letI := _root_.GD.N0232.N0720.N1434.d013564 hm hn t.2.1 t.2.2
  have hat := (_root_.GD.N0232.N0720.N1441.d013682 hm hn t).ae_le ha
  calc
    (a - t.1) ^ 2 = ∫ _x, (a - t.1) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 m n t.1 := by simp
    _ ≤ _root_.GD.N0232.N0720.N1332.d020106 m n g t.1 := by
      apply integral_mono_ae (integrable_const _)
        (_root_.GD.N0232.N0720.N1287.d019523 m n hm hn t g hg hb)
      filter_upwards [hat] with x hx
      exact (sq_le_sq₀ (sub_nonneg.mpr hta) (by linarith)).2 (by linarith)

theorem d020118 {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ} (hg : Measurable g)
    (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1) (t : _root_.GD.N0232.N0720.N1441.d013676) {b : ℝ} (hbt : b ≤ t.1)
    (hceiling : ∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, g x ≤ b) :
    (t.1 - b) ^ 2 ≤ _root_.GD.N0232.N0720.N1332.d020106 m n g t.1 := by
  letI := _root_.GD.N0232.N0720.N1434.d013564 hm hn t.2.1 t.2.2
  have hat := (_root_.GD.N0232.N0720.N1441.d013682 hm hn t).ae_le hceiling
  calc
    (t.1 - b) ^ 2 = ∫ _x, (t.1 - b) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 m n t.1 := by simp
    _ ≤ _root_.GD.N0232.N0720.N1332.d020106 m n g t.1 := by
      apply integral_mono_ae (integrable_const _)
        (_root_.GD.N0232.N0720.N1287.d019523 m n hm hn t g hg hb)
      filter_upwards [hat] with x hx
      have h := (sq_le_sq₀ (sub_nonneg.mpr hbt)
        (show 0 ≤ t.1 - g x by linarith)).2 (show t.1 - b ≤ t.1 - g x by linarith)
      nlinarith

theorem d020119
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d) {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ}
    (hg : Measurable g) (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g)
    {a : ℝ} (ha : 0 < a) : ¬ (∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, a ≤ g x) := by
  intro hfloor
  have hloss : Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1332.d020106 m n g (_root_.GD.N0232.N0720.N1399.d020100 k).1)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (_root_.GD.N0232.N0720.N1332.d020115 hm hn _root_.GD.N0232.N0720.N1399.d020101)
      (fun k ↦ _root_.GD.N0232.N0720.N1332.d020107 _ _ _ _)
      (fun k ↦ (_root_.GD.N0232.N0720.N1332.d020113 hm hn hd hg hb hrep _).le)
  have hsmall := hloss.eventually_lt_const (sq_pos_of_pos (half_pos ha))
  have hfrac := _root_.GD.N0232.N0720.N1399.d020101.eventually_lt_const (half_pos ha)
  obtain ⟨k, hk, ht⟩ := (hsmall.and hfrac).exists
  have hbound := _root_.GD.N0232.N0720.N1332.d020117 hm hn hg hb (_root_.GD.N0232.N0720.N1399.d020100 k)
    (a := a) (by linarith) hfloor
  have hgap : a / 2 < a - (_root_.GD.N0232.N0720.N1399.d020100 k).1 := by linarith
  have hsquare := (sq_lt_sq₀ (half_pos ha).le (by linarith)).2 hgap
  linarith

theorem d020120
    {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) {d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ}
    (hd : _root_.GD.N0232.N0720.N1159.d014660 m n d) {g : _root_.GD.N0232.N0720.N1436.d013217 → ℝ}
    (hg : Measurable g) (hb : ∀ x, g x ∈ Icc (0 : ℝ) 1)
    (hrep : ∀ theta, d =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0232.N0720.N1425.d014719 m n g)
    {b : ℝ} (hbone : b < 1) : ¬ (∀ᵐ x ∂_root_.GD.N0232.N0720.N1441.d013679 m n, g x ≤ b) := by
  intro hceiling
  have hgap : 0 < (1 - b) / 2 := half_pos (sub_pos.mpr hbone)
  have hloss : Tendsto (fun k ↦ _root_.GD.N0232.N0720.N1332.d020106 m n g (_root_.GD.N0232.N0720.N1399.d020102 k).1)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (_root_.GD.N0232.N0720.N1332.d020116 hm hn _root_.GD.N0232.N0720.N1399.d020103)
      (fun k ↦ _root_.GD.N0232.N0720.N1332.d020107 _ _ _ _)
      (fun k ↦ (_root_.GD.N0232.N0720.N1332.d020113 hm hn hd hg hb hrep _).le)
  have hsmall := hloss.eventually_lt_const (sq_pos_of_pos hgap)
  have hfrac := _root_.GD.N0232.N0720.N1399.d020103.eventually_const_lt
    (show (1 + b) / 2 < 1 by linarith)
  obtain ⟨k, hk, ht⟩ := (hsmall.and hfrac).exists
  have hbound := _root_.GD.N0232.N0720.N1332.d020118 hm hn hg hb (_root_.GD.N0232.N0720.N1399.d020102 k)
    (b := b) (by linarith) hceiling
  have hsquare := (sq_lt_sq₀ hgap.le
    (show 0 ≤ (_root_.GD.N0232.N0720.N1399.d020102 k).1 - b by linarith)).2
    (show (1 - b) / 2 < (_root_.GD.N0232.N0720.N1399.d020102 k).1 - b by linarith)
  linarith

end
end GD.N0232.N0720.N1332

#print axioms _root_.GD.N0232.N0720.N1332.d020113
#print axioms _root_.GD.N0232.N0720.N1332.d020114
#print axioms _root_.GD.N0232.N0720.N1332.d020119
#print axioms _root_.GD.N0232.N0720.N1332.d020120
