import GD.Module0881
import GD.Module0940












open MeasureTheory ProbabilityTheory Set

namespace GD.N0232.N0720.N1328

open _root_.GD.N0232.N0720.N1310 _root_.GD.N0232.N0720.N1309
open _root_.GD.N0232.N0720.N1313 _root_.GD.N0232.N0720.N1311
open _root_.GD.N0232.N0720.N1091 _root_.GD.N0232.N0720.N1504
open _root_.GD.N0232.N0720.N1425 _root_.GD.N0232.N0720.N1436
open _root_.GD.N0232.N0720.N1433
  (d014032 d014028)
open _root_.GD.N0107 _root_.GD.N0137 _root_.GD.N0141

noncomputable section

def d014755 (alpha beta r : ℝ) : ℝ :=
  Real.sqrt (beta * r) / (Real.sqrt (beta * r) + Real.sqrt (alpha * (1 - r)))

def d014756 (m n : ℕ) : (_root_.GD.N0137.d008894 m × _root_.GD.N0137.d008894 n) → ℝ :=
  _root_.GD.N0232.N0720.N1425.d014719 m n
    (fun x ↦ _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1)

theorem d014757 (alpha beta : ℝ) : Measurable (_root_.GD.N0232.N0720.N1328.d014755 alpha beta) := by
  unfold _root_.GD.N0232.N0720.N1328.d014755
  fun_prop

theorem d014758 {alpha beta : ℝ} (ha : 0 < alpha) (hb : 0 < beta) (r : ℝ) :
    _root_.GD.N0232.N0720.N1328.d014755 alpha beta r ∈ Icc (0 : ℝ) 1 := by
  have hd : 0 < Real.sqrt (beta * r) + Real.sqrt (alpha * (1 - r)) := by
    by_cases hr : 0 < r
    · exact add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr (mul_pos hb hr)) (Real.sqrt_nonneg _)
    · exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _)
        (Real.sqrt_pos.mpr (mul_pos ha (by linarith)))
  exact ⟨div_nonneg (Real.sqrt_nonneg _) hd.le,
    (div_le_one hd).2 (by linarith [Real.sqrt_nonneg (alpha * (1 - r))])⟩

private theorem d014759 {alpha beta r : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (hr : r ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1328.d014755 alpha beta r =
      1 - _root_.GD.N0232.N0720.N1310.d013058 1 (alpha * (1 - r) / (beta * r)) := by
  have hp : 0 < Real.sqrt (beta * r) := Real.sqrt_pos.mpr (mul_pos hb hr.1)
  have hq : 0 < Real.sqrt (alpha * (1 - r)) :=
    Real.sqrt_pos.mpr (mul_pos ha (sub_pos.mpr hr.2))
  unfold _root_.GD.N0232.N0720.N1328.d014755 _root_.GD.N0232.N0720.N1310.d013058
  rw [one_mul, Real.sqrt_div (mul_pos ha (sub_pos.mpr hr.2)).le]
  have hd : Real.sqrt (beta * r) + Real.sqrt (alpha * (1 - r)) ≠ 0 := by positivity
  have hi : 1 + Real.sqrt (alpha * (1 - r)) / Real.sqrt (beta * r) ≠ 0 := by positivity
  field_simp [hp.ne', hd, hi]
  ring

private theorem d014760 {epsilon : ℝ} (he : 0 < epsilon) :
    1 / (1 + epsilon) ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · positivity
  · exact (div_lt_one (by positivity)).2 (by linarith)

private theorem d014761 {epsilon : ℝ} (he : 0 < epsilon) :
    1 - 1 / (1 + epsilon) = _root_.GD.N0232.N0720.N1309.d013069 epsilon := by
  unfold _root_.GD.N0232.N0720.N1309.d013069
  field_simp [(by positivity : 1 + epsilon ≠ 0)]
  ring

private theorem d014762 {alpha beta epsilon : ℝ}
    (he : 0 < epsilon) :
    _root_.GD.N0232.N0720.N1091.d012762 alpha beta (1 / (1 + epsilon)) = alpha / (beta * epsilon) := by
  unfold _root_.GD.N0232.N0720.N1091.d012762
  rw [_root_.GD.N0232.N0720.N1328.d014761 he]
  unfold _root_.GD.N0232.N0720.N1309.d013069
  rw [← mul_div_assoc, mul_one, ← mul_div_assoc]
  exact div_div_div_cancel_right₀ (by positivity : 1 + epsilon ≠ 0) alpha (beta * epsilon)

private theorem d014763 {alpha beta epsilon u : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (he : 0 < epsilon) (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta (1 / (1 + epsilon))) u =
      1 - _root_.GD.N0232.N0720.N1310.d013059 (beta / alpha) epsilon (u / (1 - u)) := by
  have hp := _root_.GD.N0232.N0720.N1328.d014760 he
  have hOdds := _root_.GD.N0232.N0720.N1091.d012778 ha hb hp.1 hp.2
  have hD := (_root_.GD.N0232.N0720.N1091.d012779 hOdds hu.1 hu.2).ne'
  have hG : 1 + beta / alpha * epsilon * (u / (1 - u)) ≠ 0 :=
    (add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (mul_nonneg (div_pos hb ha).le he.le)
        (div_nonneg hu.1.le (sub_pos.mpr hu.2).le))).ne'
  unfold _root_.GD.N0232.N0720.N1091.d012763 _root_.GD.N0232.N0720.N1310.d013059
  rw [one_sub_div hG]
  have hcancel : 1 + beta / alpha * epsilon * (u / (1 - u)) -
      beta / alpha * epsilon * (u / (1 - u)) = 1 := by ring
  rw [hcancel]
  apply (div_eq_div_iff hD hG).2
  rw [_root_.GD.N0232.N0720.N1328.d014762 he]
  field_simp [ha.ne', hb.ne', he.ne', (sub_pos.mpr hu.2).ne']
  ring

private theorem d014764 {alpha beta epsilon u : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (he : 0 < epsilon) (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0232.N0720.N1328.d014755 alpha beta (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta (1 / (1 + epsilon))) u) =
      1 - _root_.GD.N0232.N0720.N1310.d013058 epsilon (u / (1 - u)) := by
  have hp := _root_.GD.N0232.N0720.N1328.d014760 he
  have hOdds := _root_.GD.N0232.N0720.N1091.d012778 ha hb hp.1 hp.2
  have hr := _root_.GD.N0232.N0720.N1091.d012780 hOdds hu.1 hu.2
  rw [_root_.GD.N0232.N0720.N1328.d014759 ha hb hr]
  have hratio : alpha * (1 - _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta (1 / (1 + epsilon))) u) /
      (beta * _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta (1 / (1 + epsilon))) u) =
      epsilon * (u / (1 - u)) := by
    have hD := (_root_.GD.N0232.N0720.N1091.d012779 hOdds hu.1 hu.2).ne'
    have hR := hr.1.ne'
    have hinner :
        (1 - _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta (1 / (1 + epsilon))) u) /
          _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta (1 / (1 + epsilon))) u =
        u / (_root_.GD.N0232.N0720.N1091.d012762 alpha beta (1 / (1 + epsilon)) * (1 - u)) := by
      unfold _root_.GD.N0232.N0720.N1091.d012763
      rw [one_sub_div hD, div_div_div_cancel_right₀ hD]
      congr 1
      ring
    calc
      _ = alpha / beta *
          ((1 - _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta (1 / (1 + epsilon))) u) /
            _root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 alpha beta (1 / (1 + epsilon))) u) := by
        field_simp [hb.ne', hR]
      _ = alpha / beta * (u /
          (_root_.GD.N0232.N0720.N1091.d012762 alpha beta (1 / (1 + epsilon)) * (1 - u))) := by rw [hinner]
      _ = epsilon * (u / (1 - u)) := by
        rw [_root_.GD.N0232.N0720.N1328.d014762 he]
        field_simp [ha.ne', hb.ne', he.ne', (sub_pos.mpr hu.2).ne']
  rw [hratio]
  simp only [_root_.GD.N0232.N0720.N1310.d013058, one_mul]


theorem d014765 {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ x, f x.1 ∂_root_.GD.N0232.N0720.N1436.d013289 m n p) =
      ∫ u, f (_root_.GD.N0232.N0720.N1091.d012763 (_root_.GD.N0232.N0720.N1091.d012762 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) p) u)
        ∂betaMeasure (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) := by
  have ha := _root_.GD.N0232.N0720.N1436.d013211 hm
  have hb := _root_.GD.N0232.N0720.N1436.d013212 hn
  rw [← _root_.GD.N0232.N0720.N1425.d014723 hm hn hp.1 hp.2
    (fun x ↦ f x.1) (hf.comp measurable_fst)]
  rw [_root_.GD.N0232.N0720.N1091.d012797 ha hb f hf]
  rw [← _root_.GD.N0232.N0720.N1504.d013979 ha hb]
  rw [integral_map
    (f := fun u : ℝ ↦ f (_root_.GD.N0232.N0720.N1091.d012763
      (_root_.GD.N0232.N0720.N1091.d012762 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) p) u))
    (_root_.GD.N0232.N0720.N1091.d012770 _ _).aemeasurable
    ((hf.comp (_root_.GD.N0232.N0720.N1091.d012771 _)).aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1091.d012782 ha hb hp.1 hp.2] with q hq
  rw [hq]

theorem d014766 {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {epsilon : ℝ} (he : 0 < epsilon) :
    (∫ x, (_root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1 -
      1 / (1 + epsilon)) ^ 2 ∂_root_.GD.N0232.N0720.N1436.d013289 m n (1 / (1 + epsilon))) =
      _root_.GD.N0232.N0720.N1309.d013070 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) epsilon := by
  rw [_root_.GD.N0232.N0720.N1328.d014765 hm hn (_root_.GD.N0232.N0720.N1328.d014760 he)
    (fun r ↦ (_root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) r -
      1 / (1 + epsilon)) ^ 2) (by unfold _root_.GD.N0232.N0720.N1328.d014755; fun_prop)]
  unfold _root_.GD.N0232.N0720.N1309.d013070
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1309.d013072 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n)] with u hu
  rw [_root_.GD.N0232.N0720.N1328.d014764 (_root_.GD.N0232.N0720.N1436.d013211 hm) (_root_.GD.N0232.N0720.N1436.d013212 hn) he hu]
  rw [← _root_.GD.N0232.N0720.N1328.d014761 he]
  ring

theorem d014767 {alpha beta epsilon : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (he : 0 < epsilon) :
    _root_.GD.N0232.N0720.N1091.d012790 alpha beta (1 / (1 + epsilon)) = _root_.GD.N0232.N0720.N1309.d013071 alpha beta epsilon := by
  unfold _root_.GD.N0232.N0720.N1091.d012790 _root_.GD.N0232.N0720.N1309.d013071
  apply integral_congr_ae
  filter_upwards [_root_.GD.N0232.N0720.N1309.d013072 alpha beta] with u hu
  rw [_root_.GD.N0232.N0720.N1328.d014763 ha hb he hu]
  rw [← _root_.GD.N0232.N0720.N1328.d014761 he]
  ring

theorem d014768 {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (mu sigma tau : ℝ) (hs : 0 < sigma) (ht : 0 < tau)
    {epsilon : ℝ} (he : 0 < epsilon)
    (hp : _root_.GD.N0107.d009046 m n sigma tau = 1 / (1 + epsilon)) :
    _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau) (fun x ↦ _root_.GD.N0232.N0720.N1328.d014756 m n x - mu) -
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau) (fun x ↦ _root_.GD.N0107.d012733 m n x - mu) =
      _root_.GD.N0107.d009045 m n sigma tau *
        (_root_.GD.N0232.N0720.N1309.d013070 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) epsilon -
          _root_.GD.N0232.N0720.N1309.d013071 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) epsilon) := by
  have ha := _root_.GD.N0232.N0720.N1436.d013211 hm
  have hb := _root_.GD.N0232.N0720.N1436.d013212 hn
  have hroot := _root_.GD.N0232.N0720.N1425.d014726
    m n hm hn mu sigma tau hs ht
    (fun x ↦ _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1)
    ((_root_.GD.N0232.N0720.N1328.d014757 _ _).comp measurable_fst) (B := 1) zero_le_one
    (fun x : _root_.GD.N0232.N0720.N1436.d013217 ↦ by
      rw [abs_of_nonneg (_root_.GD.N0232.N0720.N1328.d014758 ha hb x.1).1]
      exact (_root_.GD.N0232.N0720.N1328.d014758 ha hb x.1).2)
  rw [hp, _root_.GD.N0232.N0720.N1328.d014766 hm hn he] at hroot
  have hgd := _root_.GD.N0232.N0720.N1433.d014032 m n hm hn mu sigma tau hs ht
  change _root_.GD.N0232.N0720.N1433.d014028 m n mu sigma tau =
    _root_.GD.N0107.d009045 m n sigma tau * _root_.GD.N0232.N0720.N1091.d012790
      (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) (_root_.GD.N0107.d009046 m n sigma tau) at hgd
  rw [hp, _root_.GD.N0232.N0720.N1328.d014767 ha hb he] at hgd
  unfold _root_.GD.N0232.N0720.N1433.d014028 at hgd
  change _root_.GD.N0141.d006684 _ (fun x ↦ _root_.GD.N0232.N0720.N1425.d014719 m n
    (fun x ↦ _root_.GD.N0232.N0720.N1328.d014755 (_root_.GD.N0232.N0720.N1436.d013207 m) (_root_.GD.N0232.N0720.N1436.d013208 n) x.1) x - mu) - _ = _
  rw [hp] at hgd
  nlinarith


theorem d014769 {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {epsilon : ℝ} (he : 0 < epsilon) :
    _root_.GD.N0107.d009046 m n (Real.sqrt ((m : ℝ) * epsilon)) (Real.sqrt (n : ℝ)) =
      1 / (1 + epsilon) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold _root_.GD.N0107.d009046 _root_.GD.N0107.d009045 _root_.GD.N0107.d009043
    _root_.GD.N0107.d009044
  rw [Real.sq_sqrt (Nat.cast_nonneg n), Real.sq_sqrt (by positivity : 0 ≤ (m : ℝ) * epsilon)]
  field_simp [hmR, hnR]
  ring



theorem d014770 {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hdesign : m ≠ 2 ∨ n ≠ 2) (mu : ℝ) :
    ∃ sigma tau : ℝ, 0 < sigma ∧ 0 < tau ∧
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau) (fun x ↦ _root_.GD.N0107.d012733 m n x - mu) <
        _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau) (fun x ↦ _root_.GD.N0232.N0720.N1328.d014756 m n x - mu) := by
  have ha := _root_.GD.N0232.N0720.N1436.d013211 hm
  have hb := _root_.GD.N0232.N0720.N1436.d013212 hn
  have hshape : 1 ≤ _root_.GD.N0232.N0720.N1436.d013207 m ∨ 1 ≤ _root_.GD.N0232.N0720.N1436.d013208 n := by
    rcases hdesign with h | h
    · left
      unfold _root_.GD.N0232.N0720.N1436.d013207
      have hcast : (2 : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ m - 1 by omega)
      linarith
    · right
      unfold _root_.GD.N0232.N0720.N1436.d013208
      have hcast : (2 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - 1 by omega)
      linarith
  obtain ⟨epsilon, he, hgap⟩ := _root_.GD.N0232.N0720.N1311.d013612 ha hb hshape
  let sigma := Real.sqrt ((m : ℝ) * epsilon)
  let tau := Real.sqrt (n : ℝ)
  have hs : 0 < sigma := Real.sqrt_pos.mpr (mul_pos (by exact_mod_cast (show 0 < m by omega)) he)
  have ht : 0 < tau := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  refine ⟨sigma, tau, hs, ht, ?_⟩
  have hp := _root_.GD.N0232.N0720.N1328.d014769 (show 0 < m by omega) (show 0 < n by omega) he
  have hid := _root_.GD.N0232.N0720.N1328.d014768 hm hn mu sigma tau hs ht he hp
  have hc := _root_.GD.N0107.d009049 (show 0 < m by omega) (show 0 < n by omega) hs ht
  exact sub_pos.mp (hid.symm ▸ mul_pos hc (sub_pos.mpr hgap))

end
end GD.N0232.N0720.N1328

#print axioms _root_.GD.N0232.N0720.N1328.d014765
#print axioms _root_.GD.N0232.N0720.N1328.d014770
