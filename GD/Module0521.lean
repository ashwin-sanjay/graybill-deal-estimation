import GD.Module0518










set_option autoImplicit false
set_option warningAsError true

namespace GD.N0106.N0428.N0766.N1692

open Set _root_.GD.N0232.N0720.N1254

noncomputable section


def d007802 (alpha beta : ℝ) : ℝ :=
  min alpha beta / (4 * _root_.GD.N0232.N0720.N1254.d002510 alpha beta)

theorem d007803 {alpha beta : ℝ} (ha : 0 < alpha) (hb : 0 < beta) :
    0 < _root_.GD.N0106.N0428.N0766.N1692.d007802 alpha beta := by
  unfold _root_.GD.N0106.N0428.N0766.N1692.d007802
  exact div_pos (lt_min ha hb) (mul_pos (by norm_num) (_root_.GD.N0232.N0720.N1254.d002522 ha hb))


theorem d007804 {alpha beta e : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (he : e ∈ Icc (0 : ℝ) 1) :
    |_root_.GD.N0232.N0720.N1254.d002516 alpha beta e| ≤ max alpha beta := by
  have hnu : 0 ≤ alpha + beta := by linarith
  have hlow : -alpha ≤ _root_.GD.N0232.N0720.N1254.d002516 alpha beta e := by
    have hp := mul_nonneg hnu (sub_nonneg.mpr he.2)
    unfold _root_.GD.N0232.N0720.N1254.d002516 _root_.GD.N0232.N0720.N1254.d002510
    nlinarith
  have hupp : _root_.GD.N0232.N0720.N1254.d002516 alpha beta e ≤ beta := by
    have hp := mul_nonneg hnu he.1
    unfold _root_.GD.N0232.N0720.N1254.d002516 _root_.GD.N0232.N0720.N1254.d002510
    nlinarith
  rw [abs_le]
  exact ⟨(neg_le_neg (le_max_left alpha beta)).trans hlow,
    hupp.trans (le_max_right alpha beta)⟩

theorem d007805 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) :
    max alpha beta * _root_.GD.N0106.N0428.N0766.N1692.d007802 alpha beta = _root_.GD.N0232.N0720.N1254.d002512 alpha beta / 4 := by
  have hnu : _root_.GD.N0232.N0720.N1254.d002510 alpha beta ≠ 0 := (_root_.GD.N0232.N0720.N1254.d002522 ha hb).ne'
  unfold _root_.GD.N0106.N0428.N0766.N1692.d007802 _root_.GD.N0232.N0720.N1254.d002512
  rw [← mul_div_assoc, max_mul_min]
  field_simp

theorem d007806 {alpha beta e s : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (he : e ∈ Icc (0 : ℝ) 1)
    (hs : |s| ≤ _root_.GD.N0106.N0428.N0766.N1692.d007802 alpha beta) :
    |_root_.GD.N0232.N0720.N1254.d002516 alpha beta e * s| ≤ _root_.GD.N0232.N0720.N1254.d002512 alpha beta / 4 := by
  calc
    |_root_.GD.N0232.N0720.N1254.d002516 alpha beta e * s| = |_root_.GD.N0232.N0720.N1254.d002516 alpha beta e| * |s| := abs_mul _ _
    _ ≤ max alpha beta * _root_.GD.N0106.N0428.N0766.N1692.d007802 alpha beta :=
      mul_le_mul (_root_.GD.N0106.N0428.N0766.N1692.d007804 ha hb he) hs (abs_nonneg s)
        (ha.le.trans (le_max_left alpha beta))
    _ = _root_.GD.N0232.N0720.N1254.d002512 alpha beta / 4 := _root_.GD.N0106.N0428.N0766.N1692.d007805 ha hb



theorem d007807 {alpha beta e s t : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (he : e ∈ Icc (0 : ℝ) 1)
    (hs : |s| ≤ _root_.GD.N0106.N0428.N0766.N1692.d007802 alpha beta) (ht : 0 ≤ t) :
    3 * _root_.GD.N0232.N0720.N1254.d002512 alpha beta / 4 ≤ _root_.GD.N0232.N0720.N1254.d002521 alpha beta e s t := by
  have hds := _root_.GD.N0106.N0428.N0766.N1692.d007806 ha hb he hs
  have hlow := neg_abs_le (_root_.GD.N0232.N0720.N1254.d002516 alpha beta e * s)
  have hht := mul_nonneg (_root_.GD.N0232.N0720.N1254.d002532 he) ht
  unfold _root_.GD.N0232.N0720.N1254.d002521
  linarith



def d007808 (alpha beta : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Icc 0 1 ×ˢ (Icc (-_root_.GD.N0106.N0428.N0766.N1692.d007802 alpha beta) (_root_.GD.N0106.N0428.N0766.N1692.d007802 alpha beta) ×ˢ
    Icc 0 (_root_.GD.N0232.N0720.N1254.d002512 alpha beta / 4))

theorem d007809 (alpha beta : ℝ) : IsCompact (_root_.GD.N0106.N0428.N0766.N1692.d007808 alpha beta) :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

theorem d007810 {alpha beta e : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (he : e ∈ Icc (0 : ℝ) 1) :
    (e, (0, 0)) ∈ _root_.GD.N0106.N0428.N0766.N1692.d007808 alpha beta := by
  have hR := (_root_.GD.N0106.N0428.N0766.N1692.d007803 ha hb).le
  have hc := (_root_.GD.N0232.N0720.N1254.d002523 ha hb).le
  exact ⟨he, ⟨⟨by linarith, hR⟩, ⟨le_rfl, by positivity⟩⟩⟩

theorem d007811 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) {x : ℝ × ℝ × ℝ}
    (hx : x ∈ _root_.GD.N0106.N0428.N0766.N1692.d007808 alpha beta) :
    0 < _root_.GD.N0232.N0720.N1254.d002521 alpha beta x.1 x.2.1 x.2.2 := by
  have hreserve := _root_.GD.N0106.N0428.N0766.N1692.d007807 ha hb hx.1
    (abs_le.mpr hx.2.1) hx.2.2.1
  exact (show 0 < 3 * _root_.GD.N0232.N0720.N1254.d002512 alpha beta / 4 by
    have hc := _root_.GD.N0232.N0720.N1254.d002523 ha hb
    positivity).trans_le hreserve

theorem d007812 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) {x : ℝ × ℝ × ℝ}
    (hx : x ∈ _root_.GD.N0106.N0428.N0766.N1692.d007808 alpha beta) :
    _root_.GD.N0106.N0428.N0766.d007747 (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) (_root_.GD.N0232.N0720.N1254.d002516 alpha beta x.1) (_root_.GD.N0232.N0720.N1254.d002517 x.1)
      x.2.1 x.2.2 ≠ 0 :=
  (_root_.GD.N0106.N0428.N0766.N1692.d007811 ha hb hx).ne'

theorem d007813 (alpha beta : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun x : ℝ × ℝ × ℝ =>
      _root_.GD.N0232.N0720.N1254.d002521 alpha beta x.1 x.2.1 x.2.2) := by
  unfold _root_.GD.N0232.N0720.N1254.d002521 _root_.GD.N0232.N0720.N1254.d002516 _root_.GD.N0232.N0720.N1254.d002517
  fun_prop



theorem d007814 {alpha beta : ℝ} {n : WithTop ℕ∞}
    (ha : 0 < alpha) (hb : 0 < beta) {x : ℝ × ℝ × ℝ}
    (hx : x ∈ _root_.GD.N0106.N0428.N0766.N1692.d007808 alpha beta) (q : ℝ) :
    ContDiffAt ℝ n (fun y : ℝ × ℝ × ℝ =>
      (_root_.GD.N0232.N0720.N1254.d002521 alpha beta y.1 y.2.1 y.2.2) ^ q) x :=
  (_root_.GD.N0106.N0428.N0766.N1692.d007813 alpha beta).contDiffAt.rpow_const_of_ne
    (_root_.GD.N0106.N0428.N0766.N1692.d007811 ha hb hx).ne'

theorem d007815 {alpha beta : ℝ} {n : WithTop ℕ∞}
    (ha : 0 < alpha) (hb : 0 < beta) {x : ℝ × ℝ × ℝ}
    (hx : x ∈ _root_.GD.N0106.N0428.N0766.N1692.d007808 alpha beta) :
    ContDiffAt ℝ n (fun y : ℝ × ℝ × ℝ => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta y.1 y.2.1 y.2.2) x := by
  have hnum : ContDiff ℝ n (fun y : ℝ × ℝ × ℝ => _root_.GD.N0232.N0720.N1254.d002515 alpha beta y.1 + y.2.1) := by
    unfold _root_.GD.N0232.N0720.N1254.d002515
    fun_prop
  exact hnum.contDiffAt.mul (_root_.GD.N0106.N0428.N0766.N1692.d007814 ha hb hx (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta))

theorem d007816 {alpha beta : ℝ} {n : WithTop ℕ∞}
    (ha : 0 < alpha) (hb : 0 < beta) :
    ContDiffOn ℝ n (fun x : ℝ × ℝ × ℝ => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta x.1 x.2.1 x.2.2)
      (_root_.GD.N0106.N0428.N0766.N1692.d007808 alpha beta) :=
  fun _ hx => (_root_.GD.N0106.N0428.N0766.N1692.d007815 ha hb hx).contDiffWithinAt

theorem d007817 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) :
    ContinuousOn (fun x : ℝ × ℝ × ℝ => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta x.1 x.2.1 x.2.2)
      (_root_.GD.N0106.N0428.N0766.N1692.d007808 alpha beta) :=
  (_root_.GD.N0106.N0428.N0766.N1692.d007816 (n := 0) ha hb).continuousOn


def d007818 (alpha beta : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ :=
  let c := _root_.GD.N0232.N0720.N1254.d002512 alpha beta
  let d := _root_.GD.N0232.N0720.N1254.d002516 alpha beta x.1
  let h := _root_.GD.N0232.N0720.N1254.d002517 x.1
  let a := _root_.GD.N0232.N0720.N1254.d002515 alpha beta x.1
  let r := _root_.GD.N0232.N0720.N1254.d002513 alpha beta
  (_root_.GD.N0106.N0428.N0766.d007749 c d h a r x.2.1 x.2.2,
    _root_.GD.N0106.N0428.N0766.d007750 c d h a r x.2.1 x.2.2,
    _root_.GD.N0106.N0428.N0766.d007751 c d h a r x.2.1 x.2.2,
    _root_.GD.N0106.N0428.N0766.d007752 c d h a r x.2.1 x.2.2,
    _root_.GD.N0106.N0428.N0766.d007753 c d h a r x.2.1 x.2.2)



theorem d007819 {alpha beta : ℝ} {n : WithTop ℕ∞}
    (ha : 0 < alpha) (hb : 0 < beta) {x : ℝ × ℝ × ℝ}
    (hx : x ∈ _root_.GD.N0106.N0428.N0766.N1692.d007808 alpha beta) : ContDiffAt ℝ n (_root_.GD.N0106.N0428.N0766.N1692.d007818 alpha beta) x := by
  let r := _root_.GD.N0232.N0720.N1254.d002513 alpha beta
  have hD : ContDiffAt ℝ n (fun y : ℝ × ℝ × ℝ => _root_.GD.N0232.N0720.N1254.d002516 alpha beta y.1) x := by
    unfold _root_.GD.N0232.N0720.N1254.d002516
    fun_prop
  have hH : ContDiffAt ℝ n (fun y : ℝ × ℝ × ℝ => _root_.GD.N0232.N0720.N1254.d002517 y.1) x := by
    unfold _root_.GD.N0232.N0720.N1254.d002517
    fun_prop
  have hnum : ContDiffAt ℝ n (fun y : ℝ × ℝ × ℝ => _root_.GD.N0232.N0720.N1254.d002515 alpha beta y.1 + y.2.1) x := by
    unfold _root_.GD.N0232.N0720.N1254.d002515
    fun_prop
  have hp (q : ℝ) := _root_.GD.N0106.N0428.N0766.N1692.d007814 (n := n) ha hb hx q
  have hS := (hp (-r)).sub
    ((((contDiffAt_const (c := r)).mul hD).mul hnum).mul (hp (-r - 1)))
  have hSS := (((contDiffAt_const (c := -2 * r)).mul hD).mul (hp (-r - 1))).add
    ((((contDiffAt_const (c := r * (r + 1))).mul (hD.pow 2)).mul hnum).mul (hp (-r - 2)))
  have hSSS := (((contDiffAt_const (c := 3 * r * (r + 1))).mul (hD.pow 2)).mul
      (hp (-r - 2))).sub
    ((((contDiffAt_const (c := r * (r + 1) * (r + 2))).mul (hD.pow 3)).mul hnum).mul
      (hp (-r - 3)))
  have hT := ((((contDiffAt_const (c := -r)).mul hH).mul hnum).mul (hp (-r - 1)))
  have hST := (((contDiffAt_const (c := -r)).mul hH).mul (hp (-r - 1))).add
    (((((contDiffAt_const (c := r * (r + 1))).mul hD).mul hH).mul hnum).mul (hp (-r - 2)))
  exact hS.prodMk (hSS.prodMk (hSSS.prodMk (hT.prodMk hST)))

theorem d007820 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) :
    ContinuousOn (_root_.GD.N0106.N0428.N0766.N1692.d007818 alpha beta) (_root_.GD.N0106.N0428.N0766.N1692.d007808 alpha beta) :=
  fun _ hx => (_root_.GD.N0106.N0428.N0766.N1692.d007819 (n := 0) ha hb hx).continuousAt.continuousWithinAt


def d007821 (alpha beta : ℝ) (x : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ × ℝ :=
  (deriv (fun s => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta x.1 s x.2.2) x.2.1,
    deriv (deriv (fun s => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta x.1 s x.2.2)) x.2.1,
    deriv (deriv (deriv (fun s => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta x.1 s x.2.2))) x.2.1,
    deriv (fun t => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta x.1 x.2.1 t) x.2.2,
    deriv (fun s => deriv (fun t => _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta x.1 s t) x.2.2) x.2.1)

theorem d007822 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) {x : ℝ × ℝ × ℝ}
    (hx : x ∈ _root_.GD.N0106.N0428.N0766.N1692.d007808 alpha beta) :
    _root_.GD.N0106.N0428.N0766.N1692.d007821 alpha beta x = _root_.GD.N0106.N0428.N0766.N1692.d007818 alpha beta x := by
  have hn := _root_.GD.N0106.N0428.N0766.N1692.d007812 ha hb hx
  simp only [_root_.GD.N0106.N0428.N0766.N1692.d007821, _root_.GD.N0106.N0428.N0766.N1692.d007818, _root_.GD.N0106.N0428.N0766.N1692.d007772]
  rw [_root_.GD.N0106.N0428.N0766.d007765 _ _ _ _ _ _ _ hn,
    _root_.GD.N0106.N0428.N0766.d007767 _ _ _ _ _ _ _ hn,
    _root_.GD.N0106.N0428.N0766.d007768 _ _ _ _ _ _ _ hn,
    _root_.GD.N0106.N0428.N0766.d007766 _ _ _ _ _ _ _ hn,
    _root_.GD.N0106.N0428.N0766.d007769 _ _ _ _ _ _ _ hn]


theorem d007823 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) :
    ContinuousOn (_root_.GD.N0106.N0428.N0766.N1692.d007821 alpha beta) (_root_.GD.N0106.N0428.N0766.N1692.d007808 alpha beta) :=
  (_root_.GD.N0106.N0428.N0766.N1692.d007820 ha hb).congr
    (fun _ hx => _root_.GD.N0106.N0428.N0766.N1692.d007822 ha hb hx)

end
end GD.N0106.N0428.N0766.N1692

#print axioms _root_.GD.N0106.N0428.N0766.N1692.d007807
#print axioms _root_.GD.N0106.N0428.N0766.N1692.d007816
#print axioms _root_.GD.N0106.N0428.N0766.N1692.d007819
#print axioms _root_.GD.N0106.N0428.N0766.N1692.d007823
