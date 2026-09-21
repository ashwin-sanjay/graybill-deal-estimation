import GD.Module0521
import GD.Module0390










set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace GD.N0106.N0428.N0766.N1692

open Set Filter _root_.GD.N0232.N0720.N1254
open _root_.GD.N0232.N0720.N1104
open scoped Topology

noncomputable section

abbrev d007824 := ℝ × ℝ × ℝ × ℝ × ℝ × ℝ


def d007825 (alpha beta e h eta : ℝ) : _root_.GD.N0232.N0720.N1254.d002559 where
  minusTwoEta := _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e (-2 * h) eta
  minusEta := _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e (-h) eta
  zeroEta := _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e 0 eta
  plusEta := _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e h eta
  plusTwoEta := _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e (2 * h) eta
  minusTwoEtaLevel := _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e (-h) (2 * eta)
  zeroTwoEtaLevel := _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e 0 (2 * eta)
  plusTwoEtaLevel := _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e h (2 * eta)

def d007826 (h eta : ℝ) (g : _root_.GD.N0232.N0720.N1254.d002559) : _root_.GD.N0106.N0428.N0766.N1692.d007824 :=
  (_root_.GD.N0232.N0720.N1254.d002560 g, _root_.GD.N0232.N0720.N1254.d002561 h g, _root_.GD.N0232.N0720.N1254.d002562 h g,
    _root_.GD.N0232.N0720.N1254.d002563 h g, _root_.GD.N0232.N0720.N1254.d002564 eta g, _root_.GD.N0232.N0720.N1254.d002565 h eta g)

def d007827 (alpha beta : ℝ) (x : ℝ × ℝ × ℝ) : _root_.GD.N0106.N0428.N0766.N1692.d007824 :=
  (_root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta x.1 x.2.1 x.2.2, _root_.GD.N0106.N0428.N0766.N1692.d007818 alpha beta x)


def d007828 (alpha beta e : ℝ) : _root_.GD.N0106.N0428.N0766.N1692.d007824 :=
  (_root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e 0 0, _root_.GD.N0106.N0428.N0766.N1692.d007821 alpha beta (e, (0, 0)))

theorem d007829 {alpha beta e : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (he : e ∈ Icc (0 : ℝ) 1) :
    _root_.GD.N0106.N0428.N0766.N1692.d007827 alpha beta (e, (0, 0)) = _root_.GD.N0106.N0428.N0766.N1692.d007828 alpha beta e := by
  unfold _root_.GD.N0106.N0428.N0766.N1692.d007827 _root_.GD.N0106.N0428.N0766.N1692.d007828
  rw [_root_.GD.N0106.N0428.N0766.N1692.d007822 ha hb (_root_.GD.N0106.N0428.N0766.N1692.d007810 ha hb he)]



theorem d007830 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta > 0, ∀ e s t : ℝ,
      (e, (s, t)) ∈ _root_.GD.N0106.N0428.N0766.N1692.d007808 alpha beta → |s| < delta → |t| < delta →
      dist (_root_.GD.N0106.N0428.N0766.N1692.d007827 alpha beta (e, (s, t)))
        (_root_.GD.N0106.N0428.N0766.N1692.d007827 alpha beta (e, (0, 0))) < epsilon := by
  have hc : ContinuousOn (_root_.GD.N0106.N0428.N0766.N1692.d007827 alpha beta) (_root_.GD.N0106.N0428.N0766.N1692.d007808 alpha beta) :=
    (_root_.GD.N0106.N0428.N0766.N1692.d007817 ha hb).prodMk (_root_.GD.N0106.N0428.N0766.N1692.d007820 ha hb)
  have hu := (_root_.GD.N0106.N0428.N0766.N1692.d007809 alpha beta).uniformContinuousOn_of_continuous hc
  obtain ⟨delta, hd, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu epsilon hepsilon
  refine ⟨delta, hd, ?_⟩
  intro e s t hx hs ht
  apply hmod (e, (s, t)) hx (e, (0, 0)) (_root_.GD.N0106.N0428.N0766.N1692.d007810 ha hb hx.1)
  simpa only [Prod.dist_eq, Real.dist_eq, sub_self, sub_zero, abs_zero, max_lt_iff]
    using And.intro hd (And.intro hs ht)



theorem d007831 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta > 0, ∀ h eta : ℝ, 0 < h → 0 < eta →
      2 * h < delta → 2 * eta < delta → ∀ e ∈ Icc (0 : ℝ) 1,
      dist (_root_.GD.N0106.N0428.N0766.N1692.d007826 h eta (_root_.GD.N0106.N0428.N0766.N1692.d007825 alpha beta e h eta))
        (_root_.GD.N0106.N0428.N0766.N1692.d007828 alpha beta e) < epsilon := by
  obtain ⟨d0, hd0, hcontrol⟩ := _root_.GD.N0106.N0428.N0766.N1692.d007830 ha hb hepsilon
  let delta := min d0 (min (_root_.GD.N0106.N0428.N0766.N1692.d007802 alpha beta) (_root_.GD.N0232.N0720.N1254.d002512 alpha beta / 4))
  have hdelta : 0 < delta := lt_min hd0
    (lt_min (_root_.GD.N0106.N0428.N0766.N1692.d007803 ha hb) (div_pos (_root_.GD.N0232.N0720.N1254.d002523 ha hb) (by norm_num)))
  refine ⟨delta, hdelta, ?_⟩
  intro h eta hh heta hhd hetad e he
  have hR : 2 * h ≤ _root_.GD.N0106.N0428.N0766.N1692.d007802 alpha beta :=
    hhd.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hT : 2 * eta ≤ _root_.GD.N0232.N0720.N1254.d002512 alpha beta / 4 :=
    hetad.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hhsmall : 2 * h < d0 := hhd.trans_le (min_le_left _ _)
  have hetasmall : 2 * eta < d0 := hetad.trans_le (min_le_left _ _)
  let c := _root_.GD.N0232.N0720.N1254.d002512 alpha beta
  let d := _root_.GD.N0232.N0720.N1254.d002516 alpha beta e
  let k := _root_.GD.N0232.N0720.N1254.d002517 e
  let a := _root_.GD.N0232.N0720.N1254.d002515 alpha beta e
  let r := _root_.GD.N0232.N0720.N1254.d002513 alpha beta
  let f := _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e
  let fs := _root_.GD.N0106.N0428.N0766.d007749 c d k a r
  let fss := _root_.GD.N0106.N0428.N0766.d007750 c d k a r
  let fsss := _root_.GD.N0106.N0428.N0766.d007751 c d k a r
  let ft := _root_.GD.N0106.N0428.N0766.d007752 c d k a r
  let fst := _root_.GD.N0106.N0428.N0766.d007753 c d k a r
  have hbox (s t : ℝ) (hs : |s| ≤ 2 * h) (ht : 0 ≤ t) (ht' : t ≤ 2 * eta) :
      (e, (s, t)) ∈ _root_.GD.N0106.N0428.N0766.N1692.d007808 alpha beta :=
    ⟨he, ⟨abs_le.mp (hs.trans hR), ⟨ht, ht'.trans hT⟩⟩⟩
  have hn (s t : ℝ) (hs : |s| ≤ 2 * h) (ht : 0 ≤ t) (ht' : t ≤ 2 * eta) :
      _root_.GD.N0106.N0428.N0766.d007747 c d k s t ≠ 0 := _root_.GD.N0106.N0428.N0766.N1692.d007812 ha hb (hbox s t hs ht ht')
  have hnear (s t : ℝ) (hs : |s| ≤ 2 * h) (ht : 0 ≤ t) (ht' : t ≤ 2 * eta) :
      |f s t - f 0 0| < epsilon ∧ |fs s t - fs 0 0| < epsilon ∧
      |fss s t - fss 0 0| < epsilon ∧ |fsss s t - fsss 0 0| < epsilon ∧
      |ft s t - ft 0 0| < epsilon ∧ |fst s t - fst 0 0| < epsilon := by
    have hp := hcontrol e s t (hbox s t hs ht ht') (hs.trans_lt hhsmall)
      (by simpa only [abs_of_nonneg ht] using ht'.trans_lt hetasmall)
    simpa only [_root_.GD.N0106.N0428.N0766.N1692.d007827, _root_.GD.N0106.N0428.N0766.N1692.d007818, Prod.dist_eq, Real.dist_eq, max_lt_iff]
      using hp
  have hEtaLe : eta ≤ 2 * eta := by linarith
  have hAbs (s : ℝ) (hs : s ∈ Icc (-2 * h) (2 * h)) : |s| ≤ 2 * h :=
    abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  have hf : ∀ s ∈ Icc (-2 * h) (2 * h),
      HasDerivAt (fun u => f u eta) (fs s eta) s := by
    intro s hs
    exact _root_.GD.N0106.N0428.N0766.d007758 c d k a r s eta (hn s eta (hAbs s hs) heta.le hEtaLe)
  have hfs : ∀ s ∈ Icc (-2 * h) (2 * h),
      HasDerivAt (fun u => fs u eta) (fss s eta) s := by
    intro s hs
    exact _root_.GD.N0106.N0428.N0766.d007760 c d k a r s eta (hn s eta (hAbs s hs) heta.le hEtaLe)
  have hfss : ∀ s ∈ Icc (-2 * h) (2 * h),
      HasDerivAt (fun u => fss u eta) (fsss s eta) s := by
    intro s hs
    exact _root_.GD.N0106.N0428.N0766.d007761 c d k a r s eta (hn s eta (hAbs s hs) heta.le hEtaLe)
  have hsub : Icc (-h) h ⊆ Icc (-2 * h) (2 * h) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  obtain ⟨s10, hs10, h10⟩ := _root_.GD.N0232.N0720.N1104.d005993 hh (fun s hs => hf s (hsub hs))
  obtain ⟨s20, hs20, h20⟩ := _root_.GD.N0232.N0720.N1104.d005994 hh
    (fun s hs => hf s (hsub hs)) (fun s hs => hfs s (hsub hs))
  obtain ⟨s30, hs30, h30⟩ := _root_.GD.N0232.N0720.N1104.d005995 hh hf hfs hfss
  have hzero : |(0 : ℝ)| ≤ 2 * h := by rw [abs_zero]; linarith
  have hft : ∀ t ∈ Icc eta (eta + eta), HasDerivAt (f 0) (ft 0 t) t := by
    intro t ht
    exact _root_.GD.N0106.N0428.N0766.d007759 c d k a r 0 t
      (hn 0 t hzero (by linarith [ht.1]) (by linarith [ht.2]))
  obtain ⟨t01, ht01, h01mul⟩ := _root_.GD.N0232.N0720.N1104.d005990 heta hft
  have h01 : (f 0 (2 * eta) - f 0 eta) / eta = ft 0 t01 := by
    have heq : f 0 (2 * eta) - f 0 eta = eta * ft 0 t01 := by
      simpa only [_root_.GD.N0232.N0720.N1104.d005988, two_mul] using h01mul
    rw [heq]
    field_simp
  obtain ⟨s11, hs11, t11, ht11, h11⟩ := _root_.GD.N0232.N0720.N1104.d005996 (f := f) (fs := fs)
    (fst := fst) hh heta (by
      intro s hs t ht
      exact _root_.GD.N0106.N0428.N0766.d007758 c d k a r s t
        (hn s t (hAbs s (hsub hs)) (by linarith [ht.1]) ht.2)) (by
      intro s hs t ht
      exact _root_.GD.N0106.N0428.N0766.d007763 c d k a r s t
        (hn s t (hAbs s (hsub hs)) (by linarith [ht.1]) ht.2))
  rw [← _root_.GD.N0106.N0428.N0766.N1692.d007829 ha hb he]
  change dist (_root_.GD.N0106.N0428.N0766.N1692.d007826 h eta (_root_.GD.N0106.N0428.N0766.N1692.d007825 alpha beta e h eta))
    (f 0 0, fs 0 0, fss 0 0, fsss 0 0, ft 0 0, fst 0 0) < epsilon
  simp only [_root_.GD.N0106.N0428.N0766.N1692.d007826, Prod.dist_eq, Real.dist_eq, max_lt_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hnear 0 eta hzero heta.le hEtaLe).1
  · change |(f h eta - f (-h) eta) / (2 * h) - fs 0 0| < epsilon
    rw [h10]
    exact (hnear s10 eta (hAbs s10 (hsub ⟨hs10.1.le, hs10.2.le⟩))
      heta.le hEtaLe).2.1
  · change |(f h eta - 2 * f 0 eta + f (-h) eta) / h ^ 2 - fss 0 0| < epsilon
    rw [h20]
    exact (hnear s20 eta (hAbs s20 (hsub ⟨hs20.1.le, hs20.2.le⟩))
      heta.le hEtaLe).2.2.1
  · change |(f (2 * h) eta - 2 * f h eta + 2 * f (-h) eta - f (-2 * h) eta) /
        (2 * h ^ 3) - fsss 0 0| < epsilon
    rw [h30]
    exact (hnear s30 eta (hAbs s30 ⟨hs30.1.le, hs30.2.le⟩) heta.le hEtaLe).2.2.2.1
  · change |(f 0 (2 * eta) - f 0 eta) / eta - ft 0 0| < epsilon
    rw [h01]
    exact (hnear 0 t01 hzero (by linarith [ht01.1])
      (by linarith [ht01.2])).2.2.2.2.1
  · change |((f h (2 * eta) - f (-h) (2 * eta)) - (f h eta - f (-h) eta)) /
        (2 * h * eta) - fst 0 0| < epsilon
    rw [h11]
    exact (hnear s11 t11 (hAbs s11 (hsub ⟨hs11.1.le, hs11.2.le⟩))
      (by linarith [ht11.1]) ht11.2.le).2.2.2.2.2

theorem d007832 (alpha beta : ℝ) :
    Tendsto (_root_.GD.N0232.N0720.N1254.d002519 alpha beta) atTop (𝓝 0) := by
  convert tendsto_const_div_atTop_nhds_zero_nat (_root_.GD.N0232.N0720.N1254.d002518 alpha beta / 16) using 1
  funext n
  unfold _root_.GD.N0232.N0720.N1254.d002519
  ring

theorem d007833 (alpha beta : ℝ) :
    Tendsto (_root_.GD.N0232.N0720.N1254.d002520 alpha beta) atTop (𝓝 0) := by
  convert tendsto_const_div_atTop_nhds_zero_nat (_root_.GD.N0232.N0720.N1254.d002512 alpha beta / 8) using 1
  funext n
  unfold _root_.GD.N0232.N0720.N1254.d002520
  ring



theorem d007834 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) :
    ∀ epsilon > 0, ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N ≥ N0, ∀ e ∈ Icc (0 : ℝ) 1,
      dist (_root_.GD.N0106.N0428.N0766.N1692.d007826 (_root_.GD.N0232.N0720.N1254.d002519 alpha beta N) (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N)
        (_root_.GD.N0106.N0428.N0766.N1692.d007825 alpha beta e (_root_.GD.N0232.N0720.N1254.d002519 alpha beta N)
          (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N))) (_root_.GD.N0106.N0428.N0766.N1692.d007828 alpha beta e) < epsilon := by
  intro epsilon hepsilon
  obtain ⟨delta, hd, hsmall⟩ := _root_.GD.N0106.N0428.N0766.N1692.d007831 ha hb hepsilon
  have hH := (_root_.GD.N0106.N0428.N0766.N1692.d007832 alpha beta).const_mul 2
  have hE := (_root_.GD.N0106.N0428.N0766.N1692.d007833 alpha beta).const_mul 2
  obtain ⟨NH, hNH⟩ := Metric.tendsto_atTop.mp hH delta hd
  obtain ⟨NE, hNE⟩ := Metric.tendsto_atTop.mp hE delta hd
  refine ⟨max 1 (max NH NE), le_max_left _ _, ?_⟩
  intro N hN e he
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hN)
  have hh := _root_.GD.N0232.N0720.N1254.d002528 ha hb hNpos
  have heta := _root_.GD.N0232.N0720.N1254.d002529 ha hb hNpos
  apply hsmall _ _ hh heta _ _ e he
  · have hbound := hNH N ((le_max_left NH NE).trans ((le_max_right _ _).trans hN))
    have habs : |2 * _root_.GD.N0232.N0720.N1254.d002519 alpha beta N| < delta := by
      simpa only [mul_zero, Real.dist_eq, sub_zero] using hbound
    exact (le_abs_self _).trans_lt habs
  · have hbound := hNE N ((le_max_right NH NE).trans ((le_max_right _ _).trans hN))
    have habs : |2 * _root_.GD.N0232.N0720.N1254.d002520 alpha beta N| < delta := by
      simpa only [mul_zero, Real.dist_eq, sub_zero] using hbound
    exact (le_abs_self _).trans_lt habs

def d007835 (alpha beta : ℝ) (v : _root_.GD.N0106.N0428.N0766.N1692.d007824) : ℝ :=
  -(_root_.GD.N0232.N0720.N1254.d002545 alpha beta * v.1 + _root_.GD.N0232.N0720.N1254.d002546 alpha beta * v.2.1 +
    _root_.GD.N0232.N0720.N1254.d002547 alpha beta * v.2.2.1 + _root_.GD.N0232.N0720.N1254.d002548 alpha beta * v.2.2.2.1 +
    _root_.GD.N0232.N0720.N1254.d002549 alpha beta * v.2.2.2.2.1 + _root_.GD.N0232.N0720.N1254.d002550 alpha beta * v.2.2.2.2.2)

def d007836 (alpha beta : ℝ) : ℝ :=
  |_root_.GD.N0232.N0720.N1254.d002545 alpha beta| + |_root_.GD.N0232.N0720.N1254.d002546 alpha beta| + |_root_.GD.N0232.N0720.N1254.d002547 alpha beta| +
    |_root_.GD.N0232.N0720.N1254.d002548 alpha beta| + |_root_.GD.N0232.N0720.N1254.d002549 alpha beta| + |_root_.GD.N0232.N0720.N1254.d002550 alpha beta|

theorem d007837 (alpha beta : ℝ) : 0 ≤ _root_.GD.N0106.N0428.N0766.N1692.d007836 alpha beta := by
  unfold _root_.GD.N0106.N0428.N0766.N1692.d007836
  positivity

private theorem d007838 (a b c d e f : ℝ) :
    |a + b + c + d + e + f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  have h1 := abs_add_le a b
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le (a + b + c) d
  have h4 := abs_add_le (a + b + c + d) e
  have h5 := abs_add_le (a + b + c + d + e) f
  linarith

theorem d007839 (alpha beta : ℝ) {v w : _root_.GD.N0106.N0428.N0766.N1692.d007824} {epsilon : ℝ}
    (hclose : dist v w ≤ epsilon) :
    |_root_.GD.N0106.N0428.N0766.N1692.d007835 alpha beta v - _root_.GD.N0106.N0428.N0766.N1692.d007835 alpha beta w| ≤ _root_.GD.N0106.N0428.N0766.N1692.d007836 alpha beta * epsilon := by
  simp only [Prod.dist_eq, Real.dist_eq, max_le_iff] at hclose
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hclose
  have hid : _root_.GD.N0106.N0428.N0766.N1692.d007835 alpha beta v - _root_.GD.N0106.N0428.N0766.N1692.d007835 alpha beta w =
      -(_root_.GD.N0232.N0720.N1254.d002545 alpha beta * (v.1 - w.1) + _root_.GD.N0232.N0720.N1254.d002546 alpha beta * (v.2.1 - w.2.1) +
        _root_.GD.N0232.N0720.N1254.d002547 alpha beta * (v.2.2.1 - w.2.2.1) +
        _root_.GD.N0232.N0720.N1254.d002548 alpha beta * (v.2.2.2.1 - w.2.2.2.1) +
        _root_.GD.N0232.N0720.N1254.d002549 alpha beta * (v.2.2.2.2.1 - w.2.2.2.2.1) +
        _root_.GD.N0232.N0720.N1254.d002550 alpha beta * (v.2.2.2.2.2 - w.2.2.2.2.2)) := by
    unfold _root_.GD.N0106.N0428.N0766.N1692.d007835
    ring
  rw [hid, abs_neg]
  calc
    _ ≤ |_root_.GD.N0232.N0720.N1254.d002545 alpha beta * (v.1 - w.1)| +
        |_root_.GD.N0232.N0720.N1254.d002546 alpha beta * (v.2.1 - w.2.1)| +
        |_root_.GD.N0232.N0720.N1254.d002547 alpha beta * (v.2.2.1 - w.2.2.1)| +
        |_root_.GD.N0232.N0720.N1254.d002548 alpha beta * (v.2.2.2.1 - w.2.2.2.1)| +
        |_root_.GD.N0232.N0720.N1254.d002549 alpha beta * (v.2.2.2.2.1 - w.2.2.2.2.1)| +
        |_root_.GD.N0232.N0720.N1254.d002550 alpha beta * (v.2.2.2.2.2 - w.2.2.2.2.2)| := _root_.GD.N0106.N0428.N0766.N1692.d007838 _ _ _ _ _ _
    _ ≤ |_root_.GD.N0232.N0720.N1254.d002545 alpha beta| * epsilon + |_root_.GD.N0232.N0720.N1254.d002546 alpha beta| * epsilon +
        |_root_.GD.N0232.N0720.N1254.d002547 alpha beta| * epsilon + |_root_.GD.N0232.N0720.N1254.d002548 alpha beta| * epsilon +
        |_root_.GD.N0232.N0720.N1254.d002549 alpha beta| * epsilon + |_root_.GD.N0232.N0720.N1254.d002550 alpha beta| * epsilon := by
      simp only [abs_mul]
      gcongr
    _ = _root_.GD.N0106.N0428.N0766.N1692.d007836 alpha beta * epsilon := by unfold _root_.GD.N0106.N0428.N0766.N1692.d007836; ring

theorem d007840 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (e : ℝ) :
    _root_.GD.N0106.N0428.N0766.N1692.d007835 alpha beta (_root_.GD.N0106.N0428.N0766.N1692.d007828 alpha beta e) =
      -(_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta) := by
  have hid := _root_.GD.N0106.N0428.N0766.N1692.d007774 ha hb e
  exact congrArg Neg.neg hid



def d007841 (alpha beta : ℝ) (N : ℕ) (e : ℝ) : ℝ :=
  _root_.GD.N0232.N0720.N1254.d002566 alpha beta (_root_.GD.N0232.N0720.N1254.d002519 alpha beta N) (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N)
    (_root_.GD.N0106.N0428.N0766.N1692.d007825 alpha beta e (_root_.GD.N0232.N0720.N1254.d002519 alpha beta N) (_root_.GD.N0232.N0720.N1254.d002520 alpha beta N))

theorem d007842 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) :
    ∀ epsilon > 0, ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N ≥ N0, ∀ e ∈ Icc (0 : ℝ) 1,
      |_root_.GD.N0106.N0428.N0766.N1692.d007841 alpha beta N e +
        (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta)| < epsilon := by
  intro epsilon hepsilon
  let C := _root_.GD.N0106.N0428.N0766.N1692.d007836 alpha beta
  have hC : 0 ≤ C := _root_.GD.N0106.N0428.N0766.N1692.d007837 alpha beta
  have hden : 0 < C + 1 := by linarith
  let tol := epsilon / (C + 1)
  have htol : 0 < tol := div_pos hepsilon hden
  obtain ⟨N0, hN0, hclose⟩ := _root_.GD.N0106.N0428.N0766.N1692.d007834 ha hb tol htol
  refine ⟨N0, hN0, ?_⟩
  intro N hN e he
  have hbound := _root_.GD.N0106.N0428.N0766.N1692.d007839 alpha beta (hclose N hN e he).le
  rw [_root_.GD.N0106.N0428.N0766.N1692.d007840 ha hb e, sub_neg_eq_add] at hbound
  change |_root_.GD.N0106.N0428.N0766.N1692.d007841 alpha beta N e +
      (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta)| ≤ C * tol at hbound
  apply hbound.trans_lt
  have heq : tol * (C + 1) = epsilon := div_mul_cancel₀ epsilon hden.ne'
  nlinarith



theorem d007843 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ e ∈ Icc (0 : ℝ) 1,
      _root_.GD.N0106.N0428.N0766.N1692.d007841 alpha beta N e ≤
        -3 * (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta) / 4 := by
  let J := (_root_.GD.N0232.N0720.N1254.d002512 alpha beta) ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta)
  have hJ : 0 < J := Real.rpow_pos_of_pos (_root_.GD.N0232.N0720.N1254.d002523 ha hb) _
  obtain ⟨N, hN, hclose⟩ := _root_.GD.N0106.N0428.N0766.N1692.d007842 ha hb (J / 4) (by positivity)
  refine ⟨N, hN, ?_⟩
  intro e he
  have herr := hclose N le_rfl e he
  have hupp := le_abs_self (_root_.GD.N0106.N0428.N0766.N1692.d007841 alpha beta N e + J)
  change _root_.GD.N0106.N0428.N0766.N1692.d007841 alpha beta N e ≤ -3 * J / 4
  linarith

end
end GD.N0106.N0428.N0766.N1692

#print axioms _root_.GD.N0106.N0428.N0766.N1692.d007830
#print axioms _root_.GD.N0106.N0428.N0766.N1692.d007834
#print axioms _root_.GD.N0106.N0428.N0766.N1692.d007842
#print axioms _root_.GD.N0106.N0428.N0766.N1692.d007843
