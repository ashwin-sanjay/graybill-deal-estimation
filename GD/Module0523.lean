import GD.Module0518







set_option autoImplicit false
set_option warningAsError true

open Set

namespace GD.N0106.N0428.N0766.N1692.N1763
noncomputable section

open _root_.GD.N0232.N0720.N1254

def d007844 : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioi 0

def d007845 : Set (ℝ × ℝ × ℝ) := Icc 0 1 ×ˢ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844

def d007846 (alpha beta : ℝ) (z : ℝ × ℝ) : ℝ :=
  z.1 ^ (beta - 1) * (1 - z.1) ^ (alpha - 1) * Real.sqrt z.2

def d007847 (alpha beta e : ℝ) (z : ℝ × ℝ) : ℝ :=
  alpha * e * (1 - z.1) + beta * (1 - e) * z.1 + z.2 * e * (1 - e) / 2

def d007848 (alpha beta : ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta x.2 * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847 alpha beta x.1 x.2 ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta)

def d007849 (alpha beta : ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta x.2 * (x.2.1 - x.1) *
    _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847 alpha beta x.1 x.2 ^ (-_root_.GD.N0232.N0720.N1254.d002513 alpha beta)


def d007850 (alpha beta : ℝ) (center : ℝ × ℝ) (x : ℝ × ℝ × ℝ) : ℝ :=
  _root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta x / _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta center

theorem d007851 (alpha beta : ℝ) (z : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta z =
      z.1 ^ (beta - 1) * (1 - z.1) ^ (alpha - 1) * z.2 ^ ((1 : ℝ) / 2) := by
  simp only [_root_.GD.N0106.N0428.N0766.N1692.N1763.d007846, Real.sqrt_eq_rpow]

theorem d007852 (alpha beta : ℝ) {z : ℝ × ℝ} (hz : z ∈ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844) :
    0 < _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta z := by
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos hz.1.1 _)
    (Real.rpow_pos_of_pos (sub_pos.mpr hz.1.2) _)) (Real.sqrt_pos.mpr hz.2)

theorem d007853 {alpha beta e : ℝ} {z : ℝ × ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (he : e ∈ Icc (0 : ℝ) 1)
    (hz : z ∈ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844) : 0 < _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847 alpha beta e z := by
  have hL : 0 < z.1 := hz.1.1
  have hLc : 0 < 1 - z.1 := sub_pos.mpr hz.1.2
  have hF : 0 < z.2 := hz.2
  have he0 : 0 ≤ e := he.1
  have he1 : 0 ≤ 1 - e := sub_nonneg.mpr he.2
  by_cases hezero : e = 0
  · simpa [_root_.GD.N0106.N0428.N0766.N1692.N1763.d007847, hezero] using mul_pos hb hL
  · have hep : 0 < e := lt_of_le_of_ne he0 (Ne.symm hezero)
    have hfirst : 0 < alpha * e * (1 - z.1) := mul_pos (mul_pos ha hep) hLc
    have hsecond : 0 ≤ beta * (1 - e) * z.1 := by positivity
    have hthird : 0 ≤ z.2 * e * (1 - e) / 2 := by positivity
    exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hfirst hsecond) hthird

theorem d007854 {alpha beta : ℝ} (ha : 0 < alpha) (hb : 0 < beta)
    {x : ℝ × ℝ × ℝ} (hx : x ∈ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007845) :
    0 < _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta x :=
  mul_pos (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007852 alpha beta hx.2)
    (Real.rpow_pos_of_pos (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007853 ha hb hx.1 hx.2) _)


theorem d007855 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (e : ℝ) (z : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847 alpha beta e z =
      _root_.GD.N0232.N0720.N1254.d002521 alpha beta e (z.1 - _root_.GD.N0232.N0720.N1254.d002514 alpha beta) z.2 := by
  have hsum := (_root_.GD.N0232.N0720.N1254.d002522 ha hb).ne'
  unfold _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847 _root_.GD.N0232.N0720.N1254.d002521 _root_.GD.N0232.N0720.N1254.d002512 _root_.GD.N0232.N0720.N1254.d002516 _root_.GD.N0232.N0720.N1254.d002517 _root_.GD.N0232.N0720.N1254.d002514
  unfold _root_.GD.N0232.N0720.N1254.d002510 at *
  field_simp [hsum]
  ring

theorem d007856 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (e s F : ℝ) :
    _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847 alpha beta e (_root_.GD.N0232.N0720.N1254.d002514 alpha beta + s, F) =
      _root_.GD.N0232.N0720.N1254.d002521 alpha beta e s F := by
  simpa using _root_.GD.N0106.N0428.N0766.N1692.N1763.d007855 ha hb e
    (_root_.GD.N0232.N0720.N1254.d002514 alpha beta + s, F)

theorem d007857 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (e : ℝ) (z : ℝ × ℝ) :
    _root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta (e, z) =
      _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta z * _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e (z.1 - _root_.GD.N0232.N0720.N1254.d002514 alpha beta) z.2 := by
  rw [_root_.GD.N0106.N0428.N0766.N1692.N1763.d007849, _root_.GD.N0106.N0428.N0766.N1692.N1763.d007855 ha hb]
  unfold _root_.GD.N0106.N0428.N0766.N1692.d007772 _root_.GD.N0106.N0428.N0766.d007748 _root_.GD.N0106.N0428.N0766.d007747 _root_.GD.N0232.N0720.N1254.d002521 _root_.GD.N0232.N0720.N1254.d002515
  ring

theorem d007858 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (e : ℝ) {z : ℝ × ℝ} (hz : z ∈ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844) :
    _root_.GD.N0106.N0428.N0766.N1692.N1763.d007850 alpha beta z (e, z) =
      _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e (z.1 - _root_.GD.N0232.N0720.N1254.d002514 alpha beta) z.2 := by
  unfold _root_.GD.N0106.N0428.N0766.N1692.N1763.d007850
  rw [_root_.GD.N0106.N0428.N0766.N1692.N1763.d007857 ha hb]
  exact mul_div_cancel_left₀ _ (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007852 alpha beta hz).ne'



theorem d007859 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (e weight : ℝ)
    {z : ℝ × ℝ} (hz : z ∈ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844) :
    (weight / _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta z) * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta (e, z) =
      weight * _root_.GD.N0106.N0428.N0766.N1692.d007772 alpha beta e (z.1 - _root_.GD.N0232.N0720.N1254.d002514 alpha beta) z.2 := by
  calc
    (weight / _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta z) * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta (e, z) =
        weight * _root_.GD.N0106.N0428.N0766.N1692.N1763.d007850 alpha beta z (e, z) := by
      unfold _root_.GD.N0106.N0428.N0766.N1692.N1763.d007850
      ring
    _ = _ := by rw [_root_.GD.N0106.N0428.N0766.N1692.N1763.d007858 ha hb e hz]

theorem d007860 (alpha beta : ℝ) {z : ℝ × ℝ} (hz : z ∈ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844) :
    ContinuousAt (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta) z := by
  unfold _root_.GD.N0106.N0428.N0766.N1692.N1763.d007846
  exact ((continuous_fst.continuousAt.rpow_const (Or.inl hz.1.1.ne')).mul
    ((continuous_const.sub continuous_fst).continuousAt.rpow_const
      (Or.inl (sub_pos.mpr hz.1.2).ne'))).mul continuous_snd.sqrt.continuousAt

theorem d007861 (alpha beta : ℝ) : ContinuousOn (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta) _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844 :=
  fun _ hz => (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007860 alpha beta hz).continuousWithinAt

theorem d007862 (alpha beta : ℝ) :
    Continuous (fun x : ℝ × ℝ × ℝ => _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847 alpha beta x.1 x.2) := by
  unfold _root_.GD.N0106.N0428.N0766.N1692.N1763.d007847
  fun_prop

theorem d007863 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) {x : ℝ × ℝ × ℝ}
    (hx : x ∈ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007845) : ContinuousAt (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta) x := by
  exact ((_root_.GD.N0106.N0428.N0766.N1692.N1763.d007860 alpha beta hx.2).comp continuous_snd.continuousAt).mul
    ((_root_.GD.N0106.N0428.N0766.N1692.N1763.d007862 alpha beta).continuousAt.rpow_const
      (Or.inl (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007853 ha hb hx.1 hx.2).ne'))

theorem d007864 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) {x : ℝ × ℝ × ℝ}
    (hx : x ∈ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007845) : ContinuousAt (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta) x := by
  have hc : ContinuousAt (fun y : ℝ × ℝ × ℝ => y.2.1 - y.1) x := by fun_prop
  have h := (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007863 ha hb hx).mul hc
  convert h using 1
  funext y
  simp only [Pi.mul_apply]
  unfold _root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848
  ring

theorem d007865 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) :
    ContinuousOn (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta) _root_.GD.N0106.N0428.N0766.N1692.N1763.d007845 :=
  fun _ hx => (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007863 ha hb hx).continuousWithinAt

theorem d007866 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) :
    ContinuousOn (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta) _root_.GD.N0106.N0428.N0766.N1692.N1763.d007845 :=
  fun _ hx => (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007864 ha hb hx).continuousWithinAt

theorem d007867 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (center : ℝ × ℝ) :
    ContinuousOn (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007850 alpha beta center) _root_.GD.N0106.N0428.N0766.N1692.N1763.d007845 :=
  (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007866 ha hb).div_const (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007846 alpha beta center)

theorem d007868 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) {K : Set (ℝ × ℝ × ℝ)}
    (hK : IsCompact K) (hsub : K ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007845) :
    UniformContinuousOn (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta) K :=
  hK.uniformContinuousOn_of_continuous ((_root_.GD.N0106.N0428.N0766.N1692.N1763.d007865 ha hb).mono hsub)

theorem d007869 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) {K : Set (ℝ × ℝ × ℝ)}
    (hK : IsCompact K) (hsub : K ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007845) :
    UniformContinuousOn (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta) K :=
  hK.uniformContinuousOn_of_continuous ((_root_.GD.N0106.N0428.N0766.N1692.N1763.d007866 ha hb).mono hsub)

theorem d007870 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (center : ℝ × ℝ)
    {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K) (hsub : K ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007845) :
    UniformContinuousOn (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007850 alpha beta center) K :=
  hK.uniformContinuousOn_of_continuous ((_root_.GD.N0106.N0428.N0766.N1692.N1763.d007867 ha hb center).mono hsub)



theorem d007871 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) {K : Set (ℝ × ℝ × ℝ)}
    (hK : IsCompact K) (hsub : K ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007845) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ K,
      0 < _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta x ∧ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta x ≤ B ∧
        |_root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta x| ≤ B := by
  obtain ⟨E, hE⟩ := hK.exists_bound_of_continuousOn ((_root_.GD.N0106.N0428.N0766.N1692.N1763.d007865 ha hb).mono hsub)
  obtain ⟨T, hT⟩ := hK.exists_bound_of_continuousOn ((_root_.GD.N0106.N0428.N0766.N1692.N1763.d007866 ha hb).mono hsub)
  refine ⟨|E| + |T| + 1, by positivity, ?_⟩
  intro x hx
  have he : |_root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta x| ≤ E := by simpa only [Real.norm_eq_abs] using hE x hx
  have ht : |_root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta x| ≤ T := by simpa only [Real.norm_eq_abs] using hT x hx
  refine ⟨_root_.GD.N0106.N0428.N0766.N1692.N1763.d007854 ha hb (hsub hx), ?_, ?_⟩
  · have hh := le_abs_self (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta x)
    have he' := le_abs_self E
    have ht' := abs_nonneg T
    linarith
  · have he' := abs_nonneg E
    have ht' := le_abs_self T
    linarith

def d007872 (Llo Lhi Flo Fhi : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Icc 0 1 ×ˢ (Icc Llo Lhi ×ˢ Icc Flo Fhi)

theorem d007873 (Llo Lhi Flo Fhi : ℝ) :
    IsCompact (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007872 Llo Lhi Flo Fhi) :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

theorem d007874 {Llo Lhi Flo Fhi : ℝ}
    (hLlo : 0 < Llo) (hLhi : Lhi < 1) (hFlo : 0 < Flo) :
    _root_.GD.N0106.N0428.N0766.N1692.N1763.d007872 Llo Lhi Flo Fhi ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007845 := by
  intro x hx
  exact ⟨hx.1, ⟨⟨hLlo.trans_le hx.2.1.1, hx.2.1.2.trans_lt hLhi⟩,
    hFlo.trans_le hx.2.2.1⟩⟩

theorem d007875 {alpha beta Llo Lhi Flo Fhi : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta)
    (hLlo : 0 < Llo) (hLhi : Lhi < 1) (hFlo : 0 < Flo) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007872 Llo Lhi Flo Fhi,
      0 < _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta x ∧ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007848 alpha beta x ≤ B ∧
        |_root_.GD.N0106.N0428.N0766.N1692.N1763.d007849 alpha beta x| ≤ B :=
  _root_.GD.N0106.N0428.N0766.N1692.N1763.d007871 ha hb (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007873 _ _ _ _)
    (_root_.GD.N0106.N0428.N0766.N1692.N1763.d007874 hLlo hLhi hFlo)



theorem d007876 {alpha beta : ℝ}
    (ha : 0 < alpha) (hb : 0 < beta) (center : ℝ × ℝ)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hsub : K ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007844) :
    ∀ epsilon > 0, ∃ delta > 0, ∀ e ∈ Icc (0 : ℝ) 1,
      ∀ x ∈ K, ∀ y ∈ K, dist x y < delta →
        |_root_.GD.N0106.N0428.N0766.N1692.N1763.d007850 alpha beta center (e, x) -
          _root_.GD.N0106.N0428.N0766.N1692.N1763.d007850 alpha beta center (e, y)| < epsilon := by
  have hp : Icc (0 : ℝ) 1 ×ˢ K ⊆ _root_.GD.N0106.N0428.N0766.N1692.N1763.d007845 :=
    fun _ hx => ⟨hx.1, hsub hx.2⟩
  have hu := _root_.GD.N0106.N0428.N0766.N1692.N1763.d007870 ha hb center (isCompact_Icc.prod hK) hp
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hclose⟩ := Metric.uniformContinuousOn_iff.mp hu epsilon hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro e he x hx y hy hxy
  have hpair : dist (e, x) (e, y) < delta := by simpa using hxy
  simpa only [Real.dist_eq] using hclose (e, x) ⟨he, hx⟩ (e, y) ⟨he, hy⟩ hpair

end
end GD.N0106.N0428.N0766.N1692.N1763

#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1763.d007852
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1763.d007853
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1763.d007856
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1763.d007857
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1763.d007858
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1763.d007859
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1763.d007865
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1763.d007866
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1763.d007871
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1763.d007875
#print axioms _root_.GD.N0106.N0428.N0766.N1692.N1763.d007876
