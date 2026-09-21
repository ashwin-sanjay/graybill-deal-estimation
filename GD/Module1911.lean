import GD.Module1910
import GD.Module1443
import GD.Module1049
import GD.Module0246









set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped ENNReal

namespace GD.N0162
noncomputable section

open _root_.GD.N0232.N0720
open _root_.GD.N0232.N0720.N1080 _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1257 _root_.GD.N0232.N0720.N1256
open _root_.GD.N0232.N0720.N1228
open _root_.GD.N0082.N0334
open _root_.GD.N0082.N0335
open _root_.GD.N0082.N0336
open _root_.GD.N0230.N0611


theorem d030941
    {K : ℕ} (sizes : Fin K → ℕ) (hn : ∀ l, 2 ≤ sizes l)
    (i j : Fin K) (hij : i ≠ j) (hi : sizes i = 3) (hj : sizes j = 3) :
    ENNReal.ofReal (1 + Real.pi / 4) ≤
      _root_.GD.N0232.N0719.N0962.d012188 K sizes := by
  have h := _root_.GD.N0036.d022918 sizes hn i j hij
  simpa only [hi, hj, _root_.GD.N0184.d030936]
    using h


theorem d030942
    {K : ℕ} (sizes : Fin K → ℕ) (hn : ∀ l, 2 ≤ sizes l)
    (i j : Fin K) (hij : i ≠ j) (hi : sizes i = 3) (hj : sizes j = 3)
    (d : _root_.GD.N0232.N0719.N0859.d010811 K sizes → ℝ)
    (hd : Measurable d) :
    ENNReal.ofReal (1 + Real.pi / 4) ≤
      _root_.GD.N0232.N0719.N0962.d012187 K sizes d := by
  exact (_root_.GD.N0162.d030941 sizes hn i j hij hi hj).trans
    (_root_.GD.N0230.N0611.d003520
      (_root_.GD.N0232.N0719.N0962.d012186 K sizes) hd)


theorem d030943 {t u : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0082.N0334.d008256 t u = t + (1 - 2 * t) * u ∧
      0 < _root_.GD.N0082.N0334.d008256 t u ∧
      _root_.GD.N0082.N0334.d008256 t u ^ 2 - (u - t) ^ 2 = 4 * t * (1 - t) * u * (1 - u) ∧
      0 < 4 * t * (1 - t) * u * (1 - u) := by
  refine ⟨?_, _root_.GD.N0082.N0334.d008263 ⟨ht.1.le, ht.2.le⟩ hu, ?_, ?_⟩
  · unfold _root_.GD.N0082.N0334.d008256
    ring
  · rw [_root_.GD.N0082.N0334.d008261]
    ring
  · exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) ht.1)
      (sub_pos.mpr ht.2)) hu.1) (sub_pos.mpr hu.2)

theorem d030944 {t u : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) :
    ((u - t) / _root_.GD.N0082.N0334.d008256 t u) ^ 2 < 1 := by
  have h := _root_.GD.N0162.d030943 ht hu
  rw [div_pow, div_lt_one (sq_pos_of_pos h.2.1)]
  linarith [h.2.2.1, h.2.2.2]


theorem d030945 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    _root_.GD.N0082.N0334.d008258 id t < 1 := by
  let f : ℝ → ℝ := fun u => ((u - t) / _root_.GD.N0082.N0334.d008256 t u) ^ 2
  have hfi : Integrable f (volume.restrict (Ioo (0 : ℝ) 1)) :=
    _root_.GD.N0149.N0436.d030845 id measurable_id
      (fun u hu => ⟨hu.1.le, hu.2.le⟩) ht
  have hpos : ∀ u ∈ Ioo (0 : ℝ) 1, 0 < 1 - f u := by
    intro u hu
    exact sub_pos.mpr (_root_.GD.N0162.d030944 ht hu)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] (fun u => 1 - f u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact (hpos u hu).le
  have hs : Function.support (fun u => 1 - f u) ∩ Ioo (0 : ℝ) 1 = Ioo 0 1 := by
    apply inter_eq_right.mpr
    intro u hu
    exact (hpos u hu).ne'
  have hp : 0 < ∫ u in Ioo (0 : ℝ) 1, 1 - f u := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg
      ((integrable_const (1 : ℝ)).sub hfi)).mpr
    rw [hs]
    norm_num
  rw [integral_sub (integrable_const (1 : ℝ)) hfi] at hp
  have hc : (∫ _u in Ioo (0 : ℝ) 1, (1 : ℝ)) = 1 := by simp
  rw [hc] at hp
  change (∫ u in Ioo (0 : ℝ) 1, f u) < 1
  linarith


theorem d030946 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1256.d015547 3 3 theta (_root_.GD.N0232.N0720.N1080.d014175 3 3) =
      ENNReal.ofReal (1 + _root_.GD.N0082.N0334.d008258 id (_root_.GD.N0082.N0336.d030741 theta)) := by
  rw [← _root_.GD.N0082.N0335.d030727 3 3,
    _root_.GD.N0011.d030818 _root_.GD.N0082.N0335.d030710 _root_.GD.N0082.N0335.d030713
      _root_.GD.N0082.N0335.d030711, _root_.GD.N0082.N0336.d030748]

theorem d030947 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1256.d015547 3 3 theta (_root_.GD.N0232.N0720.N1080.d014175 3 3) < 2 := by
  rw [_root_.GD.N0162.d030946]
  have h := _root_.GD.N0162.d030945 (_root_.GD.N0082.N0336.d030742 theta)
  have h' : ENNReal.ofReal (1 + _root_.GD.N0082.N0334.d008258 id (_root_.GD.N0082.N0336.d030741 theta)) < ENNReal.ofReal 2 :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by linarith)
  simpa using h'


theorem d030948 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1066.d014320 3 3 (by norm_num) (by norm_num) theta <
      ENNReal.ofReal (2 * _root_.GD.N0232.N0720.N1257.d015508 3 3 theta) := by
  rw [_root_.GD.N0082.N0336.d030750, ← _root_.GD.N0011.d030817]
  apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos (by norm_num) (_root_.GD.N0082.N0336.d030744 theta))).mpr
  nlinarith [mul_pos (_root_.GD.N0082.N0336.d030744 theta) (sub_pos.mpr (_root_.GD.N0162.d030945 (_root_.GD.N0082.N0336.d030742 theta)))]


theorem d030949
    (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hcap : ∀ theta, _root_.GD.N0232.N0720.N1228.d016744 3 3 (by norm_num) (by norm_num) theta d ≤
      ENNReal.ofReal c) :
    ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 3 3 theta d ≤ ENNReal.ofReal ((2 * c) * _root_.GD.N0232.N0720.N1257.d015508 3 3 theta) := by
  intro theta
  have hraw := (_root_.GD.N0232.N0720.N1228.d016746 3 3 (by norm_num) (by norm_num)
    theta d c hc).mp (hcap theta)
  have hb := (ENNReal.toReal_le_toReal
    (_root_.GD.N0232.N0720.N1066.d014323 3 3 (by norm_num) (by norm_num) theta)
    ENNReal.ofReal_ne_top).mpr (_root_.GD.N0162.d030948 theta).le
  rw [ENNReal.toReal_ofReal
    (mul_nonneg (by norm_num) (_root_.GD.N0232.N0720.N1257.d015509 3 3 theta))] at hb
  apply hraw.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    c * (_root_.GD.N0232.N0720.N1066.d014320 3 3 (by norm_num) (by norm_num) theta).toReal ≤
        c * (2 * _root_.GD.N0232.N0720.N1257.d015508 3 3 theta) := mul_le_mul_of_nonneg_left hb hc
    _ = (2 * c) * _root_.GD.N0232.N0720.N1257.d015508 3 3 theta := by ring


theorem d030950
    (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ)
    (hfinite : _root_.GD.N0232.N0720.N1228.d016745 3 3 (by norm_num) (by norm_num) d ≠ ⊤) :
    _root_.GD.N0232.N0720.N1256.d015548 3 3 d ≤ ENNReal.ofReal
      (2 * (_root_.GD.N0232.N0720.N1228.d016745 3 3 (by norm_num) (by norm_num) d).toReal) := by
  let c := (_root_.GD.N0232.N0720.N1228.d016745 3 3 (by norm_num) (by norm_num) d).toReal
  have hc : 0 ≤ c := ENNReal.toReal_nonneg
  have hcap : ∀ theta, _root_.GD.N0232.N0720.N1228.d016744 3 3 (by norm_num) (by norm_num) theta d ≤
      ENNReal.ofReal c := by
    intro theta
    rw [ENNReal.ofReal_toReal hfinite]
    exact le_iSup (fun eta => _root_.GD.N0232.N0720.N1228.d016744 3 3 (by norm_num) (by norm_num) eta d) theta
  apply iSup_le
  intro theta
  exact (_root_.GD.N0232.N0720.N1256.d015553 3 3 (by norm_num) (2 * c) (by positivity) theta d).mpr
    (_root_.GD.N0162.d030949 d c hc hcap theta)

theorem d030951
    (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ) (hd : Measurable d) (c : ℝ) (hc : 0 ≤ c)
    (hcap : ∀ theta, _root_.GD.N0232.N0720.N1228.d016744 3 3 (by norm_num) (by norm_num) theta d ≤
      ENNReal.ofReal c) :
    (1 + Real.pi / 4) / 2 ≤ c := by
  have h := _root_.GD.N0185.d023077
    (2 * c) (by positivity) d hd (_root_.GD.N0162.d030949 d c hc hcap)
  linarith


theorem d030952 (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ) (hd : Measurable d) :
    ENNReal.ofReal ((1 + Real.pi / 4) / 2) ≤
      _root_.GD.N0232.N0720.N1228.d016745 3 3 (by norm_num) (by norm_num) d := by
  by_cases htop : _root_.GD.N0232.N0720.N1228.d016745 3 3 (by norm_num) (by norm_num) d = ⊤
  · rw [htop]
    exact le_top
  let c := (_root_.GD.N0232.N0720.N1228.d016745 3 3 (by norm_num) (by norm_num) d).toReal
  have hc : 0 ≤ c := ENNReal.toReal_nonneg
  have hval : ENNReal.ofReal c = _root_.GD.N0232.N0720.N1228.d016745 3 3 (by norm_num) (by norm_num) d :=
    ENNReal.ofReal_toReal htop
  have hcap : ∀ theta, _root_.GD.N0232.N0720.N1228.d016744 3 3 (by norm_num) (by norm_num) theta d ≤
      ENNReal.ofReal c := by
    intro theta
    rw [hval]
    exact le_iSup (fun eta => _root_.GD.N0232.N0720.N1228.d016744 3 3 (by norm_num) (by norm_num) eta d) theta
  rw [← hval]
  exact ENNReal.ofReal_le_ofReal (_root_.GD.N0162.d030951 d hd c hc hcap)


theorem d030953
    (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ) (theta : _root_.GD.N0232.N0720.N1080.d014168)
    (htop : _root_.GD.N0232.N0720.N1228.d016744 3 3 (by norm_num) (by norm_num) theta d = ⊤) :
    _root_.GD.N0232.N0720.N1228.d016752 3 3 (by norm_num) (by norm_num) d = ⊥ := by
  apply bot_unique
  exact (iInf_le (fun eta => (1 : EReal) -
    (_root_.GD.N0232.N0720.N1228.d016744 3 3 (by norm_num) (by norm_num) eta d : EReal)) theta).trans
      (by simp [htop])


theorem d030954
    (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ)
    (htop : _root_.GD.N0232.N0720.N1228.d016745 3 3 (by norm_num) (by norm_num) d = ⊤) :
    _root_.GD.N0232.N0720.N1228.d016752 3 3 (by norm_num) (by norm_num) d = ⊥ := by
  classical
  letI : Nonempty _root_.GD.N0232.N0720.N1080.d014168 := ⟨_root_.GD.N0232.N0720.N1080.d014169⟩
  by_cases hp : ∀ theta, _root_.GD.N0232.N0720.N1228.d016744 3 3 (by norm_num) (by norm_num) theta d ≠ ⊤
  · apply (EReal.eq_bot_iff_forall_lt _).mpr
    intro y
    have h := _root_.GD.N0230.N0686.d003547
      (_root_.GD.N0232.N0720.N1228.d016744 3 3 (by norm_num) (by norm_num)) d
      (ENNReal.ofReal (max 0 (2 - y))) ENNReal.ofReal_ne_top hp
      (by change _ ≤ _root_.GD.N0232.N0720.N1228.d016745 3 3 (by norm_num) (by norm_num) d; rw [htop]; exact le_top)
    rw [ENNReal.toReal_ofReal (le_max_left _ _)] at h
    apply h.trans_lt
    exact_mod_cast (show 1 - max 0 (2 - y) < y by linarith [le_max_right (0 : ℝ) (2 - y)])
  · push Not at hp
    obtain ⟨theta, htheta⟩ := hp
    exact _root_.GD.N0162.d030953 d theta htheta


theorem d030955
    (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ)
    (hfinite : _root_.GD.N0232.N0720.N1228.d016745 3 3 (by norm_num) (by norm_num) d ≠ ⊤) :
    _root_.GD.N0232.N0720.N1228.d016752 3 3 (by norm_num) (by norm_num) d =
      ((1 - (_root_.GD.N0232.N0720.N1228.d016745 3 3 (by norm_num) (by norm_num) d).toReal : ℝ) : EReal) := by
  letI : Nonempty _root_.GD.N0232.N0720.N1080.d014168 := ⟨_root_.GD.N0232.N0720.N1080.d014169⟩
  exact _root_.GD.N0230.N0686.d003548
    (_root_.GD.N0232.N0720.N1228.d016744 3 3 (by norm_num) (by norm_num)) d hfinite


theorem d030956
    (d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ) (hd : Measurable d) :
    _root_.GD.N0232.N0720.N1228.d016752 3 3 (by norm_num) (by norm_num) d ≤
      ((1 / 2 - Real.pi / 8 : ℝ) : EReal) := by
  by_cases htop : _root_.GD.N0232.N0720.N1228.d016745 3 3 (by norm_num) (by norm_num) d = ⊤
  · rw [_root_.GD.N0162.d030954 d htop]
    exact bot_le
  rw [_root_.GD.N0162.d030955 d htop]
  have h := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top htop).mpr
    (_root_.GD.N0162.d030952 d hd)
  rw [ENNReal.toReal_ofReal (by positivity)] at h
  exact_mod_cast (show 1 - (_root_.GD.N0232.N0720.N1228.d016745 3 3 (by norm_num) (by norm_num) d).toReal ≤
    1 / 2 - Real.pi / 8 by linarith)


theorem d030957 :
    _root_.GD.N0232.N0720.N1228.d016753 3 3 (by norm_num) (by norm_num)
      {d : _root_.GD.N0232.N0720.N1080.d014170 3 3 → ℝ | Measurable d} ≤ ((1 / 2 - Real.pi / 8 : ℝ) : EReal) := by
  apply iSup_le
  intro d
  apply iSup_le
  intro hd
  exact _root_.GD.N0162.d030956 d hd

end
end GD.N0162

#print axioms _root_.GD.N0162.d030941
#print axioms _root_.GD.N0162.d030942
#print axioms _root_.GD.N0162.d030943
#print axioms _root_.GD.N0162.d030944
#print axioms _root_.GD.N0162.d030945
#print axioms _root_.GD.N0162.d030946
#print axioms _root_.GD.N0162.d030947
#print axioms _root_.GD.N0162.d030948
#print axioms _root_.GD.N0162.d030949
#print axioms _root_.GD.N0162.d030950
#print axioms _root_.GD.N0162.d030951
#print axioms _root_.GD.N0162.d030952
#print axioms _root_.GD.N0162.d030953
#print axioms _root_.GD.N0162.d030954
#print axioms _root_.GD.N0162.d030955
#print axioms _root_.GD.N0162.d030956
#print axioms _root_.GD.N0162.d030957
