import GD.Module1565
























set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

open Set Filter Topology

namespace GD.N0106.N0428.N0770.N1711
noncomputable section

open _root_.GD.N0106.N0428.N0770.N1725




def d024178 (q e F : ℝ) : ℝ :=
  (1 / 2) * (Real.log F - Real.log e - Real.log (1 - e)) - (5 / 2) * Real.log (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)

theorem d024179 {q e F : ℝ} (he0 : 0 < e) (he1 : e < 1) (hF : 0 < F)
    (hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) : _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) = Real.exp (_root_.GD.N0106.N0428.N0770.N1711.d024178 q e F) := by
  have hprod : 0 < e * (1 - e) := mul_pos he0 (sub_pos.mpr he1)
  have hx : 0 < F / (e * (1 - e)) := div_pos hF hprod
  show Real.sqrt (F / (e * (1 - e))) * _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ (-(5 / 2 : ℝ)) = _
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hN, ← Real.exp_add]
  congr 1
  rw [Real.log_div hF.ne' hprod.ne', Real.log_mul he0.ne' (sub_pos.mpr he1).ne']
  unfold _root_.GD.N0106.N0428.N0770.N1711.d024178
  ring

theorem d024180 {q e F : ℝ} (he0 : 0 < e) (he1 : e < 1) (hF : 0 < F) (hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) :
    0 < _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) := by
  rw [_root_.GD.N0106.N0428.N0770.N1711.d024179 he0 he1 hF hN]
  exact Real.exp_pos _




def d024181 (q F : ℝ) : Set ℝ := Ioi 0 ∩ (Iio 1 ∩ (fun e => _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) ⁻¹' Ioi 0)

theorem d024182 (q F : ℝ) : Continuous (fun e => _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) := by
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024169
  fun_prop

theorem d024183 (q F : ℝ) : IsOpen (_root_.GD.N0106.N0428.N0770.N1711.d024181 q F) :=
  isOpen_Ioi.inter (isOpen_Iio.inter (isOpen_Ioi.preimage (_root_.GD.N0106.N0428.N0770.N1711.d024182 q F)))

theorem d024184 {q e F : ℝ} (he0 : 0 < e) (he1 : e < 1) (hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) :
    e ∈ _root_.GD.N0106.N0428.N0770.N1711.d024181 q F := ⟨he0, he1, hN⟩

theorem d024185 (q e F : ℝ) : HasDerivAt (fun e => _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) (1 - 2 * q) e := by
  have heq : (fun e => _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) = fun e => (1 - 2 * q) * e + (q + F * q - F * q ^ 2) := by
    funext e; unfold _root_.GD.N0106.N0428.N0770.N1725.d024169; ring
  rw [heq]
  have h := ((hasDerivAt_id e).const_mul (1 - 2 * q)).add
    (hasDerivAt_const (x := e) (c := q + F * q - F * q ^ 2))
  exact h.congr_deriv (by simp)


def d024186 (q e F : ℝ) : ℝ :=
  (1 / 2) * (-(e⁻¹) + (1 - e)⁻¹) - (5 / 2) * ((1 - 2 * q) * (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)⁻¹)


def d024187 (q e F : ℝ) : ℝ :=
  (1 / 2) * (1 / e ^ 2 + 1 / (1 - e) ^ 2) + (5 / 2) * ((1 - 2 * q) ^ 2 / (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) ^ 2)

theorem d024188 {q e F : ℝ} (he0 : 0 < e) (he1 : e < 1) (hF : 0 < F)
    (hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) : HasDerivAt (fun e => _root_.GD.N0106.N0428.N0770.N1711.d024178 q e F) (_root_.GD.N0106.N0428.N0770.N1711.d024186 q e F) e := by
  have h1e : (1 : ℝ) - e ≠ 0 := (sub_pos.mpr he1).ne'
  have hlogF : HasDerivAt (fun _ : ℝ => Real.log F) 0 e :=
    hasDerivAt_const (x := e) (c := Real.log F)
  have hloge : HasDerivAt (fun e => Real.log e) e⁻¹ e := Real.hasDerivAt_log he0.ne'
  have hlog1e : HasDerivAt (fun e => Real.log (1 - e)) (-1 / (1 - e)) e :=
    ((hasDerivAt_id e).const_sub 1).log h1e
  have hlogN : HasDerivAt (fun e => Real.log (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)) ((1 - 2 * q) / _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) e :=
    (_root_.GD.N0106.N0428.N0770.N1711.d024185 q e F).log hN.ne'
  have h := (((hlogF.sub hloge).sub hlog1e).const_mul (1 / 2)).sub (hlogN.const_mul (5 / 2))
  exact h.congr_deriv (by unfold _root_.GD.N0106.N0428.N0770.N1711.d024186; ring)

theorem d024189 {q e F : ℝ} (he0 : 0 < e) (he1 : e < 1) (hF : 0 < F)
    (hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) : HasDerivAt (fun e => _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F)) (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024186 q e F) e := by
  have hexp := (_root_.GD.N0106.N0428.N0770.N1711.d024188 he0 he1 hF hN).exp
  have hev : (fun e => _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F)) =ᶠ[𝓝 e] fun e => Real.exp (_root_.GD.N0106.N0428.N0770.N1711.d024178 q e F) := by
    refine Filter.eventuallyEq_of_mem
      ((_root_.GD.N0106.N0428.N0770.N1711.d024183 q F).mem_nhds (_root_.GD.N0106.N0428.N0770.N1711.d024184 he0 he1 hN)) ?_
    intro x hx
    obtain ⟨hx0, hx1, hxN⟩ := hx
    exact _root_.GD.N0106.N0428.N0770.N1711.d024179 hx0 hx1 hF hxN
  rw [_root_.GD.N0106.N0428.N0770.N1711.d024179 he0 he1 hF hN]
  exact hexp.congr_of_eventuallyEq hev

theorem d024190 {q e F : ℝ} (he0 : 0 < e) (he1 : e < 1) (hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) :
    HasDerivAt (fun e => _root_.GD.N0106.N0428.N0770.N1711.d024186 q e F) (_root_.GD.N0106.N0428.N0770.N1711.d024187 q e F) e := by
  have h1e : (1 : ℝ) - e ≠ 0 := (sub_pos.mpr he1).ne'
  have hinv_e : HasDerivAt (fun e : ℝ => e⁻¹) (-1 / e ^ 2) e := (hasDerivAt_id e).inv he0.ne'
  have hinv_1e : HasDerivAt (fun e : ℝ => (1 - e)⁻¹) (-(-1) / (1 - e) ^ 2) e :=
    ((hasDerivAt_id e).const_sub 1).inv h1e
  have hinv_N : HasDerivAt (fun e => (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)⁻¹) (-(1 - 2 * q) / (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) ^ 2) e :=
    (_root_.GD.N0106.N0428.N0770.N1711.d024185 q e F).inv hN.ne'
  have h := ((hinv_e.neg.add hinv_1e).const_mul (1 / 2)).sub
    ((hinv_N.const_mul (1 - 2 * q)).const_mul (5 / 2))
  exact h.congr_deriv (by unfold _root_.GD.N0106.N0428.N0770.N1711.d024187; ring)


theorem d024191 {q e F : ℝ} (he0 : 0 < e) (he1 : e < 1) (hF : 0 < F)
    (hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) :
    HasDerivAt (fun e => _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024186 q e F)
      (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024186 q e F * _root_.GD.N0106.N0428.N0770.N1711.d024186 q e F + _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024187 q e F) e :=
  (_root_.GD.N0106.N0428.N0770.N1711.d024189 he0 he1 hF hN).mul (_root_.GD.N0106.N0428.N0770.N1711.d024190 he0 he1 hN)


theorem d024192 {q e F : ℝ} (he0 : 0 < e) (he1 : e < 1) (hF : 0 < F)
    (hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) :
    HasDerivAt (fun e => (e - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F))
      (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) + (e - q) * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024186 q e F)) e := by
  have h := ((hasDerivAt_id e).sub (hasDerivAt_const (x := e) (c := q))).mul
    (_root_.GD.N0106.N0428.N0770.N1711.d024189 he0 he1 hF hN)
  exact h.congr_deriv (by simp only [Pi.sub_apply, id_eq]; ring)


theorem d024193 {q e F : ℝ} (he0 : 0 < e) (he1 : e < 1) (hF : 0 < F)
    (hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) :
    HasDerivAt (fun e => _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) + (e - q) * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024186 q e F))
      (2 * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024186 q e F) +
        (e - q) * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024186 q e F * _root_.GD.N0106.N0428.N0770.N1711.d024186 q e F + _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024187 q e F)) e := by
  have h := (_root_.GD.N0106.N0428.N0770.N1711.d024189 he0 he1 hF hN).add
    (((hasDerivAt_id e).sub (hasDerivAt_const (x := e) (c := q))).mul
      (_root_.GD.N0106.N0428.N0770.N1711.d024191 he0 he1 hF hN))
  exact h.congr_deriv (by simp only [Pi.sub_apply, id_eq]; ring)




def d024194 (q e : ℝ) : Set ℝ := Ioi 0 ∩ (fun F => _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) ⁻¹' Ioi 0

theorem d024195 (q e : ℝ) : Continuous (fun F => _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) := by
  unfold _root_.GD.N0106.N0428.N0770.N1725.d024169
  fun_prop

theorem d024196 (q e : ℝ) : IsOpen (_root_.GD.N0106.N0428.N0770.N1711.d024194 q e) :=
  isOpen_Ioi.inter (isOpen_Ioi.preimage (_root_.GD.N0106.N0428.N0770.N1711.d024195 q e))

theorem d024197 {q e F : ℝ} (hF : 0 < F) (hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) : F ∈ _root_.GD.N0106.N0428.N0770.N1711.d024194 q e := ⟨hF, hN⟩

theorem d024198 (q e F : ℝ) : HasDerivAt (fun F => _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) (q * (1 - q)) F := by
  have heq : (fun F => _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) = fun F => (q * (1 - q)) * F + (e + (1 - 2 * e) * q) := by
    funext F; unfold _root_.GD.N0106.N0428.N0770.N1725.d024169; ring
  rw [heq]
  have h := ((hasDerivAt_id F).const_mul (q * (1 - q))).add
    (hasDerivAt_const (x := F) (c := e + (1 - 2 * e) * q))
  exact h.congr_deriv (by simp)


def d024199 (q e F : ℝ) : ℝ := (1 / 2) * F⁻¹ - (5 / 2) * (q * (1 - q) * (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)⁻¹)


def d024200 (q e F : ℝ) : ℝ :=
  -(1 / 2) * (1 / F ^ 2) + (5 / 2) * ((q * (1 - q)) ^ 2 / (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) ^ 2)

theorem d024201 {q e F : ℝ} (hF : 0 < F) (hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) :
    HasDerivAt (fun F => _root_.GD.N0106.N0428.N0770.N1711.d024178 q e F) (_root_.GD.N0106.N0428.N0770.N1711.d024199 q e F) F := by
  have hlogF : HasDerivAt (fun F => Real.log F) F⁻¹ F := Real.hasDerivAt_log hF.ne'
  have hloge : HasDerivAt (fun _ : ℝ => Real.log e) 0 F :=
    hasDerivAt_const (x := F) (c := Real.log e)
  have hlog1e : HasDerivAt (fun _ : ℝ => Real.log (1 - e)) 0 F :=
    hasDerivAt_const (x := F) (c := Real.log (1 - e))
  have hlogN : HasDerivAt (fun F => Real.log (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)) (q * (1 - q) / _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) F :=
    (_root_.GD.N0106.N0428.N0770.N1711.d024198 q e F).log hN.ne'
  have h := (((hlogF.sub hloge).sub hlog1e).const_mul (1 / 2)).sub (hlogN.const_mul (5 / 2))
  exact h.congr_deriv (by unfold _root_.GD.N0106.N0428.N0770.N1711.d024199; ring)

theorem d024202 {q e F : ℝ} (he0 : 0 < e) (he1 : e < 1) (hF : 0 < F)
    (hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) : HasDerivAt (fun F => _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F)) (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024199 q e F) F := by
  have hexp := (_root_.GD.N0106.N0428.N0770.N1711.d024201 hF hN).exp
  have hev : (fun F => _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F)) =ᶠ[𝓝 F] fun F => Real.exp (_root_.GD.N0106.N0428.N0770.N1711.d024178 q e F) := by
    refine Filter.eventuallyEq_of_mem
      ((_root_.GD.N0106.N0428.N0770.N1711.d024196 q e).mem_nhds (_root_.GD.N0106.N0428.N0770.N1711.d024197 hF hN)) ?_
    intro y hy
    obtain ⟨hy0, hyN⟩ := hy
    exact _root_.GD.N0106.N0428.N0770.N1711.d024179 he0 he1 hy0 hyN
  rw [_root_.GD.N0106.N0428.N0770.N1711.d024179 he0 he1 hF hN]
  exact hexp.congr_of_eventuallyEq hev

theorem d024203 {q e F : ℝ} (hF : 0 < F) (hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) :
    HasDerivAt (fun F => _root_.GD.N0106.N0428.N0770.N1711.d024199 q e F) (_root_.GD.N0106.N0428.N0770.N1711.d024200 q e F) F := by
  have hinv_F : HasDerivAt (fun F : ℝ => F⁻¹) (-1 / F ^ 2) F := (hasDerivAt_id F).inv hF.ne'
  have hinv_N : HasDerivAt (fun F => (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)⁻¹) (-(q * (1 - q)) / (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) ^ 2) F :=
    (_root_.GD.N0106.N0428.N0770.N1711.d024198 q e F).inv hN.ne'
  have h := (hinv_F.const_mul (1 / 2)).sub
    ((hinv_N.const_mul (q * (1 - q))).const_mul (5 / 2))
  exact h.congr_deriv (by unfold _root_.GD.N0106.N0428.N0770.N1711.d024200; ring)


theorem d024204 {q e F : ℝ} (he0 : 0 < e) (he1 : e < 1) (hF : 0 < F)
    (hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) :
    HasDerivAt (fun F => _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024199 q e F)
      (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024199 q e F * _root_.GD.N0106.N0428.N0770.N1711.d024199 q e F + _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024200 q e F) F :=
  (_root_.GD.N0106.N0428.N0770.N1711.d024202 he0 he1 hF hN).mul (_root_.GD.N0106.N0428.N0770.N1711.d024203 hF hN)


theorem d024205 {q e F : ℝ} (he0 : 0 < e) (he1 : e < 1) (hF : 0 < F)
    (hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) :
    HasDerivAt (fun F => (e - q) * _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F)) ((e - q) * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024199 q e F)) F :=
  (_root_.GD.N0106.N0428.N0770.N1711.d024202 he0 he1 hF hN).const_mul (e - q)

theorem d024206 {q e F : ℝ} (he0 : 0 < e) (he1 : e < 1) (hF : 0 < F)
    (hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) :
    HasDerivAt (fun F => (e - q) * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024199 q e F))
      ((e - q) * (_root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024199 q e F * _root_.GD.N0106.N0428.N0770.N1711.d024199 q e F + _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) * _root_.GD.N0106.N0428.N0770.N1711.d024200 q e F)) F :=
  (_root_.GD.N0106.N0428.N0770.N1711.d024204 he0 he1 hF hN).const_mul (e - q)





theorem d024207 {q e F elo flo : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (he_lo : elo ≤ e) (hflo : 0 ≤ flo) (hf_lo : flo ≤ F) :
    min elo (1 / 2 + flo / 4) ≤ _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F := by
  have h1 : 0 ≤ 1 - 2 * q := by linarith
  have h2 : 0 ≤ q * (1 - q) := mul_nonneg hq0 (by linarith)
  have hNe : _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F = e * (1 - 2 * q) + q + F * (q * (1 - q)) := by unfold _root_.GD.N0106.N0428.N0770.N1725.d024169; ring
  have hA : elo * (1 - 2 * q) + q + flo * (q * (1 - q)) ≤ _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F := by
    rw [hNe]
    nlinarith [mul_le_mul_of_nonneg_right he_lo h1, mul_le_mul_of_nonneg_right hf_lo h2]
  have hm1 := min_le_left elo (1 / 2 + flo / 4)
  have hm2 := min_le_right elo (1 / 2 + flo / 4)
  have hB : min elo (1 / 2 + flo / 4) ≤ elo * (1 - 2 * q) + q + flo * (q * (1 - q)) := by
    nlinarith [mul_nonneg h1 (sub_nonneg.mpr hm1),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * q) (sub_nonneg.mpr hm2),
      mul_nonneg hflo (mul_nonneg hq0 (by linarith : (0 : ℝ) ≤ 1 / 2 - q))]
  linarith


theorem d024208 {e elo ehi eprod : ℝ} (he_lo : elo ≤ e) (he_hi : e ≤ ehi)
    (hE1 : eprod ≤ elo * (1 - elo)) (hE2 : eprod ≤ ehi * (1 - ehi)) :
    eprod ≤ e * (1 - e) := by
  rcases le_or_gt e (1 / 2) with h | h
  · nlinarith [mul_nonneg (sub_nonneg.mpr he_lo) (by linarith : (0 : ℝ) ≤ 1 - elo - e)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr he_hi) (by linarith : (0 : ℝ) ≤ e + ehi - 1)]


theorem d024209 {q e F fhi eprod pmin k : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (he0 : 0 < e) (he1 : e < 1) (hF : 0 < F)
    (hE : eprod ≤ e * (1 - e)) (heprod : 0 < eprod) (hfhi : F ≤ fhi)
    (hpmin : 0 < pmin) (hNp : pmin ≤ _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)
    (hk : 0 ≤ k) (hkk : fhi ≤ k ^ 2 * (eprod * pmin ^ 5)) : _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) ≤ k := by
  have hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F := hpmin.trans_le hNp
  have hprod : 0 < e * (1 - e) := mul_pos he0 (sub_pos.mpr he1)
  have hx : 0 ≤ F / (e * (1 - e)) := (div_pos hF hprod).le
  have hW := _root_.GD.N0106.N0428.N0770.N1725.d024174 hq ⟨he0, he1⟩ hF
  have hW0 : 0 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) := (_root_.GD.N0106.N0428.N0770.N1711.d024180 he0 he1 hF hN).le
  have hsq : _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) ^ 2 = (F / (e * (1 - e))) / _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ 5 := by
    rw [hW, div_pow, Real.sq_sqrt hx, mul_pow, Real.sq_sqrt hN.le]
    first
    | ring
    | (field_simp; ring)
  have h1 : F / (e * (1 - e)) ≤ fhi / eprod :=
    (div_le_div_of_nonneg_right hfhi hprod.le).trans
      (div_le_div_of_nonneg_left (hF.le.trans hfhi) heprod hE)
  have h2 : pmin ^ 5 ≤ _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ 5 := pow_le_pow_left₀ hpmin.le hNp 5
  have hbound : _root_.GD.N0106.N0428.N0770.N1725.d024170 q (e, F) ^ 2 ≤ k ^ 2 := by
    rw [hsq]
    calc (F / (e * (1 - e))) / _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ 5 ≤ (F / (e * (1 - e))) / pmin ^ 5 :=
          div_le_div_of_nonneg_left hx (pow_pos hpmin 5) h2
      _ ≤ (fhi / eprod) / pmin ^ 5 := div_le_div_of_nonneg_right h1 (pow_pos hpmin 5).le
      _ ≤ k ^ 2 := by
          rw [div_div, div_le_iff₀ (mul_pos heprod (pow_pos hpmin 5))]
          exact hkk
  have hs := Real.sqrt_le_sqrt hbound
  rwa [Real.sqrt_sq hW0, Real.sqrt_sq hk] at hs

theorem d024210 {q e F elo ehi pmin : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (helo : 0 < elo) (he_lo : elo ≤ e) (he_hi : e ≤ ehi) (hehi : ehi < 1)
    (hpmin : 0 < pmin) (hNp : pmin ≤ _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) :
    |_root_.GD.N0106.N0428.N0770.N1711.d024186 q e F| ≤ (1 / 2) * (1 / elo + 1 / (1 - ehi)) + (5 / 2) * (1 / pmin) := by
  have he0 : 0 < e := helo.trans_le he_lo
  have h1e : 0 < 1 - e := by linarith
  have h1ehi : 0 < 1 - ehi := by linarith
  have hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F := hpmin.trans_le hNp
  have hi1 : e⁻¹ ≤ 1 / elo := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le helo he_lo
  have hi2 : (1 - e)⁻¹ ≤ 1 / (1 - ehi) := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le h1ehi (by linarith)
  have hi3 : (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)⁻¹ ≤ 1 / pmin := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le hpmin hNp
  have hp1 : 0 < e⁻¹ := inv_pos.mpr he0
  have hp2 : 0 < (1 - e)⁻¹ := inv_pos.mpr h1e
  have hp3 : 0 < (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)⁻¹ := inv_pos.mpr hN
  have hq' : 0 ≤ (1 - 2 * q) * (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)⁻¹ := mul_nonneg (by linarith) hp3.le
  have hq'' : (1 - 2 * q) * (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)⁻¹ ≤ (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)⁻¹ :=
    mul_le_of_le_one_left hp3.le (by linarith)
  unfold _root_.GD.N0106.N0428.N0770.N1711.d024186
  rw [abs_le]
  constructor <;> nlinarith

theorem d024211 {q e F : ℝ} : 0 ≤ _root_.GD.N0106.N0428.N0770.N1711.d024187 q e F := by
  unfold _root_.GD.N0106.N0428.N0770.N1711.d024187
  positivity

theorem d024212 {q e F elo ehi pmin : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (helo : 0 < elo) (he_lo : elo ≤ e) (he_hi : e ≤ ehi) (hehi : ehi < 1)
    (hpmin : 0 < pmin) (hNp : pmin ≤ _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) :
    |_root_.GD.N0106.N0428.N0770.N1711.d024187 q e F| ≤ (1 / 2) * (1 / elo ^ 2 + 1 / (1 - ehi) ^ 2) + (5 / 2) * (1 / pmin ^ 2) := by
  have he0 : 0 < e := helo.trans_le he_lo
  have h1ehi : 0 < 1 - ehi := by linarith
  have hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F := hpmin.trans_le hNp
  have hi1 : 1 / e ^ 2 ≤ 1 / elo ^ 2 :=
    one_div_le_one_div_of_le (pow_pos helo 2) (pow_le_pow_left₀ helo.le he_lo 2)
  have hi2 : 1 / (1 - e) ^ 2 ≤ 1 / (1 - ehi) ^ 2 :=
    one_div_le_one_div_of_le (pow_pos h1ehi 2) (pow_le_pow_left₀ h1ehi.le (by linarith) 2)
  have hsq : (1 - 2 * q) ^ 2 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hN2 : 1 / _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ 2 ≤ 1 / pmin ^ 2 :=
    one_div_le_one_div_of_le (pow_pos hpmin 2) (pow_le_pow_left₀ hpmin.le hNp 2)
  have hi3 : (1 - 2 * q) ^ 2 / _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ 2 ≤ 1 / pmin ^ 2 := by
    calc (1 - 2 * q) ^ 2 / _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ 2 = (1 - 2 * q) ^ 2 * (1 / _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ 2) := by ring
      _ ≤ 1 * (1 / pmin ^ 2) := mul_le_mul hsq hN2 (by positivity) (by norm_num)
      _ = 1 / pmin ^ 2 := one_mul _
  rw [abs_of_nonneg _root_.GD.N0106.N0428.N0770.N1711.d024211]
  unfold _root_.GD.N0106.N0428.N0770.N1711.d024187
  linarith

theorem d024213 {q e F flo pmin : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hflo : 0 < flo) (hf_lo : flo ≤ F) (hpmin : 0 < pmin) (hNp : pmin ≤ _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) :
    |_root_.GD.N0106.N0428.N0770.N1711.d024199 q e F| ≤ (1 / 2) * (1 / flo) + (5 / 8) * (1 / pmin) := by
  have hF : 0 < F := hflo.trans_le hf_lo
  have hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F := hpmin.trans_le hNp
  have hi1 : F⁻¹ ≤ 1 / flo := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le hflo hf_lo
  have hi3 : (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)⁻¹ ≤ 1 / pmin := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le hpmin hNp
  have hp1 : 0 < F⁻¹ := inv_pos.mpr hF
  have hp3 : 0 < (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)⁻¹ := inv_pos.mpr hN
  have hq14 : q * (1 - q) ≤ 1 / 4 := by nlinarith [sq_nonneg (q - 1 / 2)]
  have hq0' : 0 ≤ q * (1 - q) := mul_nonneg hq0 (by linarith)
  have hq' : 0 ≤ q * (1 - q) * (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)⁻¹ := mul_nonneg hq0' hp3.le
  have hq'' : q * (1 - q) * (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)⁻¹ ≤ (1 / 4) * (_root_.GD.N0106.N0428.N0770.N1725.d024169 q e F)⁻¹ :=
    mul_le_mul_of_nonneg_right hq14 hp3.le
  unfold _root_.GD.N0106.N0428.N0770.N1711.d024199
  rw [abs_le]
  constructor <;> nlinarith

theorem d024214 {q e F flo pmin : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (hflo : 0 < flo) (hf_lo : flo ≤ F) (hpmin : 0 < pmin) (hNp : pmin ≤ _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F) :
    |_root_.GD.N0106.N0428.N0770.N1711.d024200 q e F| ≤ (1 / 2) * (1 / flo ^ 2) + (5 / 32) * (1 / pmin ^ 2) := by
  have hF : 0 < F := hflo.trans_le hf_lo
  have hN : 0 < _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F := hpmin.trans_le hNp
  have hi1 : 1 / F ^ 2 ≤ 1 / flo ^ 2 :=
    one_div_le_one_div_of_le (pow_pos hflo 2) (pow_le_pow_left₀ hflo.le hf_lo 2)
  have hp1 : 0 < 1 / F ^ 2 := by positivity
  have hq14 : q * (1 - q) ≤ 1 / 4 := by nlinarith [sq_nonneg (q - 1 / 2)]
  have hq0' : 0 ≤ q * (1 - q) := mul_nonneg hq0 (by linarith)
  have hsq : (q * (1 - q)) ^ 2 ≤ 1 / 16 := by
    calc (q * (1 - q)) ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ hq0' hq14 2
      _ = 1 / 16 := by norm_num
  have hN2 : 1 / _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ 2 ≤ 1 / pmin ^ 2 :=
    one_div_le_one_div_of_le (pow_pos hpmin 2) (pow_le_pow_left₀ hpmin.le hNp 2)
  have hi3 : (q * (1 - q)) ^ 2 / _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ 2 ≤ (1 / 16) * (1 / pmin ^ 2) := by
    calc (q * (1 - q)) ^ 2 / _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ 2 = (q * (1 - q)) ^ 2 * (1 / _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ 2) := by ring
      _ ≤ (1 / 16) * (1 / pmin ^ 2) := mul_le_mul hsq hN2 (by positivity) (by norm_num)
  have hq3 : 0 ≤ (q * (1 - q)) ^ 2 / _root_.GD.N0106.N0428.N0770.N1725.d024169 q e F ^ 2 := by positivity
  unfold _root_.GD.N0106.N0428.N0770.N1711.d024200
  rw [abs_le]
  constructor <;> nlinarith




theorem d024215 {W L LL k A1 A2 : ℝ} (hW0 : 0 ≤ W) (hWk : W ≤ k)
    (hA1 : |L| ≤ A1) (hA2 : |LL| ≤ A2) :
    |W * L * L + W * LL| ≤ k * (A1 ^ 2 + A2) := by
  have hk0 : 0 ≤ k := hW0.trans hWk
  have hA10 : 0 ≤ A1 := (abs_nonneg _).trans hA1
  have hA20 : 0 ≤ A2 := (abs_nonneg _).trans hA2
  have h1 : |W * L * L| ≤ k * A1 * A1 := by
    rw [abs_mul (W * L) L, abs_mul W L, abs_of_nonneg hW0]
    exact mul_le_mul (mul_le_mul hWk hA1 (abs_nonneg _) hk0) hA1 (abs_nonneg _)
      (mul_nonneg hk0 hA10)
  have h2 : |W * LL| ≤ k * A2 := by
    rw [abs_mul, abs_of_nonneg hW0]
    exact mul_le_mul hWk hA2 (abs_nonneg _) hk0
  calc |W * L * L + W * LL| ≤ |W * L * L| + |W * LL| := by
        first
        | exact abs_add_le _ _
        | exact abs_add _ _
    _ ≤ k * A1 * A1 + k * A2 := add_le_add h1 h2
    _ = k * (A1 ^ 2 + A2) := by ring



theorem d024216 {W L LL d k A1 A2 D : ℝ} (hW0 : 0 ≤ W) (hWk : W ≤ k)
    (hA1 : |L| ≤ A1) (hA2 : |LL| ≤ A2) (hD : |d| ≤ D) :
    |2 * (W * L) + d * (W * L * L + W * LL)| ≤ 2 * (k * A1) + D * (k * (A1 ^ 2 + A2)) := by
  have hk0 : 0 ≤ k := hW0.trans hWk
  have hD0 : 0 ≤ D := (abs_nonneg _).trans hD
  have h1 : |W * L| ≤ k * A1 := by
    rw [abs_mul, abs_of_nonneg hW0]
    exact mul_le_mul hWk hA1 (abs_nonneg _) hk0
  have h2 := _root_.GD.N0106.N0428.N0770.N1711.d024215 hW0 hWk hA1 hA2
  have hk2 : 0 ≤ k * (A1 ^ 2 + A2) := (abs_nonneg _).trans h2
  calc |2 * (W * L) + d * (W * L * L + W * LL)|
      ≤ |2 * (W * L)| + |d * (W * L * L + W * LL)| := by
        first
        | exact abs_add_le _ _
        | exact abs_add _ _
    _ = 2 * |W * L| + |d| * |W * L * L + W * LL| := by
        rw [abs_mul (2 : ℝ) (W * L), abs_mul d (W * L * L + W * LL), abs_two]
    _ ≤ 2 * (k * A1) + D * (k * (A1 ^ 2 + A2)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
          (mul_le_mul hD h2 (abs_nonneg _) hD0)


theorem d024217 {W L LL d k B1 B2 D : ℝ} (hW0 : 0 ≤ W) (hWk : W ≤ k)
    (hB1 : |L| ≤ B1) (hB2 : |LL| ≤ B2) (hD : |d| ≤ D) :
    |d * (W * L * L + W * LL)| ≤ D * (k * (B1 ^ 2 + B2)) := by
  have hD0 : 0 ≤ D := (abs_nonneg _).trans hD
  have h2 := _root_.GD.N0106.N0428.N0770.N1711.d024215 hW0 hWk hB1 hB2
  rw [abs_mul]
  exact mul_le_mul hD h2 (abs_nonneg _) hD0


theorem d024218 {q e elo ehi D : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (he_lo : elo ≤ e) (he_hi : e ≤ ehi) (hD1 : ehi ≤ D) (hD2 : 1 / 2 - elo ≤ D) :
    |e - q| ≤ D := by
  rw [abs_le]
  constructor <;> linarith

end
end GD.N0106.N0428.N0770.N1711

#print axioms _root_.GD.N0106.N0428.N0770.N1711.d024179
#print axioms _root_.GD.N0106.N0428.N0770.N1711.d024189
#print axioms _root_.GD.N0106.N0428.N0770.N1711.d024193
#print axioms _root_.GD.N0106.N0428.N0770.N1711.d024202
#print axioms _root_.GD.N0106.N0428.N0770.N1711.d024206
#print axioms _root_.GD.N0106.N0428.N0770.N1711.d024207
#print axioms _root_.GD.N0106.N0428.N0770.N1711.d024209
#print axioms _root_.GD.N0106.N0428.N0770.N1711.d024210
#print axioms _root_.GD.N0106.N0428.N0770.N1711.d024212
#print axioms _root_.GD.N0106.N0428.N0770.N1711.d024213
#print axioms _root_.GD.N0106.N0428.N0770.N1711.d024214
#print axioms _root_.GD.N0106.N0428.N0770.N1711.d024216
