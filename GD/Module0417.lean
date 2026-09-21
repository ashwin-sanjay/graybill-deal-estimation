import GD.Module0399
import GD.Module0400

























noncomputable section

open Set
open scoped Topology

namespace GD.N0132

open _root_.GD.N0111
open _root_.GD.N0110
open _root_.GD.N0112

def d006442 (α β : ℝ) : ℝ :=
  min α β / (4 * (α + β))

def d006443 (α β : ℝ) (N : ℕ) : ℝ :=
  _root_.GD.N0132.d006442 α β / (4 * N)

def d006444 (α β : ℝ) (N : ℕ) : ℝ :=
  (α * β / (α + β)) / (8 * N)

def d006445 (α β e r s t : ℝ) : ℝ :=
  _root_.GD.N0111.d006137
    (α / (α + β) - e)
    (α * β / (α + β))
    (β - (α + β) * e)
    (e * (1 - e) / 2)
    r s t

def d006446 (α β e r s t : ℝ) (p q : ℕ) : ℝ :=
  _root_.GD.N0111.d006141
    (α / (α + β) - e)
    (α * β / (α + β))
    (β - (α + β) * e)
    (e * (1 - e) / 2)
    r s t p q

theorem d006447
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    0 < _root_.GD.N0132.d006442 α β := by
  unfold _root_.GD.N0132.d006442
  positivity

theorem d006448
    {α β : ℝ} {N : ℕ} (hα : 0 < α) (hβ : 0 < β)
    (hN : 1 ≤ N) :
    0 < _root_.GD.N0132.d006443 α β N := by
  unfold _root_.GD.N0132.d006443
  have hNc : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  exact div_pos (_root_.GD.N0132.d006447 hα hβ) (mul_pos (by norm_num) hNc)

theorem d006449
    {α β : ℝ} {N : ℕ} (hα : 0 < α) (hβ : 0 < β)
    (hN : 1 ≤ N) :
    0 < _root_.GD.N0132.d006444 α β N := by
  unfold _root_.GD.N0132.d006444
  have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  positivity

theorem d006450
    {α β : ℝ} {N : ℕ} (hα : 0 < α) (hβ : 0 < β)
    (hN : 1 ≤ N) :
    2 * _root_.GD.N0132.d006443 α β N ≤ _root_.GD.N0132.d006442 α β := by
  have hR := (_root_.GD.N0132.d006447 hα hβ).le
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold _root_.GD.N0132.d006443
  have hden : (0 : ℝ) < 4 * N := by positivity
  calc
    2 * (_root_.GD.N0132.d006442 α β / (4 * N))
        = _root_.GD.N0132.d006442 α β * (2 / (4 * N)) := by ring
    _ ≤ _root_.GD.N0132.d006442 α β * 1 := by
      gcongr
      exact (div_le_one hden).2 (by nlinarith)
    _ = _root_.GD.N0132.d006442 α β := by ring

theorem d006451
    {α β : ℝ} {N : ℕ} {s : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hN : 1 ≤ N)
    (hs : s ∈ Icc (-2 * _root_.GD.N0132.d006443 α β N) (2 * _root_.GD.N0132.d006443 α β N)) :
    |s| ≤ _root_.GD.N0132.d006442 α β := by
  rw [abs_le]
  constructor
  · have hsleft : -(2 * _root_.GD.N0132.d006443 α β N) ≤ s := by
      linarith [hs.1]
    exact (neg_le_neg (_root_.GD.N0132.d006450 hα hβ hN)).trans hsleft
  · exact hs.2.trans (_root_.GD.N0132.d006450 hα hβ hN)

theorem d006452
    {α β : ℝ} {N : ℕ} {s : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hN : 1 ≤ N)
    (hs : s ∈ Icc (-_root_.GD.N0132.d006443 α β N) (_root_.GD.N0132.d006443 α β N)) :
    |s| ≤ _root_.GD.N0132.d006442 α β := by
  apply _root_.GD.N0132.d006451 hα hβ hN
  constructor <;> linarith [hs.1, hs.2, _root_.GD.N0132.d006448 hα hβ hN]

theorem d006453
    {α β e s t : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hs : |s| ≤ _root_.GD.N0132.d006442 α β) (ht : 0 ≤ t) :
    0 <
      _root_.GD.N0111.d006136 (α * β / (α + β)) (β - (α + β) * e)
        (e * (1 - e) / 2) s t := by
  have hlow :=
    _root_.GD.N0111.d006166 hα hβ he0 he1
      (by simpa [_root_.GD.N0132.d006442] using hs) ht
  exact (_root_.GD.N0111.d006167 hα hβ).trans_le hlow



theorem d006454
    (a c d h r s t : ℝ) (q : ℕ)
    (hN : _root_.GD.N0111.d006136 c d h s t ≠ 0) :
    iteratedDeriv q (fun y => _root_.GD.N0111.d006137 a c d h r s y) t =
      _root_.GD.N0111.d006141 a c d h r s t 0 q := by
  induction q generalizing t with
  | zero =>
      simp [_root_.GD.N0111.d006148]
  | succ q ih =>
      rw [iteratedDeriv_succ]
      have hcont :
          ContinuousAt (fun y => _root_.GD.N0111.d006136 c d h s y) t :=
        (_root_.GD.N0111.d006143 c d h s t).continuousAt
      have hne :
          ∀ᶠ y in 𝓝 t, _root_.GD.N0111.d006136 c d h s y ≠ 0 :=
        hcont.eventually_ne hN
      have heq :
          (fun y => iteratedDeriv q
              (fun z => _root_.GD.N0111.d006137 a c d h r s z) y) =ᶠ[𝓝 t]
            (fun y => _root_.GD.N0111.d006141 a c d h r s y 0 q) :=
        hne.mono (fun y hy => ih y hy)
      rw [heq.deriv_eq]
      exact _root_.GD.N0111.d006147 a c d h r s t 0 q hN

theorem d006455
    (a c d h r s t : ℝ) (p : ℕ)
    (hN : _root_.GD.N0111.d006136 c d h s t ≠ 0) :
    iteratedDeriv p (fun x => _root_.GD.N0111.d006137 a c d h r x t) s =
      _root_.GD.N0111.d006141 a c d h r s t p 0 := by
  induction p generalizing s with
  | zero =>
      simp [_root_.GD.N0111.d006148]
  | succ p ih =>
      rw [iteratedDeriv_succ]
      have hcont :
          ContinuousAt (fun x => _root_.GD.N0111.d006136 c d h x t) s :=
        (_root_.GD.N0111.d006142 c d h s t).continuousAt
      have hne :
          ∀ᶠ x in 𝓝 s, _root_.GD.N0111.d006136 c d h x t ≠ 0 :=
        hcont.eventually_ne hN
      have heq :
          (fun x => iteratedDeriv p
              (fun z => _root_.GD.N0111.d006137 a c d h r z t) x) =ᶠ[𝓝 s]
            (fun x => _root_.GD.N0111.d006141 a c d h r x t p 0) :=
        hne.mono (fun x hx => ih x hx)
      rw [heq.deriv_eq]
      exact _root_.GD.N0111.d006146 a c d h r s t p 0 hN

theorem d006456
    (a c d h r s t : ℝ) (p q : ℕ)
    (hN : _root_.GD.N0111.d006136 c d h s t ≠ 0) :
    iteratedDeriv p
        (fun x => iteratedDeriv q
          (fun y => _root_.GD.N0111.d006137 a c d h r x y) t) s =
      _root_.GD.N0111.d006141 a c d h r s t p q := by
  induction p generalizing s with
  | zero =>
      simpa using _root_.GD.N0132.d006454
        a c d h r s t q hN
  | succ p ih =>
      rw [iteratedDeriv_succ]
      have hcont :
          ContinuousAt (fun x => _root_.GD.N0111.d006136 c d h x t) s :=
        (_root_.GD.N0111.d006142 c d h s t).continuousAt
      have hne :
          ∀ᶠ x in 𝓝 s, _root_.GD.N0111.d006136 c d h x t ≠ 0 :=
        hcont.eventually_ne hN
      have heq :
          (fun x => iteratedDeriv p
              (fun z => iteratedDeriv q
                (fun y => _root_.GD.N0111.d006137 a c d h r z y) t) x) =ᶠ[𝓝 s]
            (fun x => _root_.GD.N0111.d006141 a c d h r x t p q) :=
        hne.mono (fun x hx => ih x hx)
      rw [heq.deriv_eq]
      exact _root_.GD.N0111.d006146 a c d h r s t p q hN

theorem d006457
    (a c d h r s t : ℝ) (p q : ℕ)
    (hN : _root_.GD.N0111.d006136 c d h s t ≠ 0) :
    HasDerivAt
      (fun y => _root_.GD.N0111.d006141 a c d h r s y p q)
      (_root_.GD.N0111.d006141 a c d h r s t p (q + 1)) t := by
  have hp :=
    _root_.GD.N0111.d006145 c d h r s t p q hN
  have hp' :=
    _root_.GD.N0111.d006145 c d h r s t (p - 1) q hN
  have hmain := hp.const_mul (a + s)
  have htail := hp'.const_mul (p : ℝ)
  have hsum := hmain.add htail
  change HasDerivAt
    ((fun y => (a + s) * _root_.GD.N0111.d006140 c d h r s y p q) +
      fun y => (p : ℝ) * _root_.GD.N0111.d006140 c d h r s y (p - 1) q)
    ((a + s) * _root_.GD.N0111.d006140 c d h r s t p (q + 1) +
      (p : ℝ) * _root_.GD.N0111.d006140 c d h r s t (p - 1) (q + 1)) t
  exact hsum

theorem d006458
    {α β e r s t : ℝ} (p : ℕ)
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hs : |s| ≤ _root_.GD.N0132.d006442 α β) (ht : 0 ≤ t) :
    iteratedDeriv p (fun x => _root_.GD.N0132.d006445 α β e r x t) s =
      _root_.GD.N0132.d006446 α β e r s t p 0 := by
  apply _root_.GD.N0132.d006455
  exact (_root_.GD.N0132.d006453 hα hβ he0 he1 hs ht).ne'

theorem d006459
    {α β e r s t : ℝ} (q : ℕ)
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hs : |s| ≤ _root_.GD.N0132.d006442 α β) (ht : 0 ≤ t) :
    iteratedDeriv q (fun y => _root_.GD.N0132.d006445 α β e r s y) t =
      _root_.GD.N0132.d006446 α β e r s t 0 q := by
  apply _root_.GD.N0132.d006454
  exact (_root_.GD.N0132.d006453 hα hβ he0 he1 hs ht).ne'



theorem d006460
    (a c d h r t : ℝ) (k : ℕ) (S : Set ℝ)
    (hN : ∀ s ∈ S, _root_.GD.N0111.d006136 c d h s t ≠ 0) :
    ContDiffOn ℝ k (fun s => _root_.GD.N0111.d006137 a c d h r s t) S := by
  have hden :
      ContDiff ℝ k (fun s => _root_.GD.N0111.d006136 c d h s t) := by
    simp only [_root_.GD.N0111.d006136]
    fun_prop
  have hpow :
      ContDiffOn ℝ k (fun s => _root_.GD.N0111.d006136 c d h s t ^ (-r)) S :=
    hden.contDiffOn.rpow_const_of_ne hN
  have hnum : ContDiffOn ℝ k (fun s : ℝ => a + s) S := by
    fun_prop
  simpa [_root_.GD.N0111.d006137] using hnum.mul hpow

theorem d006461
    (a c d h r s : ℝ) (k : ℕ) (S : Set ℝ)
    (hN : ∀ t ∈ S, _root_.GD.N0111.d006136 c d h s t ≠ 0) :
    ContDiffOn ℝ k (fun t => _root_.GD.N0111.d006137 a c d h r s t) S := by
  have hden :
      ContDiff ℝ k (fun t => _root_.GD.N0111.d006136 c d h s t) := by
    simp only [_root_.GD.N0111.d006136]
    fun_prop
  have hpow :
      ContDiffOn ℝ k (fun t => _root_.GD.N0111.d006136 c d h s t ^ (-r)) S :=
    hden.contDiffOn.rpow_const_of_ne hN
  have hnum : ContDiffOn ℝ k (fun _ : ℝ => a + s) S := by
    fun_prop
  simpa [_root_.GD.N0111.d006137] using hnum.mul hpow

theorem d006462
    {α β e r t : ℝ} (k : ℕ) (S : Set ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hS : ∀ s ∈ S, |s| ≤ _root_.GD.N0132.d006442 α β)
    (ht : 0 ≤ t) :
    ContDiffOn ℝ k (fun s => _root_.GD.N0132.d006445 α β e r s t) S := by
  apply _root_.GD.N0132.d006460
  intro s hs
  exact (_root_.GD.N0132.d006453 hα hβ he0 he1 (hS s hs) ht).ne'

theorem d006463
    {α β e r s : ℝ} (k : ℕ) (S : Set ℝ)
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hs : |s| ≤ _root_.GD.N0132.d006442 α β)
    (hS : ∀ t ∈ S, 0 ≤ t) :
    ContDiffOn ℝ k (fun t => _root_.GD.N0132.d006445 α β e r s t) S := by
  apply _root_.GD.N0132.d006461
  intro t ht
  exact (_root_.GD.N0132.d006453 hα hβ he0 he1 hs (hS t ht)).ne'



theorem d006464
    {α β e r : ℝ} {N : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hr : 0 ≤ r) (hN : 1 ≤ N) :
    |_root_.GD.N0110.d006121
          (fun s => _root_.GD.N0132.d006445 α β e r s (_root_.GD.N0132.d006444 α β N))
          (_root_.GD.N0132.d006443 α β N) -
        _root_.GD.N0132.d006446 α β e r 0 (_root_.GD.N0132.d006444 α β N) 1 0|
      ≤ _root_.GD.N0111.d006160 α β r 3 0 *
          _root_.GD.N0132.d006443 α β N ^ 2 / 6 := by
  let hs := _root_.GD.N0132.d006443 α β N
  let η := _root_.GD.N0132.d006444 α β N
  have hhs : 0 < hs := by simpa [hs] using _root_.GD.N0132.d006448 hα hβ hN
  have hη : 0 < η := by simpa [η] using _root_.GD.N0132.d006449 hα hβ hN
  rw [← _root_.GD.N0132.d006458 1 hα hβ he0 he1
    (by simpa using (_root_.GD.N0132.d006447 hα hβ).le) hη.le]
  apply _root_.GD.N0112.d006174
  · exact hhs
  · apply _root_.GD.N0132.d006462 3
      (Icc (-hs) hs) hα hβ he0 he1
    · intro s hsI
      simpa [hs] using _root_.GD.N0132.d006452
        hα hβ hN hsI
    · exact hη.le
  · intro s hsI
    rw [_root_.GD.N0132.d006458 3 hα hβ he0 he1
      (by simpa [hs] using
        _root_.GD.N0132.d006452 hα hβ hN hsI) hη.le]
    apply _root_.GD.N0111.d006168 hα hβ he0 he1
      (by simpa [_root_.GD.N0132.d006442] using
        _root_.GD.N0132.d006452 hα hβ hN hsI)
      hη.le hr

theorem d006465
    {α β e r : ℝ} {N : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hr : 0 ≤ r) (hN : 1 ≤ N) :
    |_root_.GD.N0110.d006122
          (fun s => _root_.GD.N0132.d006445 α β e r s (_root_.GD.N0132.d006444 α β N))
          (_root_.GD.N0132.d006443 α β N) -
        _root_.GD.N0132.d006446 α β e r 0 (_root_.GD.N0132.d006444 α β N) 2 0|
      ≤ _root_.GD.N0111.d006160 α β r 4 0 *
          _root_.GD.N0132.d006443 α β N ^ 2 / 12 := by
  let hs := _root_.GD.N0132.d006443 α β N
  let η := _root_.GD.N0132.d006444 α β N
  have hhs : 0 < hs := by simpa [hs] using _root_.GD.N0132.d006448 hα hβ hN
  have hη : 0 < η := by simpa [η] using _root_.GD.N0132.d006449 hα hβ hN
  rw [← _root_.GD.N0132.d006458 2 hα hβ he0 he1
    (by simpa using (_root_.GD.N0132.d006447 hα hβ).le) hη.le]
  apply _root_.GD.N0112.d006175
  · exact hhs
  · apply _root_.GD.N0132.d006462 4
      (Icc (-hs) hs) hα hβ he0 he1
    · intro s hsI
      simpa [hs] using _root_.GD.N0132.d006452
        hα hβ hN hsI
    · exact hη.le
  · intro s hsI
    rw [_root_.GD.N0132.d006458 4 hα hβ he0 he1
      (by simpa [hs] using
        _root_.GD.N0132.d006452 hα hβ hN hsI) hη.le]
    apply _root_.GD.N0111.d006168 hα hβ he0 he1
      (by simpa [_root_.GD.N0132.d006442] using
        _root_.GD.N0132.d006452 hα hβ hN hsI)
      hη.le hr

theorem d006466
    {α β e r : ℝ} {N : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hr : 0 ≤ r) (hN : 1 ≤ N) :
    |_root_.GD.N0110.d006123
          (fun s => _root_.GD.N0132.d006445 α β e r s (_root_.GD.N0132.d006444 α β N))
          (_root_.GD.N0132.d006443 α β N) -
        _root_.GD.N0132.d006446 α β e r 0 (_root_.GD.N0132.d006444 α β N) 3 0|
      ≤ (17 / 60 : ℝ) * _root_.GD.N0111.d006160 α β r 5 0 *
          _root_.GD.N0132.d006443 α β N ^ 2 := by
  let hs := _root_.GD.N0132.d006443 α β N
  let η := _root_.GD.N0132.d006444 α β N
  have hhs : 0 < hs := by simpa [hs] using _root_.GD.N0132.d006448 hα hβ hN
  have hη : 0 < η := by simpa [η] using _root_.GD.N0132.d006449 hα hβ hN
  rw [← _root_.GD.N0132.d006458 3 hα hβ he0 he1
    (by simpa using (_root_.GD.N0132.d006447 hα hβ).le) hη.le]
  apply _root_.GD.N0112.d006176
  · exact hhs
  · apply _root_.GD.N0132.d006462 5
      (Icc (-2 * hs) (2 * hs)) hα hβ he0 he1
    · intro s hsI
      simpa [hs] using _root_.GD.N0132.d006451
        hα hβ hN hsI
    · exact hη.le
  · intro s hsI
    rw [_root_.GD.N0132.d006458 5 hα hβ he0 he1
      (by simpa [hs] using
        _root_.GD.N0132.d006451 hα hβ hN hsI) hη.le]
    apply _root_.GD.N0111.d006168 hα hβ he0 he1
      (by simpa [_root_.GD.N0132.d006442] using
        _root_.GD.N0132.d006451 hα hβ hN hsI)
      hη.le hr



theorem d006467
    {α β r : ℝ} (p q : ℕ)
    (hα : 0 < α) (hβ : 0 < β) (hr : 0 ≤ r) :
    0 ≤ _root_.GD.N0111.d006160 α β r p q := by
  have hmax : 0 ≤ max α β :=
    hα.le.trans (le_max_left α β)
  have hL : 0 < _root_.GD.N0111.d006159 α β := _root_.GD.N0111.d006167 hα hβ
  have htight (k : ℕ) : 0 ≤ _root_.GD.N0111.d006153
      (_root_.GD.N0111.d006159 α β) r k := by
    unfold _root_.GD.N0111.d006153
    split_ifs <;> positivity
  unfold _root_.GD.N0111.d006160
  have hrise0 := _root_.GD.N0111.d006151 r hr (p + q)
  have hrise1 := _root_.GD.N0111.d006151 r hr ((p - 1) + q)
  have hpow0 := htight (p + q)
  have hpow1 := htight ((p - 1) + q)
  apply add_nonneg <;> positivity

theorem d006468
    {α β e r : ℝ} {N : ℕ} (p q : ℕ)
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hr : 0 ≤ r) (hN : 1 ≤ N) :
    |_root_.GD.N0132.d006446 α β e r 0 (_root_.GD.N0132.d006444 α β N) p q -
        _root_.GD.N0132.d006446 α β e r 0 0 p q|
      ≤ _root_.GD.N0132.d006444 α β N *
          _root_.GD.N0111.d006160 α β r p (q + 1) := by
  let η := _root_.GD.N0132.d006444 α β N
  let B := _root_.GD.N0111.d006160 α β r p (q + 1)
  have hη : 0 < η := by simpa [η] using _root_.GD.N0132.d006449 hα hβ hN
  have hzero : |(0 : ℝ)| ≤ _root_.GD.N0132.d006442 α β := by
    simpa using (_root_.GD.N0132.d006447 hα hβ).le
  have hf :
      ∀ t ∈ Icc (0 : ℝ) η,
        HasDerivWithinAt
          (fun y => _root_.GD.N0132.d006446 α β e r 0 y p q)
          (_root_.GD.N0132.d006446 α β e r 0 t p (q + 1))
          (Icc (0 : ℝ) η) t := by
    intro t ht
    apply HasDerivAt.hasDerivWithinAt
    apply _root_.GD.N0132.d006457
    exact (_root_.GD.N0132.d006453 hα hβ he0 he1 hzero ht.1).ne'
  have hbound :
      ∀ t ∈ Ico (0 : ℝ) η,
        ‖_root_.GD.N0132.d006446 α β e r 0 t p (q + 1)‖ ≤ B := by
    intro t ht
    rw [Real.norm_eq_abs]
    simpa [B, _root_.GD.N0132.d006446, _root_.GD.N0132.d006442] using
      (_root_.GD.N0111.d006168 hα hβ he0 he1
        (by simpa [_root_.GD.N0132.d006442] using hzero) ht.1 hr :
        |_root_.GD.N0132.d006446 α β e r 0 t p (q + 1)| ≤
          _root_.GD.N0111.d006160 α β r p (q + 1))
  have hseg :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      hf hbound η (right_mem_Icc.mpr hη.le)
  simpa [η, B, Real.norm_eq_abs, mul_comm] using hseg

theorem d006469
    {α β e r : ℝ} {N : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hr : 0 ≤ r) (hN : 1 ≤ N) :
    |_root_.GD.N0110.d006121
          (fun s => _root_.GD.N0132.d006445 α β e r s (_root_.GD.N0132.d006444 α β N))
          (_root_.GD.N0132.d006443 α β N) -
        _root_.GD.N0132.d006446 α β e r 0 0 1 0|
      ≤ _root_.GD.N0132.d006444 α β N * _root_.GD.N0111.d006160 α β r 1 1 +
          _root_.GD.N0111.d006160 α β r 3 0 *
            _root_.GD.N0132.d006443 α β N ^ 2 / 6 := by
  apply _root_.GD.N0110.d006132
    (atEta := _root_.GD.N0132.d006446 α β e r 0 (_root_.GD.N0132.d006444 α β N) 1 0)
  · exact _root_.GD.N0132.d006464 hα hβ he0 he1 hr hN
  · exact _root_.GD.N0132.d006468 1 0 hα hβ he0 he1 hr hN

theorem d006470
    {α β e r : ℝ} {N : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hr : 0 ≤ r) (hN : 1 ≤ N) :
    |_root_.GD.N0110.d006122
          (fun s => _root_.GD.N0132.d006445 α β e r s (_root_.GD.N0132.d006444 α β N))
          (_root_.GD.N0132.d006443 α β N) -
        _root_.GD.N0132.d006446 α β e r 0 0 2 0|
      ≤ _root_.GD.N0132.d006444 α β N * _root_.GD.N0111.d006160 α β r 2 1 +
          _root_.GD.N0111.d006160 α β r 4 0 *
            _root_.GD.N0132.d006443 α β N ^ 2 / 12 := by
  apply _root_.GD.N0110.d006133
    (atEta := _root_.GD.N0132.d006446 α β e r 0 (_root_.GD.N0132.d006444 α β N) 2 0)
  · exact _root_.GD.N0132.d006465 hα hβ he0 he1 hr hN
  · exact _root_.GD.N0132.d006468 2 0 hα hβ he0 he1 hr hN

theorem d006471
    {α β e r : ℝ} {N : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hr : 0 ≤ r) (hN : 1 ≤ N) :
    |_root_.GD.N0110.d006123
          (fun s => _root_.GD.N0132.d006445 α β e r s (_root_.GD.N0132.d006444 α β N))
          (_root_.GD.N0132.d006443 α β N) -
        _root_.GD.N0132.d006446 α β e r 0 0 3 0|
      ≤ _root_.GD.N0132.d006444 α β N * _root_.GD.N0111.d006160 α β r 3 1 +
          (17 / 60 : ℝ) * _root_.GD.N0111.d006160 α β r 5 0 *
            _root_.GD.N0132.d006443 α β N ^ 2 := by
  apply _root_.GD.N0110.d006134
    (atEta := _root_.GD.N0132.d006446 α β e r 0 (_root_.GD.N0132.d006444 α β N) 3 0)
  · exact _root_.GD.N0132.d006466 hα hβ he0 he1 hr hN
  · exact _root_.GD.N0132.d006468 3 0 hα hβ he0 he1 hr hN

end GD.N0132
