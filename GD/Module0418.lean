import GD.Module0417















noncomputable section

open Set
open scoped Topology

namespace GD.N0130

open _root_.GD.N0111
open _root_.GD.N0110
open _root_.GD.N0112
open _root_.GD.N0132

def d006472
    (α β e r : ℝ) (N : ℕ) (s : ℝ) : ℝ :=
  _root_.GD.N0110.d006130
    (fun t => _root_.GD.N0132.d006445 α β e r s t)
    (_root_.GD.N0132.d006444 α β N)

theorem d006473
    {α β e r s t : ℝ} (k : ℕ)
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hs : |s| ≤ _root_.GD.N0132.d006442 α β) (ht : 0 ≤ t) :
    ContDiffAt ℝ k (fun x => _root_.GD.N0132.d006445 α β e r x t) s := by
  let a := α / (α + β) - e
  let c := α * β / (α + β)
  let d := β - (α + β) * e
  let h := e * (1 - e) / 2
  have hN : _root_.GD.N0111.d006136 c d h s t ≠ 0 := by
    exact (_root_.GD.N0132.d006453 hα hβ he0 he1 hs ht).ne'
  have hden : ContDiffAt ℝ k (fun x => _root_.GD.N0111.d006136 c d h x t) s := by
    simp only [_root_.GD.N0111.d006136]
    fun_prop
  have hpow :
      ContDiffAt ℝ k (fun x => _root_.GD.N0111.d006136 c d h x t ^ (-r)) s :=
    hden.rpow_const_of_ne hN
  have hnum : ContDiffAt ℝ k (fun x : ℝ => a + x) s := by
    fun_prop
  simpa [_root_.GD.N0132.d006445, _root_.GD.N0111.d006137, a, c, d, h] using hnum.mul hpow




theorem d006474
    {α β e r s : ℝ} {N : ℕ} (p q : ℕ)
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hr : 0 ≤ r) (hN : 1 ≤ N)
    (hs : |s| ≤ _root_.GD.N0132.d006442 α β) :
    |_root_.GD.N0110.d006130
        (fun t => _root_.GD.N0132.d006446 α β e r s t p q)
        (_root_.GD.N0132.d006444 α β N)|
      ≤ _root_.GD.N0111.d006160 α β r p (q + 1) := by
  let η := _root_.GD.N0132.d006444 α β N
  let B := _root_.GD.N0111.d006160 α β r p (q + 1)
  have hη : 0 < η := by
    simpa [η] using _root_.GD.N0132.d006449 hα hβ hN
  have hf :
      ∀ t ∈ Icc η (2 * η),
        HasDerivWithinAt
          (fun y => _root_.GD.N0132.d006446 α β e r s y p q)
          (_root_.GD.N0132.d006446 α β e r s t p (q + 1))
          (Icc η (2 * η)) t := by
    intro t ht
    apply HasDerivAt.hasDerivWithinAt
    apply _root_.GD.N0132.d006457
    exact (_root_.GD.N0132.d006453 hα hβ he0 he1 hs
      (by linarith [ht.1, hη])).ne'
  have hbound :
      ∀ t ∈ Ico η (2 * η),
        ‖_root_.GD.N0132.d006446 α β e r s t p (q + 1)‖ ≤ B := by
    intro t ht
    rw [Real.norm_eq_abs]
    simpa [B, _root_.GD.N0132.d006446, _root_.GD.N0132.d006442] using
      (_root_.GD.N0111.d006168 hα hβ he0 he1
        (by simpa [_root_.GD.N0132.d006442] using hs)
        (by linarith [ht.1, hη]) hr :
        |_root_.GD.N0132.d006446 α β e r s t p (q + 1)| ≤
          _root_.GD.N0111.d006160 α β r p (q + 1))
  have hseg :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      hf hbound (2 * η) (right_mem_Icc.mpr (by linarith))
  have hdiff :
      |_root_.GD.N0132.d006446 α β e r s (2 * η) p q -
          _root_.GD.N0132.d006446 α β e r s η p q| ≤ B * η := by
    calc
      |_root_.GD.N0132.d006446 α β e r s (2 * η) p q -
          _root_.GD.N0132.d006446 α β e r s η p q|
          ≤ B * (2 * η - η) := by
            simpa [Real.norm_eq_abs] using hseg
      _ = B * η := by ring
  unfold _root_.GD.N0110.d006130
  rw [abs_div, abs_of_pos hη]
  exact (div_le_iff₀ hη).2 (by
    calc
      |_root_.GD.N0132.d006446 α β e r s (2 * η) p q -
          _root_.GD.N0132.d006446 α β e r s η p q| ≤ B * η := hdiff
      _ = B * η := rfl)



theorem d006475
    {α β e r s : ℝ} {N : ℕ} (p q : ℕ)
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hr : 0 ≤ r) (hN : 1 ≤ N)
    (hs : |s| ≤ _root_.GD.N0132.d006442 α β) :
    |_root_.GD.N0110.d006130
          (fun t => _root_.GD.N0132.d006446 α β e r s t p q)
          (_root_.GD.N0132.d006444 α β N) -
        _root_.GD.N0132.d006446 α β e r s 0 p (q + 1)|
      ≤ 2 * _root_.GD.N0132.d006444 α β N *
          _root_.GD.N0111.d006160 α β r p (q + 2) := by
  let η := _root_.GD.N0132.d006444 α β N
  let f := fun t => _root_.GD.N0132.d006446 α β e r s t p q
  let f' := fun t => _root_.GD.N0132.d006446 α β e r s t p (q + 1)
  let f'' := fun t => _root_.GD.N0132.d006446 α β e r s t p (q + 2)
  let B := _root_.GD.N0111.d006160 α β r p (q + 2)
  have hη : 0 < η := by
    simpa [η] using _root_.GD.N0132.d006449 hα hβ hN
  apply _root_.GD.N0110.d006131 f f' f'' η B hη
    (_root_.GD.N0132.d006467 p (q + 2) hα hβ hr)
  · intro t ht
    apply HasDerivAt.hasDerivWithinAt
    apply _root_.GD.N0132.d006457
    exact (_root_.GD.N0132.d006453 hα hβ he0 he1 hs
      (by linarith [ht.1, hη])).ne'
  · intro t ht
    apply HasDerivAt.hasDerivWithinAt
    apply _root_.GD.N0132.d006457
    exact (_root_.GD.N0132.d006453 hα hβ he0 he1 hs ht.1).ne'
  · intro t ht
    simpa [f'', B, Real.norm_eq_abs, _root_.GD.N0132.d006446, _root_.GD.N0132.d006442] using
      (_root_.GD.N0111.d006168 hα hβ he0 he1
        (by simpa [_root_.GD.N0132.d006442] using hs) ht.1 hr :
        |_root_.GD.N0132.d006446 α β e r s t p (q + 2)| ≤
          _root_.GD.N0111.d006160 α β r p (q + 2))

theorem d006476
    {α β e r : ℝ} {N : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hr : 0 ≤ r) (hN : 1 ≤ N) :
    |_root_.GD.N0110.d006130
          (fun t => _root_.GD.N0132.d006445 α β e r 0 t)
          (_root_.GD.N0132.d006444 α β N) -
        _root_.GD.N0132.d006446 α β e r 0 0 0 1|
      ≤ 2 * _root_.GD.N0132.d006444 α β N *
          _root_.GD.N0111.d006160 α β r 0 2 := by
  simpa [_root_.GD.N0132.d006446, _root_.GD.N0132.d006445, _root_.GD.N0111.d006148] using
    (_root_.GD.N0130.d006475 0 0 hα hβ he0 he1 hr hN
      (by simpa using (_root_.GD.N0132.d006447 hα hβ).le))

theorem d006477
    {α β e r s : ℝ} {N : ℕ} (p : ℕ)
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hN : 1 ≤ N)
    (hs : |s| ≤ _root_.GD.N0132.d006442 α β) :
    iteratedDeriv p (fun x => _root_.GD.N0130.d006472 α β e r N x) s =
      _root_.GD.N0110.d006130
        (fun t => _root_.GD.N0132.d006446 α β e r s t p 0)
        (_root_.GD.N0132.d006444 α β N) := by
  let η := _root_.GD.N0132.d006444 α β N
  have hη : 0 < η := by
    simpa [η] using _root_.GD.N0132.d006449 hα hβ hN
  have h2 :
      ContDiffAt ℝ p
        (fun x => _root_.GD.N0132.d006445 α β e r x (2 * η)) s :=
    _root_.GD.N0130.d006473 p hα hβ he0 he1 hs
      (by positivity)
  have h1 :
      ContDiffAt ℝ p
        (fun x => _root_.GD.N0132.d006445 α β e r x η) s :=
    _root_.GD.N0130.d006473 p hα hβ he0 he1 hs hη.le
  unfold _root_.GD.N0130.d006472 _root_.GD.N0110.d006130
  rw [iteratedDeriv_div_const]
  rw [iteratedDeriv_fun_sub h2 h1]
  rw [_root_.GD.N0132.d006458 p hα hβ he0 he1 hs
    (by positivity)]
  rw [_root_.GD.N0132.d006458 p hα hβ he0 he1 hs hη.le]

theorem d006478
    {α β e r : ℝ} {N : ℕ} (k : ℕ)
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hN : 1 ≤ N) :
    ContDiffOn ℝ k
      (fun s => _root_.GD.N0130.d006472 α β e r N s)
      (Icc (-_root_.GD.N0132.d006443 α β N) (_root_.GD.N0132.d006443 α β N)) := by
  let hs := _root_.GD.N0132.d006443 α β N
  let η := _root_.GD.N0132.d006444 α β N
  have hη : 0 < η := by
    simpa [η] using _root_.GD.N0132.d006449 hα hβ hN
  have hS :
      ∀ s ∈ Icc (-hs) hs, |s| ≤ _root_.GD.N0132.d006442 α β := by
    intro s hsI
    simpa [hs] using
      _root_.GD.N0132.d006452 hα hβ hN hsI
  have h2 :=
    _root_.GD.N0132.d006462 (r := r) k (Icc (-hs) hs)
      hα hβ he0 he1 hS (by positivity : 0 ≤ 2 * η)
  have h1 :=
    _root_.GD.N0132.d006462 (r := r) k (Icc (-hs) hs)
      hα hβ he0 he1 hS hη.le
  simpa [_root_.GD.N0130.d006472, _root_.GD.N0110.d006130, hs, η] using
    (h2.sub h1).div_const η

theorem d006479
    {α β e r : ℝ} {N : ℕ}
    (hα : 0 < α) (hβ : 0 < β)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hr : 0 ≤ r) (hN : 1 ≤ N) :
    |_root_.GD.N0110.d006121
          (fun s => _root_.GD.N0130.d006472 α β e r N s)
          (_root_.GD.N0132.d006443 α β N) -
        _root_.GD.N0132.d006446 α β e r 0 0 1 1|
      ≤ 2 * _root_.GD.N0132.d006444 α β N *
            _root_.GD.N0111.d006160 α β r 1 2 +
          _root_.GD.N0111.d006160 α β r 3 1 *
            _root_.GD.N0132.d006443 α β N ^ 2 / 6 := by
  let hs := _root_.GD.N0132.d006443 α β N
  let η := _root_.GD.N0132.d006444 α β N
  let forwardTarget :=
    _root_.GD.N0110.d006130
      (fun t => _root_.GD.N0132.d006446 α β e r 0 t 1 0) η
  have hhs : 0 < hs := by
    simpa [hs] using _root_.GD.N0132.d006448 hα hβ hN
  have hη : 0 < η := by
    simpa [η] using _root_.GD.N0132.d006449 hα hβ hN
  apply _root_.GD.N0110.d006135
    (forwardTarget := forwardTarget)
  · dsimp [forwardTarget]
    rw [← _root_.GD.N0130.d006477
      (α := α) (β := β) (e := e) (r := r) (s := 0) (N := N)
      1 hα hβ he0 he1 hN
      (by simpa using (_root_.GD.N0132.d006447 hα hβ).le)]
    apply _root_.GD.N0112.d006174
    · exact hhs
    · simpa [hs] using
        _root_.GD.N0130.d006478 3 hα hβ he0 he1 hN
    · intro s hsI
      rw [_root_.GD.N0130.d006477 3 hα hβ he0 he1 hN
        (by simpa [hs] using
          _root_.GD.N0132.d006452 hα hβ hN hsI)]
      exact _root_.GD.N0130.d006474 3 0 hα hβ he0 he1 hr hN
        (by simpa [hs] using
          _root_.GD.N0132.d006452 hα hβ hN hsI)
  · simpa [forwardTarget, η] using
      (_root_.GD.N0130.d006475 1 0 hα hβ he0 he1 hr hN
        (by simpa using (_root_.GD.N0132.d006447 hα hβ).le))

end GD.N0130
