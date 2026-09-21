import GD.Module0807
import GD.Module0244
import GD.Module0174

set_option autoImplicit false
set_option warningAsError true











open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace GD.N0232.N0719.N0978

noncomputable section

open _root_.GD.N0232.N0719.N0859 _root_.GD.N0232.N0719.N0896
open _root_.GD.N0232.N0719.N0965
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0632
open _root_.GD.N0230.N0560
open _root_.GD.N0230.N0622

variable {k : ℕ} {sizes : Fin k → ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]



def d012383
    (packet : ι → _root_.GD.N0232.N0719.N0859.d010809 k) (weight : ι → ℝ)
    (seed : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) : ℝ :=
  _root_.GD.N0232.N0719.N0965.d012291 packet weight seed -
    _root_.GD.N0232.N0719.N0965.d012292 (k := k) (sizes := sizes) packet weight

theorem d012384
    (packet : ι → _root_.GD.N0232.N0719.N0859.d010809 k) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (seed : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hfinite : _root_.GD.N0232.N0719.N0896.d011103 k sizes seed) :
    _root_.GD.N0232.N0719.N0978.d012383 packet weight seed =
      ∫ omega, _root_.GD.N0232.N0719.N0965.d012275 packet weight omega *
        (seed omega - _root_.GD.N0232.N0719.N0965.d012276 packet weight omega) ^ 2
        ∂_root_.GD.N0232.N0719.N0859.d010813 k sizes := by
  unfold _root_.GD.N0232.N0719.N0978.d012383
  rw [_root_.GD.N0232.N0719.N0965.d012295 packet weight hw seed
    (fun i => hfinite (packet i))]
  ring

theorem d012385
    (packet : ι → _root_.GD.N0232.N0719.N0859.d010809 k) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (seed : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hfinite : _root_.GD.N0232.N0719.N0896.d011103 k sizes seed) :
    0 ≤ _root_.GD.N0232.N0719.N0978.d012383 packet weight seed := by
  rw [_root_.GD.N0232.N0719.N0978.d012384 packet weight hw seed hfinite]
  apply integral_nonneg
  intro omega
  exact mul_nonneg
    (_root_.GD.N0230.N0617.d000169
      weight (_root_.GD.N0232.N0719.N0965.d012273 packet) hw (_root_.GD.N0232.N0719.N0965.d012279 packet) omega).le
    (sq_nonneg _)

private theorem d012386
    (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    (_root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) q).toReal = ‖q‖ ^ 2 := by
  rw [_root_.GD.N0232.N0719.N0859.d010829]
  simp only [zero_sub, norm_neg, ENNReal.toReal_ofReal (sq_nonneg _)]

private theorem d012387 (theta : _root_.GD.N0232.N0719.N0859.d010809 k)
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    _root_.GD.N0232.N0719.N0859.d010821 k sizes theta (a • p + b • q) ≤
      ENNReal.ofReal a * _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p + ENNReal.ofReal b * _root_.GD.N0232.N0719.N0859.d010821 k sizes theta q :=
  _root_.GD.N0230.N0602.d000121 (_root_.GD.N0232.N0719.N0859.d010814 k sizes theta)
    theta.location p q ha hb hab

private theorem d012388 (theta : _root_.GD.N0232.N0719.N0859.d010809 k) (c : ℝ) :
    IsClosed {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes) |
      _root_.GD.N0232.N0719.N0859.d010821 k sizes theta p ≤ ENNReal.ofReal c} := by
  simpa [_root_.GD.N0230.N0602.d000118, _root_.GD.N0232.N0719.N0859.d010821] using
    _root_.GD.N0230.N0602.d000122 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)
      (fun _ : Unit => _root_.GD.N0232.N0719.N0859.d010812 k sizes theta) (fun _ => theta.location)
      (fun _ => ENNReal.ofReal c) (fun _ => _root_.GD.N0232.N0719.N0859.d010814 k sizes theta)





theorem d012389
    (seed : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hfinite : _root_.GD.N0232.N0719.N0896.d011103 k sizes seed)
    (hminimal : ∀ q, _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) q seed → ‖seed‖ ^ 2 ≤ ‖q‖ ^ 2)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ (n : ℕ) (packet : Fin n → _root_.GD.N0232.N0719.N0859.d010809 k) (weight : Fin n → ℝ),
      (∀ i, 0 ≤ weight i) ∧ _root_.GD.N0232.N0719.N0978.d012383 packet weight seed < epsilon := by
  classical
  by_cases hsmall : ‖seed‖ ^ 2 < epsilon
  · refine ⟨0, Fin.elim0, Fin.elim0, (fun i => Fin.elim0 i), ?_⟩
    simpa [_root_.GD.N0232.N0719.N0978.d012383, _root_.GD.N0232.N0719.N0965.d012291, _root_.GD.N0232.N0719.N0965.d012292,
      _root_.GD.N0230.N0617.d000167,
      _root_.GD.N0230.N0617.d000164] using hsmall
  have hnorm : epsilon ≤ ‖seed‖ ^ 2 := le_of_not_gt hsmall
  let delta := epsilon / 2
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hdeltalt : delta < epsilon := by dsimp [delta]; linarith
  let R : Option (_root_.GD.N0232.N0719.N0859.d010809 k) → _root_.GD.N0230.N0602.d000116
      (_root_.GD.N0232.N0719.N0859.d010813 k sizes) → ℝ≥0∞ :=
    fun theta q => _root_.GD.N0232.N0719.N0859.d010821 k sizes (theta.getD (_root_.GD.N0232.N0719.N0859.d010810 k)) q
  let cap : Option (_root_.GD.N0232.N0719.N0859.d010809 k) → ℝ := fun theta =>
    match theta with
    | none => ‖seed‖ ^ 2 - delta
    | some theta => (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta seed).toReal
  have hcap : ∀ theta, 0 ≤ cap theta := by
    intro theta
    cases theta with
    | none => dsimp [cap, delta]; linarith
    | some theta => exact ENNReal.toReal_nonneg
  have hnone : ¬ ∃ q, ∀ theta, R theta q ≤ ENNReal.ofReal (cap theta) := by
    rintro ⟨q, hq⟩
    have hdom : _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) q seed := by
      intro theta
      have h := hq (some theta)
      change _root_.GD.N0232.N0719.N0859.d010821 k sizes theta q ≤ ENNReal.ofReal (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta seed).toReal at h
      rwa [ENNReal.ofReal_toReal (hfinite theta)] at h
    have hnormmin := hminimal q hdom
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hq none)
    change (_root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) q).toReal ≤
      (ENNReal.ofReal (cap none)).toReal at h
    rw [_root_.GD.N0232.N0719.N0978.d012386, ENNReal.toReal_ofReal (hcap none)] at h
    dsimp [cap] at h
    linarith
  have hdual := _root_.GD.N0230.N0632.d003536 R
    (fun theta => _root_.GD.N0232.N0719.N0978.d012387 (theta.getD (_root_.GD.N0232.N0719.N0859.d010810 k)))
    (fun theta => _root_.GD.N0232.N0719.N0978.d012388 (theta.getD (_root_.GD.N0232.N0719.N0859.d010810 k)))
    none (fun q => by
      dsimp [R]
      simpa only [zero_sub, norm_neg] using _root_.GD.N0232.N0719.N0859.d010829 k sizes q)
    ⟨seed, fun theta => hfinite (theta.getD (_root_.GD.N0232.N0719.N0859.d010810 k))⟩ cap hcap
  have hfailure := mt hdual.mpr hnone
  push Not at hfailure
  obtain ⟨F, w, hw, a, ha, hlt⟩ := hfailure
  let e : Fin F.card ≃ F := (Finset.equivFin F).symm
  let atom (i : Fin F.card) : Option (_root_.GD.N0232.N0719.N0859.d010809 k) := (e i).val
  have hsum (f : Option (_root_.GD.N0232.N0719.N0859.d010809 k) → ℝ) :
      (∑ i : Fin F.card, f (atom i)) = ∑ theta ∈ F, f theta := by
    rw [← Finset.sum_coe_sort F f]
    exact Equiv.sum_comp e (fun theta : F => f theta.val)
  let anchorWeight : Fin F.card → ℝ := fun i =>
    match atom i with
    | none => w none
    | some _ => 0
  let lambda := ∑ i, anchorWeight i
  let packet : Fin F.card → _root_.GD.N0232.N0719.N0859.d010809 k := fun i => (atom i).getD (_root_.GD.N0232.N0719.N0859.d010810 k)
  let otherWeight : Fin F.card → ℝ := fun i =>
    match atom i with
    | none => 0
    | some theta => w (some theta)
  have hatomNonneg (i : Fin F.card) : 0 ≤ w (atom i) := hw _ (e i).property
  have hotherNonneg (i : Fin F.card) : 0 ≤ otherWeight i := by
    cases hi : atom i with
    | none => simp [otherWeight, hi]
    | some theta => simpa [otherWeight, hi] using hatomNonneg i
  have hsplit (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
      (∑ theta ∈ F, w theta * (R theta q).toReal) =
        lambda * ‖q‖ ^ 2 + ∑ i, otherWeight i * (_root_.GD.N0232.N0719.N0859.d010821 k sizes (packet i) q).toReal := by
    rw [← hsum]
    dsimp [lambda]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    cases hai : atom i with
    | none => simp [R, anchorWeight, otherWeight, packet, hai, _root_.GD.N0232.N0719.N0978.d012386]
    | some theta => simp [R, anchorWeight, otherWeight, packet, hai]
  have hcapSum : (∑ theta ∈ F, w theta * cap theta) =
      (∑ theta ∈ F, w theta * (R theta seed).toReal) - delta * lambda := by
    rw [← hsum, ← hsum]
    dsimp [lambda]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    cases hai : atom i with
    | none => simp [R, cap, anchorWeight, hai, _root_.GD.N0232.N0719.N0978.d012386]; ring
    | some theta => simp [R, cap, anchorWeight, hai]
  have hseedBound := ha seed (fun theta => hfinite (theta.getD (_root_.GD.N0232.N0719.N0859.d010810 k)))
  have hlambda : 0 < lambda := by
    rw [hcapSum] at hlt
    nlinarith
  let weight (i : Fin F.card) := otherWeight i / lambda
  have hweight (i : Fin F.card) : 0 ≤ weight i := div_nonneg (hotherNonneg i) hlambda.le
  have hobjective (q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
      lambda * _root_.GD.N0232.N0719.N0965.d012291 packet weight q =
        ∑ theta ∈ F, w theta * (R theta q).toReal := by
    rw [hsplit]
    simp only [_root_.GD.N0232.N0719.N0965.d012291, mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [weight]
    field_simp [hlambda.ne']
  let q := _root_.GD.N0232.N0719.N0965.d012286 (k := k) (sizes := sizes) packet weight hweight
  have hqfinite := _root_.GD.N0232.N0719.N0965.d012288
    (k := k) (sizes := sizes) packet weight hweight
  have hqbound := ha q (fun theta => hqfinite (theta.getD (_root_.GD.N0232.N0719.N0859.d010810 k)))
  rw [← hobjective q, _root_.GD.N0232.N0719.N0965.d012297] at hqbound
  rw [hcapSum, ← hobjective seed] at hlt
  refine ⟨F.card, packet, weight, hweight, ?_⟩
  unfold _root_.GD.N0232.N0719.N0978.d012383
  nlinarith

theorem d012390
    (seed : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hfinite : _root_.GD.N0232.N0719.N0896.d011103 k sizes seed)
    (hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) seed)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ (n : ℕ) (packet : Fin n → _root_.GD.N0232.N0719.N0859.d010809 k) (weight : Fin n → ℝ),
      (∀ i, 0 ≤ weight i) ∧ _root_.GD.N0232.N0719.N0978.d012383 packet weight seed < epsilon := by
  apply _root_.GD.N0232.N0719.N0978.d012389 seed hfinite _ epsilon hepsilon
  intro q hq
  rw [hterminal q hq]



theorem d012391
    (packet : ι → _root_.GD.N0232.N0719.N0859.d010809 k) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i) :
    _root_.GD.N0230.N0622.d000607 (_root_.GD.N0230.N0632.d003532 (_root_.GD.N0232.N0719.N0859.d010821 k sizes))
      (fun theta q => (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta q).toReal) (_root_.GD.N0232.N0719.N0859.d010810 k) packet weight
      (_root_.GD.N0232.N0719.N0965.d012286 (k := k) (sizes := sizes) packet weight hw) := by
  refine ⟨hw, ?_⟩
  intro q hq
  simp only [_root_.GD.N0232.N0719.N0978.d012386]
  change _root_.GD.N0232.N0719.N0965.d012291 packet weight
      (_root_.GD.N0232.N0719.N0965.d012286 packet weight hw) ≤ _root_.GD.N0232.N0719.N0965.d012291 packet weight q
  rw [_root_.GD.N0232.N0719.N0965.d012297]
  exact sub_nonneg.mp (_root_.GD.N0232.N0719.N0978.d012385 packet weight hw q hq)

theorem d012392
    (packet : ι → _root_.GD.N0232.N0719.N0859.d010809 k) (weight : ι → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (seed : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes)) :
    _root_.GD.N0230.N0560.d000625 (fun theta q => (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta q).toReal) (_root_.GD.N0232.N0719.N0859.d010810 k)
      packet weight seed (_root_.GD.N0232.N0719.N0965.d012286 (k := k) (sizes := sizes) packet weight hw) =
      _root_.GD.N0232.N0719.N0978.d012383 packet weight seed := by
  unfold _root_.GD.N0230.N0560.d000625 _root_.GD.N0230.N0560.d000624
  simp only [_root_.GD.N0232.N0719.N0978.d012386]
  change _root_.GD.N0232.N0719.N0965.d012291 packet weight seed -
      _root_.GD.N0232.N0719.N0965.d012291 packet weight (_root_.GD.N0232.N0719.N0965.d012286 packet weight hw) = _
  rw [_root_.GD.N0232.N0719.N0965.d012297]
  rfl



theorem d012393
    (seed : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hfinite : _root_.GD.N0232.N0719.N0896.d011103 k sizes seed)
    (hminimal : ∀ q, _root_.GD.N0230.N0608.d000672 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) q seed → ‖seed‖ ^ 2 ≤ ‖q‖ ^ 2) :
    _root_.GD.N0230.N0560.d000632 (_root_.GD.N0230.N0632.d003532 (_root_.GD.N0232.N0719.N0859.d010821 k sizes))
      (fun theta q => (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta q).toReal) (_root_.GD.N0232.N0719.N0859.d010810 k) seed := by
  classical
  have hex (j : ℕ) := _root_.GD.N0232.N0719.N0978.d012389
    seed hfinite hminimal (1 / ((j : ℝ) + 1)) (by positivity)
  choose width packet weight hw hgap using hex
  refine ⟨width, packet, weight,
    (fun j => _root_.GD.N0232.N0719.N0965.d012286 (packet j) (weight j) (hw j)), ?_, ?_⟩
  · intro j
    exact ⟨_root_.GD.N0232.N0719.N0965.d012288 (packet j) (weight j) (hw j),
      _root_.GD.N0232.N0719.N0978.d012391 (packet j) (weight j) (hw j)⟩
  simp only [_root_.GD.N0232.N0719.N0978.d012392]
  exact squeeze_zero
    (fun j => _root_.GD.N0232.N0719.N0978.d012385 (packet j) (weight j) (hw j) seed hfinite)
    (fun j => (hgap j).le) tendsto_one_div_add_atTop_nhds_zero_nat

theorem d012394
    (seed : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hfinite : _root_.GD.N0232.N0719.N0896.d011103 k sizes seed)
    (hterminal : _root_.GD.N0230.N0608.d000674 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) seed) :
    _root_.GD.N0230.N0560.d000632 (_root_.GD.N0230.N0632.d003532 (_root_.GD.N0232.N0719.N0859.d010821 k sizes))
      (fun theta q => (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta q).toReal) (_root_.GD.N0232.N0719.N0859.d010810 k) seed := by
  apply _root_.GD.N0232.N0719.N0978.d012393 seed hfinite
  intro q hq
  rw [hterminal q hq]




theorem d012395
    (seed : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hfinite : _root_.GD.N0232.N0719.N0896.d011103 k sizes seed)
    (hadmissible : _root_.GD.N0230.N0556.d000031
      (fun theta (q : _root_.GD.N0230.N0632.d003532 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)) => (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta q).toReal)
      ⟨seed, hfinite⟩) :
    _root_.GD.N0230.N0560.d000632 (_root_.GD.N0230.N0632.d003532 (_root_.GD.N0232.N0719.N0859.d010821 k sizes))
      (fun theta q => (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta q).toReal) (_root_.GD.N0232.N0719.N0859.d010810 k) seed := by
  apply _root_.GD.N0232.N0719.N0978.d012393 seed hfinite
  intro q hq
  by_contra hnot
  have hqfinite : _root_.GD.N0232.N0719.N0896.d011103 k sizes q := fun theta =>
    ne_top_of_le_ne_top (hfinite theta) (hq theta)
  apply hadmissible
  refine ⟨⟨q, hqfinite⟩, (fun theta => ENNReal.toReal_mono (hfinite theta) (hq theta)),
    _root_.GD.N0232.N0719.N0859.d010810 k, ?_⟩
  simpa only [_root_.GD.N0232.N0719.N0978.d012386] using lt_of_not_ge hnot




theorem d012396
    (seed : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0719.N0859.d010813 k sizes))
    (hfinite : _root_.GD.N0232.N0719.N0896.d011103 k sizes seed) :
    _root_.GD.N0230.N0556.d000031
      (fun theta (q : _root_.GD.N0230.N0632.d003532 (_root_.GD.N0232.N0719.N0859.d010821 k sizes)) => (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta q).toReal)
      ⟨seed, hfinite⟩ ↔
    _root_.GD.N0230.N0560.d000632 (_root_.GD.N0230.N0632.d003532 (_root_.GD.N0232.N0719.N0859.d010821 k sizes))
      (fun theta q => (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta q).toReal) (_root_.GD.N0232.N0719.N0859.d010810 k) seed := by
  constructor
  · exact _root_.GD.N0232.N0719.N0978.d012395 seed hfinite
  · rintro ⟨width, packet, weight, p, hp, hzero⟩
    have hcombo := fun theta => _root_.GD.N0232.N0719.N0978.d012387 (k := k) (sizes := sizes) theta
    have hconvex := _root_.GD.N0230.N0632.d003533 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) hcombo
    apply _root_.GD.N0230.N0560.d000631 (_root_.GD.N0230.N0632.d003532 (_root_.GD.N0232.N0719.N0859.d010821 k sizes))
      (fun theta q => (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta q).toReal) (_root_.GD.N0232.N0719.N0859.d010810 k) seed hfinite
      hconvex (_root_.GD.N0230.N0632.d003534 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) hcombo) _
      width packet weight p (fun j => (hp j).2) hzero
    apply _root_.GD.N0230.N0622.d000620 (_root_.GD.N0230.N0632.d003532 (_root_.GD.N0232.N0719.N0859.d010821 k sizes))
      (fun q => (_root_.GD.N0232.N0719.N0859.d010821 k sizes (_root_.GD.N0232.N0719.N0859.d010810 k) q).toReal) hconvex
      1 0 (by norm_num)
    intro q hq
    simp only [_root_.GD.N0232.N0719.N0978.d012386, one_mul, add_zero]




theorem d012397
    (hk : 3 ≤ k) (hsizes : ∀ i, 2 ≤ sizes i)
    (hendpoint : _root_.GD.N0232.N0719.N0896.d011132 k sizes) :
    ∃ s : _root_.GD.N0232.N0719.N0896.d011106 k sizes,
      _root_.GD.N0230.N0608.d000675 (_root_.GD.N0232.N0719.N0859.d010821 k sizes) s.value (_root_.GD.N0232.N0719.N0859.d010819 k sizes hk hsizes) ∧
      _root_.GD.N0230.N0560.d000632 (_root_.GD.N0230.N0632.d003532 (_root_.GD.N0232.N0719.N0859.d010821 k sizes))
        (fun theta q => (_root_.GD.N0232.N0719.N0859.d010821 k sizes theta q).toReal) (_root_.GD.N0232.N0719.N0859.d010810 k) s.value := by
  obtain ⟨p, hrep, hstrict, hterminal⟩ :=
    (_root_.GD.N0232.N0719.N0896.d011133 k sizes hk hsizes).mp
      hendpoint
  let s := _root_.GD.N0232.N0719.N0896.d011129 k sizes hk hsizes p hrep hstrict
  exact ⟨s, hstrict, _root_.GD.N0232.N0719.N0978.d012394
    p s.finiteRisk hterminal⟩

end
end GD.N0232.N0719.N0978

#print axioms _root_.GD.N0232.N0719.N0978.d012384
#print axioms _root_.GD.N0232.N0719.N0978.d012390
#print axioms _root_.GD.N0232.N0719.N0978.d012391
#print axioms _root_.GD.N0232.N0719.N0978.d012394
#print axioms _root_.GD.N0232.N0719.N0978.d012395
#print axioms _root_.GD.N0232.N0719.N0978.d012396
#print axioms _root_.GD.N0232.N0719.N0978.d012397
