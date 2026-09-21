import GD.Module0091
import GD.Module0930
import GD.Module0963















open Filter MeasureTheory Set
open scoped ENNReal

namespace GD.N0232.N0720.N1257

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1214
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0232.N0720.N1159
open _root_.GD.N0230.N0602
open _root_.GD.N0230.N0633
open _root_.GD.N0232.N0719.N0946
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ)



def d015508 (theta : _root_.GD.N0232.N0720.N1080.d014168) : ℝ :=
  ((m : ℝ) / theta.scale₁ ^ 2 + (n : ℝ) / theta.scale₂ ^ 2)⁻¹

theorem d015509 (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    0 ≤ _root_.GD.N0232.N0720.N1257.d015508 m n theta := by
  unfold _root_.GD.N0232.N0720.N1257.d015508
  positivity

theorem d015510 (hm : 1 ≤ m) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    0 < _root_.GD.N0232.N0720.N1257.d015508 m n theta := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  unfold _root_.GD.N0232.N0720.N1257.d015508
  exact inv_pos.mpr (add_pos_of_pos_of_nonneg
    (div_pos hm' (sq_pos_of_pos theta.scale₁_pos)) (by positivity))

@[simp] theorem d015511 :
    _root_.GD.N0232.N0720.N1257.d015508 m n _root_.GD.N0232.N0720.N1080.d014169 = ((m : ℝ) + (n : ℝ))⁻¹ := by
  simp [_root_.GD.N0232.N0720.N1257.d015508, _root_.GD.N0232.N0720.N1080.d014169]

theorem d015512 (g : _root_.GD.N0232.N0719.N0946.d009229) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0232.N0720.N1257.d015508 m n (_root_.GD.N0232.N0720.N1215.d014272 g theta) =
      g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1257.d015508 m n theta := by
  have ha : g.d009239 ≠ 0 := ne_of_gt g.d009240
  have hs : theta.scale₁ ≠ 0 := ne_of_gt theta.scale₁_pos
  have ht : theta.scale₂ ≠ 0 := ne_of_gt theta.scale₂_pos
  have hprec :
      (m : ℝ) / (g.d009239 * theta.scale₁) ^ 2 +
          (n : ℝ) / (g.d009239 * theta.scale₂) ^ 2 =
        (g.d009239 ^ 2)⁻¹ *
          ((m : ℝ) / theta.scale₁ ^ 2 + (n : ℝ) / theta.scale₂ ^ 2) := by
    field_simp
  unfold _root_.GD.N0232.N0720.N1257.d015508
  simp only [_root_.GD.N0232.N0720.N1215.d014274, _root_.GD.N0232.N0720.N1215.d014275, hprec,
    mul_inv_rev, inv_inv]
  ring


def d015513 (C : ℝ) : Set (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) :=
  {p | ∀ theta, _root_.GD.N0232.N0720.N1080.d014182 m n theta p ≤ ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta)}

theorem d015514 (C : ℝ) : IsClosed (_root_.GD.N0232.N0720.N1257.d015513 m n C) := by
  simpa [_root_.GD.N0232.N0720.N1257.d015513, _root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000122 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n) _root_.GD.N0232.N0720.N1080.d014168.location
      (fun theta ↦ ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta))
      (_root_.GD.N0232.N0720.N1080.d014173 m n))

theorem d015515 (C : ℝ) : Convex ℝ (_root_.GD.N0232.N0720.N1257.d015513 m n C) := by
  simpa [_root_.GD.N0232.N0720.N1257.d015513, _root_.GD.N0232.N0720.N1080.d014182, _root_.GD.N0230.N0602.d000118] using
    (_root_.GD.N0230.N0602.d000123 (_root_.GD.N0232.N0720.N1080.d014172 m n) (_root_.GD.N0232.N0720.N1080.d014171 m n) _root_.GD.N0232.N0720.N1080.d014168.location
      (fun theta ↦ ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta))
      (_root_.GD.N0232.N0720.N1080.d014173 m n))

theorem d015516 {C : ℝ}
    {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)} (hp : p ∈ _root_.GD.N0232.N0720.N1257.d015513 m n C) :
    _root_.GD.N0232.N0720.N1159.d014637 m n p := by
  intro theta
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hp theta)

theorem d015517 {C : ℝ} (hC : 0 ≤ C)
    {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)} (hp : p ∈ _root_.GD.N0232.N0720.N1257.d015513 m n C) :
    ‖p‖ ^ 2 ≤ C * _root_.GD.N0232.N0720.N1257.d015508 m n _root_.GD.N0232.N0720.N1080.d014169 := by
  have href := hp _root_.GD.N0232.N0720.N1080.d014169
  rw [_root_.GD.N0232.N0720.N1080.d014190 m n] at href
  simp only [zero_sub, norm_neg] at href
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hC (_root_.GD.N0232.N0720.N1257.d015509 m n _root_.GD.N0232.N0720.N1080.d014169))).mp href

theorem d015518 {C : ℝ} (hC : 0 ≤ C)
    {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)} (hp : p ∈ _root_.GD.N0232.N0720.N1257.d015513 m n C) :
    ‖p‖ ≤ Real.sqrt (C * _root_.GD.N0232.N0720.N1257.d015508 m n _root_.GD.N0232.N0720.N1080.d014169) := by
  have hs := Real.sq_sqrt
    (mul_nonneg hC (_root_.GD.N0232.N0720.N1257.d015509 m n _root_.GD.N0232.N0720.N1080.d014169))
  have hb := _root_.GD.N0232.N0720.N1257.d015517 m n hC hp
  nlinarith [norm_nonneg p,
    Real.sqrt_nonneg (C * _root_.GD.N0232.N0720.N1257.d015508 m n _root_.GD.N0232.N0720.N1080.d014169)]


def d015519 (C : ℝ) : Set (WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))) :=
  toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) '' _root_.GD.N0232.N0720.N1257.d015513 m n C

theorem d015520 {C : ℝ} (hC : 0 ≤ C) :
    IsCompact (_root_.GD.N0232.N0720.N1257.d015519 m n C) := by
  exact _root_.GD.N0230.N0633.d001201
    (Real.sqrt (C * _root_.GD.N0232.N0720.N1257.d015508 m n _root_.GD.N0232.N0720.N1080.d014169))
    (_root_.GD.N0232.N0720.N1257.d015515 m n C) (_root_.GD.N0232.N0720.N1257.d015514 m n C)
    (fun p hp ↦ _root_.GD.N0232.N0720.N1257.d015518 m n hC hp)

theorem d015521 (C : ℝ) : Convex ℝ (_root_.GD.N0232.N0720.N1257.d015519 m n C) := by
  exact (_root_.GD.N0232.N0720.N1257.d015515 m n C).linear_image (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))).toLinearMap

theorem d015522 (C : ℝ)
    (p : WeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))) :
    p ∈ _root_.GD.N0232.N0720.N1257.d015519 m n C ↔
      (toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))).symm p ∈ _root_.GD.N0232.N0720.N1257.d015513 m n C := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa using hq
  · intro hp
    exact ⟨_, hp, by simp⟩

theorem d015523 {C : ℝ} (_hC : 0 ≤ C)
    (g : _root_.GD.N0232.N0719.N0946.d009229) {p : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)}
    (hp : p ∈ _root_.GD.N0232.N0720.N1257.d015513 m n C) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g p (_root_.GD.N0232.N0720.N1257.d015516 m n hp) ∈ _root_.GD.N0232.N0720.N1257.d015513 m n C := by
  intro eta
  let theta := _root_.GD.N0232.N0720.N1215.d014272 g⁻¹ eta
  have heta : _root_.GD.N0232.N0720.N1215.d014272 g theta = eta := by simp [theta]
  rw [← heta, _root_.GD.N0232.N0720.N1159.d014643, _root_.GD.N0232.N0720.N1257.d015512]
  calc
    ENNReal.ofReal (g.d009239 ^ 2) * _root_.GD.N0232.N0720.N1080.d014182 m n theta p ≤
        ENNReal.ofReal (g.d009239 ^ 2) *
          ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta) := mul_le_mul' le_rfl (hp theta)
    _ = ENNReal.ofReal (C * (g.d009239 ^ 2 * _root_.GD.N0232.N0720.N1257.d015508 m n theta)) := by
      rw [← ENNReal.ofReal_mul (sq_nonneg g.d009239)]
      congr 1
      ring


def d015524 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229) : _root_.GD.N0232.N0720.N1257.d015513 m n C → _root_.GD.N0232.N0720.N1257.d015513 m n C :=
  fun p ↦ ⟨_root_.GD.N0232.N0720.N1159.d014642 m n g p.1 (_root_.GD.N0232.N0720.N1257.d015516 m n p.2),
    _root_.GD.N0232.N0720.N1257.d015523 m n hC g p.2⟩

theorem d015525 (C : ℝ) (hC : 0 ≤ C) (p : _root_.GD.N0232.N0720.N1257.d015513 m n C) :
    _root_.GD.N0232.N0720.N1257.d015524 m n C hC 1 p = p := by
  apply Subtype.ext
  exact _root_.GD.N0232.N0720.N1482.d015159
    p.1 (_root_.GD.N0232.N0720.N1257.d015516 m n p.2)

theorem d015526 (C : ℝ) (hC : 0 ≤ C) (g h : _root_.GD.N0232.N0719.N0946.d009229) (p : _root_.GD.N0232.N0720.N1257.d015513 m n C) :
    _root_.GD.N0232.N0720.N1257.d015524 m n C hC g (_root_.GD.N0232.N0720.N1257.d015524 m n C hC h p) = _root_.GD.N0232.N0720.N1257.d015524 m n C hC (g * h) p := by
  apply Subtype.ext
  exact _root_.GD.N0232.N0720.N1482.d015161
    g h p.1 (_root_.GD.N0232.N0720.N1257.d015516 m n p.2)


def d015527 (C : ℝ) : _root_.GD.N0232.N0720.N1257.d015513 m n C ≃ _root_.GD.N0232.N0720.N1257.d015519 m n C where
  toFun p := ⟨toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n)) p.1, ⟨p.1, p.2, rfl⟩⟩
  invFun p := ⟨(toWeakSpace ℝ (_root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))).symm p.1,
    (_root_.GD.N0232.N0720.N1257.d015522 m n C p.1).mp p.2⟩
  left_inv p := by apply Subtype.ext; simp
  right_inv p := by apply Subtype.ext; simp

def d015528 (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229) :
    _root_.GD.N0232.N0720.N1257.d015519 m n C → _root_.GD.N0232.N0720.N1257.d015519 m n C :=
  fun p ↦ _root_.GD.N0232.N0720.N1257.d015527 m n C (_root_.GD.N0232.N0720.N1257.d015524 m n C hC g ((_root_.GD.N0232.N0720.N1257.d015527 m n C).symm p))



theorem d015529
    (hm : 2 ≤ m) (hn : 2 ≤ n) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p q : _root_.GD.N0230.N0602.d000116 (_root_.GD.N0232.N0720.N1080.d014172 m n))
    (hp : _root_.GD.N0232.N0720.N1159.d014637 m n p) (hq : _root_.GD.N0232.N0720.N1159.d014637 m n q)
    {a b : ℝ} (hab : a + b = 1)
    (hpq : _root_.GD.N0232.N0720.N1159.d014637 m n (a • p + b • q)) :
    _root_.GD.N0232.N0720.N1159.d014642 m n g (a • p + b • q) hpq =
      a • _root_.GD.N0232.N0720.N1159.d014642 m n g p hp +
        b • _root_.GD.N0232.N0720.N1159.d014642 m n g q hq := by
  let fp := _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n p)
  let fq := _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n q)
  let fsum := _root_.GD.N0232.N0720.N1214.d014261 m n g (_root_.GD.N0232.N0720.N1214.d014265 m n (a • p + b • q))
  let hpLp : MemLp fp 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := _root_.GD.N0232.N0720.N1159.d014641 m n g p hp
  let hqLp : MemLp fq 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) := _root_.GD.N0232.N0720.N1159.d014641 m n g q hq
  let hsumLp : MemLp fsum 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1159.d014641 m n g (a • p + b • q) hpq
  let hrawsum : MemLp (fun omega ↦ a • fp omega + b • fq omega) 2
      (_root_.GD.N0232.N0720.N1080.d014172 m n) := (hpLp.const_smul a).add (hqLp.const_smul b)
  have hraw : fsum =ᵐ[_root_.GD.N0232.N0720.N1080.d014172 m n] fun omega ↦ a • fp omega + b • fq omega := by
    exact _root_.GD.N0232.N0720.N1065.d014583
      m n hm hn g p q hab
  change MemLp.toLp fsum hsumLp = a • MemLp.toLp fp hpLp + b • MemLp.toLp fq hqLp
  calc
    MemLp.toLp fsum hsumLp =
        MemLp.toLp (fun omega ↦ a • fp omega + b • fq omega) hrawsum :=
      MemLp.toLp_congr hsumLp hrawsum hraw
    _ = MemLp.toLp (a • fp) (hpLp.const_smul a) +
        MemLp.toLp (b • fq) (hqLp.const_smul b) :=
      MemLp.toLp_add (hpLp.const_smul a) (hqLp.const_smul b)
    _ = a • MemLp.toLp fp hpLp + b • MemLp.toLp fq hqLp := by
      rw [MemLp.toLp_const_smul, MemLp.toLp_const_smul]

theorem d015530
    (hm : 2 ≤ m) (hn : 2 ≤ n) (C : ℝ) (hC : 0 ≤ C) (g : _root_.GD.N0232.N0719.N0946.d009229)
    (p q : _root_.GD.N0232.N0720.N1257.d015513 m n C) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (_root_.GD.N0232.N0720.N1257.d015524 m n C hC g
      ⟨a • p.1 + b • q.1, _root_.GD.N0232.N0720.N1257.d015515 m n C p.2 q.2 ha hb hab⟩).1 =
      a • (_root_.GD.N0232.N0720.N1257.d015524 m n C hC g p).1 + b • (_root_.GD.N0232.N0720.N1257.d015524 m n C hC g q).1 := by
  exact _root_.GD.N0232.N0720.N1257.d015529 m n hm hn g p.1 q.1
    (_root_.GD.N0232.N0720.N1257.d015516 m n p.2) (_root_.GD.N0232.N0720.N1257.d015516 m n q.2) hab
    (_root_.GD.N0232.N0720.N1257.d015516 m n (_root_.GD.N0232.N0720.N1257.d015515 m n C p.2 q.2 ha hb hab))



theorem d015531 (C : ℝ)
    (d : _root_.GD.N0232.N0720.N1080.d014170 m n → ℝ) (hd : Measurable d)
    (hbound : ∀ theta, _root_.GD.N0232.N0720.N1080.d014197 m n theta d ≤
      ENNReal.ofReal (C * _root_.GD.N0232.N0720.N1257.d015508 m n theta)) :
    ∃ p ∈ _root_.GD.N0232.N0720.N1257.d015513 m n C, ∀ theta, _root_.GD.N0232.N0720.N1080.d014182 m n theta p = _root_.GD.N0232.N0720.N1080.d014197 m n theta d := by
  have hdLp : MemLp d 2 (_root_.GD.N0232.N0720.N1080.d014172 m n) :=
    _root_.GD.N0232.N0720.N1215.d014285 m n d hd
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound _root_.GD.N0232.N0720.N1080.d014169))
  refine ⟨hdLp.toLp d, ?_, ?_⟩
  · intro theta
    rw [← _root_.GD.N0232.N0720.N1080.d014198 m n theta d hdLp]
    exact hbound theta
  · intro theta
    exact (_root_.GD.N0232.N0720.N1080.d014198 m n theta d hdLp).symm

end
end GD.N0232.N0720.N1257

#print axioms _root_.GD.N0232.N0720.N1257.d015512
#print axioms _root_.GD.N0232.N0720.N1257.d015520
#print axioms _root_.GD.N0232.N0720.N1257.d015523
#print axioms _root_.GD.N0232.N0720.N1257.d015526
#print axioms _root_.GD.N0232.N0720.N1257.d015529
#print axioms _root_.GD.N0232.N0720.N1257.d015531
