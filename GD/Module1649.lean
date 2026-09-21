import GD.Module0553
import GD.Module1414

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GD.N0076.N0314

noncomputable section

open _root_.GD.N0079.N0323
open _root_.GD.N0076.N0312

section Order

variable {Θ D S V : Type*} [Preorder V]
variable {R : Θ → D → V} {r : Θ → S → V}



theorem d028063 (F : _root_.GD.N0079.N0323.d008229 R r) (s : S) :
    _root_.GD.N0079.N0323.d008228 R (F.embed s) ↔ _root_.GD.N0079.N0323.d008228 r s ∧
      ∀ d, _root_.GD.N0079.N0323.d008225 R d (F.embed s) → F.project d = s → d = F.embed s := by
  constructor
  · intro h
    refine ⟨?_, fun d hd _ => h d hd⟩
    intro t ht
    exact F.d008230 (h (F.embed t) ((F.d008231 t s).mpr ht))
  · rintro ⟨ht, hf⟩
    exact (F.d008236 s hf).mpr ht


theorem d028064 (F : _root_.GD.N0079.N0323.d008229 R r) {d : D} {s : S}
    (h : ∀ θ, R θ d < R θ (F.embed s)) :
    ∀ θ, r θ (F.project d) < r θ s := by
  intro θ
  exact (lt_of_le_of_lt (F.improve θ d) (h θ)).trans_eq (F.preserve θ s)


theorem d028065 (F : _root_.GD.N0079.N0323.d008229 R r)
    {J : Type*} (B : J → Θ → V) :
    (∃ d, ∀ j θ, R θ d ≤ B j θ) ↔ (∃ s, ∀ j θ, r θ s ≤ B j θ) := by
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨F.project d, fun j θ => (F.improve θ d).trans (hd j θ)⟩
  · rintro ⟨s, hs⟩
    exact ⟨F.embed s, fun j θ => (F.preserve θ s).trans_le (hs j θ)⟩

theorem d028066 {Ξ : Type*}
    (q : Ξ → S → V) (T : Θ → Ξ) (hT : Function.Surjective T) (s t : S) :
    _root_.GD.N0079.N0323.d008225 (fun θ => q (T θ)) s t ↔ _root_.GD.N0079.N0323.d008225 q s t := by
  constructor
  · intro h ξ
    obtain ⟨θ, rfl⟩ := hT ξ
    exact h θ
  · intro h θ
    exact h (T θ)

theorem d028067 {Ξ : Type*}
    (q : Ξ → S → V) (T : Θ → Ξ) (hT : Function.Surjective T) (s : S) :
    _root_.GD.N0079.N0323.d008228 (fun θ => q (T θ)) s ↔ _root_.GD.N0079.N0323.d008228 q s := by
  simp only [_root_.GD.N0079.N0323.d008228, _root_.GD.N0076.N0314.d028066 q T hT]



theorem d028068 {Ξ : Type*}
    (q : Ξ → S → V) (T : Θ → Ξ) (hT : Function.Surjective T)
    (F : _root_.GD.N0079.N0323.d008229 R (fun θ => q (T θ))) (s : S) :
    _root_.GD.N0079.N0323.d008228 R (F.embed s) ↔ _root_.GD.N0079.N0323.d008228 q s ∧
      ∀ d, _root_.GD.N0079.N0323.d008225 R d (F.embed s) → F.project d = s → d = F.embed s := by
  rw [_root_.GD.N0076.N0314.d028063 F s, _root_.GD.N0076.N0314.d028067 q T hT]

end Order

section Kernel

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z]


def d028069 (μ : Measure X) (κ : Kernel X Y) (c : ℝ) (d : Y → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, ENNReal.ofReal ((d y - c) ^ 2) ∂κ x ∂μ

theorem d028070 (μ : Measure X) (κ : Kernel X Y)
    (c : ℝ) (d : Y → ℝ) (hd : Measurable d) :
    _root_.GD.N0076.N0314.d028069 μ κ c d = _root_.GD.N0076.N0312.d022661 (κ ∘ₘ μ) c d := by
  symm
  exact Measure.lintegral_bind κ.aemeasurable (by fun_prop)



theorem d028071 (μ : Measure X) (ν : Measure Y)
    (κ : Kernel X Y) (c : ℝ) :
    κ ∘ₘ μ = ν ↔ ∀ d : Y → ℝ, Measurable d →
      _root_.GD.N0076.N0314.d028069 μ κ c d = _root_.GD.N0076.N0312.d022661 ν c d := by
  simpa only [_root_.GD.N0076.N0314.d028069, _root_.GD.N0076.N0312.d022661] using
    _root_.GD.N0076.N0312.d022666 μ ν κ c

theorem d028072 (μ : Measure X) (ν : Measure Y) (ξ : Measure Z)
    (κ : Kernel X Y) (η : Kernel Y Z)
    (hκ : κ ∘ₘ μ = ν) (hη : η ∘ₘ ν = ξ) :
    (η ∘ₖ κ) ∘ₘ μ = ξ := by
  rw [← Measure.comp_assoc, hκ, hη]

end Kernel

section Relative

variable {Θ Ξ D S : Type*}



theorem d028073
    (R : Θ → D → ℝ≥0∞) (r : Ξ → S → ℝ≥0∞)
    (T : Θ → Ξ) (E : S → D) (β : Θ → ℝ≥0∞) (b : Ξ → ℝ≥0∞)
    (hR : ∀ θ s, R θ (E s) = r (T θ) s)
    (c : ℝ≥0∞) (s : S)
    (hs : ∀ ξ, r ξ s ≤ c * b ξ)
    (hb : ∀ θ, c * b (T θ) ≤ c * β θ) :
    ∀ θ, R θ (E s) ≤ c * β θ := by
  intro θ
  rw [hR]
  exact (hs (T θ)).trans (hb θ)

theorem d028074
    (R : Θ → D → ℝ≥0∞) (r : Ξ → S → ℝ≥0∞)
    (T : Θ → Ξ) (E : S → D) (β : Θ → ℝ≥0∞) (b : Ξ → ℝ≥0∞)
    (hR : ∀ θ s, R θ (E s) = r (T θ) s)
    (hb : ∀ θ, b (T θ) ≤ β θ) (c : ℝ≥0∞) (s : S)
    (hs : ∀ ξ, r ξ s ≤ c * b ξ) :
    ∀ θ, R θ (E s) ≤ c * β θ :=
  _root_.GD.N0076.N0314.d028073 R r T E β b hR c s hs
    (fun θ => mul_le_mul' le_rfl (hb θ))



theorem d028075
    (R : Θ → D → ℝ≥0∞) (r : Ξ → S → ℝ≥0∞)
    (T : Θ → Ξ) (hT : Function.Surjective T) (E : S → D)
    (β : Θ → ℝ≥0∞) (b : Ξ → ℝ≥0∞)
    (hR : ∀ θ s, R θ (E s) = r (T θ) s)
    (hb : ∀ θ, β θ = b (T θ)) (c : ℝ≥0∞) (s : S) :
    (∀ θ, R θ (E s) ≤ c * β θ) ↔ (∀ ξ, r ξ s ≤ c * b ξ) := by
  constructor
  · intro h ξ
    obtain ⟨θ, rfl⟩ := hT ξ
    simpa only [hR, hb] using h θ
  · intro h θ
    simpa only [hR, hb] using h (T θ)

end Relative

section GaussianDeletion

open _root_.GD.N0232.N0719.N0900
open _root_.GD.N0107
open scoped BigOperators



def d028076 : _root_.GD.N0232.N0719.N0900.d009094 2 (fun _ => 3) → _root_.GD.N0232.N0719.N0900.d009094 2 (fun _ => 2) :=
  _root_.GD.N0076.N0312.d022672 (fun i => i) (fun _ => Fin.castSucc)

def d028077 : _root_.GD.N0232.N0719.N0900.d009094 2 (fun _ => 3) := fun _ => ![0, 2, 4]

def d028078 : _root_.GD.N0232.N0719.N0900.d009094 2 (fun _ => 3) := fun _ => ![0, 2, 7]

theorem d028079 (θ : _root_.GD.N0232.N0719.N0859.d010809 2) :
    (_root_.GD.N0232.N0719.N0859.d010812 2 (fun _ => 3) θ).map
      _root_.GD.N0076.N0314.d028076 =
      _root_.GD.N0232.N0719.N0859.d010812 2 (fun _ => 2) θ := by
  simpa only [_root_.GD.N0076.N0314.d028076, _root_.GD.N0076.N0312.d022673, Function.comp_def] using
    _root_.GD.N0076.N0312.d022676 (n := fun _ : Fin 2 => 3) (m := fun _ : Fin 2 => 2)
      (fun i => i) Function.injective_id (fun _ => Fin.castSucc)
      (fun _ => Fin.castSucc_injective 2) θ

theorem d028080 : _root_.GD.N0076.N0314.d028076 _root_.GD.N0076.N0314.d028077 = _root_.GD.N0076.N0314.d028076 _root_.GD.N0076.N0314.d028078 := by
  funext i j
  fin_cases j <;> norm_num [_root_.GD.N0076.N0314.d028076, _root_.GD.N0076.N0312.d022672, _root_.GD.N0076.N0314.d028077, _root_.GD.N0076.N0314.d028078]

theorem d028081 {k : ℕ} (hk : 0 < k)
    (s : _root_.GD.N0232.N0719.N0900.d009096 k) (a : ℝ) (h : ∀ i, s.mean i = a) : _root_.GD.N0232.N0719.N0900.d009110 s = a := by
  simp only [_root_.GD.N0232.N0719.N0900.d009110, h, ← Finset.sum_mul, _root_.GD.N0232.N0719.N0900.d009131 hk, one_mul]

theorem d028082 :
    _root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 3) _root_.GD.N0076.N0314.d028077 = 2 ∧
    _root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 3) _root_.GD.N0076.N0314.d028078 = 3 ∧
    _root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 2) (_root_.GD.N0076.N0314.d028076 _root_.GD.N0076.N0314.d028077) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    apply _root_.GD.N0076.N0314.d028081 (by norm_num)
    intro i
    norm_num [_root_.GD.N0232.N0719.N0900.d009104, _root_.GD.N0232.N0719.N0900.d009102, _root_.GD.N0107.d009084,
      _root_.GD.N0126.d006420, _root_.GD.N0126.d006419,
      _root_.GD.N0076.N0314.d028077, _root_.GD.N0076.N0314.d028078, _root_.GD.N0076.N0314.d028076, _root_.GD.N0076.N0312.d022672,
      Fin.sum_univ_succ]


theorem d028083 :
    (∀ i, 0 < _root_.GD.N0232.N0719.N0900.d009103 2 (fun _ => 3) _root_.GD.N0076.N0314.d028077 i) ∧
    (∀ i, 0 < _root_.GD.N0232.N0719.N0900.d009103 2 (fun _ => 3) _root_.GD.N0076.N0314.d028078 i) ∧
    (∀ i, 0 < _root_.GD.N0232.N0719.N0900.d009103 2 (fun _ => 2) (_root_.GD.N0076.N0314.d028076 _root_.GD.N0076.N0314.d028077) i) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    intro i
    norm_num [_root_.GD.N0232.N0719.N0900.d009103, _root_.GD.N0107.d009085,
      _root_.GD.N0126.d006422, _root_.GD.N0126.d006421,
      _root_.GD.N0126.d006420, _root_.GD.N0126.d006419,
      _root_.GD.N0076.N0314.d028077, _root_.GD.N0076.N0314.d028078, _root_.GD.N0076.N0314.d028076, _root_.GD.N0076.N0312.d022672,
      Fin.sum_univ_succ]



theorem d028084 :
    ¬ ∃ f : _root_.GD.N0232.N0719.N0900.d009094 2 (fun _ => 2) → ℝ,
      _root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 3) = f ∘ _root_.GD.N0076.N0314.d028076 := by
  apply _root_.GD.N0076.N0312.d022668 _root_.GD.N0076.N0314.d028076 (_root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 3))
    _root_.GD.N0076.N0314.d028077 _root_.GD.N0076.N0314.d028078 _root_.GD.N0076.N0314.d028080
  rw [_root_.GD.N0076.N0314.d028082.1, _root_.GD.N0076.N0314.d028082.2.1]
  norm_num

theorem d028085 :
    _root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 2) ∘ _root_.GD.N0076.N0314.d028076 ≠ _root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 3) := by
  intro h
  exact _root_.GD.N0076.N0314.d028084 ⟨_root_.GD.N0232.N0719.N0900.d009111 2 (fun _ => 2), h.symm⟩

end GaussianDeletion

end
end GD.N0076.N0314

#print axioms _root_.GD.N0076.N0314.d028063
#print axioms _root_.GD.N0076.N0314.d028064
#print axioms _root_.GD.N0076.N0314.d028065
#print axioms _root_.GD.N0076.N0314.d028066
#print axioms _root_.GD.N0076.N0314.d028067
#print axioms _root_.GD.N0076.N0314.d028068
#print axioms _root_.GD.N0076.N0314.d028070
#print axioms _root_.GD.N0076.N0314.d028071
#print axioms _root_.GD.N0076.N0314.d028072
#print axioms _root_.GD.N0076.N0314.d028073
#print axioms _root_.GD.N0076.N0314.d028074
#print axioms _root_.GD.N0076.N0314.d028075
#print axioms _root_.GD.N0076.N0314.d028079
#print axioms _root_.GD.N0076.N0314.d028080
#print axioms _root_.GD.N0076.N0314.d028081
#print axioms _root_.GD.N0076.N0314.d028082
#print axioms _root_.GD.N0076.N0314.d028083
#print axioms _root_.GD.N0076.N0314.d028084
#print axioms _root_.GD.N0076.N0314.d028085
