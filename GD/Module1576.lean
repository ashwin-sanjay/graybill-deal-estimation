import GD.Module1575









set_option autoImplicit false
set_option warningAsError true

open Set
open _root_.GD.N0232.N0720.N1164
open _root_.GD.N0106.N0428.N0770.N1725
open _root_.GD.N0106.N0428.N0770.N1719
open _root_.GD.N0106.N0428.N0770.N1728
open _root_.GD.N0106.N0428.N0770.N1727

namespace GD.N0106.N0428.N0770.N1703
noncomputable section

def d024458 (lo hi : ℕ) : _root_.GD.N0232.N0720.N1164.d006809 := ⟨(lo : ℚ) / 100000, (hi : ℚ) / 100000⟩

def d024459 : List _root_.GD.N0106.N0428.N0770.N1728.d024386 :=
  [(0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1)]

theorem d024460 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : i ∈ _root_.GD.N0106.N0428.N0770.N1703.d024459 := by
  rcases i with ⟨r, s⟩
  fin_cases r <;> fin_cases s <;> simp [_root_.GD.N0106.N0428.N0770.N1703.d024459]

def d024461 (R : _root_.GD.N0106.N0428.N0770.N1719.d024281) (J K : _root_.GD.N0232.N0720.N1164.d006809) : Decidable (R.d024282 J K) := by
  letI (a b : ℚ) : Decidable (a < b) := _root_.GD.N0232.N0720.N1164.d006825 a b
  letI (a b : ℚ) : Decidable (a ≤ b) := _root_.GD.N0232.N0720.N1164.d006826 a b
  exact decidable_of_iff
    (0 < J.lo ∧ J.lo ≤ J.hi ∧ 0 ≤ R.ratioRoot.lo ∧ R.ratioRoot.lo ≤ R.ratioRoot.hi ∧
      R.ratioRoot.lo ^ 2 ≤ K.lo ∧ K.hi ≤ R.ratioRoot.hi ^ 2 ∧ 0 < R.nRoot.lo ∧
      R.nRoot.lo ≤ R.nRoot.hi ∧ R.nRoot.lo ^ 2 ≤ J.lo ∧ J.hi ≤ R.nRoot.hi ^ 2)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ =>
        ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩,
      fun h => ⟨h.nlo, h.norder, h.ratioLo, h.ratioOrder, h.ratioLower, h.ratioUpper,
        h.rootLo, h.rootOrder, h.rootLower, h.rootUpper⟩⟩

def d024462 (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : _root_.GD.N0232.N0720.N1164.d006809 :=
  _root_.GD.N0106.N0428.N0770.N1719.d024260 (_root_.GD.N0106.N0428.N0770.N1727.d024430 i / (_root_.GD.N0106.N0428.N0770.N1727.d024429 i * (1 - _root_.GD.N0106.N0428.N0770.N1727.d024429 i)))

def d024463 (I : _root_.GD.N0232.N0720.N1164.d006809) (R : _root_.GD.N0106.N0428.N0770.N1728.d024386 → _root_.GD.N0106.N0428.N0770.N1719.d024281) (i : _root_.GD.N0106.N0428.N0770.N1728.d024386) : Bool :=
  @decide ((R i).d024282 (_root_.GD.N0106.N0428.N0770.N1719.d024266 I (_root_.GD.N0106.N0428.N0770.N1727.d024429 i) (_root_.GD.N0106.N0428.N0770.N1727.d024430 i)) (_root_.GD.N0106.N0428.N0770.N1703.d024462 i))
    (_root_.GD.N0106.N0428.N0770.N1703.d024461 (R i) (_root_.GD.N0106.N0428.N0770.N1719.d024266 I (_root_.GD.N0106.N0428.N0770.N1727.d024429 i) (_root_.GD.N0106.N0428.N0770.N1727.d024430 i)) (_root_.GD.N0106.N0428.N0770.N1703.d024462 i))

def d024464 (I : _root_.GD.N0232.N0720.N1164.d006809) (R : _root_.GD.N0106.N0428.N0770.N1728.d024386 → _root_.GD.N0106.N0428.N0770.N1719.d024281) : Bool :=
  @decide ((_root_.GD.N0106.N0428.N0770.N1727.d024433 I 1 R).hi < -47 / 200)
    (_root_.GD.N0232.N0720.N1164.d006825 (_root_.GD.N0106.N0428.N0770.N1727.d024433 I 1 R).hi (-47 / 200))

def d024465 (lo hi : ℕ) (R : _root_.GD.N0106.N0428.N0770.N1728.d024386 → _root_.GD.N0106.N0428.N0770.N1719.d024281) : Bool :=
  _root_.GD.N0106.N0428.N0770.N1703.d024459.all (_root_.GD.N0106.N0428.N0770.N1703.d024463 (_root_.GD.N0106.N0428.N0770.N1703.d024458 lo hi) R) && _root_.GD.N0106.N0428.N0770.N1703.d024464 (_root_.GD.N0106.N0428.N0770.N1703.d024458 lo hi) R



theorem d024466 {lo hi : ℕ} {R : _root_.GD.N0106.N0428.N0770.N1728.d024386 → _root_.GD.N0106.N0428.N0770.N1719.d024281}
    (h : _root_.GD.N0106.N0428.N0770.N1703.d024465 lo hi R = true) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1)
    (hI : (_root_.GD.N0106.N0428.N0770.N1703.d024458 lo hi).d006810 q) : _root_.GD.N0106.N0428.N0770.N1728.d024397 q < -47 / 200 := by
  obtain ⟨hall, hcap⟩ := Bool.and_eq_true_iff.mp h
  have hR : ∀ i : _root_.GD.N0106.N0428.N0770.N1728.d024386, (R i).d024282
      (_root_.GD.N0106.N0428.N0770.N1719.d024266 (_root_.GD.N0106.N0428.N0770.N1703.d024458 lo hi) (_root_.GD.N0106.N0428.N0770.N1727.d024429 i) (_root_.GD.N0106.N0428.N0770.N1727.d024430 i))
      (_root_.GD.N0106.N0428.N0770.N1719.d024260 (_root_.GD.N0106.N0428.N0770.N1727.d024430 i / (_root_.GD.N0106.N0428.N0770.N1727.d024429 i * (1 - _root_.GD.N0106.N0428.N0770.N1727.d024429 i)))) := by
    intro i
    exact @of_decide_eq_true _
      (_root_.GD.N0106.N0428.N0770.N1703.d024461 (R i) (_root_.GD.N0106.N0428.N0770.N1719.d024266 (_root_.GD.N0106.N0428.N0770.N1703.d024458 lo hi) (_root_.GD.N0106.N0428.N0770.N1727.d024429 i) (_root_.GD.N0106.N0428.N0770.N1727.d024430 i))
        (_root_.GD.N0106.N0428.N0770.N1703.d024462 i)) (List.all_eq_true.mp hall i (_root_.GD.N0106.N0428.N0770.N1703.d024460 i))
  have hbox := _root_.GD.N0106.N0428.N0770.N1727.d024435 hq hI hR
  have hcap' : (_root_.GD.N0106.N0428.N0770.N1727.d024433 (_root_.GD.N0106.N0428.N0770.N1703.d024458 lo hi) 1 R).hi < (-47 / 200 : ℚ) :=
    @of_decide_eq_true _
      (_root_.GD.N0232.N0720.N1164.d006825 (_root_.GD.N0106.N0428.N0770.N1727.d024433 (_root_.GD.N0106.N0428.N0770.N1703.d024458 lo hi) 1 R).hi (-47 / 200)) hcap
  have hcast : ((_root_.GD.N0106.N0428.N0770.N1727.d024433 (_root_.GD.N0106.N0428.N0770.N1703.d024458 lo hi) 1 R).hi : ℝ) < ((-47 / 200 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr hcap'
  have hcast' : ((_root_.GD.N0106.N0428.N0770.N1727.d024433 (_root_.GD.N0106.N0428.N0770.N1703.d024458 lo hi) 1 R).hi : ℝ) < -47 / 200 := by
    simpa using hcast
  exact hbox.2.trans_lt hcast'



def d024467 (lo hi : ℕ) : Prop :=
  ∀ q : ℝ, q ∈ Icc (0 : ℝ) 1 →
    q ∈ Icc ((lo : ℝ) / 100000) ((hi : ℝ) / 100000) → _root_.GD.N0106.N0428.N0770.N1728.d024397 q < -47 / 200

theorem d024468 {lo hi : ℕ} {R : _root_.GD.N0106.N0428.N0770.N1728.d024386 → _root_.GD.N0106.N0428.N0770.N1719.d024281}
    (h : _root_.GD.N0106.N0428.N0770.N1703.d024465 lo hi R = true) : _root_.GD.N0106.N0428.N0770.N1703.d024467 lo hi := by
  intro q hq hI
  apply _root_.GD.N0106.N0428.N0770.N1703.d024466 h hq
  change (((lo : ℚ) / 100000 : ℚ) : ℝ) ≤ q ∧
    q ≤ (((hi : ℚ) / 100000 : ℚ) : ℝ)
  push_cast
  exact hI



theorem d024469 {lo mid hi : ℕ} (hleft : _root_.GD.N0106.N0428.N0770.N1703.d024467 lo mid) (hright : _root_.GD.N0106.N0428.N0770.N1703.d024467 mid hi) :
    _root_.GD.N0106.N0428.N0770.N1703.d024467 lo hi := by
  intro q hq hI
  by_cases hm : q ≤ (mid : ℝ) / 100000
  · exact hleft q hq ⟨hI.1, hm⟩
  · exact hright q hq ⟨(lt_of_not_ge hm).le, hI.2⟩



theorem d024470 (hhalf : _root_.GD.N0106.N0428.N0770.N1703.d024467 0 50000)
    {k : ℕ} (hk : k < 50000) {q : ℝ}
    (hI : q ∈ Icc ((k : ℝ) / 100000) (((k : ℝ) + 1) / 100000)) :
    _root_.GD.N0106.N0428.N0770.N1728.d024397 q < -47 / 200 := by
  have hk' : (k : ℝ) + 1 ≤ 50000 := by exact_mod_cast Nat.succ_le_iff.mpr hk
  have hq0 : 0 ≤ q := (div_nonneg (Nat.cast_nonneg k) (by norm_num)).trans hI.1
  have hqhi : q ≤ 1 / 2 := by linarith [hI.2]
  apply hhalf q ⟨hq0, hqhi.trans (by norm_num)⟩
  norm_num
  exact ⟨hq0, hqhi⟩


theorem d024471 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) (1 / 2)) :
    ∃ k : ℕ, k < 50000 ∧ (k : ℝ) / 100000 ≤ q ∧ q ≤ ((k : ℝ) + 1) / 100000 := by
  have h0 : (0 : ℝ) ≤ 100000 * q := mul_nonneg (by norm_num) hq.1
  have hfl : ((⌊100000 * q⌋₊ : ℕ) : ℝ) ≤ 100000 * q := Nat.floor_le h0
  have hlt : 100000 * q < ((⌊100000 * q⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  by_cases hcase : ⌊100000 * q⌋₊ < 50000
  · refine ⟨⌊100000 * q⌋₊, hcase, ?_, ?_⟩ <;> linarith
  · have h50 : (50000 : ℝ) ≤ ((⌊100000 * q⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast not_lt.mp hcase
    refine ⟨49999, by norm_num, ?_, ?_⟩ <;> norm_num <;> linarith [hq.2]

end
end GD.N0106.N0428.N0770.N1703

#print axioms _root_.GD.N0106.N0428.N0770.N1703.d024466
#print axioms _root_.GD.N0106.N0428.N0770.N1703.d024469
#print axioms _root_.GD.N0106.N0428.N0770.N1703.d024470
#print axioms _root_.GD.N0106.N0428.N0770.N1703.d024471
