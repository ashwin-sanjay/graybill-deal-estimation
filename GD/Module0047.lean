import GD.Module0046
import Mathlib.Topology.Semicontinuity.Basic

























open scoped ENNReal

namespace GD
namespace N0230
namespace N0598

open Filter Topology
open _root_.GD.N0230.N0648
open _root_.GD.N0230.N0649
open _root_.GD.N0230.N0685

variable {Θ Rule : Type*}


def d000586
    (risk : Θ → Rule → ℝ≥0∞) (cap : Θ → ℝ≥0∞) : Set Rule :=
  {d | ∀ θ, risk θ d ≤ cap θ}


def d000587
    (risk : Θ → Rule → ℝ≥0∞) (cap : Θ → ℝ≥0∞)
    (sample : ℕ → Θ) : Set Rule :=
  {d | ∀ n, risk (sample n) d ≤ cap (sample n)}


def d000588
    (risk : Θ → Rule → ℝ≥0∞) (cap : Θ → ℝ≥0∞)
    (sample : ℕ → Θ) (N : ℕ) : Set Rule :=
  {d | ∀ n, n < N → risk (sample n) d ≤ cap (sample n)}

@[simp]
theorem d000589
    (risk : Θ → Rule → ℝ≥0∞) (cap : Θ → ℝ≥0∞) (d : Rule) :
    d ∈ _root_.GD.N0230.N0598.d000586 risk cap ↔ ∀ θ, risk θ d ≤ cap θ := by
  rfl

@[simp]
theorem d000590
    (risk : Θ → Rule → ℝ≥0∞) (cap : Θ → ℝ≥0∞)
    (sample : ℕ → Θ) (d : Rule) :
    d ∈ _root_.GD.N0230.N0598.d000587 risk cap sample ↔
      ∀ n, risk (sample n) d ≤ cap (sample n) := by
  rfl

@[simp]
theorem d000591
    (risk : Θ → Rule → ℝ≥0∞) (cap : Θ → ℝ≥0∞)
    (sample : ℕ → Θ) (N : ℕ) (d : Rule) :
    d ∈ _root_.GD.N0230.N0598.d000588 risk cap sample N ↔
      ∀ n, n < N → risk (sample n) d ≤ cap (sample n) := by
  rfl



theorem d000592
    [TopologicalSpace Θ]
    (risk : Θ → Rule → ℝ≥0∞) (cap : Θ → ℝ≥0∞)
    (sample : ℕ → Θ) (hdense : DenseRange sample) (d : Rule)
    (hopen : IsOpen {θ | cap θ < risk θ d}) :
    (∀ n, risk (sample n) d ≤ cap (sample n)) ↔
      ∀ θ, risk θ d ≤ cap θ := by
  constructor
  · intro hsample θ
    by_contra hθ
    have hnonempty : ({η | cap η < risk η d} : Set Θ).Nonempty :=
      ⟨θ, lt_of_not_ge hθ⟩
    obtain ⟨n, hn⟩ := hdense.exists_mem_open hopen hnonempty
    exact (not_lt_of_ge (hsample n)) hn
  · intro hall n
    exact hall (sample n)



theorem d000593
    [TopologicalSpace Θ]
    (candidate cap : Θ → ℝ≥0∞)
    (hcap : UpperSemicontinuous cap)
    (hcandidate : LowerSemicontinuous candidate) :
    IsOpen {θ | cap θ < candidate θ} := by
  rw [isOpen_iff_mem_nhds]
  intro θ hθ
  have hθ' : cap θ < candidate θ := hθ
  obtain ⟨c, hcapc, hccandidate⟩ := exists_between hθ'
  filter_upwards [hcap θ c hcapc, hcandidate θ c hccandidate] with η hcapη hη
  exact hcapη.trans hη


theorem d000594
    [TopologicalSpace Θ]
    (risk : Θ → Rule → ℝ≥0∞) (cap : Θ → ℝ≥0∞)
    (sample : ℕ → Θ) (hdense : DenseRange sample) (d : Rule)
    (hcap : UpperSemicontinuous cap)
    (hrisk : LowerSemicontinuous (fun θ ↦ risk θ d)) :
    (∀ n, risk (sample n) d ≤ cap (sample n)) ↔
      ∀ θ, risk θ d ≤ cap θ := by
  exact _root_.GD.N0230.N0598.d000592
    risk cap sample hdense d
      (_root_.GD.N0230.N0598.d000593
        (fun θ ↦ risk θ d) cap hcap hrisk)



theorem d000595
    [TopologicalSpace Θ]
    (risk : Θ → Rule → ℝ≥0∞) (cap : Θ → ℝ≥0∞)
    (sample : ℕ → Θ) (hdense : DenseRange sample)
    (hopen : ∀ d, d ∈ _root_.GD.N0230.N0598.d000587 risk cap sample →
      IsOpen {θ | cap θ < risk θ d}) :
    _root_.GD.N0230.N0598.d000587 risk cap sample = _root_.GD.N0230.N0598.d000586 risk cap := by
  ext d
  constructor
  · intro hd
    exact (_root_.GD.N0230.N0598.d000592
      risk cap sample hdense d (hopen d hd)).mp hd
  · intro hd n
    exact hd (sample n)



theorem d000596
    [TopologicalSpace Θ]
    (risk : Θ → Rule → ℝ≥0∞) (cap : Θ → ℝ≥0∞)
    (sample : ℕ → Θ) (hdense : DenseRange sample)
    (hcap : UpperSemicontinuous cap)
    (hrisk : ∀ d, d ∈ _root_.GD.N0230.N0598.d000587 risk cap sample →
      LowerSemicontinuous (fun θ ↦ risk θ d)) :
    _root_.GD.N0230.N0598.d000587 risk cap sample = _root_.GD.N0230.N0598.d000586 risk cap := by
  apply _root_.GD.N0230.N0598.d000595
    risk cap sample hdense
  intro d hd
  exact _root_.GD.N0230.N0598.d000593
    (fun θ ↦ risk θ d) cap hcap (hrisk d hd)


theorem d000597
    (risk : Θ → Rule → ℝ≥0∞) (cap : Θ → ℝ≥0∞)
    (sample : ℕ → Θ) :
    Antitone (_root_.GD.N0230.N0598.d000588 risk cap sample) := by
  intro N M hNM d hd n hn
  exact hd n (lt_of_lt_of_le hn hNM)


theorem d000598
    (risk : Θ → Rule → ℝ≥0∞) (cap : Θ → ℝ≥0∞)
    (sample : ℕ → Θ) :
    (⋂ N, _root_.GD.N0230.N0598.d000588 risk cap sample N) =
      _root_.GD.N0230.N0598.d000587 risk cap sample := by
  ext d
  constructor
  · intro hd n
    have hprefix : d ∈ _root_.GD.N0230.N0598.d000588 risk cap sample (n + 1) :=
      Set.mem_iInter.mp hd (n + 1)
    exact hprefix n (Nat.lt_succ_self n)
  · intro hd
    rw [Set.mem_iInter]
    intro N n hn
    exact hd n



theorem d000599
    [TopologicalSpace Θ]
    (risk : Θ → Rule → ℝ≥0∞) (cap : Θ → ℝ≥0∞)
    (sample : ℕ → Θ) (hdense : DenseRange sample)
    (hopen : ∀ d, d ∈ _root_.GD.N0230.N0598.d000587 risk cap sample →
      IsOpen {θ | cap θ < risk θ d}) :
    (⋂ N, _root_.GD.N0230.N0598.d000588 risk cap sample N) =
      _root_.GD.N0230.N0598.d000586 risk cap := by
  rw [_root_.GD.N0230.N0598.d000598]
  exact _root_.GD.N0230.N0598.d000595
    risk cap sample hdense hopen



theorem d000600
    [TopologicalSpace Θ]
    (risk : Θ → Rule → ℝ≥0∞) (cap : Θ → ℝ≥0∞)
    (sample : ℕ → Θ) (hdense : DenseRange sample)
    (hcap : UpperSemicontinuous cap)
    (hrisk : ∀ d, d ∈ _root_.GD.N0230.N0598.d000587 risk cap sample →
      LowerSemicontinuous (fun θ ↦ risk θ d)) :
    (⋂ N, _root_.GD.N0230.N0598.d000588 risk cap sample N) =
      _root_.GD.N0230.N0598.d000586 risk cap := by
  rw [_root_.GD.N0230.N0598.d000598]
  exact _root_.GD.N0230.N0598.d000596
    risk cap sample hdense hcap hrisk

section Projection

variable [TopologicalSpace Θ]
variable [NormedAddCommGroup Rule] [InnerProductSpace ℝ Rule]



theorem d000601
    [CompleteSpace Rule]
    (risk : Θ → Rule → ℝ≥0∞) (cap : Θ → ℝ≥0∞)
    (sample : ℕ → Θ) (hdense : DenseRange sample)
    (p : ℕ → Rule) (plim : Rule)
    (hopen : ∀ d, d ∈ _root_.GD.N0230.N0598.d000587 risk cap sample →
      IsOpen {θ | cap θ < risk θ d})
    (hclosed : ∀ N, IsClosed (_root_.GD.N0230.N0598.d000588 risk cap sample N))
    (hp : ∀ N,
      _root_.GD.N0230.N0685.d000511 (_root_.GD.N0230.N0598.d000588 risk cap sample N) 0 (p N))
    (hplim : _root_.GD.N0230.N0685.d000511 (_root_.GD.N0230.N0598.d000586 risk cap) 0 plim) :
    Tendsto p atTop (nhds plim) := by
  have hinter : (⋂ N, _root_.GD.N0230.N0598.d000588 risk cap sample N) =
      _root_.GD.N0230.N0598.d000586 risk cap :=
    _root_.GD.N0230.N0598.d000599
      risk cap sample hdense hopen
  have hplim' :
      _root_.GD.N0230.N0685.d000511 (⋂ N, _root_.GD.N0230.N0598.d000588 risk cap sample N) 0 plim := by
    rw [hinter]
    exact hplim
  exact _root_.GD.N0230.N0649.d000583
    (_root_.GD.N0230.N0598.d000588 risk cap sample) p plim
    (_root_.GD.N0230.N0598.d000597 risk cap sample) hclosed hp hplim'


theorem d000602
    [CompleteSpace Rule]
    (risk : Θ → Rule → ℝ≥0∞) (cap : Θ → ℝ≥0∞)
    (sample : ℕ → Θ) (hdense : DenseRange sample)
    (p : ℕ → Rule) (plim : Rule)
    (hcap : UpperSemicontinuous cap)
    (hrisk : ∀ d, d ∈ _root_.GD.N0230.N0598.d000587 risk cap sample →
      LowerSemicontinuous (fun θ ↦ risk θ d))
    (hclosed : ∀ N, IsClosed (_root_.GD.N0230.N0598.d000588 risk cap sample N))
    (hp : ∀ N,
      _root_.GD.N0230.N0685.d000511 (_root_.GD.N0230.N0598.d000588 risk cap sample N) 0 (p N))
    (hplim : _root_.GD.N0230.N0685.d000511 (_root_.GD.N0230.N0598.d000586 risk cap) 0 plim) :
    Tendsto p atTop (nhds plim) := by
  apply _root_.GD.N0230.N0598.d000601
    risk cap sample hdense p plim
  · intro d hd
    exact _root_.GD.N0230.N0598.d000593
      (fun θ ↦ risk θ d) cap hcap (hrisk d hd)
  · exact hclosed
  · exact hp
  · exact hplim


theorem d000603
    (risk : Θ → Rule → ℝ≥0∞) (cap : Θ → ℝ≥0∞)
    (sample : ℕ → Θ) (hdense : DenseRange sample)
    (p : ℕ → Rule) (plim : Rule)
    (hopen : ∀ d, d ∈ _root_.GD.N0230.N0598.d000587 risk cap sample →
      IsOpen {θ | cap θ < risk θ d})
    (hp : ∀ N,
      _root_.GD.N0230.N0685.d000511 (_root_.GD.N0230.N0598.d000588 risk cap sample N) 0 (p N))
    (hplim : _root_.GD.N0230.N0685.d000511 (_root_.GD.N0230.N0598.d000586 risk cap) 0 plim)
    (N : ℕ) :
    ‖plim - p N‖ ^ 2 ≤ ‖plim‖ ^ 2 - ‖p N‖ ^ 2 := by
  have hinter : (⋂ n, _root_.GD.N0230.N0598.d000588 risk cap sample n) =
      _root_.GD.N0230.N0598.d000586 risk cap :=
    _root_.GD.N0230.N0598.d000599
      risk cap sample hdense hopen
  have hplim' :
      _root_.GD.N0230.N0685.d000511 (⋂ n, _root_.GD.N0230.N0598.d000588 risk cap sample n) 0 plim := by
    rw [hinter]
    exact hplim
  exact _root_.GD.N0230.N0648.d000576
    (_root_.GD.N0230.N0598.d000588 risk cap sample) p plim hp hplim' N



theorem d000604
    (risk : Θ → Rule → ℝ≥0∞) (cap : Θ → ℝ≥0∞)
    (sample : ℕ → Θ) (hdense : DenseRange sample)
    (p : ℕ → Rule) (plim e : Rule)
    (hopen : ∀ d, d ∈ _root_.GD.N0230.N0598.d000587 risk cap sample →
      IsOpen {θ | cap θ < risk θ d})
    (hp : ∀ N,
      _root_.GD.N0230.N0685.d000511 (_root_.GD.N0230.N0598.d000588 risk cap sample N) 0 (p N))
    (hplim : _root_.GD.N0230.N0685.d000511 (_root_.GD.N0230.N0598.d000586 risk cap) 0 plim)
    (he : e ∈ _root_.GD.N0230.N0598.d000586 risk cap)
    (N : ℕ) :
    ‖plim - p N‖ ^ 2 ≤ ‖e‖ ^ 2 - ‖p N‖ ^ 2 := by
  have hinter : (⋂ n, _root_.GD.N0230.N0598.d000588 risk cap sample n) =
      _root_.GD.N0230.N0598.d000586 risk cap :=
    _root_.GD.N0230.N0598.d000599
      risk cap sample hdense hopen
  have hplim' :
      _root_.GD.N0230.N0685.d000511 (⋂ n, _root_.GD.N0230.N0598.d000588 risk cap sample n) 0 plim := by
    rw [hinter]
    exact hplim
  have he' : e ∈ ⋂ n, _root_.GD.N0230.N0598.d000588 risk cap sample n := by
    rw [hinter]
    exact he
  exact _root_.GD.N0230.N0648.d000577
    (_root_.GD.N0230.N0598.d000588 risk cap sample) p plim e hp hplim' he' N

end Projection

end N0598
end N0230
end GD

#print axioms _root_.GD.N0230.N0598.d000592
#print axioms _root_.GD.N0230.N0598.d000593
#print axioms _root_.GD.N0230.N0598.d000596
#print axioms _root_.GD.N0230.N0598.d000597
#print axioms _root_.GD.N0230.N0598.d000600
#print axioms _root_.GD.N0230.N0598.d000601
#print axioms _root_.GD.N0230.N0598.d000602
#print axioms _root_.GD.N0230.N0598.d000603
#print axioms _root_.GD.N0230.N0598.d000604
