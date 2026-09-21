import GD.Module0928






















open Set

namespace GD
namespace N0232
namespace N0720
namespace N1076

noncomputable section

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1025
open _root_.GD.N0232.N0720.N1066
open _root_.GD.N0232.N0720.N1069
open _root_.GD.N0232.N0720.N1075
open _root_.GD.N0232.N0720.N1215
open _root_.GD.N0230.N0565
open _root_.GD.N0230.N0567
open _root_.GD.N0230.N0608
open _root_.GD.N0230.N0718
open _root_.GD.N0232.N0719.N0946.d009229

variable (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)

include hm hn





theorem d014517
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    LowerSemicontinuousOn
      (_root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) := by
  let scale : ℝ := _root_.GD.N0232.N0720.N1075.d014501 m n epsilon theta
  let center : ℝ := _root_.GD.N0232.N0720.N1075.d014487 m n theta
  let renormalize : ℝ → ℝ := fun value ↦ (value - center) / scale
  have hscale : 0 < scale := by
    exact _root_.GD.N0232.N0720.N1075.d014502 m n hm hn hepsilon theta
  have hcontinuous : Continuous renormalize := by
    dsimp [renormalize]
    fun_prop
  have hmonotone : Monotone renormalize := by
    intro x y hxy
    dsimp [renormalize]
    exact (div_le_div_iff_of_pos_right hscale).2
      (sub_le_sub_right hxy center)
  change LowerSemicontinuousOn
    (renormalize ∘ _root_.GD.N0232.N0720.N1066.d014327 m n hm hn theta)
    (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
  exact hcontinuous.comp_lowerSemicontinuousOn
    (_root_.GD.N0232.N0720.N1066.d014335 m n hm hn theta)
    hmonotone



theorem d014518
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    LowerSemicontinuousOn
      (_root_.GD.N0232.N0720.N1075.d014507 m n hm hn epsilon hepsilon)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) := by
  unfold _root_.GD.N0232.N0720.N1075.d014507
  exact _root_.GD.N0230.N0567.d001640
    (_root_.GD.N0232.N0720.N1075.d014506 m n hm hn epsilon hepsilon)
    (_root_.GD.N0232.N0720.N1076.d014517
      m n hm hn hepsilon)





def d014519
    (band : _root_.GD.N0232.N0720.N1080.d014168 → Prop)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    _root_.GD.N0230.N0567.d001622 {theta : _root_.GD.N0232.N0720.N1080.d014168 // band theta}
      (_root_.GD.N0232.N0720.N1025.d014303 m n) (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
      (-1 / epsilon) (1 / epsilon) where
  profile theta :=
    _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta.1
  mem_Icc := by
    intro theta d _hd
    exact _root_.GD.N0232.N0720.N1075.d014505
      m n hm hn hepsilon theta.1 d


def d014520
    (band : _root_.GD.N0232.N0720.N1080.d014168 → Prop)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (d : _root_.GD.N0232.N0720.N1025.d014303 m n) : ℝ :=
  _root_.GD.N0230.N0567.d001636
    (_root_.GD.N0232.N0720.N1076.d014519
      m n hm hn band epsilon hepsilon) d




theorem d014521
    (band : _root_.GD.N0232.N0720.N1080.d014168 → Prop)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    LowerSemicontinuousOn
      (_root_.GD.N0232.N0720.N1076.d014520
        m n hm hn band epsilon hepsilon)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) := by
  unfold _root_.GD.N0232.N0720.N1076.d014520
  exact _root_.GD.N0230.N0567.d001640
    (_root_.GD.N0232.N0720.N1076.d014519
      m n hm hn band epsilon hepsilon)
    (fun theta ↦
      _root_.GD.N0232.N0720.N1076.d014517
        m n hm hn hepsilon theta.1)



theorem d014522
    (band : _root_.GD.N0232.N0720.N1080.d014168 → Prop)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    _root_.GD.N0230.N0565.d000737 (_root_.GD.N0232.N0720.N1025.d014305 m n)
      (_root_.GD.N0232.N0720.N1076.d014520
        m n hm hn band epsilon hepsilon) := by
  classical
  cases isEmpty_or_nonempty {theta : _root_.GD.N0232.N0720.N1080.d014168 // band theta} with
  | inl hempty =>
      letI := hempty
      intro e d _hed
      unfold _root_.GD.N0232.N0720.N1076.d014520 _root_.GD.N0230.N0567.d001636
      have hfun :
          (fun theta : {theta : _root_.GD.N0232.N0720.N1080.d014168 // band theta} ↦
            (_root_.GD.N0232.N0720.N1076.d014519
              m n hm hn band epsilon hepsilon).profile theta e) =
          (fun theta : {theta : _root_.GD.N0232.N0720.N1080.d014168 // band theta} ↦
            (_root_.GD.N0232.N0720.N1076.d014519
              m n hm hn band epsilon hepsilon).profile theta d) :=
        Subsingleton.elim _ _
      rw [hfun]
  | inr hnonempty =>
    letI := hnonempty
    intro e d hed
    unfold _root_.GD.N0232.N0720.N1076.d014520 _root_.GD.N0230.N0567.d001636
    apply ciSup_le
    intro theta
    calc
      _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta.1 e ≤
          _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta.1 d :=
        _root_.GD.N0232.N0720.N1075.d014511
          m n hm hn hepsilon theta.1 hed
      _ ≤ ⨆ eta : {eta : _root_.GD.N0232.N0720.N1080.d014168 // band eta},
          _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon eta.1 d := by
        exact le_ciSup
          (f := fun eta : {eta : _root_.GD.N0232.N0720.N1080.d014168 // band eta} ↦
            _root_.GD.N0232.N0720.N1075.d014503
              m n hm hn epsilon eta.1 d)
          (by
            refine ⟨1 / epsilon, ?_⟩
            rintro value ⟨eta, rfl⟩
            exact (_root_.GD.N0232.N0720.N1075.d014505
              m n hm hn hepsilon eta.1 d).2)
          theta



theorem d014523
    (band : _root_.GD.N0232.N0720.N1080.d014168 → Prop)
    [Nonempty {theta : _root_.GD.N0232.N0720.N1080.d014168 // band theta}]
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {d : _root_.GD.N0232.N0720.N1025.d014303 m n} (hd : d ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    IsLUB
      (Set.range (fun theta : {theta : _root_.GD.N0232.N0720.N1080.d014168 // band theta} ↦
        _root_.GD.N0232.N0720.N1075.d014503
          m n hm hn epsilon theta.1 d))
      (_root_.GD.N0232.N0720.N1076.d014520
        m n hm hn band epsilon hepsilon d) := by
  exact _root_.GD.N0230.N0567.d001638
    (_root_.GD.N0232.N0720.N1076.d014519
      m n hm hn band epsilon hepsilon) hd



theorem d014524
    (band : _root_.GD.N0232.N0720.N1080.d014168 → Prop)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (theta : {theta : _root_.GD.N0232.N0720.N1080.d014168 // band theta})
    {p q : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hq : q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    (_root_.GD.N0232.N0720.N1076.d014519
          m n hm hn band epsilon hepsilon).profile theta
          (_root_.GD.N0230.N0718.d001528 p q) +
        _root_.GD.N0232.N0720.N1075.d014504
          m n hm hn epsilon theta.1 p q =
      ((_root_.GD.N0232.N0720.N1076.d014519
            m n hm hn band epsilon hepsilon).profile theta p +
        (_root_.GD.N0232.N0720.N1076.d014519
            m n hm hn band epsilon hepsilon).profile theta q) / 2 := by
  exact _root_.GD.N0232.N0720.N1075.d014513
    m n hm hn hepsilon theta.1 hp hq


theorem d014525
    (band : _root_.GD.N0232.N0720.N1080.d014168 → Prop)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (theta : {theta : _root_.GD.N0232.N0720.N1080.d014168 // band theta})
    {p q : _root_.GD.N0232.N0720.N1025.d014303 m n}
    (hp : p ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn)
    (hq : q ∈ _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    0 ≤ _root_.GD.N0232.N0720.N1075.d014504
      m n hm hn epsilon theta.1 p q := by
  exact _root_.GD.N0232.N0720.N1075.d014514
    m n hm hn hepsilon theta.1 hp hq





def d014526 (band : _root_.GD.N0232.N0720.N1080.d014168 → Prop) : Prop :=
  ∀ (g : _root_.GD.N0232.N0720.N1025.d014301) (theta : _root_.GD.N0232.N0720.N1080.d014168),
    band (_root_.GD.N0232.N0720.N1215.d014272 g theta) ↔ band theta



theorem d014527
    (band : _root_.GD.N0232.N0720.N1080.d014168 → Prop) (hband : _root_.GD.N0232.N0720.N1076.d014526 band)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (g : _root_.GD.N0232.N0720.N1025.d014301) (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1076.d014520 m n hm hn band epsilon hepsilon
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1 =
      _root_.GD.N0232.N0720.N1076.d014520
        m n hm hn band epsilon hepsilon p.1 := by
  classical
  cases isEmpty_or_nonempty {theta : _root_.GD.N0232.N0720.N1080.d014168 // band theta} with
  | inl hempty =>
      letI := hempty
      unfold _root_.GD.N0232.N0720.N1076.d014520 _root_.GD.N0230.N0567.d001636
      have hfun :
          (fun theta : {theta : _root_.GD.N0232.N0720.N1080.d014168 // band theta} ↦
            (_root_.GD.N0232.N0720.N1076.d014519
              m n hm hn band epsilon hepsilon).profile theta
                (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1) =
          (fun theta : {theta : _root_.GD.N0232.N0720.N1080.d014168 // band theta} ↦
            (_root_.GD.N0232.N0720.N1076.d014519
              m n hm hn band epsilon hepsilon).profile theta p.1) :=
        Subsingleton.elim _ _
      rw [hfun]
  | inr hnonempty =>
    letI := hnonempty
    unfold _root_.GD.N0232.N0720.N1076.d014520 _root_.GD.N0230.N0567.d001636
    apply le_antisymm
    · apply ciSup_le
      intro theta
      change _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta.1
          (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1 ≤
        ⨆ eta : {eta : _root_.GD.N0232.N0720.N1080.d014168 // band eta},
          _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon eta.1 p.1
      rw [_root_.GD.N0232.N0720.N1075.d014515
        m n hm hn hepsilon g theta.1 p]
      have hmem : band (_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ theta.1) :=
        (hband g⁻¹ theta.1).2 theta.2
      exact le_ciSup
        (f := fun eta : {eta : _root_.GD.N0232.N0720.N1080.d014168 // band eta} ↦
          _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon eta.1 p.1)
        (by
          refine ⟨1 / epsilon, ?_⟩
          rintro value ⟨eta, rfl⟩
          exact (_root_.GD.N0232.N0720.N1075.d014505
            m n hm hn hepsilon eta.1 p.1).2)
        ⟨_root_.GD.N0232.N0720.N1215.d014272 g⁻¹ theta.1, hmem⟩
    · apply ciSup_le
      intro eta
      change _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon eta.1 p.1 ≤
        ⨆ theta : {theta : _root_.GD.N0232.N0720.N1080.d014168 // band theta},
          _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta.1
            (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1
      have hmem : band (_root_.GD.N0232.N0720.N1215.d014272 g eta.1) :=
        (hband g eta.1).2 eta.2
      have hle := le_ciSup
        (show BddAbove (Set.range (fun theta :
            {theta : _root_.GD.N0232.N0720.N1080.d014168 // band theta} ↦
          _root_.GD.N0232.N0720.N1075.d014503 m n hm hn epsilon theta.1
            (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1)) by
          refine ⟨1 / epsilon, ?_⟩
          rintro value ⟨theta, rfl⟩
          exact (_root_.GD.N0232.N0720.N1075.d014505
            m n hm hn hepsilon theta.1
              (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1).2)
        ⟨_root_.GD.N0232.N0720.N1215.d014272 g eta.1, hmem⟩
      rw [_root_.GD.N0232.N0720.N1075.d014515
        m n hm hn hepsilon g (_root_.GD.N0232.N0720.N1215.d014272 g eta.1) p] at hle
      simpa using hle




def d014528 (j : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ j

omit hm hn in
theorem d014529 (j : ℕ) :
    0 < _root_.GD.N0232.N0720.N1076.d014528 j := by
  unfold _root_.GD.N0232.N0720.N1076.d014528
  positivity

omit hm hn in
theorem d014530 (j : ℕ) :
    _root_.GD.N0232.N0720.N1076.d014528 (j + 1) = _root_.GD.N0232.N0720.N1076.d014528 j / 2 := by
  unfold _root_.GD.N0232.N0720.N1076.d014528
  rw [pow_succ]
  ring





def d014531 (j : ℕ) : ℝ :=
  (_root_.GD.N0232.N0720.N1076.d014528 (j + 1)) ^ 2

omit hm hn in
theorem d014532 (j : ℕ) :
    0 < _root_.GD.N0232.N0720.N1076.d014531 j := by
  unfold _root_.GD.N0232.N0720.N1076.d014531
  exact pow_pos (_root_.GD.N0232.N0720.N1076.d014529 (j + 1)) 2


def d014533 (j : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168) : Prop :=
  _root_.GD.N0232.N0720.N1076.d014528 (j + 1) ≤ _root_.GD.N0232.N0720.N1069.d014352 m n theta ∧
    _root_.GD.N0232.N0720.N1069.d014352 m n theta ≤ _root_.GD.N0232.N0720.N1076.d014528 j


def d014534 (j : ℕ) (theta : _root_.GD.N0232.N0720.N1080.d014168) : Prop :=
  _root_.GD.N0232.N0720.N1076.d014528 (j + 1) ≤ 1 - _root_.GD.N0232.N0720.N1069.d014352 m n theta ∧
    1 - _root_.GD.N0232.N0720.N1069.d014352 m n theta ≤ _root_.GD.N0232.N0720.N1076.d014528 j



theorem d014535 (j : ℕ) :
    _root_.GD.N0232.N0720.N1076.d014526 (_root_.GD.N0232.N0720.N1076.d014533 m n j) := by
  intro g theta
  simp only [_root_.GD.N0232.N0720.N1076.d014533, _root_.GD.N0232.N0720.N1069.d014355 m n hm hn]



theorem d014536 (j : ℕ) :
    _root_.GD.N0232.N0720.N1076.d014526 (_root_.GD.N0232.N0720.N1076.d014534 m n j) := by
  intro g theta
  simp only [_root_.GD.N0232.N0720.N1076.d014534, _root_.GD.N0232.N0720.N1069.d014355 m n hm hn]


def d014537
    (j : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (d : _root_.GD.N0232.N0720.N1025.d014303 m n) : ℝ :=
  _root_.GD.N0232.N0720.N1076.d014520 m n hm hn
    (_root_.GD.N0232.N0720.N1076.d014533 m n j) epsilon hepsilon d


def d014538
    (j : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (d : _root_.GD.N0232.N0720.N1025.d014303 m n) : ℝ :=
  _root_.GD.N0232.N0720.N1076.d014520 m n hm hn
    (_root_.GD.N0232.N0720.N1076.d014534 m n j) epsilon hepsilon d



def d014539
    (j : ℕ) (d : _root_.GD.N0232.N0720.N1025.d014303 m n) : ℝ :=
  _root_.GD.N0232.N0720.N1076.d014537 m n hm hn j
    (_root_.GD.N0232.N0720.N1076.d014531 j) (_root_.GD.N0232.N0720.N1076.d014532 j) d



def d014540
    (j : ℕ) (d : _root_.GD.N0232.N0720.N1025.d014303 m n) : ℝ :=
  _root_.GD.N0232.N0720.N1076.d014538 m n hm hn j
    (_root_.GD.N0232.N0720.N1076.d014531 j) (_root_.GD.N0232.N0720.N1076.d014532 j) d

theorem d014541
    (j : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    LowerSemicontinuousOn
      (_root_.GD.N0232.N0720.N1076.d014537
        m n hm hn j epsilon hepsilon)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) := by
  exact _root_.GD.N0232.N0720.N1076.d014521
    m n hm hn (_root_.GD.N0232.N0720.N1076.d014533 m n j) hepsilon

theorem d014542
    (j : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    LowerSemicontinuousOn
      (_root_.GD.N0232.N0720.N1076.d014538
        m n hm hn j epsilon hepsilon)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) := by
  exact _root_.GD.N0232.N0720.N1076.d014521
    m n hm hn (_root_.GD.N0232.N0720.N1076.d014534 m n j) hepsilon

theorem d014543
    (j : ℕ) :
    LowerSemicontinuousOn
      (_root_.GD.N0232.N0720.N1076.d014539 m n hm hn j)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) := by
  exact _root_.GD.N0232.N0720.N1076.d014541
    m n hm hn j (_root_.GD.N0232.N0720.N1076.d014532 j)

theorem d014544
    (j : ℕ) :
    LowerSemicontinuousOn
      (_root_.GD.N0232.N0720.N1076.d014540 m n hm hn j)
      (_root_.GD.N0232.N0720.N1025.d014304 m n hm hn) := by
  exact _root_.GD.N0232.N0720.N1076.d014542
    m n hm hn j (_root_.GD.N0232.N0720.N1076.d014532 j)

theorem d014545
    (j : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    _root_.GD.N0230.N0565.d000737 (_root_.GD.N0232.N0720.N1025.d014305 m n)
      (_root_.GD.N0232.N0720.N1076.d014537
        m n hm hn j epsilon hepsilon) := by
  exact _root_.GD.N0232.N0720.N1076.d014522
    m n hm hn (_root_.GD.N0232.N0720.N1076.d014533 m n j) hepsilon

theorem d014546
    (j : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    _root_.GD.N0230.N0565.d000737 (_root_.GD.N0232.N0720.N1025.d014305 m n)
      (_root_.GD.N0232.N0720.N1076.d014538
        m n hm hn j epsilon hepsilon) := by
  exact _root_.GD.N0232.N0720.N1076.d014522
    m n hm hn (_root_.GD.N0232.N0720.N1076.d014534 m n j) hepsilon

theorem d014547
    (j : ℕ) :
    _root_.GD.N0230.N0565.d000737 (_root_.GD.N0232.N0720.N1025.d014305 m n)
      (_root_.GD.N0232.N0720.N1076.d014539 m n hm hn j) := by
  exact _root_.GD.N0232.N0720.N1076.d014545
    m n hm hn j (_root_.GD.N0232.N0720.N1076.d014532 j)

theorem d014548
    (j : ℕ) :
    _root_.GD.N0230.N0565.d000737 (_root_.GD.N0232.N0720.N1025.d014305 m n)
      (_root_.GD.N0232.N0720.N1076.d014540 m n hm hn j) := by
  exact _root_.GD.N0232.N0720.N1076.d014546
    m n hm hn j (_root_.GD.N0232.N0720.N1076.d014532 j)

theorem d014549
    (j : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (g : _root_.GD.N0232.N0720.N1025.d014301) (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1076.d014537 m n hm hn j epsilon hepsilon
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1 =
      _root_.GD.N0232.N0720.N1076.d014537
        m n hm hn j epsilon hepsilon p.1 := by
  exact _root_.GD.N0232.N0720.N1076.d014527
    m n hm hn (_root_.GD.N0232.N0720.N1076.d014533 m n j)
      (_root_.GD.N0232.N0720.N1076.d014535 m n hm hn j) hepsilon g p

theorem d014550
    (j : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (g : _root_.GD.N0232.N0720.N1025.d014301) (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1076.d014538 m n hm hn j epsilon hepsilon
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1 =
      _root_.GD.N0232.N0720.N1076.d014538
        m n hm hn j epsilon hepsilon p.1 := by
  exact _root_.GD.N0232.N0720.N1076.d014527
    m n hm hn (_root_.GD.N0232.N0720.N1076.d014534 m n j)
      (_root_.GD.N0232.N0720.N1076.d014536 m n hm hn j) hepsilon g p

theorem d014551
    (j : ℕ) (g : _root_.GD.N0232.N0720.N1025.d014301)
    (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1076.d014539 m n hm hn j
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1 =
      _root_.GD.N0232.N0720.N1076.d014539 m n hm hn j p.1 := by
  exact _root_.GD.N0232.N0720.N1076.d014549
    m n hm hn j (_root_.GD.N0232.N0720.N1076.d014532 j) g p

theorem d014552
    (j : ℕ) (g : _root_.GD.N0232.N0720.N1025.d014301)
    (p : _root_.GD.N0232.N0720.N1025.d014304 m n hm hn) :
    _root_.GD.N0232.N0720.N1076.d014540 m n hm hn j
        (_root_.GD.N0232.N0720.N1025.d014316 m n hm hn g p).1 =
      _root_.GD.N0232.N0720.N1076.d014540 m n hm hn j p.1 := by
  exact _root_.GD.N0232.N0720.N1076.d014550
    m n hm hn j (_root_.GD.N0232.N0720.N1076.d014532 j) g p

end

end N1076
end N0720
end N0232
end GD

#print axioms _root_.GD.N0232.N0720.N1076.d014518
#print axioms _root_.GD.N0232.N0720.N1076.d014521
#print axioms _root_.GD.N0232.N0720.N1076.d014522
#print axioms _root_.GD.N0232.N0720.N1076.d014527
#print axioms _root_.GD.N0232.N0720.N1076.d014541
#print axioms _root_.GD.N0232.N0720.N1076.d014549
