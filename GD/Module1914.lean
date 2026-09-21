import GD.Module0529
import GD.Module1345
import GD.Module1728
import GD.Module1913





set_option autoImplicit false
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace GD.N0138.N0429
noncomputable section
open _root_.GD.N0138.N0430

theorem d030968 {n : ℕ} (x : _root_.GD.N0138.N0430.d007904 n) :
    _root_.GD.N0138.N0430.d007910 n x = _root_.GD.N0107.d009084 x := by
  simp [_root_.GD.N0138.N0430.d007910, _root_.GD.N0107.d009084,
    _root_.GD.N0126.d006420, _root_.GD.N0126.d006419]

theorem d030969 {n : ℕ} (x : _root_.GD.N0138.N0430.d007904 n) :
    _root_.GD.N0138.N0430.d007911 n x = _root_.GD.N0107.d009085 x := by
  simp [_root_.GD.N0138.N0430.d007911, _root_.GD.N0138.N0429.d030968, _root_.GD.N0107.d009085,
    _root_.GD.N0126.d006422, _root_.GD.N0126.d006421,
    _root_.GD.N0107.d009084]

theorem d030970 (m n : ℕ) (mu sigma tau : ℝ) :
    _root_.GD.N0138.N0430.d007909 m n mu sigma tau = _root_.GD.N0107.d009030 m n mu sigma tau := by
  rfl

theorem d030971 (k : ℕ) (sizes : Fin k → ℕ) (mu : ℝ) (sigma : Fin k → ℝ) :
    _root_.GD.N0138.N0430.d007908 k sizes mu sigma = _root_.GD.N0232.N0719.d009176 k sizes mu sigma := by
  rfl

theorem d030972 (k : ℕ) (sizes : Fin k → ℕ) :
    _root_.GD.N0138.N0430.d007913 k sizes = _root_.GD.N0232.N0719.N0900.d009111 k sizes := by
  funext x
  simp [_root_.GD.N0138.N0430.d007913, _root_.GD.N0138.N0430.d007912, _root_.GD.N0138.N0429.d030968, _root_.GD.N0138.N0429.d030969,
    _root_.GD.N0232.N0719.N0900.d009111,
    _root_.GD.N0232.N0719.N0900.d009110,
    _root_.GD.N0232.N0719.N0900.d009104,
    _root_.GD.N0232.N0719.N0900.d009102,
    _root_.GD.N0232.N0719.N0900.d009103,
    _root_.GD.N0232.N0719.N0900.d009108,
    _root_.GD.N0232.N0719.N0900.d009107,
    _root_.GD.N0232.N0719.N0900.d009106,
    _root_.GD.N0232.N0719.N0900.d009105]

theorem d030973 : _root_.GD.N0138.N0430.d007917 := by
  intro k hk mu sigma hsigma
  let theta : _root_.GD.N0232.N0719.N0859.d010809 k := ⟨mu, sigma, hsigma⟩
  have h := _root_.GD.N0106.N0428.N0770.N1748.d021783 hk theta
  have h' :
      _root_.GD.N0138.N0430.d007915
          (_root_.GD.N0138.N0430.d007908 k (fun _ => 2) mu sigma)
          mu (_root_.GD.N0138.N0430.d007913 k (fun _ => 2)) =
        ((∑ i, sigma i) / (∑ i, (sigma i)⁻¹) +
          (k : ℝ) / (∑ i, (sigma i)⁻¹) ^ 2) / 4 := by
    simpa [_root_.GD.N0232.N0719.N0972.d012340,
      _root_.GD.N0232.N0719.N0859.d010812,
      _root_.GD.N0232.N0719.N0859.d010815,
      _root_.GD.N0141.d006684, _root_.GD.N0138.N0430.d007915, _root_.GD.N0138.N0429.d030971, _root_.GD.N0138.N0429.d030972, theta] using h
  exact h'

open _root_.GD.N0232.N0720.N1080 in
theorem d030974 (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (theta : _root_.GD.N0232.N0720.N1080.d014168) :
    _root_.GD.N0138.N0430.d007914 m n =ᵐ[_root_.GD.N0232.N0720.N1080.d014171 m n theta] _root_.GD.N0107.d012733 m n := by
  apply (_root_.GD.N0232.N0720.N1080.d014173 m n theta).ae_le
  rw [_root_.GD.N0232.N0720.N1449.d018839]
  have hpos := _root_.GD.N0119.d009075
    m n hm hn (e := 1 / 2) (by norm_num) (by norm_num)
  filter_upwards [hpos] with x hx
  have hx' : 0 < _root_.GD.N0107.d009085 x.1 := hx.1
  have hy' : 0 < _root_.GD.N0107.d009085 x.2 := hx.2
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hden := add_pos (div_pos hx' hm') (div_pos hy' hn')
  simp [_root_.GD.N0138.N0430.d007914, _root_.GD.N0138.N0429.d030969, _root_.GD.N0138.N0429.d030968, if_pos hden,
    _root_.GD.N0107.d012733, _root_.GD.N0107.d009091,
    _root_.GD.N0107.d009090]

theorem d030975 : _root_.GD.N0138.N0430.d007918 := by
  intro m n hm hn
  have hm2 : 2 ≤ m := hm
  have hn2 : 2 ≤ n := hn
  obtain ⟨epsilon, _, hmeas, h⟩ :=
    _root_.GD.N0106.N0428.N0766.N1689.d028789 m n hm2 hn2
  refine ⟨_, hmeas, ?_⟩
  intro mu sigma tau hsigma htau
  obtain ⟨hint, _, hlt⟩ := h mu sigma tau hsigma htau
  refine ⟨by simpa only [_root_.GD.N0138.N0429.d030970] using hint, ?_⟩
  have hbase := _root_.GD.N0138.N0429.d030974 m n hm2 hn2 ⟨mu, sigma, tau, hsigma, htau⟩
  have hrisk : _root_.GD.N0138.N0430.d007915 (_root_.GD.N0138.N0430.d007909 m n mu sigma tau) mu (_root_.GD.N0138.N0430.d007914 m n) =
      _root_.GD.N0141.d006684 (_root_.GD.N0107.d009030 m n mu sigma tau)
        (fun x => _root_.GD.N0107.d012733 m n x - mu) := by
    unfold _root_.GD.N0138.N0430.d007915 _root_.GD.N0141.d006684
    rw [_root_.GD.N0138.N0429.d030970]
    apply integral_congr_ae
    filter_upwards [hbase] with x hx
    rw [hx]
  rw [hrisk]
  exact hlt

theorem d030976 : _root_.GD.N0138.N0430.d007919 =
    _root_.GD.N0200.d030833 := by
  funext x
  rw [_root_.GD.N0200.d030836]
  simp only [_root_.GD.N0138.N0430.d007919, _root_.GD.N0138.N0429.d030969, _root_.GD.N0138.N0429.d030968]
  have hz (a b : ℝ) : a ^ 2 + b ^ 2 = 0 ↔ a = 0 ∧ b = 0 := by
    constructor
    · intro h
      constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
    · rintro ⟨rfl, rfl⟩
      norm_num
  simp only [hz]

open _root_.GD.N0232.N0720.N1080
open _root_.GD.N0232.N0720.N1256

def d030977 (mu : ℝ) (sigma tau : _root_.GD.N0138.N0430.d007920) : _root_.GD.N0232.N0720.N1080.d014168 :=
  ⟨mu, sigma, tau, sigma.property, tau.property⟩

theorem d030978 (d : _root_.GD.N0138.N0430.d007904 3 × _root_.GD.N0138.N0430.d007904 3 → ℝ)
    (mu : ℝ) (sigma tau : _root_.GD.N0138.N0430.d007920) :
    _root_.GD.N0138.N0430.d007921 d mu sigma tau = _root_.GD.N0232.N0720.N1256.d015547 3 3 (_root_.GD.N0138.N0429.d030977 mu sigma tau) d := by
  simp [_root_.GD.N0138.N0430.d007921, _root_.GD.N0138.N0430.d007916, _root_.GD.N0232.N0720.N1256.d015547, _root_.GD.N0232.N0720.N1080.d014197,
    _root_.GD.N0232.N0720.N1257.d015508, _root_.GD.N0232.N0720.N1080.d014171, _root_.GD.N0138.N0429.d030977, _root_.GD.N0138.N0429.d030970,
    one_div]

theorem d030979 (d : _root_.GD.N0138.N0430.d007904 3 × _root_.GD.N0138.N0430.d007904 3 → ℝ) :
    _root_.GD.N0138.N0430.d007922 d = _root_.GD.N0232.N0720.N1256.d015548 3 3 d := by
  unfold _root_.GD.N0138.N0430.d007922 _root_.GD.N0232.N0720.N1256.d015548 _root_.GD.N0230.N0611.d003516
  simp only [_root_.GD.N0138.N0429.d030978]
  apply le_antisymm
  · exact iSup_le fun mu => iSup_le fun sigma => iSup_le fun tau =>
      le_iSup (fun theta => _root_.GD.N0232.N0720.N1256.d015547 3 3 theta d) (_root_.GD.N0138.N0429.d030977 mu sigma tau)
  · apply iSup_le
    intro theta
    exact le_iSup_of_le theta.location (le_iSup_of_le ⟨theta.scale₁, theta.scale₁_pos⟩
      (le_iSup_of_le ⟨theta.scale₂, theta.scale₂_pos⟩ (by rfl)))

theorem d030980 : _root_.GD.N0138.N0430.d007923 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d hd
    rw [_root_.GD.N0138.N0429.d030979]
    exact _root_.GD.N0184.d030934 d hd
  · rw [_root_.GD.N0138.N0429.d030976]
    exact _root_.GD.N0200.d030838
  · rw [_root_.GD.N0138.N0429.d030979, _root_.GD.N0138.N0429.d030976]
    exact _root_.GD.N0199.d030966
  · intro mu sigma tau
    rw [_root_.GD.N0138.N0429.d030978, _root_.GD.N0138.N0429.d030976]
    exact _root_.GD.N0199.d030964 _

end
end GD.N0138.N0429
