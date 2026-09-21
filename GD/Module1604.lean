import GD.Module1581
import GD.Module1582
import GD.Module1583
import GD.Module1584
import GD.Module1585
import GD.Module1586
import GD.Module1587
import GD.Module1588
import GD.Module1589
import GD.Module1590
import GD.Module1591
import GD.Module1592
import GD.Module1593
import GD.Module1594
import GD.Module1595
import GD.Module1596
import GD.Module1597
import GD.Module1598
import GD.Module1599
import GD.Module1600
import GD.Module1601
import GD.Module1602
import GD.Module1603
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000
open Set
open _root_.GD.N0106.N0428.N0770.N1704
open _root_.GD.N0106.N0428.N0770.N1705
open _root_.GD.N0106.N0428.N0770.N1728
namespace GD.N0106.N0428.N0770.N1706
noncomputable section
theorem d027363 : _root_.GD.N0106.N0428.N0770.N1704.d026300 0 (1/2) := (_root_.GD.N0106.N0428.N0770.N1704.d026302 (_root_.GD.N0106.N0428.N0770.N1704.d026302 (_root_.GD.N0106.N0428.N0770.N1704.d026302 (_root_.GD.N0106.N0428.N0770.N1704.d026302 _root_.GD.N0106.N0428.N0770.N1705.d026351 _root_.GD.N0106.N0428.N0770.N1705.d026400) (_root_.GD.N0106.N0428.N0770.N1704.d026302 _root_.GD.N0106.N0428.N0770.N1705.d026449 (_root_.GD.N0106.N0428.N0770.N1704.d026302 _root_.GD.N0106.N0428.N0770.N1705.d026498 _root_.GD.N0106.N0428.N0770.N1705.d026547))) (_root_.GD.N0106.N0428.N0770.N1704.d026302 (_root_.GD.N0106.N0428.N0770.N1704.d026302 _root_.GD.N0106.N0428.N0770.N1705.d026596 (_root_.GD.N0106.N0428.N0770.N1704.d026302 _root_.GD.N0106.N0428.N0770.N1705.d026645 _root_.GD.N0106.N0428.N0770.N1705.d026694)) (_root_.GD.N0106.N0428.N0770.N1704.d026302 _root_.GD.N0106.N0428.N0770.N1705.d026743 (_root_.GD.N0106.N0428.N0770.N1704.d026302 _root_.GD.N0106.N0428.N0770.N1705.d026792 _root_.GD.N0106.N0428.N0770.N1705.d026841)))) (_root_.GD.N0106.N0428.N0770.N1704.d026302 (_root_.GD.N0106.N0428.N0770.N1704.d026302 (_root_.GD.N0106.N0428.N0770.N1704.d026302 _root_.GD.N0106.N0428.N0770.N1705.d026890 _root_.GD.N0106.N0428.N0770.N1705.d026939) (_root_.GD.N0106.N0428.N0770.N1704.d026302 _root_.GD.N0106.N0428.N0770.N1705.d026988 (_root_.GD.N0106.N0428.N0770.N1704.d026302 _root_.GD.N0106.N0428.N0770.N1705.d027037 _root_.GD.N0106.N0428.N0770.N1705.d027086))) (_root_.GD.N0106.N0428.N0770.N1704.d026302 (_root_.GD.N0106.N0428.N0770.N1704.d026302 _root_.GD.N0106.N0428.N0770.N1705.d027135 (_root_.GD.N0106.N0428.N0770.N1704.d026302 _root_.GD.N0106.N0428.N0770.N1705.d027184 _root_.GD.N0106.N0428.N0770.N1705.d027233)) (_root_.GD.N0106.N0428.N0770.N1704.d026302 _root_.GD.N0106.N0428.N0770.N1705.d027282 (_root_.GD.N0106.N0428.N0770.N1704.d026302 _root_.GD.N0106.N0428.N0770.N1705.d027331 _root_.GD.N0106.N0428.N0770.N1705.d027362)))))
theorem d027364 (q : ℝ) (hq : q ∈ Icc (0 : ℝ) (1/2)) : _root_.GD.N0106.N0428.N0770.N1728.d024397 q < -47/200 := by
  apply _root_.GD.N0106.N0428.N0770.N1706.d027363 q ⟨hq.1, hq.2.trans (by norm_num)⟩
  · simpa using hq.1
  · simpa using hq.2


theorem d027365 (k : ℕ) (hk : k < 50000) {q : ℝ}
    (hlo : (k : ℝ) / 100000 ≤ q) (hhi : q ≤ ((k : ℝ)+1)/100000) : _root_.GD.N0106.N0428.N0770.N1728.d024397 q < -47/200 := by
  apply _root_.GD.N0106.N0428.N0770.N1706.d027364 q
  constructor
  · exact (div_nonneg (Nat.cast_nonneg k) (by norm_num)).trans hlo
  · have hkR : (k : ℝ)+1 ≤ 50000 := by exact_mod_cast (Nat.succ_le_iff.mpr hk)
    linarith


theorem d027366 {q : ℝ} (hq : q ∈ Icc (0 : ℝ) (1/2)) :
    ∃ k : ℕ, k < 50000 ∧ (k : ℝ)/100000 ≤ q ∧ q ≤ ((k : ℝ)+1)/100000 := by
  have h0 : (0 : ℝ) ≤ 100000*q := mul_nonneg (by norm_num) hq.1
  have hfl : ((⌊100000*q⌋₊ : ℕ) : ℝ) ≤ 100000*q := Nat.floor_le h0
  have hlt : 100000*q < ((⌊100000*q⌋₊ : ℕ) : ℝ)+1 := Nat.lt_floor_add_one _
  by_cases hcase : ⌊100000*q⌋₊ < 50000
  · exact ⟨⌊100000*q⌋₊, hcase, by linarith, by linarith⟩
  · have h50 : (50000 : ℝ) ≤ ((⌊100000*q⌋₊ : ℕ) : ℝ) := by exact_mod_cast not_lt.mp hcase
    refine ⟨49999, by norm_num, ?_, ?_⟩ <;> norm_num <;> linarith [hq.2]

end
end GD.N0106.N0428.N0770.N1706
#print axioms _root_.GD.N0106.N0428.N0770.N1706.d027364
#print axioms _root_.GD.N0106.N0428.N0770.N1706.d027365
#print axioms _root_.GD.N0106.N0428.N0770.N1706.d027366
