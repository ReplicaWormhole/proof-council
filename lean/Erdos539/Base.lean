import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.Interval
import Erdos539.Basic

open scoped Finset

namespace Erdos539

def boolNatPoint (r s : ℕ) : NatPoint Bool
  | false => r
  | true => s

def boolIntPoint (r s : ℤ) : IntPoint Bool
  | false => r
  | true => s

def basePoint (a b : ℕ) : IntPoint Bool :=
  boolIntPoint a ((b : ℤ) - a)

section BaseFamily

variable [DecidableEq (IntPoint Bool)]

def baseFamily (W : ℕ) : Finset (IntPoint Bool) :=
  (Finset.range (W ^ 2) ×ˢ Finset.range W).image fun p ↦ basePoint p.1 p.2

omit [DecidableEq (IntPoint Bool)] in
theorem basePoint_injective :
    Function.Injective (fun p : ℕ × ℕ ↦ basePoint p.1 p.2) := by
  intro p q h
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  have haZ : (a : ℤ) = c := congrFun h false
  have ha : a = c := Int.ofNat_inj.1 haZ
  subst c
  have hbZ : (b : ℤ) = d := by
    have htrue := congrFun h true
    simp [basePoint, boolIntPoint] at htrue
    omega
  have hb : b = d := Int.ofNat_inj.1 hbZ
  subst d
  rfl

theorem card_baseFamily (W : ℕ) :
    #(baseFamily W) = W ^ 3 := by
  rw [baseFamily, Finset.card_image_of_injective]
  · rw [Finset.card_product, Finset.card_range, Finset.card_range]
    ring
  · exact basePoint_injective

end BaseFamily

section PositiveDifferences

variable [DecidableEq (NatPoint Bool)]

def baseFalseAxis (W : ℕ) : Finset (NatPoint Bool) :=
  (Finset.range (W ^ 2 + 1)).image fun r ↦ boolNatPoint r 0

def baseTrueAxis (W : ℕ) : Finset (NatPoint Bool) :=
  (Finset.range (W ^ 2 + W + 1)).image fun s ↦ boolNatPoint 0 s

def baseCornerBox (W : ℕ) : Finset (NatPoint Bool) :=
  (Finset.range W ×ˢ Finset.range W).image fun p ↦ boolNatPoint p.1 p.2

def basePosCover (W : ℕ) : Finset (NatPoint Bool) :=
  baseFalseAxis W ∪ (baseTrueAxis W ∪ baseCornerBox W)

theorem card_baseFalseAxis_le (W : ℕ) :
    #(baseFalseAxis W) ≤ W ^ 2 + 1 := by
  calc
    #(baseFalseAxis W) ≤ #(Finset.range (W ^ 2 + 1)) := Finset.card_image_le
    _ = W ^ 2 + 1 := Finset.card_range _

theorem card_baseTrueAxis_le (W : ℕ) :
    #(baseTrueAxis W) ≤ W ^ 2 + W + 1 := by
  calc
    #(baseTrueAxis W) ≤ #(Finset.range (W ^ 2 + W + 1)) := Finset.card_image_le
    _ = W ^ 2 + W + 1 := Finset.card_range _

theorem card_baseCornerBox_le (W : ℕ) :
    #(baseCornerBox W) ≤ W ^ 2 := by
  calc
    #(baseCornerBox W) ≤ #(Finset.range W ×ˢ Finset.range W) := Finset.card_image_le
    _ = W ^ 2 := by rw [Finset.card_product, Finset.card_range, pow_two]

theorem card_basePosCover_le (W : ℕ) :
    #(basePosCover W) ≤ (W ^ 2 + 1) + (W ^ 2 + W + 1) + W ^ 2 := by
  calc
    #(basePosCover W) ≤ #(baseFalseAxis W) + #(baseTrueAxis W ∪ baseCornerBox W) := by
      rw [basePosCover]
      exact Finset.card_union_le _ _
    _ ≤ #(baseFalseAxis W) + (#(baseTrueAxis W) + #(baseCornerBox W)) := by
      exact Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ ≤ (W ^ 2 + 1) + ((W ^ 2 + W + 1) + W ^ 2) := by
      exact Nat.add_le_add (card_baseFalseAxis_le W)
        (Nat.add_le_add (card_baseTrueAxis_le W) (card_baseCornerBox_le W))
    _ = (W ^ 2 + 1) + (W ^ 2 + W + 1) + W ^ 2 := by omega

theorem card_basePosCover_le_six (W : ℕ) (hW : 1 ≤ W) :
    #(basePosCover W) ≤ 6 * W ^ 2 := by
  calc
    #(basePosCover W) ≤ (W ^ 2 + 1) + (W ^ 2 + W + 1) + W ^ 2 :=
      card_basePosCover_le W
    _ ≤ 6 * W ^ 2 := by
      nlinarith [sq_nonneg ((W : ℤ) - 1)]

omit [DecidableEq (NatPoint Bool)] in
theorem delta_basePoint (a b c d : ℕ) :
    delta (basePoint a b) (basePoint c d) =
      boolNatPoint (Int.toNat ((a : ℤ) - c))
        (Int.toNat (((b : ℤ) - a) - ((d : ℤ) - c))) := by
  ext t
  cases t <;>
    simp [delta, basePoint, boolIntPoint, boolNatPoint, sub_eq_add_neg, add_left_comm,
      add_assoc]

theorem delta_basePoint_mem_basePosCover {W a b c d : ℕ}
    (ha : a ∈ Finset.range (W ^ 2)) (hb : b ∈ Finset.range W)
    (hc : c ∈ Finset.range (W ^ 2)) (hd : d ∈ Finset.range W) :
    delta (basePoint a b) (basePoint c d) ∈ basePosCover W := by
  let r := Int.toNat ((a : ℤ) - c)
  let s := Int.toNat (((b : ℤ) - a) - ((d : ℤ) - c))
  have ha_lt : a < W ^ 2 := by simpa using ha
  have hb_lt : b < W := by simpa using hb
  have hc_lt : c < W ^ 2 := by simpa using hc
  have hd_lt : d < W := by simpa using hd
  rw [delta_basePoint]
  change boolNatPoint r s ∈ basePosCover W
  by_cases hs0 : s = 0
  · have hr_le : r ≤ W ^ 2 := by
      rw [Int.toNat_le]
      omega
    have hr_lt : r < W ^ 2 + 1 := by omega
    have hmem : boolNatPoint r 0 ∈ baseFalseAxis W :=
      Finset.mem_image.2 ⟨r, by simpa using hr_lt, rfl⟩
    rw [basePosCover]
    exact Finset.mem_union.2 <| Or.inl <| by simpa [hs0] using hmem
  · by_cases hr0 : r = 0
    · have hs_le : s ≤ W ^ 2 + W := by
        rw [Int.toNat_le]
        omega
      have hs_lt : s < W ^ 2 + W + 1 := by omega
      have hmem : boolNatPoint 0 s ∈ baseTrueAxis W :=
        Finset.mem_image.2 ⟨s, by simpa using hs_lt, rfl⟩
      rw [basePosCover]
      exact Finset.mem_union.2 <| Or.inr <| Finset.mem_union.2 <| Or.inl <| by
        simpa [hr0] using hmem
    · have hr_pos_int : 0 < (a : ℤ) - c := by
        have hle : ¬ (a : ℤ) - c ≤ 0 := by
          intro hle
          exact hr0 (Int.toNat_eq_zero.2 hle)
        omega
      have hs_pos_int : 0 < ((b : ℤ) - a) - ((d : ℤ) - c) := by
        have hle : ¬ ((b : ℤ) - a) - ((d : ℤ) - c) ≤ 0 := by
          intro hle
          exact hs0 (Int.toNat_eq_zero.2 hle)
        omega
      have hr_cast : (r : ℤ) = (a : ℤ) - c := by
        exact Int.toNat_of_nonneg (le_of_lt hr_pos_int)
      have hs_cast : (s : ℤ) = ((b : ℤ) - a) - ((d : ℤ) - c) := by
        exact Int.toNat_of_nonneg (le_of_lt hs_pos_int)
      have hrs_cast : ((r + s : ℕ) : ℤ) = (b : ℤ) - d := by
        rw [Nat.cast_add, hr_cast, hs_cast]
        ring
      have hrs_lt_int : ((r + s : ℕ) : ℤ) < W := by
        rw [hrs_cast]
        omega
      have hrs_lt : r + s < W := by omega
      have hr_lt : r < W := by omega
      have hs_lt : s < W := by omega
      have hmem : boolNatPoint r s ∈ baseCornerBox W :=
        Finset.mem_image.2 ⟨(r, s), by simp [hr_lt, hs_lt], rfl⟩
      rw [basePosCover]
      exact Finset.mem_union.2 <| Or.inr <| Finset.mem_union.2 <| Or.inr hmem

variable [DecidableEq (IntPoint Bool)]

theorem posDiffs_baseFamily_subset_cover (W : ℕ) :
    posDiffs (baseFamily W) ⊆ basePosCover W := by
  intro u hu
  rw [posDiffs] at hu
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨hx, hy⟩ := Finset.mem_product.1 hp
  rw [baseFamily] at hx hy
  obtain ⟨ab, hab, hab_eq⟩ := Finset.mem_image.1 hx
  obtain ⟨cd, hcd, hcd_eq⟩ := Finset.mem_image.1 hy
  rw [← hab_eq, ← hcd_eq]
  exact delta_basePoint_mem_basePosCover
    (Finset.mem_product.1 hab).1 (Finset.mem_product.1 hab).2
    (Finset.mem_product.1 hcd).1 (Finset.mem_product.1 hcd).2

theorem card_posDiffs_baseFamily_le (W : ℕ) (hW : 1 ≤ W) :
    #(posDiffs (baseFamily W)) ≤ 6 * W ^ 2 :=
  le_trans (Finset.card_le_card (posDiffs_baseFamily_subset_cover W))
    (card_basePosCover_le_six W hW)

end PositiveDifferences

section OrdinaryDifferences

variable [DecidableEq (IntPoint Bool)]

def baseFirstDiffs (W : ℕ) : Finset ℤ :=
  Finset.Icc (-((W ^ 2 : ℕ) : ℤ)) ((W ^ 2 : ℕ) : ℤ)

def baseSumDiffs (W : ℕ) : Finset ℤ :=
  Finset.Icc (-(W : ℤ)) (W : ℤ)

def baseDiffCover (W : ℕ) : Finset (IntPoint Bool) :=
  (baseFirstDiffs W ×ˢ baseSumDiffs W).image fun p ↦
    boolIntPoint p.1 (p.2 - p.1)

omit [DecidableEq (IntPoint Bool)] in
theorem pointSub_basePoint (a b c d : ℕ) :
    pointSub (basePoint a b) (basePoint c d) =
      boolIntPoint ((a : ℤ) - c) (((b : ℤ) - d) - ((a : ℤ) - c)) := by
  ext t
  cases t <;>
    simp [pointSub, basePoint, boolIntPoint, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc]

omit [DecidableEq (IntPoint Bool)] in
theorem card_baseFirstDiffs (W : ℕ) :
    #(baseFirstDiffs W) = 2 * W ^ 2 + 1 := by
  have hle : (-((W ^ 2 : ℕ) : ℤ)) ≤ ((W ^ 2 : ℕ) : ℤ) + 1 := by omega
  have hcard := Int.card_Icc_of_le (-((W ^ 2 : ℕ) : ℤ)) ((W ^ 2 : ℕ) : ℤ) hle
  rw [baseFirstDiffs]
  omega

omit [DecidableEq (IntPoint Bool)] in
theorem card_baseSumDiffs (W : ℕ) :
    #(baseSumDiffs W) = 2 * W + 1 := by
  have hle : (-(W : ℤ)) ≤ (W : ℤ) + 1 := by omega
  have hcard := Int.card_Icc_of_le (-(W : ℤ)) (W : ℤ) hle
  rw [baseSumDiffs]
  omega

theorem card_baseDiffCover_le (W : ℕ) :
    #(baseDiffCover W) ≤ (2 * W ^ 2 + 1) * (2 * W + 1) := by
  calc
    #(baseDiffCover W) ≤ #(baseFirstDiffs W ×ˢ baseSumDiffs W) := Finset.card_image_le
    _ = (2 * W ^ 2 + 1) * (2 * W + 1) := by
      rw [Finset.card_product, card_baseFirstDiffs, card_baseSumDiffs]

theorem card_baseDiffCover_le_nine (W : ℕ) (hW : 1 ≤ W) :
    #(baseDiffCover W) ≤ 9 * W ^ 3 := by
  calc
    #(baseDiffCover W) ≤ (2 * W ^ 2 + 1) * (2 * W + 1) := card_baseDiffCover_le W
    _ ≤ 9 * W ^ 3 := by
      nlinarith [sq_nonneg ((W : ℤ) - 1), sq_nonneg (W : ℤ)]

theorem pointSub_basePoint_mem_baseDiffCover {W a b c d : ℕ}
    (ha : a ∈ Finset.range (W ^ 2)) (hb : b ∈ Finset.range W)
    (hc : c ∈ Finset.range (W ^ 2)) (hd : d ∈ Finset.range W) :
    pointSub (basePoint a b) (basePoint c d) ∈ baseDiffCover W := by
  have ha_lt : a < W ^ 2 := by simpa using ha
  have hb_lt : b < W := by simpa using hb
  have hc_lt : c < W ^ 2 := by simpa using hc
  have hd_lt : d < W := by simpa using hd
  rw [pointSub_basePoint]
  refine Finset.mem_image.2 ⟨((a : ℤ) - c, (b : ℤ) - d), ?_, rfl⟩
  rw [Finset.mem_product]
  constructor
  · rw [baseFirstDiffs, Finset.mem_Icc]
    constructor <;> omega
  · rw [baseSumDiffs, Finset.mem_Icc]
    constructor <;> omega

theorem diffSet_baseFamily_subset_cover (W : ℕ) :
    diffSet (baseFamily W) ⊆ baseDiffCover W := by
  intro z hz
  rw [diffSet, Finset.mem_image2] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  rw [baseFamily] at hx hy
  obtain ⟨ab, hab, hab_eq⟩ := Finset.mem_image.1 hx
  obtain ⟨cd, hcd, hcd_eq⟩ := Finset.mem_image.1 hy
  rw [← hab_eq, ← hcd_eq]
  exact pointSub_basePoint_mem_baseDiffCover
    (Finset.mem_product.1 hab).1 (Finset.mem_product.1 hab).2
    (Finset.mem_product.1 hcd).1 (Finset.mem_product.1 hcd).2

theorem card_diffSet_baseFamily_le (W : ℕ) (hW : 1 ≤ W) :
    #(diffSet (baseFamily W)) ≤ 9 * W ^ 3 :=
  le_trans (Finset.card_le_card (diffSet_baseFamily_subset_cover W))
    (card_baseDiffCover_le_nine W hW)

end OrdinaryDifferences

end Erdos539
