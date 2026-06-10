import Mathlib.Tactic.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Ring.Int
import Erdos539.Basic

open scoped Finset

namespace Erdos539

abbrev SuspIndex (ι : Type*) := Option (Sum ι ι)

variable {ι : Type*}

def suspPoint (M : ℤ) (j : ℕ) (x y : IntPoint ι) : IntPoint (SuspIndex ι)
  | none => j
  | some (Sum.inl i) => x i + (j : ℤ) * M
  | some (Sum.inr i) => y i - (j : ℤ) * M

section SuspensionSet

variable [DecidableEq (IntPoint (SuspIndex ι))]

def suspension (K : ℕ) (M : ℤ) (F : Finset (IntPoint ι)) :
    Finset (IntPoint (SuspIndex ι)) :=
  (Finset.range K ×ˢ (F ×ˢ F)).image fun p ↦ suspPoint M p.1 p.2.1 p.2.2

omit [DecidableEq (IntPoint (SuspIndex ι))] in
theorem suspPoint_injective (M : ℤ) :
    Function.Injective
      (fun p : ℕ × (IntPoint ι × IntPoint ι) ↦
        suspPoint M p.1 p.2.1 p.2.2) := by
  intro p q h
  rcases p with ⟨j, x, y⟩
  rcases q with ⟨l, x', y'⟩
  have hjz : (j : ℤ) = l := congrFun h none
  have hj : j = l := Int.ofNat_inj.1 hjz
  subst l
  have hx : x = x' := by
    ext i
    simpa [suspPoint] using congrFun h (some (Sum.inl i))
  have hy : y = y' := by
    ext i
    simpa [suspPoint] using congrFun h (some (Sum.inr i))
  subst x'
  subst y'
  rfl

theorem card_suspension (K : ℕ) (M : ℤ) (F : Finset (IntPoint ι)) :
    #(suspension K M F) = K * #F ^ 2 := by
  rw [suspension, Finset.card_image_of_injective]
  · rw [Finset.card_product, Finset.card_range, Finset.card_product, pow_two]
  · exact suspPoint_injective M

end SuspensionSet

def joinNat (u v : NatPoint ι) : NatPoint (SuspIndex ι)
  | none => 0
  | some (Sum.inl i) => u i
  | some (Sum.inr i) => v i

section SameLevel

variable [DecidableEq (NatPoint ι)] [DecidableEq (NatPoint (SuspIndex ι))]

def sameLevelPosDiffs (F : Finset (IntPoint ι)) : Finset (NatPoint (SuspIndex ι)) :=
  (posDiffs F ×ˢ posDiffs F).image fun p ↦ joinNat p.1 p.2

theorem card_sameLevelPosDiffs_le (F : Finset (IntPoint ι)) :
    #(sameLevelPosDiffs F) ≤ #(posDiffs F) ^ 2 := by
  calc
    #(sameLevelPosDiffs F) ≤ #(posDiffs F ×ˢ posDiffs F) := Finset.card_image_le
    _ = #(posDiffs F) ^ 2 := by rw [Finset.card_product, pow_two]

omit [DecidableEq (NatPoint ι)] [DecidableEq (NatPoint (SuspIndex ι))] in
theorem delta_suspPoint_same_level (M : ℤ) (j : ℕ)
    (x y x' y' : IntPoint ι) :
    delta (suspPoint M j x y) (suspPoint M j x' y') =
      joinNat (delta x x') (delta y y') := by
  ext t
  cases t with
  | none =>
      simp [delta, suspPoint, joinNat]
  | some s =>
      cases s with
      | inl i =>
          simp [delta, suspPoint, joinNat, sub_eq_add_neg, add_comm, add_assoc]
      | inr i =>
          simp [delta, suspPoint, joinNat, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

theorem delta_suspPoint_same_level_mem {F : Finset (IntPoint ι)} {M : ℤ} {j : ℕ}
    {x y x' y' : IntPoint ι}
    (hx : x ∈ F) (hy : y ∈ F) (hx' : x' ∈ F) (hy' : y' ∈ F) :
    delta (suspPoint M j x y) (suspPoint M j x' y') ∈ sameLevelPosDiffs F := by
  rw [delta_suspPoint_same_level]
  exact Finset.mem_image.2
    ⟨(delta x x', delta y y'),
      by simp [delta_mem_posDiffs hx hx', delta_mem_posDiffs hy hy'], rfl⟩

end SameLevel

def suspensionSeparated (M : ℤ) (F : Finset (IntPoint ι)) : Prop :=
  ∀ a : ℕ, 1 ≤ a → ∀ x ∈ F, ∀ y ∈ F, ∀ i,
    x i - y i - (a : ℤ) * M ≤ 0

section SeparationExists

variable [Fintype ι]

def coordinateDifferences (F : Finset (IntPoint ι)) : Finset ℤ :=
  (((F ×ˢ F) ×ˢ (Finset.univ : Finset ι)).image fun p ↦
    p.1.1 p.2 - p.1.2 p.2)

def separationScale (F : Finset (IntPoint ι)) : ℤ :=
  (insert 0 (coordinateDifferences F)).max' (Finset.insert_nonempty _ _)

theorem coordinateDifference_mem {F : Finset (IntPoint ι)}
    {x y : IntPoint ι} (hx : x ∈ F) (hy : y ∈ F) (i : ι) :
    x i - y i ∈ coordinateDifferences F := by
  rw [coordinateDifferences, Finset.mem_image]
  refine ⟨((x, y), i), ?_, rfl⟩
  simp [hx, hy]

theorem coordinateDifference_le_separationScale {F : Finset (IntPoint ι)}
    {x y : IntPoint ι} (hx : x ∈ F) (hy : y ∈ F) (i : ι) :
    x i - y i ≤ separationScale F := by
  have hmem : x i - y i ∈ insert 0 (coordinateDifferences F) :=
    Finset.mem_insert.2 <| Or.inr <| coordinateDifference_mem hx hy i
  exact Finset.le_max' _ _ hmem

theorem zero_le_separationScale (F : Finset (IntPoint ι)) :
    0 ≤ separationScale F := by
  have hmem : (0 : ℤ) ∈ insert 0 (coordinateDifferences F) := Finset.mem_insert_self _ _
  exact Finset.le_max' _ _ hmem

theorem separationScale_add_one_separated (F : Finset (IntPoint ι)) :
    suspensionSeparated (separationScale F + 1) F := by
  intro a ha x hx y hy i
  have hdiff : x i - y i ≤ separationScale F :=
    coordinateDifference_le_separationScale hx hy i
  have hscale : 0 ≤ separationScale F := zero_le_separationScale F
  have hM : 0 ≤ separationScale F + 1 := by omega
  have haZ : (1 : ℤ) ≤ (a : ℤ) := by omega
  have hmul : separationScale F + 1 ≤ (a : ℤ) * (separationScale F + 1) := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right haZ hM
  omega

theorem exists_suspensionSeparated (F : Finset (IntPoint ι)) :
    ∃ M : ℤ, suspensionSeparated M F :=
  ⟨separationScale F + 1, separationScale_add_one_separated F⟩

end SeparationExists

def upperGapNat (M : ℤ) (a : ℕ) (z : IntPoint ι) : NatPoint (SuspIndex ι)
  | none => a
  | some (Sum.inl i) => Int.toNat (z i + (a : ℤ) * M)
  | some (Sum.inr _) => 0

def lowerGapNat (M : ℤ) (a : ℕ) (z : IntPoint ι) : NatPoint (SuspIndex ι)
  | none => 0
  | some (Sum.inl _) => 0
  | some (Sum.inr i) => Int.toNat (z i + (a : ℤ) * M)

def positiveLevelGaps (K : ℕ) : Finset ℕ :=
  (Finset.range K).erase 0

section MixedLevels

variable [DecidableEq (IntPoint ι)] [DecidableEq (NatPoint ι)]
  [DecidableEq (NatPoint (SuspIndex ι))]

theorem card_positiveLevelGaps (K : ℕ) :
    #(positiveLevelGaps K) = K - 1 := by
  cases K with
  | zero => simp [positiveLevelGaps]
  | succ K =>
      rw [positiveLevelGaps, Finset.card_erase_of_mem]
      · simp
      · simp

def upperMixedPosDiffs (K : ℕ) (M : ℤ) (F : Finset (IntPoint ι)) :
    Finset (NatPoint (SuspIndex ι)) :=
  (positiveLevelGaps K ×ˢ diffSet F).image fun p ↦ upperGapNat M p.1 p.2

def lowerMixedPosDiffs (K : ℕ) (M : ℤ) (F : Finset (IntPoint ι)) :
    Finset (NatPoint (SuspIndex ι)) :=
  (positiveLevelGaps K ×ˢ diffSet F).image fun p ↦ lowerGapNat M p.1 p.2

omit [DecidableEq (NatPoint ι)] in
theorem card_upperMixedPosDiffs_le (K : ℕ) (M : ℤ) (F : Finset (IntPoint ι)) :
    #(upperMixedPosDiffs K M F) ≤ (K - 1) * #(diffSet F) := by
  calc
    #(upperMixedPosDiffs K M F) ≤ #(positiveLevelGaps K ×ˢ diffSet F) := Finset.card_image_le
    _ = (K - 1) * #(diffSet F) := by rw [Finset.card_product, card_positiveLevelGaps]

omit [DecidableEq (NatPoint ι)] in
theorem card_lowerMixedPosDiffs_le (K : ℕ) (M : ℤ) (F : Finset (IntPoint ι)) :
    #(lowerMixedPosDiffs K M F) ≤ (K - 1) * #(diffSet F) := by
  calc
    #(lowerMixedPosDiffs K M F) ≤ #(positiveLevelGaps K ×ˢ diffSet F) := Finset.card_image_le
    _ = (K - 1) * #(diffSet F) := by rw [Finset.card_product, card_positiveLevelGaps]

omit [DecidableEq (IntPoint ι)] [DecidableEq (NatPoint ι)]
  [DecidableEq (NatPoint (SuspIndex ι))] in
theorem delta_suspPoint_upper_level
    {F : Finset (IntPoint ι)} {M : ℤ} (hsep : suspensionSeparated M F)
    {j l : ℕ} (hlj : l < j)
    {x y x' y' : IntPoint ι}
    (_hx : x ∈ F) (hy : y ∈ F) (_hx' : x' ∈ F) (hy' : y' ∈ F) :
    delta (suspPoint M j x y) (suspPoint M l x' y') =
      upperGapNat M (j - l) (pointSub x x') := by
  ext t
  cases t with
  | none =>
      change Int.toNat ((j : ℤ) - (l : ℤ)) = j - l
      rw [← Nat.cast_sub hlj.le]
      simp
  | some s =>
      cases s with
      | inl i =>
          rw [delta, upperGapNat, pointSub]
          congr 1
          simp [suspPoint]
          rw [Nat.cast_sub hlj.le]
          ring_nf
      | inr i =>
          rw [delta, upperGapNat]
          apply Int.toNat_eq_zero.2
          have hle := hsep (j - l) (by omega) y hy y' hy' i
          rw [Nat.cast_sub hlj.le] at hle
          convert hle using 1
          simp [suspPoint]
          ring_nf

omit [DecidableEq (IntPoint ι)] [DecidableEq (NatPoint ι)]
  [DecidableEq (NatPoint (SuspIndex ι))] in
theorem delta_suspPoint_lower_level
    {F : Finset (IntPoint ι)} {M : ℤ} (hsep : suspensionSeparated M F)
    {j l : ℕ} (hjl : j < l)
    {x y x' y' : IntPoint ι}
    (hx : x ∈ F) (_hy : y ∈ F) (hx' : x' ∈ F) (_hy' : y' ∈ F) :
    delta (suspPoint M j x y) (suspPoint M l x' y') =
      lowerGapNat M (l - j) (pointSub y y') := by
  ext t
  cases t with
  | none =>
      change Int.toNat ((j : ℤ) - (l : ℤ)) = 0
      apply Int.toNat_eq_zero.2
      omega
  | some s =>
      cases s with
      | inl i =>
          rw [delta, lowerGapNat]
          apply Int.toNat_eq_zero.2
          have hle := hsep (l - j) (by omega) x hx x' hx' i
          rw [Nat.cast_sub hjl.le] at hle
          convert hle using 1
          simp [suspPoint]
          ring_nf
      | inr i =>
          rw [delta, lowerGapNat, pointSub]
          congr 1
          simp [suspPoint]
          rw [Nat.cast_sub hjl.le]
          ring_nf

omit [DecidableEq (NatPoint ι)] in
theorem delta_suspPoint_upper_level_mem
    {F : Finset (IntPoint ι)} {K : ℕ} {M : ℤ} (hsep : suspensionSeparated M F)
    {j l : ℕ} (hj : j ∈ Finset.range K) (hlj : l < j)
    {x y x' y' : IntPoint ι}
    (hx : x ∈ F) (hy : y ∈ F) (hx' : x' ∈ F) (hy' : y' ∈ F) :
    delta (suspPoint M j x y) (suspPoint M l x' y') ∈ upperMixedPosDiffs K M F := by
  rw [delta_suspPoint_upper_level hsep hlj hx hy hx' hy']
  refine Finset.mem_image.2 ⟨(j - l, pointSub x x'), ?_, rfl⟩
  rw [Finset.mem_product]
  constructor
  · rw [positiveLevelGaps, Finset.mem_erase, Finset.mem_range]
    exact ⟨by omega, by
      have hjK := Finset.mem_range.1 hj
      omega⟩
  · rw [diffSet, Finset.mem_image2]
    exact ⟨x, hx, x', hx', rfl⟩

omit [DecidableEq (NatPoint ι)] in
theorem delta_suspPoint_lower_level_mem
    {F : Finset (IntPoint ι)} {K : ℕ} {M : ℤ} (hsep : suspensionSeparated M F)
    {j l : ℕ} (hl : l ∈ Finset.range K) (hjl : j < l)
    {x y x' y' : IntPoint ι}
    (hx : x ∈ F) (hy : y ∈ F) (hx' : x' ∈ F) (hy' : y' ∈ F) :
    delta (suspPoint M j x y) (suspPoint M l x' y') ∈ lowerMixedPosDiffs K M F := by
  rw [delta_suspPoint_lower_level hsep hjl hx hy hx' hy']
  refine Finset.mem_image.2 ⟨(l - j, pointSub y y'), ?_, rfl⟩
  rw [Finset.mem_product]
  constructor
  · rw [positiveLevelGaps, Finset.mem_erase, Finset.mem_range]
    exact ⟨by omega, by
      have hlK := Finset.mem_range.1 hl
      omega⟩
  · rw [diffSet, Finset.mem_image2]
    exact ⟨y, hy, y', hy', rfl⟩

def suspensionPosDiffsCover (K : ℕ) (M : ℤ) (F : Finset (IntPoint ι)) :
    Finset (NatPoint (SuspIndex ι)) :=
  sameLevelPosDiffs F ∪ upperMixedPosDiffs K M F ∪ lowerMixedPosDiffs K M F

theorem posDiffs_suspension_subset_cover
    [DecidableEq (IntPoint (SuspIndex ι))]
    {K : ℕ} {M : ℤ} {F : Finset (IntPoint ι)} (hsep : suspensionSeparated M F) :
    posDiffs (suspension K M F) ⊆ suspensionPosDiffsCover K M F := by
  intro u hu
  rw [posDiffs, suspension] at hu
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.1 hp
  obtain ⟨a, ha, hpa⟩ := Finset.mem_image.1 hp₁
  obtain ⟨b, hb, hpb⟩ := Finset.mem_image.1 hp₂
  rw [← hpa, ← hpb]
  rcases a with ⟨j, x, y⟩
  rcases b with ⟨l, x', y'⟩
  obtain ⟨hj, hxy⟩ := Finset.mem_product.1 ha
  obtain ⟨hx, hy⟩ := Finset.mem_product.1 hxy
  obtain ⟨hl, hx'y'⟩ := Finset.mem_product.1 hb
  obtain ⟨hx', hy'⟩ := Finset.mem_product.1 hx'y'
  rcases lt_trichotomy j l with hjl | rfl | hlj
  · exact Finset.mem_union.2 <| Or.inr
      (delta_suspPoint_lower_level_mem hsep hl hjl hx hy hx' hy')
  · exact Finset.mem_union.2 <| Or.inl <| Finset.mem_union.2 <| Or.inl <| by
      simpa using delta_suspPoint_same_level_mem hx hy hx' hy'
  · exact Finset.mem_union.2 <| Or.inl <| Finset.mem_union.2 <| Or.inr
      (delta_suspPoint_upper_level_mem hsep hj hlj hx hy hx' hy')

theorem card_posDiffs_suspension_le
    [DecidableEq (IntPoint (SuspIndex ι))]
    {K : ℕ} {M : ℤ} {F : Finset (IntPoint ι)} (hsep : suspensionSeparated M F) :
    #(posDiffs (suspension K M F)) ≤
      #(posDiffs F) ^ 2 + (K - 1) * #(diffSet F) + (K - 1) * #(diffSet F) := by
  calc
    #(posDiffs (suspension K M F)) ≤ #(suspensionPosDiffsCover K M F) :=
      Finset.card_le_card (posDiffs_suspension_subset_cover hsep)
    _ = #((sameLevelPosDiffs F ∪ upperMixedPosDiffs K M F) ∪ lowerMixedPosDiffs K M F) := by
      rfl
    _ ≤ #(sameLevelPosDiffs F ∪ upperMixedPosDiffs K M F) +
        #(lowerMixedPosDiffs K M F) :=
      Finset.card_union_le _ _
    _ ≤ #(sameLevelPosDiffs F) + #(upperMixedPosDiffs K M F) +
        #(lowerMixedPosDiffs K M F) :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ #(posDiffs F) ^ 2 + (K - 1) * #(diffSet F) + (K - 1) * #(diffSet F) :=
      Nat.add_le_add
        (Nat.add_le_add (card_sameLevelPosDiffs_le F) (card_upperMixedPosDiffs_le K M F))
        (card_lowerMixedPosDiffs_le K M F)

theorem card_posDiffs_suspension_le_explicit
    [DecidableEq (IntPoint (SuspIndex ι))]
    {K : ℕ} {M : ℤ} {F : Finset (IntPoint ι)} (hsep : suspensionSeparated M F) :
    #(posDiffs (suspension K M F)) ≤
      #(posDiffs F) ^ 2 + 2 * (K - 1) * #(diffSet F) := by
  calc
    #(posDiffs (suspension K M F)) ≤
        #(posDiffs F) ^ 2 + (K - 1) * #(diffSet F) + (K - 1) * #(diffSet F) :=
      card_posDiffs_suspension_le hsep
    _ = #(posDiffs F) ^ 2 + 2 * (K - 1) * #(diffSet F) := by
      rw [add_assoc]
      congr 1
      rw [← two_mul ((K - 1) * #(diffSet F)), Nat.mul_assoc]

end MixedLevels

def levelDiffs (K : ℕ) : Finset ℤ :=
  (Finset.range K ×ˢ Finset.range K).image fun p ↦ (p.1 : ℤ) - p.2

theorem levelDiffs_subset_Icc (K : ℕ) :
    levelDiffs K ⊆ Finset.Icc ((1 : ℤ) - K) ((K : ℤ) - 1) := by
  intro z hz
  rw [levelDiffs, Finset.mem_image] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  obtain ⟨hj, hl⟩ := Finset.mem_product.1 hp
  have hjK := Finset.mem_range.1 hj
  have hlK := Finset.mem_range.1 hl
  rw [Finset.mem_Icc]
  constructor <;> omega

theorem card_levelDiffs_le (K : ℕ) :
    #(levelDiffs K) ≤ 2 * K - 1 := by
  calc
    #(levelDiffs K) ≤ #(Finset.Icc ((1 : ℤ) - K) ((K : ℤ) - 1)) :=
      Finset.card_le_card (levelDiffs_subset_Icc K)
    _ = 2 * K - 1 := by
      apply Nat.cast_injective (R := ℤ)
      rw [Int.card_Icc]
      cases K with
      | zero => norm_num
      | succ K =>
          rw [Int.toNat_of_nonneg]
          · norm_num
            omega
          · omega

def joinIntGap (M a : ℤ) (u v : IntPoint ι) : IntPoint (SuspIndex ι)
  | none => a
  | some (Sum.inl i) => u i + a * M
  | some (Sum.inr i) => v i - a * M

section OrdinaryDiff

variable [DecidableEq (IntPoint ι)] [DecidableEq (IntPoint (SuspIndex ι))]

def suspensionDiffCover (K : ℕ) (M : ℤ) (F : Finset (IntPoint ι)) :
    Finset (IntPoint (SuspIndex ι)) :=
  (levelDiffs K ×ˢ (diffSet F ×ˢ diffSet F)).image fun p ↦
    joinIntGap M p.1 p.2.1 p.2.2

omit [DecidableEq (IntPoint ι)] [DecidableEq (IntPoint (SuspIndex ι))] in
theorem pointSub_suspPoint (M : ℤ) (j l : ℕ) (x y x' y' : IntPoint ι) :
    pointSub (suspPoint M j x y) (suspPoint M l x' y') =
      joinIntGap M ((j : ℤ) - l) (pointSub x x') (pointSub y y') := by
  ext t
  cases t with
  | none =>
      simp [pointSub, suspPoint, joinIntGap]
  | some s =>
      cases s with
      | inl i =>
          simp [pointSub, suspPoint, joinIntGap]
          ring_nf
      | inr i =>
          simp [pointSub, suspPoint, joinIntGap]
          ring_nf

theorem diffSet_suspension_subset_cover
    (K : ℕ) (M : ℤ) (F : Finset (IntPoint ι)) :
    diffSet (suspension K M F) ⊆ suspensionDiffCover K M F := by
  intro z hz
  rw [diffSet, suspension, Finset.mem_image2] at hz
  obtain ⟨p, hp, q, hq, rfl⟩ := hz
  obtain ⟨a, ha, hpa⟩ := Finset.mem_image.1 hp
  obtain ⟨b, hb, hqb⟩ := Finset.mem_image.1 hq
  rcases a with ⟨j, x, y⟩
  rcases b with ⟨l, x', y'⟩
  obtain ⟨hj, hxy⟩ := Finset.mem_product.1 ha
  obtain ⟨hx, hy⟩ := Finset.mem_product.1 hxy
  obtain ⟨hl, hx'y'⟩ := Finset.mem_product.1 hb
  obtain ⟨hx', hy'⟩ := Finset.mem_product.1 hx'y'
  rw [← hpa, ← hqb, pointSub_suspPoint]
  refine Finset.mem_image.2 ⟨((j : ℤ) - l, (pointSub x x', pointSub y y')), ?_, rfl⟩
  rw [Finset.mem_product]
  constructor
  · rw [levelDiffs, Finset.mem_image]
    exact ⟨(j, l), by simp [hj, hl], rfl⟩
  · rw [Finset.mem_product]
    constructor
    · rw [diffSet, Finset.mem_image2]
      exact ⟨x, hx, x', hx', rfl⟩
    · rw [diffSet, Finset.mem_image2]
      exact ⟨y, hy, y', hy', rfl⟩

theorem card_suspensionDiffCover_le (K : ℕ) (M : ℤ) (F : Finset (IntPoint ι)) :
    #(suspensionDiffCover K M F) ≤ #(levelDiffs K) * #(diffSet F) ^ 2 := by
  calc
    #(suspensionDiffCover K M F) ≤ #(levelDiffs K ×ˢ (diffSet F ×ˢ diffSet F)) :=
      Finset.card_image_le
    _ = #(levelDiffs K) * #(diffSet F) ^ 2 := by
      rw [Finset.card_product, Finset.card_product, pow_two]

theorem card_diffSet_suspension_le (K : ℕ) (M : ℤ) (F : Finset (IntPoint ι)) :
    #(diffSet (suspension K M F)) ≤ #(levelDiffs K) * #(diffSet F) ^ 2 := by
  exact le_trans (Finset.card_le_card (diffSet_suspension_subset_cover K M F))
    (card_suspensionDiffCover_le K M F)

theorem card_diffSet_suspension_le_explicit (K : ℕ) (M : ℤ) (F : Finset (IntPoint ι)) :
    #(diffSet (suspension K M F)) ≤ (2 * K - 1) * #(diffSet F) ^ 2 := by
  exact le_trans (card_diffSet_suspension_le K M F)
    (Nat.mul_le_mul_right _ (card_levelDiffs_le K))

end OrdinaryDiff

end Erdos539
