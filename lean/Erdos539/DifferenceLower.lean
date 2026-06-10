import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.PiLex
import Erdos539.Basic

open scoped Finset

namespace Erdos539

def orderedDiffSet {α : Type*} [Sub α] [DecidableEq α] (S : Finset α) : Finset α :=
  Finset.image2 (fun x y ↦ x - y) S S

def intDiffSet (S : Finset ℤ) : Finset ℤ :=
  orderedDiffSet S

private instance instLexPiIsOrderedCancelAddMonoid
    {ι : Type*} {α : ι → Type*} [LinearOrder ι]
    [∀ i, AddCommMonoid (α i)] [∀ i, PartialOrder (α i)]
    [∀ i, IsOrderedCancelAddMonoid (α i)] :
    IsOrderedCancelAddMonoid (Lex (∀ i, α i)) where
  add_le_add_left _ _ hxy z :=
    hxy.elim (fun hxyz ↦ hxyz ▸ le_rfl) fun ⟨i, hi⟩ ↦
      Or.inr ⟨i, fun j hji ↦ congr_arg (· + z j) (hi.1 j hji),
        add_lt_add_left hi.2 _⟩
  le_of_add_le_add_left _ _ _ hxyz :=
    hxyz.elim (fun h ↦ (add_left_cancel h).le) fun ⟨i, hi⟩ ↦
      Or.inr ⟨i, fun j hj ↦ add_left_cancel (hi.1 j hj), lt_of_add_lt_add_left hi.2⟩

private instance instLexIntPointIsOrderedCancelAddMonoid
    {ι : Type*} [LinearOrder ι] :
    IsOrderedCancelAddMonoid (Lex (IntPoint ι)) :=
  instLexPiIsOrderedCancelAddMonoid (ι := ι) (α := fun _ ↦ ℤ)

theorem two_mul_sub_one_eq_add_pred (n : ℕ) :
    2 * n - 1 = n + (n - 1) := by
  omega

theorem mem_orderedDiffSet {α : Type*} [Sub α] [DecidableEq α]
    {S : Finset α} {x y : α} (hx : x ∈ S) (hy : y ∈ S) :
    x - y ∈ orderedDiffSet S := by
  rw [orderedDiffSet, Finset.mem_image2]
  exact ⟨x, hx, y, hy, rfl⟩

theorem card_orderedDiffSet_lower {α : Type*} [DecidableEq α] [AddCommGroup α]
    [LinearOrder α] [IsOrderedCancelAddMonoid α] {S : Finset α} (hS : S.Nonempty) :
    2 * #S - 1 ≤ #(orderedDiffSet S) := by
  let m := S.max' hS
  let A : Finset α := S.image fun x ↦ x - m
  let B : Finset α := (S.erase m).image fun x ↦ m - x
  have hm : m ∈ S := S.max'_mem hS
  have hAcard : #A = #S := by
    dsimp [A]
    refine Finset.card_image_of_injective S ?_
    intro x y hxy
    exact (add_left_inj (-m)).1 (by simpa [sub_eq_add_neg] using hxy)
  have hBcard : #B = #S - 1 := by
    dsimp [B]
    rw [Finset.card_image_of_injective, Finset.card_erase_of_mem hm]
    intro x y hxy
    have hneg : -x = -y := (add_right_inj m).1 (by simpa [sub_eq_add_neg] using hxy)
    exact neg_injective hneg
  have hA_subset : A ⊆ orderedDiffSet S := by
    intro z hz
    dsimp [A] at hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    exact mem_orderedDiffSet hx hm
  have hB_subset : B ⊆ orderedDiffSet S := by
    intro z hz
    dsimp [B] at hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    exact mem_orderedDiffSet hm (Finset.mem_of_mem_erase hx)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro z hzA hzB
    dsimp [A] at hzA
    dsimp [B] at hzB
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hzA
    obtain ⟨y, hy, hyz⟩ := Finset.mem_image.1 hzB
    have hxle : x ≤ m := S.le_max' x hx
    have hylt : y < m := S.lt_max'_of_mem_erase_max' hS hy
    have hnonpos : x - m ≤ 0 := sub_nonpos.2 hxle
    have hpos : 0 < x - m := by
      rw [← hyz]
      exact sub_pos.2 hylt
    exact (not_lt_of_ge hnonpos) hpos
  calc
    2 * #S - 1 = #S + (#S - 1) := two_mul_sub_one_eq_add_pred #S
    _ = #A + #B := by rw [hAcard, hBcard]
    _ = #(A ∪ B) := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ #(orderedDiffSet S) := Finset.card_le_card (Finset.union_subset hA_subset hB_subset)

theorem card_intDiffSet_lower {S : Finset ℤ} (hS : S.Nonempty) :
    2 * #S - 1 ≤ #(intDiffSet S) := by
  exact card_orderedDiffSet_lower hS

theorem orderedDiffSet_lex_image_image_ofLex
    {ι : Type*} [DecidableEq (IntPoint ι)] (B : Finset (IntPoint ι)) :
    (orderedDiffSet (B.image toLex : Finset (Lex (IntPoint ι)))).image ofLex = diffSet B := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz
    rw [orderedDiffSet, Finset.mem_image2] at hw
    obtain ⟨a, ha, b, hb, rfl⟩ := hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
    rw [diffSet, Finset.mem_image2]
    refine ⟨x, hx, y, hy, ?_⟩
    ext i
    rfl
  · intro hz
    rw [diffSet, Finset.mem_image2] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    refine Finset.mem_image.2 ⟨toLex (pointSub x y), ?_, rfl⟩
    rw [orderedDiffSet, Finset.mem_image2]
    refine ⟨toLex x, Finset.mem_image.2 ⟨x, hx, rfl⟩,
      toLex y, Finset.mem_image.2 ⟨y, hy, rfl⟩, ?_⟩
    rw [show pointSub x y = x - y by
      ext i
      rfl]
    simp

theorem card_diffSet_lower
    {ι : Type*} [DecidableEq (IntPoint ι)] [LinearOrder ι] [WellFoundedLT ι]
    (B : Finset (IntPoint ι)) (hB : B.Nonempty) :
    2 * #B - 1 ≤ #(diffSet B) := by
  let BL : Finset (Lex (IntPoint ι)) := B.image toLex
  have hBL : BL.Nonempty := hB.image _
  have hBLcard : #BL = #B := Finset.card_image_of_injective B toLex.injective
  have hlow : 2 * #BL - 1 ≤ #(orderedDiffSet BL) := by
    exact @card_orderedDiffSet_lower (Lex (IntPoint ι)) _ _ _
      (instLexIntPointIsOrderedCancelAddMonoid (ι := ι)) BL hBL
  calc
    2 * #B - 1 = 2 * #BL - 1 := by rw [hBLcard]
    _ ≤ #(orderedDiffSet BL) := hlow
    _ = #((orderedDiffSet BL).image ofLex) :=
      (Finset.card_image_of_injective (orderedDiffSet BL) ofLex.injective).symm
    _ = #(diffSet B) := by rw [orderedDiffSet_lex_image_image_ofLex B]

theorem exact_posDiffs_lower
    {ι : Type*} [DecidableEq (IntPoint ι)] [DecidableEq (NatPoint ι)]
    [LinearOrder ι] [WellFoundedLT ι]
    (B : Finset (IntPoint ι)) (hB : B.Nonempty) :
    2 * #B - 1 ≤ #(posDiffs B) * (#(posDiffs B) - 1) + 1 :=
  exact_lower_bound_from_diffSet_card B (card_diffSet_lower B hB)

theorem square_posDiffs_lower
    {ι : Type*} [DecidableEq (IntPoint ι)] [DecidableEq (NatPoint ι)]
    [LinearOrder ι] [WellFoundedLT ι]
    (B : Finset (IntPoint ι)) (hB : B.Nonempty) :
    2 * #B - 1 ≤ #(posDiffs B) ^ 2 :=
  lower_bound_from_diffSet_card B (card_diffSet_lower B hB)

end Erdos539
