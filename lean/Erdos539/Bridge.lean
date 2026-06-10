import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Ring.Int
import Erdos539.Basic

open scoped Finset

namespace Erdos539

variable {ι : Type*}

def translatePoint (t x : IntPoint ι) : IntPoint ι :=
  fun i => x i + t i

section Translation

variable [DecidableEq (IntPoint ι)]

def translateFinset (t : IntPoint ι) (B : Finset (IntPoint ι)) : Finset (IntPoint ι) :=
  B.image (translatePoint t)

omit [DecidableEq (IntPoint ι)] in
theorem translatePoint_injective (t : IntPoint ι) :
    Function.Injective (translatePoint t) := by
  intro x y h
  ext i
  have hi := congrFun h i
  simp [translatePoint] at hi
  omega

theorem card_translateFinset (t : IntPoint ι) (B : Finset (IntPoint ι)) :
    #(translateFinset t B) = #B := by
  rw [translateFinset, Finset.card_image_of_injective]
  exact translatePoint_injective t

omit [DecidableEq (IntPoint ι)] in
theorem delta_translatePoint (t x y : IntPoint ι) :
    delta (translatePoint t x) (translatePoint t y) = delta x y := by
  ext i
  rw [delta, delta, translatePoint, translatePoint]
  congr 1
  omega

variable [DecidableEq (NatPoint ι)]

theorem posDiffs_translateFinset (t : IntPoint ι) (B : Finset (IntPoint ι)) :
    posDiffs (translateFinset t B) = posDiffs B := by
  ext u
  constructor
  · intro hu
    rw [posDiffs] at hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨hx, hy⟩ := Finset.mem_product.1 hp
    rw [translateFinset] at hx hy
    obtain ⟨x, hxB, hx_eq⟩ := Finset.mem_image.1 hx
    obtain ⟨y, hyB, hy_eq⟩ := Finset.mem_image.1 hy
    rw [← hx_eq, ← hy_eq, delta_translatePoint]
    exact delta_mem_posDiffs hxB hyB
  · intro hu
    rw [posDiffs] at hu ⊢
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨hx, hy⟩ := Finset.mem_product.1 hp
    exact Finset.mem_image.2
      ⟨(translatePoint t p.1, translatePoint t p.2), by
        rw [Finset.mem_product]
        constructor
        · rw [translateFinset]
          exact Finset.mem_image.2 ⟨p.1, hx, rfl⟩
        · rw [translateFinset]
          exact Finset.mem_image.2 ⟨p.2, hy, rfl⟩,
        by rw [delta_translatePoint]⟩

theorem card_posDiffs_translateFinset (t : IntPoint ι) (B : Finset (IntPoint ι)) :
    #(posDiffs (translateFinset t B)) = #(posDiffs B) := by
  rw [posDiffs_translateFinset]

end Translation

section NonnegativeTranslation

def coordinateShift (B : Finset (IntPoint ι)) : IntPoint ι :=
  fun i => (insert 0 (B.image fun x => -x i)).max' (Finset.insert_nonempty _ _)

theorem zero_le_coordinateShift (B : Finset (IntPoint ι)) (i : ι) :
    0 ≤ coordinateShift B i := by
  have hmem : (0 : ℤ) ∈ insert 0 (B.image fun x => -x i) := Finset.mem_insert_self _ _
  exact Finset.le_max' _ _ hmem

theorem neg_coordinate_le_coordinateShift {B : Finset (IntPoint ι)}
    {x : IntPoint ι} (hx : x ∈ B) (i : ι) :
    -x i ≤ coordinateShift B i := by
  have hmem : -x i ∈ insert 0 (B.image fun x => -x i) := by
    exact Finset.mem_insert.2 <| Or.inr <| Finset.mem_image.2 ⟨x, hx, rfl⟩
  exact Finset.le_max' _ _ hmem

theorem translate_coordinateShift_nonneg {B : Finset (IntPoint ι)}
    {x : IntPoint ι} (hx : x ∈ B) (i : ι) :
    0 ≤ translatePoint (coordinateShift B) x i := by
  have h := neg_coordinate_le_coordinateShift hx i
  simp [translatePoint]
  omega

end NonnegativeTranslation

def natPointOfInt (x : IntPoint ι) : NatPoint ι :=
  fun i => Int.toNat (x i)

def natDelta (x y : NatPoint ι) : NatPoint ι :=
  fun i => x i - y i

theorem toNat_sub_toNat_of_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a.toNat - b.toNat = (a - b).toNat := by
  by_cases h : b ≤ a
  · apply Int.ofNat.inj
    change ((a.toNat - b.toNat : ℕ) : ℤ) = (((a - b).toNat : ℕ) : ℤ)
    have hle : b.toNat ≤ a.toNat := by omega
    have hnon : 0 ≤ a - b := by omega
    rw [Int.ofNat_sub hle, Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb,
      Int.toNat_of_nonneg hnon]
  · have hle : a.toNat ≤ b.toNat := by omega
    have hsub : a - b ≤ 0 := by omega
    rw [Nat.sub_eq_zero_of_le hle, Int.toNat_eq_zero.2 hsub]

section TranslatedNatSet

variable [DecidableEq (NatPoint ι)]

def natPosDiffs (B : Finset (NatPoint ι)) : Finset (NatPoint ι) :=
  (B ×ˢ B).image fun p => natDelta p.1 p.2

def translatedNatFinset (B : Finset (IntPoint ι)) : Finset (NatPoint ι) :=
  B.image fun x => natPointOfInt (translatePoint (coordinateShift B) x)

omit [DecidableEq (NatPoint ι)] in
theorem translatedNatPoint_injective_on (B : Finset (IntPoint ι)) :
    Set.InjOn (fun x => natPointOfInt (translatePoint (coordinateShift B) x)) ↑B := by
  intro x hx y hy hxy
  ext i
  have hi := congrFun hxy i
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) hi
  simp [natPointOfInt] at hcast
  rw [max_eq_left (translate_coordinateShift_nonneg hx i),
    max_eq_left (translate_coordinateShift_nonneg hy i)] at hcast
  simp [translatePoint] at hcast
  omega

theorem card_translatedNatFinset (B : Finset (IntPoint ι)) :
    #(translatedNatFinset B) = #B := by
  rw [translatedNatFinset]
  exact Finset.card_image_of_injOn (translatedNatPoint_injective_on B)

omit [DecidableEq (NatPoint ι)] in
theorem natDelta_translatedNatPoint {B : Finset (IntPoint ι)}
    {x y : IntPoint ι} (hx : x ∈ B) (hy : y ∈ B) :
    natDelta (natPointOfInt (translatePoint (coordinateShift B) x))
      (natPointOfInt (translatePoint (coordinateShift B) y)) = delta x y := by
  ext i
  simp only [natDelta, natPointOfInt, delta]
  rw [toNat_sub_toNat_of_nonneg (translate_coordinateShift_nonneg hx i)
    (translate_coordinateShift_nonneg hy i)]
  congr 1
  simp [translatePoint]

theorem natPosDiffs_translatedNatFinset_subset_posDiffs (B : Finset (IntPoint ι)) :
    natPosDiffs (translatedNatFinset B) ⊆ posDiffs B := by
  intro u hu
  rw [natPosDiffs] at hu
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨hx, hy⟩ := Finset.mem_product.1 hp
  rw [translatedNatFinset] at hx hy
  obtain ⟨x, hxB, hx_eq⟩ := Finset.mem_image.1 hx
  obtain ⟨y, hyB, hy_eq⟩ := Finset.mem_image.1 hy
  rw [← hx_eq, ← hy_eq, natDelta_translatedNatPoint hxB hyB]
  exact delta_mem_posDiffs hxB hyB

theorem card_natPosDiffs_translatedNatFinset_le_posDiffs (B : Finset (IntPoint ι)) :
    #(natPosDiffs (translatedNatFinset B)) ≤ #(posDiffs B) :=
  Finset.card_le_card (natPosDiffs_translatedNatFinset_subset_posDiffs B)

end TranslatedNatSet

end Erdos539
