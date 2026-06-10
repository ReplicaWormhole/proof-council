import Mathlib.Data.Finset.Prod

open scoped Finset

namespace Erdos539

theorem nat_mul_self_sub_self_eq_mul_pred (n : ℕ) :
    n * n - n = n * (n - 1) := by
  cases n with
  | zero => simp
  | succ n => simp [Nat.mul_succ]

namespace Finset

variable {α β γ : Type*} [DecidableEq γ]

def image2 (f : α → β → γ) (s : Finset α) (t : Finset β) : Finset γ :=
  (s ×ˢ t).image fun p ↦ f p.1 p.2

theorem mem_image2 {f : α → β → γ} {s : Finset α} {t : Finset β} {c : γ} :
    c ∈ image2 f s t ↔ ∃ a ∈ s, ∃ b ∈ t, f a b = c := by
  simp [image2, and_assoc]

theorem card_image2_le (f : α → β → γ) (s : Finset α) (t : Finset β) :
    #(image2 f s t) ≤ #s * #t := by
  calc
    #(image2 f s t) ≤ #(s ×ˢ t) := Finset.card_image_le
    _ = #s * #t := Finset.card_product s t

end Finset

abbrev IntPoint (ι : Type*) := ι → ℤ
abbrev NatPoint (ι : Type*) := ι → ℕ

variable {ι : Type*}

def pointSub (x y : IntPoint ι) : IntPoint ι :=
  fun i ↦ x i - y i

def delta (x y : IntPoint ι) : NatPoint ι :=
  fun i ↦ Int.toNat (x i - y i)

def intDelta (x y : IntPoint ι) : IntPoint ι :=
  fun i ↦ (delta x y i : ℤ)

theorem sub_eq_intDelta_sub_intDelta (x y : IntPoint ι) :
    pointSub x y = pointSub (intDelta x y) (intDelta y x) := by
  ext i
  simpa [pointSub, delta, intDelta, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    using (Int.toNat_sub_toNat_neg (x i - y i)).symm

variable [DecidableEq (ι → ℤ)] [DecidableEq (ι → ℕ)]

def posDiffs (B : Finset (IntPoint ι)) : Finset (NatPoint ι) :=
  (B ×ˢ B).image fun p ↦ delta p.1 p.2

omit [DecidableEq (ι → ℤ)] in
theorem delta_mem_posDiffs {B : Finset (IntPoint ι)} {x y : IntPoint ι}
    (hx : x ∈ B) (hy : y ∈ B) :
    delta x y ∈ posDiffs B :=
  Finset.mem_image.2 ⟨(x, y), by simp [hx, hy], rfl⟩

omit [DecidableEq (ι → ℤ)] in
theorem posDiffs_mono {B C : Finset (IntPoint ι)} (hBC : B ⊆ C) :
    posDiffs B ⊆ posDiffs C := by
  intro u hu
  rw [posDiffs] at hu ⊢
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
  exact Finset.mem_image.2
    ⟨p, by exact Finset.mem_product.2 ⟨hBC (Finset.mem_product.1 hp).1,
      hBC (Finset.mem_product.1 hp).2⟩, rfl⟩

omit [DecidableEq (ι → ℤ)] in
theorem card_posDiffs_le_of_subset {B C : Finset (IntPoint ι)} (hBC : B ⊆ C) :
    #(posDiffs B) ≤ #(posDiffs C) :=
  Finset.card_le_card (posDiffs_mono hBC)

def posDiffsInt (B : Finset (IntPoint ι)) : Finset (IntPoint ι) :=
  (posDiffs B).image fun v i ↦ (v i : ℤ)

def diffSet (B : Finset (IntPoint ι)) : Finset (IntPoint ι) :=
  Finset.image2 pointSub B B

omit [DecidableEq (ι → ℕ)] in
theorem diffSet_mono {B C : Finset (IntPoint ι)} (hBC : B ⊆ C) :
    diffSet B ⊆ diffSet C := by
  intro z hz
  rw [diffSet, Finset.mem_image2] at hz ⊢
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  exact ⟨x, hBC hx, y, hBC hy, rfl⟩

omit [DecidableEq (ι → ℕ)] in
theorem card_diffSet_le_of_subset {B C : Finset (IntPoint ι)} (hBC : B ⊆ C) :
    #(diffSet B) ≤ #(diffSet C) :=
  Finset.card_le_card (diffSet_mono hBC)

theorem intDelta_mem_posDiffsInt {B : Finset (IntPoint ι)} {x y : IntPoint ι}
    (hx : x ∈ B) (hy : y ∈ B) :
    intDelta x y ∈ posDiffsInt B := by
  refine Finset.mem_image.2 ?_
  refine ⟨delta x y, ?_, rfl⟩
  exact delta_mem_posDiffs hx hy

theorem diffSet_subset_posDiffsInt_diff (B : Finset (IntPoint ι)) :
    diffSet B ⊆ Finset.image2 pointSub (posDiffsInt B) (posDiffsInt B) := by
  intro z hz
  rw [diffSet, Finset.mem_image2] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  rw [Finset.mem_image2]
  refine ⟨intDelta x y, intDelta_mem_posDiffsInt hx hy,
    intDelta y x, intDelta_mem_posDiffsInt hy hx, ?_⟩
  exact (sub_eq_intDelta_sub_intDelta x y).symm

theorem card_diffSet_le_card_posDiffsInt_sq (B : Finset (IntPoint ι)) :
    #(diffSet B) ≤ #(posDiffsInt B) ^ 2 := by
  calc
    #(diffSet B) ≤ #(Finset.image2 pointSub (posDiffsInt B) (posDiffsInt B)) :=
      Finset.card_le_card (diffSet_subset_posDiffsInt_diff B)
    _ ≤ #(posDiffsInt B) * #(posDiffsInt B) :=
      Finset.card_image2_le pointSub (posDiffsInt B) (posDiffsInt B)
    _ = #(posDiffsInt B) ^ 2 := by rw [pow_two]

theorem card_posDiffsInt_le_card_posDiffs (B : Finset (IntPoint ι)) :
    #(posDiffsInt B) ≤ #(posDiffs B) :=
  Finset.card_image_le

omit [DecidableEq (ι → ℕ)] in
theorem card_diffSet_le_card_mul_pred_add_one (S : Finset (IntPoint ι)) :
    #(diffSet S) ≤ #S * (#S - 1) + 1 := by
  let offImage : Finset (IntPoint ι) := S.offDiag.image fun p ↦ pointSub p.1 p.2
  have hsubset : diffSet S ⊆ insert (0 : IntPoint ι) offImage := by
    intro z hz
    rw [diffSet, Finset.mem_image2] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    by_cases hxy : x = y
    · subst y
      rw [Finset.mem_insert]
      left
      ext i
      simp [pointSub]
    · rw [Finset.mem_insert]
      right
      refine Finset.mem_image.2 ⟨(x, y), ?_, rfl⟩
      rw [Finset.mem_offDiag]
      exact ⟨hx, hy, hxy⟩
  calc
    #(diffSet S) ≤ #(insert (0 : IntPoint ι) offImage) := Finset.card_le_card hsubset
    _ ≤ #offImage + 1 := Finset.card_insert_le _ _
    _ ≤ #S.offDiag + 1 := Nat.add_le_add_right Finset.card_image_le 1
    _ = (#S * #S - #S) + 1 := by rw [Finset.offDiag_card]
    _ = #S * (#S - 1) + 1 := by rw [nat_mul_self_sub_self_eq_mul_pred]

theorem card_diffSet_le_card_posDiffs_sq (B : Finset (IntPoint ι)) :
    #(diffSet B) ≤ #(posDiffs B) ^ 2 := by
  calc
    #(diffSet B) ≤ #(posDiffsInt B) ^ 2 := card_diffSet_le_card_posDiffsInt_sq B
    _ ≤ #(posDiffs B) ^ 2 :=
      Nat.pow_le_pow_left (card_posDiffsInt_le_card_posDiffs B) 2

theorem lower_bound_from_diffSet_card (B : Finset (IntPoint ι))
    (hB : 2 * #B - 1 ≤ #(diffSet B)) :
    2 * #B - 1 ≤ #(posDiffs B) ^ 2 :=
  le_trans hB (card_diffSet_le_card_posDiffs_sq B)

theorem card_diffSet_le_card_posDiffs_mul_pred_add_one (B : Finset (IntPoint ι)) :
    #(diffSet B) ≤ #(posDiffs B) * (#(posDiffs B) - 1) + 1 := by
  have hcard : #(posDiffsInt B) ≤ #(posDiffs B) := card_posDiffsInt_le_card_posDiffs B
  calc
    #(diffSet B) ≤ #(diffSet (posDiffsInt B)) := by
      simpa [diffSet] using Finset.card_le_card (diffSet_subset_posDiffsInt_diff B)
    _ ≤ #(posDiffsInt B) * (#(posDiffsInt B) - 1) + 1 :=
      card_diffSet_le_card_mul_pred_add_one (posDiffsInt B)
    _ ≤ #(posDiffs B) * (#(posDiffs B) - 1) + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul hcard (Nat.sub_le_sub_right hcard 1)) 1

theorem exact_lower_bound_from_diffSet_card (B : Finset (IntPoint ι))
    (hB : 2 * #B - 1 ≤ #(diffSet B)) :
    2 * #B - 1 ≤ #(posDiffs B) * (#(posDiffs B) - 1) + 1 :=
  le_trans hB (card_diffSet_le_card_posDiffs_mul_pred_add_one B)

end Erdos539
