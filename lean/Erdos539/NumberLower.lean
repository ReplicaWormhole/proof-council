import Erdos539.DifferenceLower
import Erdos539.NumberBridge

open scoped Finset

namespace Erdos539

def primeSupport (A : Finset ℕ) : Finset ℕ :=
  A.biUnion Nat.primeFactors

abbrev PrimeIndex (A : Finset ℕ) := {p // p ∈ primeSupport A}

def exponentVector (A : Finset ℕ) (a : ℕ) : IntPoint (PrimeIndex A) :=
  fun p => (a.factorization p.val : ℤ)

def exponentSet (A : Finset ℕ) : Finset (IntPoint (PrimeIndex A)) :=
  A.image (exponentVector A)

def quotientExponentVector (A : Finset ℕ) (q : ℕ) : NatPoint (PrimeIndex A) :=
  fun p => q.factorization p.val

theorem prime_mem_primeSupport {A : Finset ℕ} {a p : ℕ}
    (ha : a ∈ A) (hp : p ∈ a.primeFactors) :
    p ∈ primeSupport A := by
  rw [primeSupport, Finset.mem_biUnion]
  exact ⟨a, ha, hp⟩

theorem factorization_eq_zero_of_not_mem_primeSupport
    {A : Finset ℕ} {a p : ℕ} (ha : a ∈ A) (ha0 : a ≠ 0)
    (hp : p ∉ primeSupport A) :
    a.factorization p = 0 := by
  by_cases hprime : Nat.Prime p
  · by_cases hdvd : p ∣ a
    · have hmem : p ∈ a.primeFactors := Nat.mem_primeFactors.2 ⟨hprime, hdvd, ha0⟩
      exact (hp (prime_mem_primeSupport ha hmem)).elim
    · exact Nat.factorization_eq_zero_of_not_dvd hdvd
  · exact Nat.factorization_eq_zero_of_not_prime a hprime

theorem exponentVector_injOn {A : Finset ℕ}
    (hpos : ∀ a ∈ A, a ≠ 0) :
    Set.InjOn (exponentVector A) ↑A := by
  intro a ha b hb hab
  apply Nat.factorization_inj (hpos a ha) (hpos b hb)
  ext p
  by_cases hp : p ∈ primeSupport A
  · have hcoord := congrFun hab ⟨p, hp⟩
    exact Int.ofNat_inj.1 hcoord
  · rw [factorization_eq_zero_of_not_mem_primeSupport ha (hpos a ha) hp,
      factorization_eq_zero_of_not_mem_primeSupport hb (hpos b hb) hp]

theorem card_exponentSet {A : Finset ℕ} (hpos : ∀ a ∈ A, a ≠ 0) :
    #(exponentSet A) = #A := by
  rw [exponentSet]
  exact Finset.card_image_of_injOn (exponentVector_injOn hpos)

theorem int_toNat_natCast_sub_natCast (m n : ℕ) :
    Int.toNat ((m : ℤ) - n) = m - n := by
  by_cases h : n ≤ m
  · apply Int.ofNat.inj
    change (((((m : ℤ) - n).toNat) : ℕ) : ℤ) = ((m - n : ℕ) : ℤ)
    rw [Int.toNat_of_nonneg (by omega), Int.ofNat_sub h]
  · have hle : m ≤ n := by omega
    have hsub : (m : ℤ) - n ≤ 0 := by omega
    rw [Int.toNat_eq_zero.2 hsub, Nat.sub_eq_zero_of_le hle]

theorem factorization_normalizedQuotient_apply {a b p : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (normalizedQuotient a b).factorization p = a.factorization p - b.factorization p := by
  rw [normalizedQuotient, Nat.factorization_div (Nat.gcd_dvd_left a b),
    Nat.factorization_gcd ha hb]
  simp
  omega

theorem quotientExponentVector_eq_delta {A : Finset ℕ} {a b : ℕ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    quotientExponentVector A (normalizedQuotient a b) =
      delta (exponentVector A a) (exponentVector A b) := by
  ext p
  simp [quotientExponentVector, exponentVector, delta,
    factorization_normalizedQuotient_apply ha0 hb0]

theorem posDiffs_exponentSet_subset_quotientSet_image
    {A : Finset ℕ} (hpos : ∀ a ∈ A, a ≠ 0) :
    posDiffs (exponentSet A) ⊆ (quotientSet A).image (quotientExponentVector A) := by
  intro u hu
  rw [posDiffs] at hu
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨hx, hy⟩ := Finset.mem_product.1 hp
  rw [exponentSet] at hx hy
  obtain ⟨a, ha, ha_eq⟩ := Finset.mem_image.1 hx
  obtain ⟨b, hb, hb_eq⟩ := Finset.mem_image.1 hy
  rw [← ha_eq, ← hb_eq, ← quotientExponentVector_eq_delta (hpos a ha) (hpos b hb)]
  refine Finset.mem_image.2 ?_
  refine ⟨normalizedQuotient a b, ?_, rfl⟩
  rw [quotientSet, Finset.mem_image2]
  exact ⟨a, ha, b, hb, rfl⟩

theorem card_posDiffs_exponentSet_le_quotientSet
    {A : Finset ℕ} (hpos : ∀ a ∈ A, a ≠ 0) :
    #(posDiffs (exponentSet A)) ≤ #(quotientSet A) := by
  calc
    #(posDiffs (exponentSet A)) ≤ #((quotientSet A).image (quotientExponentVector A)) :=
      Finset.card_le_card (posDiffs_exponentSet_subset_quotientSet_image hpos)
    _ ≤ #(quotientSet A) := Finset.card_image_le

theorem card_quotientSet_square_lower
    (A : Finset ℕ) (hpos : ∀ a ∈ A, a ≠ 0) (hA : A.Nonempty) :
    2 * #A - 1 ≤ #(quotientSet A) ^ 2 := by
  have hExpNonempty : (exponentSet A).Nonempty := hA.image _
  calc
    2 * #A - 1 = 2 * #(exponentSet A) - 1 := by rw [card_exponentSet hpos]
    _ ≤ #(posDiffs (exponentSet A)) ^ 2 :=
      square_posDiffs_lower (exponentSet A) hExpNonempty
    _ ≤ #(quotientSet A) ^ 2 :=
      Nat.pow_le_pow_left (card_posDiffs_exponentSet_le_quotientSet hpos) 2

theorem card_quotientSet_exact_lower
    (A : Finset ℕ) (hpos : ∀ a ∈ A, a ≠ 0) (hA : A.Nonempty) :
    2 * #A - 1 ≤ #(quotientSet A) * (#(quotientSet A) - 1) + 1 := by
  have hExpNonempty : (exponentSet A).Nonempty := hA.image _
  have hle : #(posDiffs (exponentSet A)) ≤ #(quotientSet A) :=
    card_posDiffs_exponentSet_le_quotientSet hpos
  calc
    2 * #A - 1 = 2 * #(exponentSet A) - 1 := by rw [card_exponentSet hpos]
    _ ≤ #(posDiffs (exponentSet A)) * (#(posDiffs (exponentSet A)) - 1) + 1 :=
      exact_posDiffs_lower (exponentSet A) hExpNonempty
    _ ≤ #(quotientSet A) * (#(quotientSet A) - 1) + 1 := by
      exact Nat.add_le_add_right (Nat.mul_le_mul hle (Nat.sub_le_sub_right hle 1)) 1

end Erdos539
