import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Erdos539.Bridge
import Erdos539.Iteration

open scoped Finset

namespace Erdos539

variable {ι : Type*}

noncomputable def finitePrimeEmbedding (ι : Type*) [Fintype ι] : ι → ℕ :=
  fun i => Nat.nth Nat.Prime ((Fintype.equivFin ι i).val)

theorem finitePrimeEmbedding_prime (ι : Type*) [Fintype ι] (i : ι) :
    Nat.Prime (finitePrimeEmbedding ι i) := by
  rw [finitePrimeEmbedding]
  exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _

theorem finitePrimeEmbedding_injective (ι : Type*) [Fintype ι] :
    Function.Injective (finitePrimeEmbedding ι) := by
  intro i j hij
  rw [finitePrimeEmbedding] at hij
  have hval := Nat.nth_injective Nat.infinite_setOf_prime hij
  have hfin : Fintype.equivFin ι i = Fintype.equivFin ι j := Fin.ext hval
  exact (Fintype.equivFin ι).injective hfin

def encodeNatPoint [Fintype ι] (p : ι → ℕ) (x : NatPoint ι) : ℕ :=
  ∏ i, p i ^ x i

theorem encodeNatPoint_ne_zero [Fintype ι] {p : ι → ℕ}
    (hp : ∀ i, Nat.Prime (p i)) (x : NatPoint ι) :
    encodeNatPoint p x ≠ 0 := by
  classical
  rw [encodeNatPoint]
  exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hp i).ne_zero

theorem factorization_encodeNatPoint_apply [Fintype ι] {p : ι → ℕ}
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (x : NatPoint ι) (i : ι) :
    (encodeNatPoint p x).factorization (p i) = x i := by
  classical
  rw [encodeNatPoint]
  rw [Nat.factorization_prod]
  · simp only [(hp _).factorization_pow, Finsupp.coe_finset_sum, Finset.sum_apply]
    change (∑ c, (Finsupp.single (p c) (x c)) (p i)) = x i
    calc
      (∑ c, (Finsupp.single (p c) (x c)) (p i)) =
          (Finsupp.single (p i) (x i)) (p i) := by
        refine @Finset.sum_eq_single ι ℕ _ Finset.univ
          (fun c => (Finsupp.single (p c) (x c)) (p i)) i ?_ ?_
        · intro j _ hji
          exact Finsupp.single_eq_of_ne
            (show p i ≠ p j by
              intro hpij
              exact hji (hinj hpij.symm))
        · intro hi
          simp at hi
      _ = x i := Finsupp.single_eq_same
  · intro j _
    exact pow_ne_zero _ (hp j).ne_zero

theorem encodeNatPoint_injective [Fintype ι] {p : ι → ℕ}
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p) :
    Function.Injective (encodeNatPoint p) := by
  intro x y hxy
  ext i
  have hfac := congrArg (fun n : ℕ => n.factorization (p i)) hxy
  change (encodeNatPoint p x).factorization (p i) =
    (encodeNatPoint p y).factorization (p i) at hfac
  rw [factorization_encodeNatPoint_apply hp hinj x i,
    factorization_encodeNatPoint_apply hp hinj y i] at hfac
  exact hfac

theorem factorization_encodeNatPoint_eq_zero_of_not_mem [Fintype ι] {p : ι → ℕ}
    (hp : ∀ i, Nat.Prime (p i)) {r : ℕ} (hr : r ∉ Set.range p)
    (x : NatPoint ι) :
    (encodeNatPoint p x).factorization r = 0 := by
  classical
  rw [encodeNatPoint, Nat.factorization_prod]
  · simp only [(hp _).factorization_pow, Finsupp.coe_finset_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero ?_
    intro i _
    exact Finsupp.single_eq_of_ne
      (show r ≠ p i by
        intro h
        exact hr ⟨i, h.symm⟩)
  · intro j _
    exact pow_ne_zero _ (hp j).ne_zero

def normalizedQuotient (a b : ℕ) : ℕ :=
  a / Nat.gcd a b

theorem factorization_normalizedQuotient_encodeNatPoint_apply [Fintype ι] {p : ι → ℕ}
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (x y : NatPoint ι) (i : ι) :
    (normalizedQuotient (encodeNatPoint p x) (encodeNatPoint p y)).factorization (p i) =
      natDelta x y i := by
  classical
  let ax := encodeNatPoint p x
  let ay := encodeNatPoint p y
  have hax : ax ≠ 0 := encodeNatPoint_ne_zero hp x
  have hay : ay ≠ 0 := encodeNatPoint_ne_zero hp y
  rw [normalizedQuotient, Nat.factorization_div (Nat.gcd_dvd_left ax ay),
    Nat.factorization_gcd hax hay]
  simp [ax, ay, factorization_encodeNatPoint_apply hp hinj, natDelta]
  omega

theorem normalizedQuotient_encodeNatPoint_eq [Fintype ι] {p : ι → ℕ}
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (x y : NatPoint ι) :
    normalizedQuotient (encodeNatPoint p x) (encodeNatPoint p y) =
      encodeNatPoint p (natDelta x y) := by
  classical
  let ax := encodeNatPoint p x
  let ay := encodeNatPoint p y
  have hax : ax ≠ 0 := encodeNatPoint_ne_zero hp x
  have hleft : normalizedQuotient ax ay ≠ 0 := by
    exact ne_of_gt (Nat.div_pos (Nat.gcd_le_left ay (Nat.pos_of_ne_zero hax))
      (Nat.gcd_pos_of_pos_left ay (Nat.pos_of_ne_zero hax)))
  have hright : encodeNatPoint p (natDelta x y) ≠ 0 := encodeNatPoint_ne_zero hp (natDelta x y)
  apply Nat.factorization_inj hleft hright
  ext r
  by_cases hr : r ∈ Set.range p
  · obtain ⟨i, rfl⟩ := hr
    rw [factorization_normalizedQuotient_encodeNatPoint_apply hp hinj,
      factorization_encodeNatPoint_apply hp hinj]
  · have hay : ay ≠ 0 := encodeNatPoint_ne_zero hp y
    rw [normalizedQuotient, Nat.factorization_div (Nat.gcd_dvd_left ax ay),
      Nat.factorization_gcd hax hay]
    simp [ax, ay, factorization_encodeNatPoint_eq_zero_of_not_mem hp hr]

section FiniteSets

variable [Fintype ι] [DecidableEq (NatPoint ι)]

def encodedNatSet (p : ι → ℕ) (B : Finset (NatPoint ι)) : Finset ℕ :=
  B.image (encodeNatPoint p)

def quotientSet (A : Finset ℕ) : Finset ℕ :=
  Finset.image2 normalizedQuotient A A

def NumberUpperWitness (n q : ℕ) : Prop :=
  ∃ A : Finset ℕ, (∀ a ∈ A, 0 < a) ∧ #A = n ∧ #(quotientSet A) ≤ q

theorem NumberUpperWitness.mono {n q r : ℕ}
    (h : NumberUpperWitness n q) (hqr : q ≤ r) :
    NumberUpperWitness n r := by
  rcases h with ⟨A, hpos, hcard, hq⟩
  exact ⟨A, hpos, hcard, le_trans hq hqr⟩

omit [Fintype ι] in
theorem natDelta_mem_natPosDiffs {B : Finset (NatPoint ι)} {x y : NatPoint ι}
    (hx : x ∈ B) (hy : y ∈ B) :
    natDelta x y ∈ natPosDiffs B :=
  Finset.mem_image.2 ⟨(x, y), by simp [hx, hy], rfl⟩

omit [DecidableEq (NatPoint ι)] in
theorem card_encodedNatSet (p : ι → ℕ)
    (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (B : Finset (NatPoint ι)) :
    #(encodedNatSet p B) = #B := by
  rw [encodedNatSet, Finset.card_image_of_injective]
  exact encodeNatPoint_injective hp hinj

theorem quotientSet_encodedNatSet_subset
    {p : ι → ℕ} (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (B : Finset (NatPoint ι)) :
    quotientSet (encodedNatSet p B) ⊆ (natPosDiffs B).image (encodeNatPoint p) := by
  intro q hq
  rw [quotientSet, Finset.mem_image2] at hq
  obtain ⟨a, ha, b, hb, rfl⟩ := hq
  rw [encodedNatSet] at ha hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb
  rw [normalizedQuotient_encodeNatPoint_eq hp hinj]
  exact Finset.mem_image.2 ⟨natDelta x y, natDelta_mem_natPosDiffs hx hy, rfl⟩

theorem card_quotientSet_encodedNatSet_le
    {p : ι → ℕ} (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    (B : Finset (NatPoint ι)) :
    #(quotientSet (encodedNatSet p B)) ≤ #(natPosDiffs B) := by
  calc
    #(quotientSet (encodedNatSet p B)) ≤ #((natPosDiffs B).image (encodeNatPoint p)) :=
      Finset.card_le_card (quotientSet_encodedNatSet_subset hp hinj B)
    _ ≤ #(natPosDiffs B) := Finset.card_image_le

theorem numberUpperWitness_of_vector
    {p : ι → ℕ} (hp : ∀ i, Nat.Prime (p i)) (hinj : Function.Injective p)
    {B : Finset (IntPoint ι)} {n q : ℕ}
    (hBcard : #B = n) (hBdiff : #(posDiffs B) ≤ q) :
    NumberUpperWitness n q := by
  let C := translatedNatFinset B
  let A := encodedNatSet p C
  refine ⟨A, ?_, ?_, ?_⟩
  · intro a ha
    simp [A, encodedNatSet] at ha
    obtain ⟨x, _hx, rfl⟩ := ha
    exact Nat.pos_of_ne_zero (encodeNatPoint_ne_zero hp x)
  · change #(encodedNatSet p C) = n
    rw [card_encodedNatSet p hp hinj C]
    change #(translatedNatFinset B) = n
    rw [card_translatedNatFinset, hBcard]
  · calc
      #(quotientSet A) ≤ #(natPosDiffs C) := by
        change #(quotientSet (encodedNatSet p C)) ≤ #(natPosDiffs C)
        exact card_quotientSet_encodedNatSet_le hp hinj C
      _ ≤ #(posDiffs B) := by
        change #(natPosDiffs (translatedNatFinset B)) ≤ #(posDiffs B)
        exact card_natPosDiffs_translatedNatFinset_le_posDiffs B
      _ ≤ q := hBdiff

theorem numberUpperWitness_of_vector'
    {B : Finset (IntPoint ι)} {n q : ℕ}
    (hBcard : #B = n) (hBdiff : #(posDiffs B) ≤ q) :
    NumberUpperWitness n q :=
  numberUpperWitness_of_vector (finitePrimeEmbedding_prime ι)
    (finitePrimeEmbedding_injective ι) hBcard hBdiff

theorem numberUpperWitness_iterated
    (k W n : ℕ) (hW : 1 ≤ W) (hn : n ≤ W ^ iterA k) :
    NumberUpperWitness n (iterPosConst k * W ^ iterB k) := by
  classical
  obtain ⟨B, hBcard, hBdiff⟩ :=
    exists_subset_iterated_family_posDiffs_le k W n hW hn
  exact numberUpperWitness_of_vector' hBcard hBdiff

theorem numberUpperWitness_iterated_nthRoot (k n : ℕ) :
    NumberUpperWitness n
      (iterPosConst k * (Nat.nthRoot (iterA k) n + 1) ^ iterB k) := by
  have hA : iterA k ≠ 0 := by
    have hpos : 0 < iterA k := by
      induction k with
      | zero =>
          simp [iterA]
      | succ k ih =>
          rw [iterA]
          omega
    exact Nat.ne_of_gt hpos
  exact numberUpperWitness_iterated k (Nat.nthRoot (iterA k) n + 1) n
    (Nat.succ_le_succ (Nat.zero_le _)) (le_of_lt (Nat.lt_pow_nthRoot_add_one hA n))

theorem numberUpperWitness_iterated_nthRoot_const (k n : ℕ) :
    NumberUpperWitness n
      (iterConstBound k * (Nat.nthRoot (iterA k) n + 1) ^ iterB k) :=
  (numberUpperWitness_iterated_nthRoot k n).mono
    (Nat.mul_le_mul_right _ (iterPosConst_le_iterConstBound k))

end FiniteSets

end Erdos539
