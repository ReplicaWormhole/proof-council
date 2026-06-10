import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Erdos539.Base
import Erdos539.Suspension

open scoped Finset

namespace Erdos539

def IterIndex : ℕ → Type
  | 0 => Bool
  | k + 1 => SuspIndex (IterIndex k)

instance iterIndexFintype (k : ℕ) : Fintype (IterIndex k) := by
  induction k with
  | zero =>
      simp [IterIndex]
      infer_instance
  | succ k ih =>
      haveI := ih
      change Fintype (Option (Sum (IterIndex k) (IterIndex k)))
      infer_instance

def iterA : ℕ → ℕ
  | 0 => 3
  | k + 1 => 1 + 2 * iterA k

def iterB : ℕ → ℕ
  | 0 => 2
  | k + 1 => 2 * iterB k

def iterDiffConst : ℕ → ℕ
  | 0 => 9
  | k + 1 => 2 * iterDiffConst k ^ 2

def iterPosConst : ℕ → ℕ
  | 0 => 6
  | k + 1 => iterPosConst k ^ 2 + 2 * iterDiffConst k

def iterConstBound (k : ℕ) : ℕ :=
  27 ^ (2 ^ (k + 1) - 1)

noncomputable def iterFamily : (k W : ℕ) → Finset (IntPoint (IterIndex k))
  | 0, W => by
      classical
      exact baseFamily W
  | k + 1, W => by
      classical
      let F := iterFamily k W
      exact suspension W (separationScale F + 1) F

theorem pow_iterA_succ (W k : ℕ) :
    W * (W ^ iterA k) ^ 2 = W ^ iterA (k + 1) := by
  rw [iterA, pow_two, ← pow_add, ← pow_succ']
  congr 1
  omega

theorem iterA_add_one_eq_two_iterB (k : ℕ) :
    iterA k + 1 = 2 * iterB k := by
  induction k with
  | zero =>
      simp [iterA, iterB]
  | succ k ih =>
      rw [iterA, iterB]
      omega

theorem iterB_eq_pow (k : ℕ) :
    iterB k = 2 ^ (k + 1) := by
  induction k with
  | zero =>
      simp [iterB]
  | succ k ih =>
      simp [iterB, ih, pow_succ']

theorem iterA_add_one_eq_pow (k : ℕ) :
    iterA k + 1 = 2 ^ (k + 2) := by
  rw [iterA_add_one_eq_two_iterB, iterB_eq_pow]
  simp [pow_succ']

theorem iterA_eq_pow_sub_one (k : ℕ) :
    iterA k = 2 ^ (k + 2) - 1 := by
  have h := iterA_add_one_eq_pow k
  omega

theorem iterA_pos (k : ℕ) : 0 < iterA k := by
  induction k with
  | zero =>
      simp [iterA]
  | succ k ih =>
      rw [iterA]
      omega

theorem iterA_ne_zero (k : ℕ) : iterA k ≠ 0 :=
  Nat.ne_of_gt (iterA_pos k)

theorem iterA_ge_succ (k : ℕ) : k + 1 ≤ iterA k := by
  induction k with
  | zero =>
      simp [iterA]
  | succ k ih =>
      rw [iterA]
      omega

theorem iterConstBound_succ (k : ℕ) :
    iterConstBound (k + 1) = 27 * iterConstBound k ^ 2 := by
  unfold iterConstBound
  rw [pow_two, ← pow_add, ← pow_succ']
  congr 1
  have hpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
  rw [show k + 1 + 1 = k + 2 by omega]
  rw [show 2 ^ (k + 2) = 2 * 2 ^ (k + 1) by
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ']]
  omega

theorem iterConstBound_le_sq (k : ℕ) :
    iterConstBound k ≤ iterConstBound k ^ 2 := by
  rw [pow_two]
  exact Nat.le_mul_self _

theorem iterDiffConst_le_iterConstBound (k : ℕ) :
    iterDiffConst k ≤ iterConstBound k := by
  induction k with
  | zero =>
      simp [iterDiffConst, iterConstBound]
  | succ k ih =>
      rw [iterDiffConst, iterConstBound_succ]
      calc
        2 * iterDiffConst k ^ 2 ≤ 2 * iterConstBound k ^ 2 :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left ih 2)
        _ ≤ 27 * iterConstBound k ^ 2 := Nat.mul_le_mul_right _ (by omega)

theorem iterPosConst_le_iterConstBound (k : ℕ) :
    iterPosConst k ≤ iterConstBound k := by
  induction k with
  | zero =>
      simp [iterPosConst, iterConstBound]
  | succ k ih =>
      have hd := iterDiffConst_le_iterConstBound k
      rw [iterPosConst, iterConstBound_succ]
      calc
        iterPosConst k ^ 2 + 2 * iterDiffConst k ≤
            iterConstBound k ^ 2 + 2 * iterConstBound k := by
          exact Nat.add_le_add (Nat.pow_le_pow_left ih 2) (Nat.mul_le_mul_left 2 hd)
        _ ≤ iterConstBound k ^ 2 + 2 * iterConstBound k ^ 2 := by
          exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 (iterConstBound_le_sq k)) _
        _ = 3 * iterConstBound k ^ 2 := by ring
        _ ≤ 27 * iterConstBound k ^ 2 := Nat.mul_le_mul_right _ (by omega)

theorem mul_pow_sq (C W b : ℕ) :
    (C * W ^ b) ^ 2 = C ^ 2 * W ^ (2 * b) := by
  rw [show 2 * b = b * 2 by omega, pow_mul]
  ring

theorem card_iterFamily (k W : ℕ) :
    #(iterFamily k W) = W ^ iterA k := by
  induction k with
  | zero =>
      exact card_baseFamily W
  | succ k ih =>
      classical
      rw [iterFamily]
      calc
        #(suspension W (separationScale (iterFamily k W) + 1) (iterFamily k W)) =
            W * #(iterFamily k W) ^ 2 :=
          card_suspension W (separationScale (iterFamily k W) + 1) (iterFamily k W)
        _ = W * (W ^ iterA k) ^ 2 := by rw [ih]
        _ = W ^ iterA (k + 1) := pow_iterA_succ W k

theorem card_diffSet_iterFamily_le (k W : ℕ) (hW : 1 ≤ W) :
    #(diffSet (iterFamily k W)) ≤ iterDiffConst k * W ^ iterA k := by
  induction k with
  | zero =>
      simpa [iterFamily, iterA, iterDiffConst] using card_diffSet_baseFamily_le W hW
  | succ k ih =>
      classical
      rw [iterFamily]
      let F := iterFamily k W
      let M := separationScale F + 1
      calc
        #(diffSet (suspension W M F)) ≤ (2 * W - 1) * #(diffSet F) ^ 2 :=
          card_diffSet_suspension_le_explicit W M F
        _ ≤ (2 * W) * (iterDiffConst k * W ^ iterA k) ^ 2 := by
          exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.pow_le_pow_left ih 2)
        _ = iterDiffConst (k + 1) * W ^ iterA (k + 1) := by
          rw [iterDiffConst, iterA, show 2 * iterA k = iterA k + iterA k by omega,
            pow_add, pow_succ']
          ring

theorem card_posDiffs_iterFamily_le (k W : ℕ) (hW : 1 ≤ W) :
    #(posDiffs (iterFamily k W)) ≤ iterPosConst k * W ^ iterB k := by
  induction k with
  | zero =>
      simpa [iterFamily, iterB, iterPosConst] using card_posDiffs_baseFamily_le W hW
  | succ k ih =>
      classical
      rw [iterFamily]
      let F := iterFamily k W
      let M := separationScale F + 1
      have hsep : suspensionSeparated M F := separationScale_add_one_separated F
      have hdiff : #(diffSet F) ≤ iterDiffConst k * W ^ iterA k :=
        card_diffSet_iterFamily_le k W hW
      calc
        #(posDiffs (suspension W M F)) ≤
            #(posDiffs F) ^ 2 + 2 * (W - 1) * #(diffSet F) :=
          card_posDiffs_suspension_le_explicit (K := W) (M := M) (F := F) hsep
        _ ≤ (iterPosConst k * W ^ iterB k) ^ 2 +
            2 * W * (iterDiffConst k * W ^ iterA k) := by
          have hterm :
              2 * (W - 1) * #(diffSet F) ≤
                2 * W * (iterDiffConst k * W ^ iterA k) := by
            calc
              2 * (W - 1) * #(diffSet F) =
                  2 * ((W - 1) * #(diffSet F)) := by ring
              _ ≤ 2 * (W * (iterDiffConst k * W ^ iterA k)) :=
                Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.sub_le W 1) hdiff)
              _ = 2 * W * (iterDiffConst k * W ^ iterA k) := by ring
          exact Nat.add_le_add (Nat.pow_le_pow_left ih 2) hterm
        _ = iterPosConst k ^ 2 * W ^ (2 * iterB k) +
            2 * iterDiffConst k * W ^ (iterA k + 1) := by
          rw [mul_pow_sq, pow_succ']
          ring
        _ = iterPosConst k ^ 2 * W ^ (2 * iterB k) +
            2 * iterDiffConst k * W ^ (2 * iterB k) := by
          rw [iterA_add_one_eq_two_iterB k]
        _ = iterPosConst (k + 1) * W ^ iterB (k + 1) := by
          rw [iterPosConst, iterB]
          ring

theorem exists_iterated_family_bounds (k W : ℕ) (hW : 1 ≤ W) :
    ∃ F : Finset (IntPoint (IterIndex k)),
      #F = W ^ iterA k ∧
      #(posDiffs F) ≤ iterPosConst k * W ^ iterB k ∧
      #(diffSet F) ≤ iterDiffConst k * W ^ iterA k :=
  ⟨iterFamily k W, card_iterFamily k W, card_posDiffs_iterFamily_le k W hW,
    card_diffSet_iterFamily_le k W hW⟩

theorem exists_subset_iterated_family_posDiffs_le
    (k W n : ℕ) (hW : 1 ≤ W) (hn : n ≤ W ^ iterA k) :
    ∃ B : Finset (IntPoint (IterIndex k)),
      #B = n ∧ #(posDiffs B) ≤ iterPosConst k * W ^ iterB k := by
  classical
  have hncard : n ≤ #(iterFamily k W) := by
    rw [card_iterFamily]
    exact hn
  obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hncard
  refine ⟨B, hBcard, ?_⟩
  exact le_trans (card_posDiffs_le_of_subset hBsub) (card_posDiffs_iterFamily_le k W hW)

def VectorUpperWitness (n q : ℕ) : Prop :=
  ∃ ι : Type, ∃ _ : DecidableEq (NatPoint ι),
    ∃ B : Finset (IntPoint ι),
      #B = n ∧ #(@posDiffs ι ‹DecidableEq (NatPoint ι)› B) ≤ q

theorem vectorUpperWitness_iterated
    (k W n : ℕ) (hW : 1 ≤ W) (hn : n ≤ W ^ iterA k) :
    VectorUpperWitness n (iterPosConst k * W ^ iterB k) := by
  classical
  obtain ⟨B, hBcard, hBdiff⟩ :=
    exists_subset_iterated_family_posDiffs_le k W n hW hn
  exact ⟨IterIndex k, inferInstance, B, hBcard, hBdiff⟩

end Erdos539
