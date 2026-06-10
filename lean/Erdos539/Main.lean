import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Erdos539.NumberLower

open scoped Finset

namespace Erdos539

theorem numberUpperWitness_exists (n : ℕ) :
    ∃ q, NumberUpperWitness n q := by
  classical
  let A : Finset ℕ := (Finset.range n).image fun i => i + 1
  refine ⟨#(quotientSet A), A, ?_, ?_, le_rfl⟩
  · intro a ha
    simp [A] at ha
    obtain ⟨i, _hi, rfl⟩ := ha
    omega
  · change #((Finset.range n).image fun i => i + 1) = n
    rw [Finset.card_image_of_injective]
    · exact Finset.card_range n
    · intro a b hab
      exact Nat.succ.inj hab

noncomputable def erdosH (n : ℕ) : ℕ := by
  classical
  exact Nat.find (numberUpperWitness_exists n)

theorem erdosH_spec (n : ℕ) :
    NumberUpperWitness n (erdosH n) := by
  classical
  rw [erdosH]
  exact Nat.find_spec (numberUpperWitness_exists n)

theorem erdosH_le_of_witness {n q : ℕ} (h : NumberUpperWitness n q) :
    erdosH n ≤ q := by
  classical
  rw [erdosH]
  exact Nat.find_min' (numberUpperWitness_exists n) h

theorem erdosH_upper_iterated_nthRoot (k n : ℕ) :
    erdosH n ≤
      iterPosConst k * (Nat.nthRoot (iterA k) n + 1) ^ iterB k :=
  erdosH_le_of_witness (numberUpperWitness_iterated_nthRoot k n)

theorem erdosH_upper_iterated_nthRoot_const (k n : ℕ) :
    erdosH n ≤
      iterConstBound k * (Nat.nthRoot (iterA k) n + 1) ^ iterB k :=
  erdosH_le_of_witness (numberUpperWitness_iterated_nthRoot_const k n)

theorem nthRoot_add_one_pow_le_two_pow_mul
    {a n : ℕ} (ha : a ≠ 0) (hn : 1 ≤ n) :
    (Nat.nthRoot a n + 1) ^ a ≤ 2 ^ a * n := by
  let r := Nat.nthRoot a n
  have hr1 : 1 ≤ r := by
    rw [Nat.le_nthRoot_iff ha]
    simpa using hn
  calc
    (Nat.nthRoot a n + 1) ^ a = (r + 1) ^ a := rfl
    _ ≤ (2 * r) ^ a := Nat.pow_le_pow_left (by omega) a
    _ = 2 ^ a * r ^ a := by rw [Nat.mul_pow]
    _ ≤ 2 ^ a * n := Nat.mul_le_mul_left _ (Nat.pow_nthRoot_le (Or.inl ha))

theorem erdosH_upper_iterated_power_const (k n : ℕ) (hn : 1 ≤ n) :
    erdosH n ^ iterA k ≤
      iterConstBound k ^ iterA k * (2 ^ iterA k * n) ^ iterB k := by
  let W := Nat.nthRoot (iterA k) n + 1
  have hA : iterA k ≠ 0 := iterA_ne_zero k
  have hWpow : W ^ iterA k ≤ 2 ^ iterA k * n :=
    nthRoot_add_one_pow_le_two_pow_mul hA hn
  have hup := erdosH_upper_iterated_nthRoot_const k n
  calc
    erdosH n ^ iterA k ≤ (iterConstBound k * W ^ iterB k) ^ iterA k :=
      Nat.pow_le_pow_left hup _
    _ = iterConstBound k ^ iterA k * (W ^ iterA k) ^ iterB k := by
      rw [Nat.mul_pow]
      congr 1
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ iterConstBound k ^ iterA k * (2 ^ iterA k * n) ^ iterB k := by
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hWpow _)

theorem erdosH_upper_iterated_power_const_expanded (k n : ℕ) (hn : 1 ≤ n) :
    erdosH n ^ iterA k ≤
      iterConstBound k ^ iterA k * 2 ^ (iterA k * iterB k) * n ^ iterB k := by
  calc
    erdosH n ^ iterA k ≤
        iterConstBound k ^ iterA k * (2 ^ iterA k * n) ^ iterB k :=
      erdosH_upper_iterated_power_const k n hn
    _ = iterConstBound k ^ iterA k * 2 ^ (iterA k * iterB k) * n ^ iterB k := by
      rw [Nat.mul_pow, pow_mul]
      ring

theorem iterConstBound_pos (k : ℕ) : 0 < iterConstBound k := by
  unfold iterConstBound
  exact pow_pos (by norm_num : 0 < 27) _

theorem erdosH_square_lower (n : ℕ) (hn : 0 < n) :
    2 * n - 1 ≤ erdosH n ^ 2 := by
  classical
  rcases erdosH_spec n with ⟨A, hpos, hcard, hq⟩
  have hA : A.Nonempty := by
    rw [← Finset.card_pos, hcard]
    exact hn
  have hlower :=
    card_quotientSet_square_lower A (fun a ha => Nat.ne_of_gt (hpos a ha)) hA
  calc
    2 * n - 1 = 2 * #A - 1 := by rw [hcard]
    _ ≤ #(quotientSet A) ^ 2 := hlower
    _ ≤ erdosH n ^ 2 := Nat.pow_le_pow_left hq 2

theorem erdosH_exact_lower (n : ℕ) (hn : 0 < n) :
    2 * n - 1 ≤ erdosH n * (erdosH n - 1) + 1 := by
  classical
  rcases erdosH_spec n with ⟨A, hpos, hcard, hq⟩
  have hA : A.Nonempty := by
    rw [← Finset.card_pos, hcard]
    exact hn
  have hlower :=
    card_quotientSet_exact_lower A (fun a ha => Nat.ne_of_gt (hpos a ha)) hA
  calc
    2 * n - 1 = 2 * #A - 1 := by rw [hcard]
    _ ≤ #(quotientSet A) * (#(quotientSet A) - 1) + 1 := hlower
    _ ≤ erdosH n * (erdosH n - 1) + 1 := by
      exact Nat.add_le_add_right (Nat.mul_le_mul hq (Nat.sub_le_sub_right hq 1)) 1

theorem erdosH_pos {n : ℕ} (hn : 0 < n) : 0 < erdosH n := by
  have hsquare := erdosH_square_lower n hn
  have hleft : 0 < 2 * n - 1 := by omega
  have hsqpos : 0 < erdosH n ^ 2 := lt_of_lt_of_le hleft hsquare
  exact Nat.pos_of_ne_zero (by
    intro hzero
    rw [hzero] at hsqpos
    simp at hsqpos)

theorem erdosH_log_upper_iterated (k n : ℕ) (hn : 1 ≤ n) :
    (iterA k : ℝ) * Real.log (erdosH n) ≤
      (iterA k : ℝ) * Real.log (iterConstBound k) +
        (iterA k * iterB k : ℕ) * Real.log 2 +
        (iterB k : ℝ) * Real.log n := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hHpos : 0 < erdosH n := erdosH_pos hnpos
  have hCposNat : 0 < iterConstBound k := iterConstBound_pos k
  have hnposR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hCposR : 0 < (iterConstBound k : ℝ) := by exact_mod_cast hCposNat
  have hnat := erdosH_upper_iterated_power_const_expanded k n hn
  have hreal : ((erdosH n ^ iterA k : ℕ) : ℝ) ≤
      ((iterConstBound k ^ iterA k * 2 ^ (iterA k * iterB k) *
        n ^ iterB k : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hpowreal : (erdosH n : ℝ) ^ iterA k ≤
      ((iterConstBound k ^ iterA k * 2 ^ (iterA k * iterB k) *
        n ^ iterB k : ℕ) : ℝ) := by
    simpa [Nat.cast_pow] using hreal
  have hleftpos : 0 < ((erdosH n : ℝ) ^ iterA k) := by
    positivity
  have hlog := Real.log_le_log hleftpos hpowreal
  rw [Real.log_pow] at hlog
  rw [Nat.cast_mul, Nat.cast_mul] at hlog
  rw [Real.log_mul, Real.log_mul] at hlog
  · rw [Nat.cast_pow, Real.log_pow] at hlog
    rw [Nat.cast_pow, Real.log_pow] at hlog
    rw [Nat.cast_pow, Real.log_pow] at hlog
    simpa [Nat.cast_mul, add_assoc] using hlog
  · positivity
  · positivity
  · positivity
  · positivity

theorem erdosH_log_upper_iterated_div (k n : ℕ) (hn : 1 ≤ n) :
    Real.log (erdosH n) ≤
      Real.log (iterConstBound k) +
        (iterB k : ℝ) * Real.log 2 +
        ((iterB k : ℝ) / (iterA k : ℝ)) * Real.log n := by
  have h := erdosH_log_upper_iterated k n hn
  have hApos : 0 < (iterA k : ℝ) := by exact_mod_cast iterA_pos k
  have hdiv := div_le_div_of_nonneg_right h hApos.le
  have hleft_eq : ((iterA k : ℝ) * Real.log (erdosH n)) / (iterA k : ℝ) =
      Real.log (erdosH n) := by
    field_simp [hApos.ne']
  have hright_eq :
      ((iterA k : ℝ) * Real.log (iterConstBound k) +
          (iterA k * iterB k : ℕ) * Real.log 2 +
          (iterB k : ℝ) * Real.log n) / (iterA k : ℝ) =
        Real.log (iterConstBound k) +
          (iterB k : ℝ) * Real.log 2 +
          ((iterB k : ℝ) / (iterA k : ℝ)) * Real.log n := by
    rw [Nat.cast_mul]
    field_simp [hApos.ne']
  rwa [hleft_eq, hright_eq] at hdiv

theorem log_iterConstBound (k : ℕ) :
    Real.log (iterConstBound k) = (2 ^ (k + 1) - 1 : ℕ) * Real.log 27 := by
  rw [iterConstBound, Nat.cast_pow, Real.log_pow]
  norm_num

theorem iterB_div_iterA_eq_half_add (k : ℕ) :
    (iterB k : ℝ) / (iterA k : ℝ) =
      (1 : ℝ) / 2 + 1 / (2 * (iterA k : ℝ)) := by
  have hApos : 0 < (iterA k : ℝ) := by exact_mod_cast iterA_pos k
  have h : (2 * iterB k : ℝ) = (iterA k : ℝ) + 1 := by
    exact_mod_cast (iterA_add_one_eq_two_iterB k).symm
  field_simp [hApos.ne']
  linarith

theorem erdosH_log_upper_half_error (k n : ℕ) (hn : 1 ≤ n) :
    Real.log (erdosH n) ≤
      (1 : ℝ) / 2 * Real.log n +
        Real.log n / (2 * (iterA k : ℝ)) +
        Real.log (iterConstBound k) +
        (iterB k : ℝ) * Real.log 2 := by
  calc
    Real.log (erdosH n) ≤
        Real.log (iterConstBound k) +
          (iterB k : ℝ) * Real.log 2 +
          ((iterB k : ℝ) / (iterA k : ℝ)) * Real.log n :=
      erdosH_log_upper_iterated_div k n hn
    _ = (1 : ℝ) / 2 * Real.log n +
        Real.log n / (2 * (iterA k : ℝ)) +
        Real.log (iterConstBound k) +
        (iterB k : ℝ) * Real.log 2 := by
      rw [iterB_div_iterA_eq_half_add]
      ring

theorem erdosH_log_ratio_lower (n : ℕ) (hn : 2 ≤ n) :
    (1 : ℝ) / 2 ≤ Real.log (erdosH n) / Real.log n := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hsq := erdosH_square_lower n hnpos
  have hnle : n ≤ 2 * n - 1 := by omega
  have hn_hsq : n ≤ erdosH n ^ 2 := le_trans hnle hsq
  have hreal : (n : ℝ) ≤ (erdosH n : ℝ) ^ 2 := by
    exact_mod_cast hn_hsq
  have hnposR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hlog := Real.log_le_log hnposR hreal
  rw [Real.log_pow] at hlog
  norm_num at hlog
  have hhalf : (1 : ℝ) / 2 * Real.log n ≤ Real.log (erdosH n) := by
    linarith
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  rw [le_div_iff₀ hlogpos]
  exact hhalf

theorem erdosH_log_ratio_upper (k n : ℕ) (hn : 2 ≤ n) :
    Real.log (erdosH n) / Real.log n ≤
      (1 : ℝ) / 2 + 1 / (2 * (iterA k : ℝ)) +
        (Real.log (iterConstBound k) + (iterB k : ℝ) * Real.log 2) / Real.log n := by
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have h := erdosH_log_upper_half_error k n hn1
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hdiv := div_le_div_of_nonneg_right h hlogpos.le
  have hright :
      ((1 : ℝ) / 2 * Real.log n + Real.log n / (2 * (iterA k : ℝ)) +
        Real.log (iterConstBound k) + (iterB k : ℝ) * Real.log 2) / Real.log n =
      (1 : ℝ) / 2 + 1 / (2 * (iterA k : ℝ)) +
        (Real.log (iterConstBound k) + (iterB k : ℝ) * Real.log 2) / Real.log n := by
    field_simp [hlogpos.ne']
    ring_nf
  rwa [hright] at hdiv

theorem erdosH_log_div_log_tendsto :
    Filter.Tendsto (fun n : ℕ => Real.log (erdosH n) / Real.log n)
      Filter.atTop (nhds ((1 : ℝ) / 2)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε3
  have hgap : 1 / (2 * (iterA k : ℝ)) < ε / 3 := by
    have hle : k + 1 ≤ iterA k := iterA_ge_succ k
    have hkpos : 0 < (k : ℝ) + 1 := by positivity
    have hden : (k : ℝ) + 1 ≤ 2 * (iterA k : ℝ) := by
      have hleR : ((k + 1 : ℕ) : ℝ) ≤ iterA k := by exact_mod_cast hle
      norm_num at hleR ⊢
      nlinarith
    have hgap_le : 1 / (2 * (iterA k : ℝ)) ≤ 1 / ((k : ℝ) + 1) :=
      one_div_le_one_div_of_le hkpos hden
    exact lt_of_le_of_lt hgap_le hk
  let C : ℝ := Real.log (iterConstBound k) + (iterB k : ℝ) * Real.log 2
  have hlog_atTop :
      Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hconst_zero :
      Filter.Tendsto (fun n : ℕ => C / Real.log (n : ℝ)) Filter.atTop (nhds 0) :=
    (tendsto_const_nhds (x := C)).div_atTop hlog_atTop
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, C / Real.log (n : ℝ) < ε / 3 :=
    hconst_zero.eventually (eventually_lt_nhds hε3)
  filter_upwards [Filter.eventually_ge_atTop 2, hsmall] with n hn2 hsmalln
  have hlower := erdosH_log_ratio_lower n hn2
  have hupper0 := erdosH_log_ratio_upper k n hn2
  have hupper : Real.log (erdosH n) / Real.log n < (1 : ℝ) / 2 + ε := by
    calc
      Real.log (erdosH n) / Real.log n ≤
          (1 : ℝ) / 2 + 1 / (2 * (iterA k : ℝ)) + C / Real.log n := hupper0
      _ < (1 : ℝ) / 2 + ε := by linarith
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end Erdos539
