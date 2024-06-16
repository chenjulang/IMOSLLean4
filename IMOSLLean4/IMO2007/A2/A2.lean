/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.PNat.Basic

/-!
# IMO 2007 A2

A function $f : ℕ → ℕ$ is called *good* if, for any $m, n ∈ ℕ$,
$$ f(m + n + 1) ≥ f(m) + f(f(n)). $$
For any $N ∈ ℕ$, determine all $k ∈ ℕ$ for which
  there exists a good function $f$ such that $f(N) = k$.
-/

namespace IMOSL
namespace IMO2007A2

/-! ## `ℕ` version -/

def good (f : ℕ → ℕ) := ∀ m n : ℕ, f m + f (f n) ≤ f (m + n + 1)



theorem sub_right_is_good (C : ℕ) : good (· - C) := λ m n ↦ by
  dsimp only; rcases le_total n C with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.zero_sub, add_zero, add_assoc]
    exact Nat.sub_le_sub_right le_self_add _
  · rw [le_iff_exists_add] at h; rcases h with ⟨d, rfl⟩
    rw [Nat.add_sub_cancel_left, add_right_comm, C.add_comm, ← add_assoc, Nat.add_sub_cancel]
    exact add_le_add ((Nat.sub_le m C).trans m.le_succ) (Nat.sub_le d C)

theorem add_cond_modeq_zero_is_good (h : K ≠ 1) :
    good (λ n ↦ n + cond ((n.succ % K).beq 0) 1 0) := λ m n ↦ by
  dsimp only; cases h0 : (n.succ % K).beq 0 with
  | false =>
      rw [cond_false, n.add_zero, h0, cond_false, n.add_zero, Nat.add_right_comm]
      apply le_add_right; cases (m.succ % K).beq 0 with
        | true => exact (m + n + 1).le_refl
        | false => exact (m + n).le_succ
  | true =>
      have h1 : n.succ % K = 0 := by rwa [← Nat.beq_eq]
      rw [cond_true, n.succ.succ_eq_add_one, n.succ.add_mod, h1, Nat.zero_add, Nat.mod_mod,
        Nat.one_mod_of_ne_one h, add_add_add_comm, m.add_assoc n, Nat.add_le_add_iff_left]
      refine (congrFun₂ (congrArg cond ?_) 1 0).le
      rw [← Nat.succ_add, m.succ.add_mod n.succ, h1, add_zero, Nat.mod_mod]



section

variable {f : ℕ → ℕ} (h : good f)

theorem good_monotone : Monotone f := λ x y h0 ↦ by
  rw [le_iff_exists_add] at h0; rcases h0 with ⟨_ | c, rfl⟩
  exacts [(f y).le_refl, le_of_add_le_left (h x c)]

theorem good_map_zero : f 0 = 0 :=
  (f 0).eq_zero_or_pos.resolve_right λ h0 ↦
    (good_monotone h h0).not_lt ((Nat.lt_add_of_pos_left h0).trans_le (h 0 0))

theorem good_val_bound (N : ℕ) : f N ≤ N + 1 := by
  rw [← not_lt, ← Nat.add_one_le_iff]; intro h0
  -- `f(m(N + 1)) ≥ mf(N + 1)` for all `m : ℕ`.
  have h1 : ∀ m : ℕ, f (N + 1) * m ≤ f ((N + 1) * m) :=
    Nat.rec (f 0).zero_le λ n h1 ↦ (h _ _).trans'
      (Nat.add_le_add h1 (good_monotone h (le_of_lt h0)))
  -- For the case `m = N + 1`, get some `d ≥ N` such that `f((N + 1)^2) = (N + 1)^2 + d + 1`
  replace h1 : ∃ d : ℕ, N ≤ d ∧ f ((N + 1) * (N + 1)) = (N + 1) * (N + 1) + d + 1 := by
    apply (good_monotone h N.le_succ).trans' at h0
    obtain ⟨c, h1⟩ := Nat.exists_eq_add_of_le ((Nat.mul_le_mul_right _ h0).trans (h1 (N + 1)))
    refine ⟨N + c, le_self_add, ?_⟩
    rw [h1, Nat.succ_mul, Nat.add_assoc, Nat.add_assoc _ (N + c), N.add_right_comm]
  -- Finishing: prove `f(d) = 0`
  rcases h1 with ⟨d, h1, h2⟩
  apply ((N + 1).succ_pos.trans_le (h0.trans (good_monotone h h1))).ne.symm
  specialize h d ((N + 1) * (N + 1))
  rwa [add_comm d, h2, add_le_iff_nonpos_left, nonpos_iff_eq_zero] at h

end



/-- Final solution -/
theorem final_solution :
    (∃ f : ℕ → ℕ, good f ∧ f N = k) ↔ cond (N.beq 0) (k = 0) (k ≤ N.succ) := by
  cases h : N.beq 0 with
  | true =>
      rw [Nat.beq_eq] at h; subst h
      exact ⟨λ ⟨f, h, h0⟩ ↦ h0.symm.trans (good_map_zero h),
        λ h ↦ ⟨id, sub_right_is_good 0, h.symm⟩⟩
  | false =>
      refine ⟨λ ⟨f, h, h0⟩ ↦ h0.symm.trans_le (good_val_bound h N), λ h0 ↦ ?_⟩
      rw [cond_false, le_iff_lt_or_eq, Nat.lt_succ_iff] at h0
      rcases h0 with h0 | rfl
      · exact ⟨_, sub_right_is_good (N - k), Nat.sub_sub_self h0⟩
      · refine ⟨_, add_cond_modeq_zero_is_good (Nat.ne_of_beq_eq_false h : N + 1 ≠ 1), ?_⟩
        rw [Nat.mod_self]; rfl





/-! ## `ℕ+` (original) version -/

def goodPNat (f : ℕ+ → ℕ+) := ∀ m n : ℕ+, f m + f (f n) ≤ f (m + n) + 1

theorem PNat_to_Nat_Prop {P : ℕ+ → Prop} : (∀ n : ℕ+, P n) ↔ ∀ n : ℕ, P n.succPNat :=
  ⟨λ h n ↦ h n.succPNat, λ h n ↦ n.succPNat_natPred ▸ h _⟩

theorem PNat_to_Nat_Prop2 {P : ℕ+ → ℕ+ → Prop} :
    (∀ m n : ℕ+, P m n) ↔ ∀ m n : ℕ, P m.succPNat n.succPNat := by
  simp only [PNat_to_Nat_Prop]

theorem succPNat_add_succPNat (m n : ℕ) :
    m.succPNat + n.succPNat = (m + n).succPNat + 1 := by
  rw [← PNat.coe_inj, PNat.add_coe, Nat.succPNat_coe, Nat.succPNat_coe,
    PNat.add_coe, Nat.succPNat_coe, Nat.add_succ, Nat.succ_add, PNat.val_ofNat]

theorem goodPNat_iff_good {f : ℕ+ → ℕ+} :
    goodPNat f ↔ good λ x ↦ (f x.succPNat).natPred := by
  obtain ⟨g, rfl⟩ : ∃ g : ℕ → ℕ, f = λ x ↦ (g x.natPred).succPNat :=
    ⟨λ x ↦ (f x.succPNat).natPred,
    funext λ x ↦ by rw [PNat.succPNat_natPred, PNat.succPNat_natPred]⟩
  rw [goodPNat, PNat_to_Nat_Prop2]
  refine forall₂_congr λ m n ↦ ?_
  rw [Nat.natPred_succPNat, succPNat_add_succPNat, succPNat_add_succPNat,
    add_le_add_iff_right, Nat.succPNat_le_succPNat]; rfl

theorem good_correspondence {N k : ℕ+} :
    (∃ f : ℕ+ → ℕ+, goodPNat f ∧ f N = k) ↔ ∃ f : ℕ → ℕ, good f ∧ f N.natPred = k.natPred :=
  ⟨λ h ↦ by
    rcases h with ⟨f, h, rfl⟩
    exact ⟨_, goodPNat_iff_good.mp h, N.succPNat_natPred ▸ rfl⟩,
  λ h ↦ by
    rcases h with ⟨f, h, h0⟩
    exact ⟨λ x ↦ (f x.natPred).succPNat, goodPNat_iff_good.mpr h,
      (congrArg _ h0).trans k.succPNat_natPred⟩⟩

/-- Final solution, `ℕ+` version -/
theorem final_solution_PNat {N k : ℕ+} :
    (∃ f : ℕ+ → ℕ+, goodPNat f ∧ f N = k) ↔ if N = 1 then k = 1 else k ≤ N + 1 := by
  rw [good_correspondence, final_solution, cond_eq_if]
  have X {n : ℕ+} : n.natPred = 0 ↔ n = 1 := PNat.natPred_inj (n := 1)
  refine if_congr_prop (Nat.beq_eq ▸ X) X ?_
  rw [← PNat.natPred_le_natPred, Nat.succ_eq_add_one, PNat.natPred_add_one]; rfl
