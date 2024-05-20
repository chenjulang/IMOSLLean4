/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2012.A5.A5Defs
import Mathlib.RingTheory.Subring.Basic
import Mathlib.Tactic.Ring

/-!
# IMO 2012 A5 (`x ↦ x^2 - 1`)

We show that the map `x : R ↦ x^2 - 1` on a commutative ring `R` is a good map.
For the purpose of the problem, this map's codomain is restricted
  to the subring `R_2 ⊆ R` generated by the squares in `R`.
-/

namespace IMOSL
namespace IMO2012A5

variable [CommRing R]

def RestrictedSqSubOne (x : R) : Subring.closure (Set.range λ x : R ↦ x ^ 2) :=
  ⟨x ^ 2 - 1, Subring.sub_mem _ (Subring.subset_closure ⟨x, rfl⟩) (Subring.one_mem _)⟩

theorem RestrictedSqSubOne_apply_zero : RestrictedSqSubOne (R := R) 0 = -1 :=
  Subtype.ext <| sub_eq_neg_self.mpr <| zero_pow (Nat.succ_ne_zero 1)

theorem sq_sub_one_is_good [CommRing R] : good (λ (x : R) ↦ x ^ 2 - 1) :=
  λ _ _ ↦ by ring

theorem RestrictedSqSubOne_is_good : good (RestrictedSqSubOne (R := R)) :=
  λ x y ↦ Subtype.ext (sq_sub_one_is_good x y)

theorem RestrictedSqSubOne_is_NontrivialGood :
    NontrivialGood (RestrictedSqSubOne (R := R)) :=
  ⟨RestrictedSqSubOne_is_good, sub_eq_zero_of_eq (one_pow 2),
    add_eq_zero_iff_eq_neg.mpr RestrictedSqSubOne_apply_zero⟩
