
-- #mathlib 2022-02-03 30a731ca565b92955e40274652f4c2b6f4db79f4
/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunhao Zheng, Stanislas Polu, David Renshaw, OpenAI GPT-f
-/
import imports.olympiad_core

open_locale big_operators
open_locale real
open_locale nat
open_locale topological_space

theorem induction_nfactltnexpnm1ngt3
  (n : ℕ)
  (h₀ : 3 ≤ n) :
  nat.factorial n < n^(n - 1) :=
begin
  induction h₀ with k h₀ IH,
  { norm_num },
  {
    have k_ge_one : 1 ≤ k := le_trans dec_trivial h₀,
    calc k.succ.factorial = k.succ * k.factorial : rfl
                      ... < k.succ * k ^ (k-1) : (mul_lt_mul_left (nat.succ_pos k)).mpr IH
                      ... ≤ k.succ * (k.succ) ^ (k-1): nat.mul_le_mul_left _ $ nat.pow_le_pow_of_le_left (nat.le_succ k) (k-1)
                      ... = k.succ ^ (k-1 + 1): by rw ← (pow_succ k.succ (k-1))
                      ... = k.succ ^ k: by rw nat.sub_add_cancel k_ge_one,
  }
end