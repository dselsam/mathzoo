
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

theorem numbertheory_4x3m7y3neq2003
  (x y : ℤ) :
  4 * x^3 - 7 * y^3 ≠ 2003 :=
begin
  intro hneq,
  apply_fun (coe : ℤ → zmod 7) at hneq,
  push_cast at hneq,
  have : (2003 : zmod 7) = (1 : zmod 7),
    dec_trivial,
  rw this at hneq,
  have : (7 : zmod 7) = (0 : zmod 7),
    dec_trivial,
  rw this at hneq,
  rw zero_mul at hneq,
  rw sub_zero at hneq,
  have main : ∀ (x : zmod 7), x^3 ∈ [(0 : zmod 7), 1, -1],
    dec_trivial,
  rcases main x with h' | h' | h' | h,
  iterate 3 {
    rw h' at hneq,
    revert hneq,
    dec_trivial,
  },
  exact h,
end