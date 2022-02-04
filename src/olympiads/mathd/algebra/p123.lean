
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

theorem mathd_algebra_123
  (a b : ℕ+)
  (h₀ : a + b = 20)
  (h₁ : a = 3 * b) :
  a - b = 10 :=
begin
  rw h₁ at h₀,
  rw h₁,
  have h₂ : 3 * (b:ℕ) + (b:ℕ) = (20:ℕ), {
    exact subtype.mk.inj h₀,
  },
  have h₃ : (b:ℕ) = 5, linarith,
  have h₄ : b = 5, {
    exact pnat.eq h₃,
  },
  rw h₄,
  calc (3:ℕ+) * 5 - 5 = 15 - 5 : by {congr,}
            ... = 10 : by {exact rfl},
end