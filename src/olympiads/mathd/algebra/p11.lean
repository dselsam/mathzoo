
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

theorem mathd_algebra_11
  (a b : ℝ)
  (h₀ : a ≠ b)
  (h₁ : a ≠ 2*b)
  (h₂ : (4 * a + 3 * b) / (a - 2 * b) = 5) :
  (a + 11 * b) / (a - b) = 2 :=
begin
  rw eq_comm,
  refine (eq_div_iff _).mpr _,
  exact sub_ne_zero_of_ne h₀,
  rw eq_comm at h₂,
  suffices : a = 13 * b, linarith,
  have key : 5 * (a - 2 * b) = (4 * a + 3 * b), rwa (eq_div_iff (sub_ne_zero_of_ne h₁)).mp,
  linarith,
end