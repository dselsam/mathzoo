
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

theorem amc12b_2002_p6
  (a b : ℝ)
  (h₀ : a ≠ 0 ∧ b ≠ 0)
  (h₁ : ∀ x, x^2 + a * x + b = (x - a) * (x - b)) :
  a = 1 ∧ b = -2 :=
begin
  have h₂ := h₁ a,
  have h₃ := h₁ b,
  have h₄ := h₁ 0,
  simp at *,
  have h₅ : b * (1 - a) = 0, linarith,
  simp at h₅,
  cases h₅ with h₅ h₆,
  exfalso,
  exact absurd h₅ h₀.2,
  have h₆ : a = 1, linarith,
  split,
  exact h₆,
  rw h₆ at h₂,
  linarith,
end