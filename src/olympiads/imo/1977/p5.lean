
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

axiom imo_1977_p5
  (a b q r : ℕ)
  (h₀ : r < a + b)
  (h₁ : a^2 + b^2 = (a + b) * q + r)
  (h₂ : q^2 + r = 1977) :
  (abs ((a:ℤ) - 22) = 15 ∧ abs ((b:ℤ) - 22) = 28) ∨ (abs ((a:ℤ) - 22) = 28 ∧ abs ((b:ℤ) - 22) = 15) 