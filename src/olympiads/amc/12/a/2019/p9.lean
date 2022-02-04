
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

axiom amc12a_2019_p9
  (a : ℕ+ → ℚ)
  (h₀ : a 1 = 1)
  (h₁ : a 2 = 3 / 7)
  (h₂ : ∀ n, a (n + 2) = (a n * a (n + 1)) / (2 * a n - a (n + 1))) :
  ↑(a 2019).denom + (a 2019).num = 8078 