
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

axiom mathd_algebra_69
  (r s : ℕ+)
  (h₀ : ↑r * ↑s = (450:ℤ))
  (h₁ : (↑r + 5) * (↑s - 3) = (450:ℤ)) :
  r = 25 