
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

axiom amc12b_2003_p17
  (x y : ℝ)
  (h₀ : 0 < x ∧ 0 < y)
  (h₁ : real.log (x * y^3) = 1)
  (h₂ : real.log (x^2 * y) = 1) :
  real.log (x * y) = 3 / 5 