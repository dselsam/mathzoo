
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

axiom aimeI_2000_p7
  (x y z : ℝ)
  (m : ℚ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : x * y * z = 1)
  (h₂ : x + 1 / z = 5)
  (h₃ : y + 1 / x = 29)
  (h₄ : z + 1 / y = m)
  (h₅ : 0 < m) :
  ↑m.denom + m.num = 5 