
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

axiom algebra_abpbcpcageq3_sumaonsqrtapbgeq3onsqrt2
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : 3 ≤ a * b + b * c + c * a) :
  3 / real.sqrt 2 ≤ a / real.sqrt (a + b) + b / real.sqrt (b + c) + c / real.sqrt (c + a) 