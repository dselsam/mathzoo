
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

axiom mathd_numbertheory_435
  (k : ℕ)
  (h₀ : 0 < k)
  (h₁ : ∀ n, gcd (6 * n + k) (6 * n + 3) = 1)
  (h₂ : ∀ n, gcd (6 * n + k) (6 * n + 2) = 1)
  (h₃ : ∀ n, gcd (6 * n + k) (6 * n + 1) = 1) :
  5 ≤ k 