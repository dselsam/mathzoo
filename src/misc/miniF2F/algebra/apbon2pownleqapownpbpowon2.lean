-- #mathlib 2022-02-16 8a286af6e972afb8aaa36786edeb6dd5676f7b53
/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunhao Zheng, Stanislas Polu, David Renshaw, OpenAI GPT-f
-/
import imports.miniF2F

open_locale nat rat real big_operators topological_space

axiom algebra_apbon2pownleqapownpbpowon2
  (a b : ℝ)
  (n : ℕ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : 0 < n) :
  ((a + b) / 2)^n ≤ (a^n + b^n) / 2 