-- #mathlib 2022-02-16 8a286af6e972afb8aaa36786edeb6dd5676f7b53
/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunhao Zheng, Stanislas Polu, David Renshaw, OpenAI GPT-f
-/
import imports.miniF2F

open_locale nat rat real big_operators topological_space

axiom imo_1967_p3
  (k m n : ℕ)
  (c : ℕ → ℕ)
  (h₀ : 0 < k ∧ 0 < m ∧ 0 < n)
  (h₁ : ∀ s, c s = s * (s + 1))
  (h₂ : nat.prime (k + m + 1))
  (h₃ : n + 1 < k + m + 1) :
  (∏ i in finset.range (n + 1) \ finset.range 1, c i) ∣ (∏ i in finset.range (n + 1) \ finset.range 1, (c (m + i) - c k)) 