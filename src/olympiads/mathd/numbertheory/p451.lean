
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

axiom mathd_numbertheory_451
  (h₀ : fintype {n : ℕ | 2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, (finset.card (nat.divisors m) = 4 ∧ ∑ p in (nat.divisors m), p = n)}) :
  ∑ k in {n : ℕ | 2010 ≤ n ∧ n ≤ 2019 ∧ ∃ m, (finset.card (nat.divisors m) = 4 ∧ ∑ p in (nat.divisors m), p = n)}.to_finset, k = 2016 