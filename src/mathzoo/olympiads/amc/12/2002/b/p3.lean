/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunhao Zheng and Stanislas Polu and David Renshaw and OpenAI GPT-f
-/
import mathzoo.imports.miniF2F

open_locale nat rat real big_operators topological_space

axiom amc12b_2002_p3
  (n : ℕ)
  (h₀ : 0 < n)
  -- note: we use this over (n^2 - 3 * n + 2) because nat subtraction truncates the latter at 1 and 2
  (h₁ : nat.prime (n^2 + 2 - 3 * n)) :
  n = 3 