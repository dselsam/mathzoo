/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunhao Zheng and Stanislas Polu and David Renshaw and OpenAI GPT-f
-/
import mathzoo.imports.miniF2F

open_locale nat rat real big_operators topological_space

axiom mathd_numbertheory_326
  (n : ℕ)
  (h₀ : (↑n - 1) * ↑n * (↑n + 1) = (720:ℤ)) :
  (n + 1) = 10 