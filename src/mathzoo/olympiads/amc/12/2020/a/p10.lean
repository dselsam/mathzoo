/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunhao Zheng and Stanislas Polu and David Renshaw and OpenAI GPT-f
-/
import mathzoo.imports.miniF2F

open_locale nat rat real big_operators topological_space

axiom amc12a_2020_p10
  (n : ℕ+)
  (h₀ : real.log (real.log n / real.log 16) / real.log 2 = real.log (real.log n / real.log 4) / real.log 4) :
  n = 256 