/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunhao Zheng and Stanislas Polu and David Renshaw and OpenAI GPT-f
-/
import mathzoo.imports.miniF2F

open_locale nat rat real big_operators topological_space

axiom amc12a_2002_p1
  (f : ℂ → ℂ)
  (h₀ : ∀ x, f x = (2 * x + 3) * (x - 4) + (2 * x + 3) * (x - 6))
  (h₁ : fintype (f ⁻¹' {0})) :
  ∑ y in (f⁻¹' {0}).to_finset, y = 7 / 2 