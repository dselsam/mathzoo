/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunhao Zheng and Stanislas Polu and David Renshaw and OpenAI GPT-f
-/
import mathzoo.imports.miniF2F

open_locale nat rat real big_operators topological_space

theorem mathd_algebra_398
  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : 9 * b = 20 * c)
  (h₂ : 7 * a = 4 * b) :
  63 * a = 80 * c :=
begin
  linarith,
end