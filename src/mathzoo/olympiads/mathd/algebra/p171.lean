-- #mathlib 2022-02-16 8a286af6e972afb8aaa36786edeb6dd5676f7b53
/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunhao Zheng, Stanislas Polu, David Renshaw, OpenAI GPT-f
-/
import mathzoo.imports.miniF2F

open_locale nat rat real big_operators topological_space

theorem mathd_algebra_171
  (f : ℝ → ℝ)
  (h₀ : ∀x, f x = 5 * x + 4) :
  f 1 = 9 :=
begin
  rw h₀,
  linarith,
end