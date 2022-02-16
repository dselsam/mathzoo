-- #mathlib 2022-02-16 8a286af6e972afb8aaa36786edeb6dd5676f7b53
/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunhao Zheng, Stanislas Polu, David Renshaw, OpenAI GPT-f
-/
import imports.miniF2F

open_locale nat rat real big_operators topological_space

theorem mathd_algebra_314
  (n : ℕ)
  (h₀ : n = 11) :
  (1 / 4)^(n + 1) * 2^(2 * n) = 1 / 4 :=
begin
  rw h₀,
  norm_num,
end