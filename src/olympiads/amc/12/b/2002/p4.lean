-- #mathlib 2022-02-16 8a286af6e972afb8aaa36786edeb6dd5676f7b53
/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunhao Zheng, Stanislas Polu, David Renshaw, OpenAI GPT-f
-/
import imports.miniF2F

open_locale nat rat real big_operators topological_space

axiom amc12b_2002_p4
  (n : ℕ+)
  (h₀ : (1 /. 2 + 1 /. 3 + 1 /. 7 + 1 /. ↑n).denom = 1) :
  n = 42 