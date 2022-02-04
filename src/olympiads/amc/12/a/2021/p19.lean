
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

axiom amc12a_2021_p19
  (h₀ : fintype {x : ℝ | 0 ≤ x ∧ x ≤ real.pi ∧ real.sin (real.pi / 2 * real.cos x) = real.cos (real.pi / 2 * real.sin x)}) :
  finset.card {x : ℝ | 0 ≤ x ∧ x ≤ real.pi ∧ real.sin (real.pi / 2 * real.cos x) = real.cos (real.pi / 2 * real.sin x)}.to_finset = 2 