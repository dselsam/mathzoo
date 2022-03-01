/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunhao Zheng and Stanislas Polu and David Renshaw and OpenAI GPT-f
-/
import mathzoo.imports.miniF2F

open_locale nat rat real big_operators topological_space

axiom imo_1993_p5 :
  ∃ f : ℕ+ → ℕ+, (∀ a b, (a < b) ↔ f a < f b) ∧ f 1 = 2 ∧ ∀ n, f (f n) = f n + n 