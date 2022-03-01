/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunhao Zheng and Stanislas Polu and David Renshaw and OpenAI GPT-f
-/
import mathzoo.imports.miniF2F

open_locale nat rat real big_operators topological_space

axiom mathd_algebra_141
  (a b : nnreal)
  (h₁ : (a * b)=180)
  (h₂ : 2 * (a + b)=54) :
  nnreal.sqrt (a^2 + b^2) = 369 