/-
Copyright (c) 2021 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kunhao Zheng, Stanislas Polu, David Renshaw, OpenAI GPT-f
-/
import mathzoo.imports.miniF2F

open_locale nat rat real big_operators topological_space

theorem mathd_algebra_245
  (x : ℝ)
  (h₀ : x ≠ 0) :
  (4 / x)⁻¹ * ((3 * x^3) / x)^2 * ((1 / (2 * x))⁻¹)^3 = 18 * x^8 :=
begin
  field_simp [(show x ≠ 0, by simpa using h₀), mul_comm x]; ring,
end