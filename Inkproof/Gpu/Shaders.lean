/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu.Shader

namespace Inkproof.Gpu

open Shader

/-- Places a vertex given relative to its tile origin. `u_slope` and `u_offset` are the rebased affine map from tile coordinates to clip space, computed in double precision by the caller. -/
def vertexShader : Shader where
  ins := [⟨"a_position", 2⟩]
  uniforms := [⟨"u_slope", 2⟩, ⟨"u_offset", 2⟩]
  outs := []
  decls := [⟨"p", 2, .bin .add (.bin .mul (.var "a_position") (.var "u_slope")) (.var "u_offset")⟩]
  assigns := [("gl_Position", .vec4 (.comp 0 (.var "p")) (.comp 1 (.var "p")) (.lit 0) (.lit 1))]

/-- Fills with one colour. -/
def fragmentShader : Shader where
  ins := []
  uniforms := [⟨"u_colour", 4⟩]
  outs := [⟨"o_colour", 4⟩]
  decls := []
  assigns := [("o_colour", .var "u_colour")]

theorem vertexShader_wellTyped : vertexShader.WellTyped := by decide

theorem fragmentShader_wellTyped : fragmentShader.WellTyped := by decide

/-- The vertex shader computes `a_position * u_slope + u_offset` componentwise in Float32. -/
theorem vertexShader_run (env : String → Option (List Float32)) (x y a b c d : Float32)
    (hp : env "a_position" = some [x, y]) (hs : env "u_slope" = some [a, b])
    (ho : env "u_offset" = some [c, d]) :
    vertexShader.run env = some [("gl_Position", [x * a + c, y * b + d, 0, 1])] := by
  simp [vertexShader, Shader.run, Expr.eval, Op.lift, Op.apply, scalar, hp, hs, ho]

end Inkproof.Gpu
