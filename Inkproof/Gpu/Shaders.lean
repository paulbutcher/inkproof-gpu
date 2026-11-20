/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Inkproof.Gpu.Shader

namespace Inkproof.Gpu

open Shader

private def sv (n : String) : Expr := .var n
private def sc (i : Fin 4) (n : String) : Expr := .comp i (.var n)
private def sm (a b : Expr) : Expr := .bin .mul a b

/-- Places a vertex given relative to its tile origin. `u_slope` and `u_offset` are the rebased affine map from tile coordinates to clip space, computed in double precision by the caller. A vertex is also pushed away from that point by `u_size` pixels times its corner: `a_corner.x` along the pixel-space direction of `a_dir` (a direction in tile coordinates) and `a_corner.y` across it, so a stroke keeps its width in pixels under any map. `u_view` is half the target's width and height, then their reciprocals doubled, which converts between clip space and pixels. -/
def vertexShader : Shader where
  ins := [⟨"a_position", 2⟩, ⟨"a_dir", 2⟩, ⟨"a_corner", 2⟩]
  uniforms := [⟨"u_slope", 2⟩, ⟨"u_offset", 2⟩, ⟨"u_size", 1⟩, ⟨"u_view", 4⟩]
  outs := []
  decls := [
    ⟨"p", 2, .bin .add (sm (sv "a_position") (sv "u_slope")) (sv "u_offset")⟩,
    ⟨"d", 2, sm (sm (sv "a_dir") (sv "u_slope")) (.vec2 (sc 0 "u_view") (sc 1 "u_view"))⟩,
    ⟨"r", 1, .rsqrt (.bin .add (sm (sc 0 "d") (sc 0 "d")) (sm (sc 1 "d") (sc 1 "d")))⟩,
    ⟨"t", 2, sm (sv "d") (sv "r")⟩,
    ⟨"n", 2, .vec2 (.bin .sub (.lit 0) (sc 1 "t")) (sc 0 "t")⟩,
    ⟨"o", 2, sm (.bin .add (sm (sv "t") (sc 0 "a_corner")) (sm (sv "n") (sc 1 "a_corner"))) (sv "u_size")⟩]
  assigns := [("gl_Position", .vec4
    (.bin .add (sc 0 "p") (sm (sc 0 "o") (sc 2 "u_view")))
    (.bin .add (sc 1 "p") (sm (sc 1 "o") (sc 3 "u_view"))) (.lit 0) (.lit 1))]

/-- Fills with one colour. -/
def fragmentShader : Shader where
  ins := []
  uniforms := [⟨"u_colour", 4⟩]
  outs := [⟨"o_colour", 4⟩]
  decls := []
  assigns := [("o_colour", .var "u_colour")]

theorem vertexShader_wellTyped : vertexShader.WellTyped := by decide

theorem fragmentShader_wellTyped : fragmentShader.WellTyped := by decide

/-- The vertex shader places the vertex at `a_position * u_slope + u_offset`, plus the pixel offset along and across the pixel-space direction. -/
theorem vertexShader_run (env : String → Option (List Float32)) (x y dx dy kx ky a b c d z : Float32)
    (w0 w1 w2 w3 : Float32)
    (hp : env "a_position" = some [x, y]) (hd : env "a_dir" = some [dx, dy])
    (hk : env "a_corner" = some [kx, ky]) (hs : env "u_slope" = some [a, b])
    (ho : env "u_offset" = some [c, d]) (hz : env "u_size" = some [z])
    (hv : env "u_view" = some [w0, w1, w2, w3]) :
    vertexShader.run env = some [("gl_Position",
      [x * a + c + ((((dx * a * w0) * (1 / ((dx * a * w0) * (dx * a * w0) + (dy * b * w1) * (dy * b * w1)).sqrt)) * kx +
          (0 - (dy * b * w1) * (1 / ((dx * a * w0) * (dx * a * w0) + (dy * b * w1) * (dy * b * w1)).sqrt)) * ky) * z) * w2,
       y * b + d + ((((dy * b * w1) * (1 / ((dx * a * w0) * (dx * a * w0) + (dy * b * w1) * (dy * b * w1)).sqrt)) * kx +
          ((dx * a * w0) * (1 / ((dx * a * w0) * (dx * a * w0) + (dy * b * w1) * (dy * b * w1)).sqrt)) * ky) * z) * w3,
       0, 1])] := by
  simp [vertexShader, Shader.run, Expr.eval, Op.lift, Op.apply, scalar, sv, sc, sm, hp, hd, hk, hs, ho, hz, hv]
  rfl

end Inkproof.Gpu
