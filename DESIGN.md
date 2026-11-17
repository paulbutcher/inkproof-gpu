# Inkproof.Gpu design

## Command set and wire format

`Inkproof.Gpu.specs` is the one definition of the command set: each command has a name, an opcode and a list of operand kinds, and nothing in it names a graphics API. The Lean encoder and decoder are driven by the table, and `Inkproof.Gpu.js` prints the JavaScript decoder and interpreter from it, so they cannot drift. The WebGL2 realisation of each command lives only in the JavaScript printer (`webglBody`), which is where a WebGPU backend would differ.

A command list is one buffer: a little-endian 32-bit command count, then each command as an opcode byte followed by its operands. `generated/gpu.js` is the printed output; `lake exe gen generated` regenerates it. The GLSL shaders beside it and the JavaScript tests fail when it is stale. `createProgram` builds the renderer's one program from the shader sources embedded in `gpu.js`; `uniform` names a uniform by its position in `uniformNames` and sets it with as many floats as it is given, and `draw` reads each vertex as two floats.

## Compiling a display list

`compile` turns a view's tiles (a display list, the transform uniforms and a map from clip rectangles to scissor words) into `Op`s; `Op.toCmd` gives the wire command. The caller supplies `tess`, the vertex words of one command, and its raster fidelity is outside the theorems. Buffers are cached by content, so a tile whose vertex words match a cached entry reuses its buffers and pan and zoom upload nothing. Unused buffers are deleted and handles are never reused. A frame sets the state (the three uniforms and the scissor) and draws once per command, in layer order; the host binds the program. The scissor is four Int32 words (x, y, width, height in device pixels from the bottom left) that `Tile.scissor` computes from a clip rectangle in grid coordinates, or none for no restriction; a command whose clips leave nothing gets an empty scissor. `clipRect_region` states that no point of a shape lies outside the rectangle it is scissored to.

The theorems are stated against `Gpu` in `Proofs/Compile.lean`, an abstract model of buffers, uniform and draw log. Handles go on the wire modulo `2 ^ 32`, so the model is exact only while fewer than that many buffers are allocated.

## Frame of a pixel-grid chart

`pixelTile w h list` is the tile of a display list in device pixels from the top left of a `w` by `h` target, with origin at the top left pixel: slope `(2/w, -2/h)` and offset `(-1, 1)` rounded to Float32, taken from the `Scale.Affine` maps `pixelX` and `pixelY` (`pixelX_apply` and `pixelY_apply` state the exact maps, `2x/w - 1` and `1 - 2y/h`), and a scissor that flips y and clamps to the target (`pixelBox_covers`). `frame` is `frameSetup` (build the program when the context is fresh, use it, lift the scissor, clear) followed by `compile` of that one tile; the scissor is lifted first because `clear` respects it. `frame_roundtrip` states that it survives encode and decode.

## Tessellation

`tessellate origin` is the `tess` that `compile` takes: the vertex words of one command, as three vertices per triangle, each vertex two Float32 words (x then y, little-endian on the wire like all words) holding the position relative to `origin`, a point in grid coordinates that the caller also uses as the tile origin. Coordinates are converted from Scene's exact rationals to Float32 after subtracting the origin, so a tile's words do not depend on where it sits.

`triangles` gives the triangles in grid coordinates. Rectangles, text boxes and square markers are two triangles; a strip is Scene's `stripTriangles`; an area or envelope is two triangles per column pair; a circle marker is an octagon fan that contains the circle. A clipped shape gives the triangles of the shape it clips; the scissor keeps the drawing inside the clip box.

`region_sub_triangles` states that every point of a polygonal shape lies in one of its triangles, and `covers_triangles` that a command's covered pixels each meet a triangle. Circles are excluded: the octagon containing the circle is checked by a test, not proved. How a GPU rasterises a triangle, which pixels it samples, is outside the theorems.

The renderer's uniforms are `u_slope` and `u_offset` (two floats each) and `u_colour` (four floats, the command's colour as red, green, blue and alpha in 0 to 1). For a map from grid coordinates to clip space `clip = A * p + B` computed in double precision, a tile with origin `o` takes `u_slope = A` and `u_offset = A * o + B`, so that `(p - o) * u_slope + u_offset = clip`. Before each draw `compile` sets `u_slope` and `u_offset` from the tile (`Tile.slope`, `Tile.offset`), `u_colour` from the command's colour (`colourWords`), and the scissor.

## Shader language

`Inkproof.Gpu.Shader` is a small Float32 language: scalars and vectors, componentwise `+`, `-` and `*` with scalar broadcast, vector construction and component selection. A `Shader` is typed inputs, uniforms and outputs, local declarations and assignments. `Shader.run` gives its meaning over inkproof-float's Float32 and `Shader.glsl` prints GLSL ES 3.00; the renderer's shaders (`vertexShader`, `fragmentShader`) are values of this type and `generated/*.glsl` are printed from them. Division and fused multiply-add are not in the language.

The vertex shader maps a position relative to its tile origin through the rebased affine map `a_position * u_slope + u_offset`, with the slope and offset computed in double precision by the caller.

### What is not proved

The printer preserves meaning only under the Float32 model of inkproof-float, which assumes IEEE binary32 rounding for `+`, `-` and `*`. GLSL ES 3.00 guarantees far less for `highp` (a relative precision of 2^-16 and no stated rounding), so no theorem can relate the printed text to the language under the specification's own precision model; the placement bound holds on hardware that implements binary32.

The half-pixel placement bound (`vertexShader_placement`) is proved directly from inkproof-float's Float32 rounding lemmas, for the two operations the shader performs. The origin is subtracted on the CPU in double precision, so the rebased affine theorem of inkproof-scale, which models the subtraction in the same precision, does not describe this shader; the bound is on the Float32 inputs the shader receives.
