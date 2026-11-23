# Changelog

## [0.19.0]

- A circle marker is a polygon about the circle with a side count that follows its radius, within a quarter of a unit of the circle, instead of an octagon; `octagonTriangles` is replaced by `discTriangles` and `discVertices`.

## [0.18.0]

- `strokeFrame` and `strokeFrameBytes` draw a frame in device pixels with strips and markers at exactly their size, where `frameBytes` draws Scene's wider conservative triangles.

## [0.17.0]

- A strip ends in a half octagon that shares its edge with the segment instead of a whole octagon over it, so a translucent stroke is no darker at its ends; `stripVerticesFrom` takes `Option Pt` and `capVertices` is new.

## [0.16.1]

- Uses `List.rightpad` and `List.zip_toArray` from Lean core in place of local copies.

## [0.16.0]

- Removes `clamp01`; the gradient proofs use `Float.clamp 0 1` from inkproof-float.

## [0.15.0]

- Turns the octagon at each strip value to its segment's direction (`octagonVertices` takes a direction, `stripVerticesFrom` is new), so a thin vertical or horizontal stroke has no foot at its end.

## [0.14.0]

- Draws `Shading.steps`: `Gradient.ofSteps` and `shadingState` give hard-edged colour changes at each stop, for fills and strokes.
- Builds against Scene v0.22.0.

## [0.13.0]

- Strips from `tessellateStroke` have round joins and caps, so no square corners protrude at vertices.
- Adds `areaTriangles`: an area whose line crosses its baseline is split at the crossing and filled only between line and baseline.
- Premultiplies the fragment colour and blends source-over, so overlapping translucent fills mix; `useProgram` enables blending.
- Builds against Scene v0.21.0, whose raster model blends source-over.

## [0.12.0]

- Draws gradient shadings, along x or y with up to five stops, for fills and strokes: `shadingColour` is replaced by `shadingState`, `Tile` has an `origin`, `State` has the gradient uniforms (numbers 5 to 11), and the fragment shader and `Shader.Expr.sat` are new.

## [0.11.0]

- Adds `viewOverlayFrame`: a data list under a view plus a pixel-space overlay in one compile, with each list's buffers kept across frames and views.

## [0.10.0]

- Adds `tessellateStroke`: under `viewFrame`, a strip's half width and a marker's radius are in pixels whatever the view, with no new upload per view.
- `draw` takes a third operand, the vertex stride in words.
- The vertex shader has inputs `a_dir` and `a_corner` and uniforms `u_size` and `u_view`.
- Colour is now uniform 4.

## [0.9.0]

- Adds `viewFrame` and `viewTile`, a frame of a display list in data coordinates under a view, so zooming reuses uploaded buffers.

## [0.8.0]

- Builds against Scene v0.19.0; a command whose shading is a gradient is not drawn (empty scissor) until gradients are supported.

## [0.7.1]

- Compiling a frame runs in constant stack in the number of commands, so a display list of 40000 commands encodes in the browser.

## [0.7.0]

- Adds `frameBytes`, the wire bytes of a fresh frame of a display list in one call.

## [0.6.2]

- Adds `releaseState` to the generated interpreter, which deletes the buffers and programs a state holds.

## [0.6.1]

- Expresses `chainTriangles` through Scene's `Item.fold` (Scene v0.9.0), removing the private traversal.

## [0.6.0]

- Adds `pixelTile` and `frame`, the commands of a frame of a display list in device pixels from the top left, with theorems for the clip-space map, the scissor and the wire round trip.

## [0.5.1]

- Tests the generated JavaScript under Lasm 0.8.0.

## [0.5.0]

- Adds a `scissor` command, and `compile` now sets `u_slope`, `u_offset`, `u_colour` and the scissor before every draw, so clipped shapes and colours draw; a `Tile` carries `slope`, `offset` and a `scissor` map in place of `uniform`.
- Adds `tessellate`, which turns a Scene command into the vertex words `compile` takes, with theorems that its triangles cover the command's shape.

## [0.4.0]

- Adds a `createProgram` command, so the generated interpreter builds the renderer's program, numbers its uniforms and binds vertices, and draws visible geometry on WebGL2.
- Prints `#version` before the header comments in the GLSL, which WebGL2 requires.

## [0.3.0]

- Draws each tile's commands in Scene's paint order instead of a local layer sort, and depends on Scene v0.6.0.

## [0.2.0]

- Compiler from Scene display lists to GPU command lists, caching buffers per tile so pan and zoom upload nothing.
- Proved against an abstract GPU model: every command drawn once in layer order, and the same draws cached or fresh.

## [0.1.0]

- Command set with binary encoding, a proved round trip, and a generated JavaScript decoder and interpreter.
- Float32 shader language, GLSL ES 3.00 printer, and the renderer's vertex and fragment shaders written in it.
- Proved half-pixel placement bound for the vertex shader under the Float32 model.
