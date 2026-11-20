# Changelog

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
