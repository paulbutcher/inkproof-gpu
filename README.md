# Inkproof.Gpu

GPU command lists for Inkproof charts: the command set and its binary encoding, a small shader language that prints GLSL, and a generated JavaScript decoder and interpreter that runs a command list on WebGL2. The command set and the shaders are defined once, in Lean, and everything else is generated from them. Released under the Apache 2.0 license; see `LICENSE`.

## What it does

- Describe the GPU command set, backend-neutrally, and encode and decode command lists to a binary buffer: `specs`, `Cmd`, `Op`, `encode`, `decode`.
- Run a command list on WebGL2 in the browser: the generated JavaScript decoder and interpreter in `generated/gpu.js`, printed by `js` (regenerate with `lake exe gen generated`). Free what a run left on the GL context with `releaseState(gl, state)`.
- Model what a command list does to buffers, uniforms and draws, to state theorems about it: `Gpu`, `Gpu.run`, `Gpu.step`.
- Turn a view's tiles of Scene display-list commands into GPU ops, caching vertex buffers by content so pan and zoom upload nothing: `compile`, `compileCmds`, `Cache`, `Tile`, `frameDraws`.
- Tessellate Scene commands (rectangles, text boxes, markers, strips, areas, envelopes) into triangles, and into Float32 vertex words relative to a tile origin: `triangles`, `tessellate`, `triWords`, `vertexWords`; or into vertices whose strip width and marker radius the vertex shader applies in pixels: `tessellateStroke`, `strokeVertices`, `strokeSize`.
- Compute per-draw state: colour words, gradient uniforms, and the scissor rectangle for a clip: `colourWords`, `clipRect`, `Tile.stateOf`.
- Draw a gradient shading, for fills and strokes: a `Scene.Shading.gradient` along x or y with up to five stops is drawn with its colour interpolated between the stops across the shape (`shadingState`, `Gradient.ofStops`), and a flat shading as before. A gradient with more stops, or stops that descend, is not drawn. `evalStops_close` states how the shader's blend relates to `Shading.at`.
- Draw a chart in device pixels from the top left of a target, with a scissor that flips y, and build the commands of a whole frame, setup and clear included: `pixelTile`, `pixelScissor`, `pixelBox`, `frame`, `frameSetup`; get a fresh frame's wire bytes in one call with `frameBytes`.
- Zoom or pan a chart without re-uploading: draw a display list compiled once in data coordinates under a view's visible x and y ranges, filling a plot rectangle of the target: `View`, `viewTile`, `viewFrame`, `viewFrameBytes`; `viewFrame_cached` states that a frame under another view uploads nothing.
- Draw a zooming chart's axes and gridlines in pixels beside its data in one frame: `viewOverlayFrame` (and `viewOverlayFrameBytes`) takes the data list and an overlay list in device pixels; `viewOverlayFrame_cached` and `viewOverlayFrame_data_cached` state that zooming uploads nothing for the data.
- Draw strips and markers of a zooming chart at a constant size in pixels, with no new upload per view: `viewFrame` with `tessellateStroke` (which `viewFrameBytes` uses) takes a strip's half width and a marker's radius in pixels; `viewFrame_stroke_cached` states that nothing is uploaded under another view.
- Write shaders in a small Float32 language, evaluate them, and print GLSL ES 3.00: `Shader.Shader`, `Shader.Shader.run`, `Shader.Shader.glsl`, `Shader.Shader.WellTyped`. A reciprocal square root is `Shader.Expr.rsqrt` and a clamp to 0 to 1 is `Shader.Expr.sat`.
- Get the renderer's shaders and their uniform names: `vertexShader`, `fragmentShader`, `uniformNames` (printed to `generated/vertex.glsl` and `generated/fragment.glsl`).
- Rely on proofs that tessellation covers what Scene's raster model draws, that decoding inverts encoding, and that vertex placement is within half a pixel: see `Inkproof/Gpu/Proofs/`.

## Using it

Require it at a release tag in your `lakefile.lean`:

```lean
require «inkproof-gpu» from git "https://github.com/paulbutcher/inkproof-gpu" @ "v0.5.1"
```

`DESIGN.md` describes the wire format, compilation, tessellation and the shader language, and what is not proved.
