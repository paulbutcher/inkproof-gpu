# Inkproof.Gpu design

## Command set and wire format

`Inkproof.Gpu.specs` is the one definition of the command set: each command has a name, an opcode and a list of operand kinds, and nothing in it names a graphics API. The Lean encoder and decoder are driven by the table, and `Inkproof.Gpu.js` prints the JavaScript decoder and interpreter from it, so they cannot drift. The WebGL2 realisation of each command lives only in the JavaScript printer (`webglBody`), which is where a WebGPU backend would differ.

A command list is one buffer: a little-endian 32-bit command count, then each command as an opcode byte followed by its operands. `generated/gpu.js` is the printed output; `lake exe gen generated` regenerates it. The GLSL shaders beside it and the JavaScript tests fail when it is stale. `createProgram` builds the renderer's one program from the shader sources embedded in `gpu.js`; `uniform` names a uniform by its position in `uniformNames` and sets it with as many floats as it is given, and `draw` reads each vertex as two floats.

## Compiling a display list

`compile` turns a view's tiles (a display list and the transform uniform) into `Op`s; `Op.toCmd` gives the wire command. The caller supplies `tess`, the vertex words of one command, and its raster fidelity is outside the theorems. Buffers are cached by content, so a tile whose vertex words match a cached entry reuses its buffers and pan and zoom upload nothing. Unused buffers are deleted and handles are never reused. A frame sets the uniform and draws once per command, in layer order; the host binds the program.

The theorems are stated against `Gpu` in `Proofs/Compile.lean`, an abstract model of buffers, uniform and draw log. Handles go on the wire modulo `2 ^ 32`, so the model is exact only while fewer than that many buffers are allocated.

## Shader language

`Inkproof.Gpu.Shader` is a small Float32 language: scalars and vectors, componentwise `+`, `-` and `*` with scalar broadcast, vector construction and component selection. A `Shader` is typed inputs, uniforms and outputs, local declarations and assignments. `Shader.run` gives its meaning over inkproof-float's Float32 and `Shader.glsl` prints GLSL ES 3.00; the renderer's shaders (`vertexShader`, `fragmentShader`) are values of this type and `generated/*.glsl` are printed from them. Division and fused multiply-add are not in the language.

The vertex shader maps a position relative to its tile origin through the rebased affine map `a_position * u_slope + u_offset`, with the slope and offset computed in double precision by the caller.

### What is not proved

The printer preserves meaning only under the Float32 model of inkproof-float, which assumes IEEE binary32 rounding for `+`, `-` and `*`. GLSL ES 3.00 guarantees far less for `highp` (a relative precision of 2^-16 and no stated rounding), so no theorem can relate the printed text to the language under the specification's own precision model; the placement bound holds on hardware that implements binary32.

The half-pixel placement bound (`vertexShader_placement`) is proved directly from inkproof-float's Float32 rounding lemmas, for the two operations the shader performs. The origin is subtracted on the CPU in double precision, so the rebased affine theorem of inkproof-scale, which models the subtraction in the same precision, does not describe this shader; the bound is on the Float32 inputs the shader receives.
