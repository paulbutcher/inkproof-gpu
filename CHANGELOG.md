# Changelog

## [0.2.0]

- Compiler from Scene display lists to GPU command lists, caching buffers per tile so pan and zoom upload nothing.
- Proved against an abstract GPU model: every command drawn once in layer order, and the same draws cached or fresh.

## [0.1.0]

- Command set with binary encoding, a proved round trip, and a generated JavaScript decoder and interpreter.
- Float32 shader language, GLSL ES 3.00 printer, and the renderer's vertex and fragment shaders written in it.
- Proved half-pixel placement bound for the vertex shader under the Float32 model.
