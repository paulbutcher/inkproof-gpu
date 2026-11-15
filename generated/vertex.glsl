#version 300 es
// Copyright (c) 2026 Paul Butcher. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Generated from Inkproof.Gpu.Shader. Do not edit.
precision highp float;
in vec2 a_position;
uniform vec2 u_slope;
uniform vec2 u_offset;
void main() {
  vec2 p = ((a_position * u_slope) + u_offset);
  gl_Position = vec4(p.x, p.y, 0.0, 1.0);
}
