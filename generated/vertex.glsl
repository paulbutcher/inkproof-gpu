#version 300 es
// Copyright (c) 2026 Paul Butcher. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Generated from Inkproof.Gpu.Shader. Do not edit.
precision highp float;
in vec2 a_position;
in vec2 a_dir;
in vec2 a_corner;
uniform vec2 u_slope;
uniform vec2 u_offset;
uniform float u_size;
uniform vec4 u_view;
out vec2 v_pos;
void main() {
  vec2 p = ((a_position * u_slope) + u_offset);
  vec2 d = ((a_dir * u_slope) * vec2(u_view.x, u_view.y));
  float r = inversesqrt(((d.x * d.x) + (d.y * d.y)));
  vec2 t = (d * r);
  vec2 n = vec2((0.0 - t.y), t.x);
  vec2 o = (((t * a_corner.x) + (n * a_corner.y)) * u_size);
  gl_Position = vec4((p.x + (o.x * u_view.z)), (p.y + (o.y * u_view.w)), 0.0, 1.0);
  v_pos = a_position;
}
