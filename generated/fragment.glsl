#version 300 es
// Copyright (c) 2026 Paul Butcher. All rights reserved.
// Released under Apache 2.0 license as described in the file LICENSE.
// Generated from Inkproof.Gpu.Shader. Do not edit.
precision highp float;
in vec2 v_pos;
uniform vec4 u_colour;
uniform vec2 u_axis;
uniform vec4 u_start;
uniform vec4 u_inv;
uniform vec4 u_delta0;
uniform vec4 u_delta1;
uniform vec4 u_delta2;
uniform vec4 u_delta3;
out vec4 o_colour;
void main() {
  float t = ((v_pos.x * u_axis.x) + (v_pos.y * u_axis.y));
  float w0 = clamp(((t - u_start.x) * u_inv.x), 0.0, 1.0);
  float w1 = clamp(((t - u_start.y) * u_inv.y), 0.0, 1.0);
  float w2 = clamp(((t - u_start.z) * u_inv.z), 0.0, 1.0);
  float w3 = clamp(((t - u_start.w) * u_inv.w), 0.0, 1.0);
  o_colour = ((((u_colour + (u_delta0 * w0)) + (u_delta1 * w1)) + (u_delta2 * w2)) + (u_delta3 * w3));
}
