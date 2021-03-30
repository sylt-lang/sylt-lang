//! Stuff used internally for rendering. Probably not that interesting for normal usage.

use luminance::pipeline::TextureBinding;
use luminance::pixel::NormUnsigned;
use luminance::shader::Uniform;
use luminance::texture::Dim3;
use luminance_derive::{Semantics, UniformInterface, Vertex};

#[derive(Copy, Clone, Debug, Semantics)]
pub enum VertexSemantics {
    #[sem(name = "co", repr = "[f32; 2]", wrapper = "VPosition")]
    VPosition,

    #[sem(name = "position", repr = "[f32; 2]", wrapper = "IPosition")]
    IPosition,
    #[sem(name = "rotation", repr = "f32", wrapper = "IRotation")]
    IRotation,
    #[sem(name = "scale", repr = "[f32; 2]", wrapper = "IScale")]
    IScale,
    #[sem(name = "color", repr = "[f32; 4]", wrapper = "IColor")]
    IColor,
    #[sem(name = "sheet", repr = "f32", wrapper = "ISheet")]
    ISheet,
    #[sem(name = "uv", repr = "[f32; 4]", wrapper = "IUV")]
    IUV,

    #[sem(name = "spawn", repr = "f32", wrapper = "PSpawn")]
    PSpawn,
    #[sem(name = "lifetime", repr = "f32", wrapper = "PLifetime")]
    PLifetime,
    #[sem(name = "velocity", repr = "[f32; 2]", wrapper = "PVelocity")]
    PVelocity,
    #[sem(name = "acceleration", repr = "[f32; 2]", wrapper = "PAcceleration")]
    PAcceleration,
    #[sem(name = "drag", repr = "f32", wrapper = "PDrag")]
    PDrag,

    #[sem(name = "angle_info", repr = "[f32; 3]", wrapper = "PAngleInfo")]
    PAngleInfo,

    #[sem(name = "scale_extrems", repr = "[f32; 4]", wrapper = "PScaleExtrems")]
    PScaleExtrems,

    #[sem(name = "start_color", repr = "[f32; 4]", wrapper = "PStartColor")]
    PStartColor,
    #[sem(name = "end_color", repr = "[f32; 4]", wrapper = "PEndColor")]
    PEndColor,
}

/// What is placed in a simple vertex. Only used for the simple Rect.
/// Used internally.
#[repr(C)]
#[derive(Vertex, Copy, Clone, PartialEq, Debug)]
#[vertex(sem = "VertexSemantics")]
pub struct Vertex {
    pub position: VPosition,
}

/// All the ways to change how an instance is rendered.
/// Used internally.
#[repr(C)]
#[derive(Vertex, Copy, Clone, PartialEq, Debug)]
#[vertex(sem = "VertexSemantics", instanced = "true")]
pub struct Instance {
    pub position: IPosition,
    pub rotation: IRotation,
    pub scale: IScale,
    pub color: IColor,
    pub sheet: ISheet,
    pub uv: IUV,
}

/// What is needed to render a particle.
/// Used internally.
#[repr(C)]
#[derive(Vertex, Copy, Clone, PartialEq)]
#[vertex(sem = "VertexSemantics", instanced = "true")]
pub struct Particle {
    pub spawn: PSpawn,
    pub lifetime: PLifetime,
    pub position: IPosition,
    pub velocity: PVelocity,
    pub acceleration: PAcceleration,
    pub drag: PDrag,

    pub angle_info: PAngleInfo,

    pub scale_extrems: PScaleExtrems,

    pub start_color: PStartColor,
    pub end_color: PEndColor,

    pub sheet: ISheet,
    pub uv: IUV,
}

/// Interface for passing uniforms.
/// Used internally.
#[derive(Debug, UniformInterface)]
pub struct ShaderInterface {
    #[uniform(unbound)]
    pub t: Uniform<f32>,

    pub view: Uniform<[[f32; 4]; 4]>,

    pub tex: Uniform<TextureBinding<Dim3, NormUnsigned>>,
}
