//! Puts pixels on your screen.
//!
//! A basic example:
//! ```ignore
//! let mut renderer = Renderer::new(&mut context, sampler);
//! loop {
//!     renderer.push(Rect::new()
//!         .at(0.5, 0.1)
//!         .angle(0.5)
//!         .scale(0.1, 2.0)
//!     );
//!
//!     renderer.renderer(&mut context).unwrap();
//! }
//! ```
//!
//! Here we instance a Rect, and then place it using some
//! convenience functions. We then tell the renderer to render it.
//!
//! Since the renderer is based around
//! [instancing](https://www.khronos.org/opengl/wiki/Vertex_Rendering#Instancing),
//! some things (like skewing) are harder to do.

use cgmath::Vector2;
use luminance::context::GraphicsContext;
use luminance::pipeline::PipelineState;
use luminance::pixel::NormRGBA8UI;
use luminance::render_state::RenderState;
use luminance::tess::Mode;
use luminance::texture::{Dim3, GenMipmaps, Sampler, Texture};
use luminance_sdl2::GL33Surface;
use rand::prelude::*;

// Me no likey, but at least it's not documented.
use crate::semantics::*;

/// Vertex shader source code.
const VS_STR: &str = include_str!("vs.glsl");
/// Fragment shader source code.
const FS_STR: &str = include_str!("fs.glsl");
/// Particle vertex shader source code.
const VS_PARTICLE_STR: &str = include_str!("vs_particle.glsl");
/// The maximum size of a sprite sheet, and the maximum number of
/// sprite sheets.
const SPRITE_SHEET_SIZE: [u32; 3] = [512, 512, 512];

/// A simple rectangle for rendering sprites and the like.
const RECT: [Vertex; 6] = [
    Vertex::new(VPosition::new([-0.5, -0.5])),
    Vertex::new(VPosition::new([0.5, -0.5])),
    Vertex::new(VPosition::new([0.5, 0.5])),
    Vertex::new(VPosition::new([0.5, 0.5])),
    Vertex::new(VPosition::new([-0.5, 0.5])),
    Vertex::new(VPosition::new([-0.5, -0.5])),
];

/// Wraps the construction of a SpriteSheet.
//
// I have some ideas of typing this harder to make sure
// you place a tile dimension on it. #CatchThoseMistakes
//
// The struct might also be useless, and we could easily just
// give out a SpriteSheet directly.
#[derive(Clone, Debug)]
pub struct SpriteSheetBuilder {
    pub image: Vec<u8>,
    pub image_dim: (Pixels, Pixels),
    pub tile_dim: Option<(Pixels, Pixels)>,
}

/// A marker type for the unit pixels.
pub type Pixels = usize;

impl SpriteSheetBuilder {
    pub fn new(width: Pixels, height: Pixels, image: Vec<u8>) -> Self {
        Self {
            image,
            image_dim: (width, height),
            tile_dim: None,
        }
    }

    pub fn tile_size(mut self, tile_width: Pixels, tile_height: Pixels) -> Self {
        self.tile_dim = Some((tile_width, tile_height));
        self
    }
}

/// A light reference to a SpriteSheet that lives on the GPU.
#[derive(Clone, Copy, Debug)]
pub struct SpriteSheet {
    id: usize,
    image_dim: (Pixels, Pixels),
    tile_dim: Option<(Pixels, Pixels)>,
}

impl SpriteSheet {
    /// Returns the SpriteRegion of a tile given the specified tile sizes,
    /// starting from the top left.
    pub fn grid(&self, tx: usize, ty: usize) -> SpriteRegion {
        if let Some(tile_dim) = self.tile_dim {
            let xlo = ((tile_dim.0 * tx) as f32) / (SPRITE_SHEET_SIZE[0] as f32);
            let ylo = ((tile_dim.1 * ty) as f32) / (SPRITE_SHEET_SIZE[1] as f32);
            let w = (tile_dim.0 as f32) / (SPRITE_SHEET_SIZE[0] as f32);
            let h = (tile_dim.1 as f32) / (SPRITE_SHEET_SIZE[1] as f32);
            (
                self.id as f32 / (SPRITE_SHEET_SIZE[2] as f32),
                [xlo, ylo, xlo + w, ylo + h],
            )
        } else {
            // TODO(ed): We could potentially catch this as a type error
            // using the SpriteSheet as an enum?
            // TODO(ed):
            // We could also find grid slices that are out of bounds,
            // if we checked the image dimension.
            panic!();
        }
    }
}

// Helper macro for fast writing of boilerplate code.
macro_rules! impl_transform {
    (deref, $fn:ident, $op:tt, $( $var:ident : $type:ident => $set:tt ),*) => {
        fn $fn(&mut self, $( $var : $type ),*) -> &mut Self {
            $(
                *self.$set() $op $var;
            )*
            self
        }
    };

    (arr, $fn:ident, $op:tt, $( $var:ident : $type:ident => $arr:tt [ $idx:expr ] ),*) => {
        fn $fn(&mut self, $( $var : $type ),*) -> &mut Self {
            $(
                self.$arr()[$idx] $op $var;
            )*
            self
        }
    };
}

// A fast and hacky way to implement the Transform trait when
// the fields are named the same. Maybe make it a bit more robust?
macro_rules! impl_transform_for {
    ($ty:ident) => {
        impl Transform for $ty {
            fn x_mut(&mut self) -> &mut f32 {
                &mut self.position.x
            }
            fn y_mut(&mut self) -> &mut f32 {
                &mut self.position.y
            }

            fn sx_mut(&mut self) -> &mut f32 {
                &mut self.scale.x
            }

            fn sy_mut(&mut self) -> &mut f32 {
                &mut self.scale.y
            }

            fn r_mut(&mut self) -> &mut f32 {
                &mut self.rotation
            }
        }
    };
}

/// Manipulate and move things around.
/// Designed to be chainable.
pub trait Transform {
    /// The x-component of the position.
    fn x_mut(&mut self) -> &mut f32;
    /// The y-component of the position.
    fn y_mut(&mut self) -> &mut f32;

    /// The x-component of the scale.
    fn sx_mut(&mut self) -> &mut f32;
    /// The y-component of the scale.
    fn sy_mut(&mut self) -> &mut f32;

    /// The rotation.
    fn r_mut(&mut self) -> &mut f32;

    // TODO(ed): Comment on the functions the macro implement?
    impl_transform!(deref, move_by,  +=, x:  f32 => x_mut,         y:  f32 => y_mut);
    impl_transform!(deref, at,       =,  x:  f32 => x_mut,         y:  f32 => y_mut);
    impl_transform!(deref, angle,    =,  r:  f32 => r_mut);
    impl_transform!(deref, rotate,   +=, r:  f32 => r_mut);
    impl_transform!(deref, scale_by, *=, sx: f32 => sx_mut,        sy: f32 => sy_mut);
    impl_transform!(deref, scale,     =, sx: f32 => sx_mut,        sy: f32 => sy_mut);
}

/// Colorable things are Tint-able!
pub trait Tint {
    fn color_mut(&mut self) -> &mut [f32; 4];

    // TODO(ed): Comment on the functions the macro implement?
    impl_transform!(arr, rgb,  =,  r:  f32 => color_mut[0],  g:  f32 => color_mut[1], b: f32 => color_mut[2]);
    impl_transform!(arr, rgba, *=, r:  f32 => color_mut[0],  g:  f32 => color_mut[1], b: f32 => color_mut[2], a: f32 => color_mut[3]);
    impl_transform!(arr, r,    *=, r:  f32 => color_mut[0]);
    impl_transform!(arr, g,    *=, g:  f32 => color_mut[1]);
    impl_transform!(arr, b,    *=, b:  f32 => color_mut[2]);
    impl_transform!(arr, a,    *=, a:  f32 => color_mut[3]);

    fn tint(&mut self, r: f32, g: f32, b: f32, a: f32) -> &mut Self {
        self.rgba(r, g, b, a)
    }
}

/// Type used to simplify some types.
pub type Tex = Texture<<GL33Surface as GraphicsContext>::Backend, Dim3, NormRGBA8UI>;
/// A function that renders.
pub type RenderFn = dyn FnMut(
    &[Instance],
    &[FrozenParticles],
    &mut Tex,
    cgmath::Matrix4<f32>,
    &mut GL33Surface,
) -> Result<(), ()>;

/// A way to handle random variables.
pub enum Distribution {
    /// Always returns 0.
    NoDice,
    /// All values are equally likely, no bias.
    Uniform,
    /// The fun name for Uniform.
    Die,
    /// Biased towards 0.5. Looks like a triangle.
    TwoDice,
    /// Biased towards 0.5. Looks like a bellcurve.
    ThreeDice,
    /// Biased towards 0. Looks like 1/x.
    Square,
}

impl Distribution {
    /// Returns a random value from the given distribution.
    pub fn sample(&self) -> f32 {
        let mut rng = rand::thread_rng();

        match self {
            Distribution::NoDice => 0.0,
            Distribution::Uniform | Distribution::Die => rng.gen::<f32>(),
            Distribution::TwoDice => (rng.gen::<f32>() + rng.gen::<f32>()) / 2.0,
            Distribution::ThreeDice => {
                (rng.gen::<f32>() + rng.gen::<f32>() + rng.gen::<f32>()) / 3.0
            }
            Distribution::Square => rng.gen::<f32>() * rng.gen::<f32>(),
        }
    }
}

/// Takes a lower bound and an upper bound and randomly selects values in-between.
pub struct RandomProperty {
    pub distribution: Distribution,
    pub range: [f32; 2],
}

impl Default for RandomProperty {
    fn default() -> Self {
        Self {
            distribution: Distribution::Uniform,
            range: [0.0, 1.0],
        }
    }
}

impl RandomProperty {
    pub fn new(lo: f32, hi: f32) -> Self {
        Self {
            distribution: Distribution::ThreeDice,
            range: [lo, hi],
        }
    }

    /// Samples a random value in the given range.
    pub fn sample(&self) -> f32 {
        self.range[0] + (self.range[1] - self.range[0]) * self.distribution.sample()
    }
}

/// An actual particle system. Contains a lot of
/// knobs.
///
/// Particles are rendered only on the GPU and as such are 'almost' free.
#[derive(Default)]
pub struct ParticleSystem {
    pub time: f32,
    pub particles: Vec<Particle>,

    // TODO(ed): GRR!! I want this to be Vector2
    // and implement Transform
    pub position: [f32; 2],

    pub sprites: Vec<SpriteRegion>,

    /// Allowed x-coordinates to spawn on, relative to 'position'.
    pub x: RandomProperty,
    /// Allowed y-coordinates to spawn on, relative to 'position'.
    pub y: RandomProperty,

    /// How long, in seconds, the particle should live.
    pub lifetime: RandomProperty,

    // TODO(ed): Options for how this is selected
    /// The angle of the velocity in radians.
    pub v_angle: RandomProperty,
    /// How fast a particle should move when it spawns.
    pub v_magnitude: RandomProperty,

    /// What direction to accelerate in.
    pub acceleration_angle: RandomProperty,
    /// How strong the acceleration is in that direction.
    pub acceleration_magnitude: RandomProperty,

    /// A fake 'air-resistance'. Lower values mean less resistance.
    /// Negative values give energy over time.
    pub drag: RandomProperty,

    /// The rotation to spawn with.
    pub angle: RandomProperty,
    /// How fast the angle should change when the particle spawns.
    pub angle_velocity: RandomProperty,
    /// A fake 'energy-loss'. Lower values mean less resistance.
    /// Negative values give energy over time.
    pub angle_drag: RandomProperty,

    /// How large the particle should be in X when it starts.
    pub start_sx: RandomProperty,
    /// How large the particle should be in Y when it starts.
    pub start_sy: RandomProperty,

    /// How large the particle should be in X when it dies.
    pub end_sx: RandomProperty,
    /// How large the particle should be in Y when it dies.
    pub end_sy: RandomProperty,

    /// How red the particle should be when it spawns.
    pub start_red: RandomProperty,
    /// How green the particle should be when it spawns.
    pub start_green: RandomProperty,
    /// How blue the particle should be when it spawns.
    pub start_blue: RandomProperty,
    /// How transparent the particle should be when it spawns.
    pub start_alpha: RandomProperty,

    /// How red the particle should be when it dies.
    pub end_red: RandomProperty,
    /// How green the particle should be when it dies.
    pub end_green: RandomProperty,
    /// How blue the particle should be when it dies.
    pub end_blue: RandomProperty,
    /// How transparent the particle should be when it dies.
    pub end_alpha: RandomProperty,
}

impl ParticleSystem {
    pub fn new() -> Self {
        Self {
            time: 0.0,
            particles: Vec::new(),

            x: RandomProperty::new(-0.1, 0.1),
            y: RandomProperty::new(-0.1, 0.1),

            v_angle: RandomProperty::new(0.0, 2.0 * std::f32::consts::PI),

            acceleration_angle: RandomProperty::new(0.0, 2.0 * std::f32::consts::PI),

            start_sx: RandomProperty::new(1.0, 1.0),
            start_sy: RandomProperty::new(1.0, 1.0),

            ..Self::default()
        }
    }

    /// Steps the particle system some delta-time forward. Removes dead particles.
    pub fn update(&mut self, delta: f32) {
        self.time += delta;

        self.particles = std::mem::take(&mut self.particles)
            .into_iter()
            .filter(|x| *x.lifetime > (self.time - *x.spawn))
            .collect();
    }

    /// Spawns a new particle.
    pub fn spawn(&mut self) {
        let velocity_angle = self.v_angle.sample();
        let velocity_magnitude = self.v_magnitude.sample();

        let acceleration_angle = self.acceleration_angle.sample();
        let acceleration_magnitude = self.acceleration_magnitude.sample();

        let (sheet, uv) = if self.sprites.is_empty() {
            &(-1.0, [0.0, 0.0, 0.0, 0.0])
        } else {
            self.sprites.choose(&mut rand::thread_rng()).unwrap()
        };

        self.particles.push(Particle {
            spawn: PSpawn::new(self.time),
            lifetime: PLifetime::new(self.lifetime.sample()),

            position: IPosition::new([
                self.x.sample() + self.position[0],
                self.y.sample() + self.position[1],
            ]),
            velocity: PVelocity::new([
                velocity_angle.cos() * velocity_magnitude,
                velocity_angle.sin() * velocity_magnitude,
            ]),
            acceleration: PAcceleration::new([
                acceleration_angle.cos() * acceleration_magnitude,
                acceleration_angle.sin() * acceleration_magnitude,
            ]),
            drag: PDrag::new(self.drag.sample()),

            angle_info: PAngleInfo::new([
                self.angle.sample(),
                self.angle_velocity.sample(),
                self.angle_drag.sample(),
            ]),

            scale_extrems: PScaleExtrems::new([
                self.start_sx.sample(),
                self.start_sy.sample(),
                self.end_sx.sample(),
                self.end_sy.sample(),
            ]),

            start_color: PStartColor::new([
                self.start_red.sample(),
                self.start_green.sample(),
                self.start_blue.sample(),
                self.start_alpha.sample(),
            ]),
            end_color: PEndColor::new([
                self.end_red.sample(),
                self.end_green.sample(),
                self.end_blue.sample(),
                self.end_alpha.sample(),
            ]),

            sheet: ISheet::new(*sheet),
            uv: IUV::new(*uv),
        });
    }

    /// Copies out the rendering information.
    pub fn freeze(&self) -> FrozenParticles {
        // TODO(ed): Can we get rid of this clone?
        FrozenParticles {
            position: self.position,
            time: self.time,
            particles: self.particles.clone(),
        }
    }
}

/// A particle system that can be rendered.
/// Used internally.
pub struct FrozenParticles {
    pub position: [f32; 2],
    pub time: f32,
    pub particles: Vec<Particle>,
}

/// From where you see the world. Can be moved around via [Transform].
pub struct Camera {
    position: Vector2<f32>,
    scale: Vector2<f32>,
    rotation: f32,
}

impl_transform_for!(Camera);

impl Camera {
    pub fn new() -> Self {
        Self {
            position: Vector2::new(0.0, 0.0),
            scale: Vector2::new(1.0, 1.0),
            rotation: 0.0,
        }
    }

    /// Converts the camera to a matrix for sending to the GPU.
    pub fn matrix(&self) -> cgmath::Matrix4<f32> {
        use cgmath::{Matrix4, Rad, Vector3};
        let scale = Matrix4::from_nonuniform_scale(self.scale.x, self.scale.y, 0.0);
        let rotation = Matrix4::from_angle_z(Rad(self.rotation));
        let translation =
            Matrix4::from_translation(Vector3::new(self.position.x, self.position.y, 0.0));
        scale * rotation * translation
    }
}

/// A big struct holding all the rendering state.
pub struct Renderer {
    pub camera: Camera,
    pub render_fn: Box<RenderFn>,
    pub instances: Vec<Instance>,
    pub particles: Vec<FrozenParticles>,
    pub tex: Tex,
    pub sprite_sheets: Vec<SpriteSheet>,
}

/// If something can be rendered, it has to be Stamp.
pub trait Stamp {
    fn stamp(self) -> Instance;
}

/// A rectangle that can be rendered to the screen.
#[derive(Clone, Copy, Debug)]
pub struct Rect {
    position: Vector2<f32>,
    scale: Vector2<f32>,
    rotation: f32,
    color: [f32; 4],
}

impl_transform_for!(Rect);

impl Tint for Rect {
    fn color_mut(&mut self) -> &mut [f32; 4] {
        &mut self.color
    }
}

impl Stamp for &Rect {
    fn stamp(self) -> Instance {
        Instance {
            position: IPosition::new(self.position.into()),
            rotation: IRotation::new(self.rotation),
            scale: IScale::new(self.scale.into()),
            color: IColor::new(self.color),
            sheet: ISheet::new(-1.0),
            uv: IUV::new([0.0, 0.0, 1.0, 1.0]),
        }
    }
}

impl Stamp for Rect {
    fn stamp(self) -> Instance {
        (&self).stamp()
    }
}

// TODO(ed): This feels dumb...
impl Stamp for &mut Rect {
    fn stamp(self) -> Instance {
        (*self).stamp()
    }
}

#[allow(dead_code)]
impl Rect {
    pub fn new() -> Self {
        Self {
            position: Vector2::new(0.0, 0.0),
            scale: Vector2::new(1.0, 1.0),
            rotation: 0.0,
            color: [1.0, 1.0, 1.0, 1.0],
        }
    }
}

/// A rectangle that has a nice image on it.
#[derive(Clone, Copy, Debug)]
pub struct Sprite {
    position: Vector2<f32>,
    scale: Vector2<f32>,
    rotation: f32,
    color: [f32; 4],
    sheet: f32,
    rect: [f32; 4],
}

impl_transform_for!(Sprite);

impl Tint for Sprite {
    fn color_mut(&mut self) -> &mut [f32; 4] {
        &mut self.color
    }
}

impl Stamp for &Sprite {
    fn stamp(self) -> Instance {
        Instance {
            position: IPosition::new(self.position.into()),
            rotation: IRotation::new(self.rotation),
            scale: IScale::new(self.scale.into()),
            color: IColor::new(self.color),
            sheet: ISheet::new(self.sheet),
            uv: IUV::new(self.rect),
        }
    }
}

impl Stamp for Sprite {
    fn stamp(self) -> Instance {
        (&self).stamp()
    }
}

impl Stamp for &mut Sprite {
    fn stamp(self) -> Instance {
        (*self).stamp()
    }
}

/// A piece of a SpriteSheet to render.
type SpriteRegion = (f32, [f32; 4]);

#[allow(dead_code)]
impl Sprite {
    pub fn new(region: SpriteRegion) -> Self {
        Self {
            position: Vector2::new(0.0, 0.0),
            scale: Vector2::new(1.0, 1.0),
            rotation: 0.0,
            color: [1.0, 1.0, 1.0, 1.0],
            sheet: region.0,
            rect: region.1,
        }
    }
}

// TODO(ed): This should return an image type, so we can separate bytes
// from an image.
/// A fast and easy way to convert bytes to an image.
pub fn load_image_from_memory(bytes: &[u8]) -> Option<(u32, u32, Vec<u8>)> {
    // SAFETY: stbi either succeeds or returns a null pointer
    let mut w: i32 = 0;
    let mut h: i32 = 0;
    let mut comp: i32 = 4;
    unsafe {
        use stb_image::stb_image::bindgen::*;
        stbi_set_flip_vertically_on_load(1);
        let image = stbi_load_from_memory(
            bytes.as_ptr(),
            bytes.len() as i32,
            &mut w,
            &mut h,
            &mut comp,
            4,
        );
        if image.is_null() {
            None
        } else {
            let image =
                Vec::from_raw_parts(image as *mut u8, (w * h * 4) as usize, (w * h * 4) as usize);
            Some((w as u32, h as u32, image))
        }
    }
}

impl Renderer {
    pub fn new(context: &mut GL33Surface, sampler: Sampler) -> Self {
        let back_buffer = context.back_buffer().unwrap();
        let mut sprite_program = context
            .new_shader_program::<VertexSemantics, (), ShaderInterface>()
            .from_strings(VS_STR, None, None, FS_STR)
            .unwrap()
            .ignore_warnings();

        let mut particle_program = context
            .new_shader_program::<VertexSemantics, (), ShaderInterface>()
            .from_strings(VS_PARTICLE_STR, None, None, FS_STR)
            .unwrap()
            .ignore_warnings();

        let tex: Tex =
            Texture::new(context, SPRITE_SHEET_SIZE, 0, sampler).expect("texture createtion!");

        let render_fn = move |instances: &[Instance],
                              systems: &[FrozenParticles],
                              tex: &mut Tex,
                              view: cgmath::Matrix4<f32>,
                              context: &mut GL33Surface| {
            let triangle = context
                .new_tess()
                .set_vertices(&RECT[..])
                .set_instances(&instances[..])
                .set_mode(Mode::Triangle)
                .build()
                .unwrap();

            let particles: Vec<_> = systems
                .iter()
                .map(|s| {
                    (
                        s.time,
                        context
                            .new_tess()
                            .set_vertices(&RECT[..])
                            .set_instances(&s.particles[..])
                            .set_mode(Mode::Triangle)
                            .build()
                            .unwrap(),
                    )
                })
                .collect();

            let render = context
                .new_pipeline_gate()
                .pipeline(
                    &back_buffer,
                    &PipelineState::default(),
                    |pipeline, mut shd_gate| {
                        let bound_tex = pipeline.bind_texture(tex)?;

                        let state = RenderState::default().set_depth_test(None);
                        shd_gate.shade(&mut sprite_program, |mut iface, uni, mut rdr_gate| {
                            iface.set(&uni.tex, bound_tex.binding());
                            iface.set(&uni.view, view.into());

                            rdr_gate.render(&state, |mut tess_gate| tess_gate.render(&triangle))
                        })?;

                        shd_gate.shade(&mut particle_program, |mut iface, uni, mut rdr_gate| {
                            iface.set(&uni.tex, bound_tex.binding());
                            iface.set(&uni.view, view.into());
                            rdr_gate.render(&state, |mut tess_gate| {
                                for (t, p) in particles {
                                    iface.set(&uni.t, t);
                                    tess_gate.render(&p)?;
                                }
                                Ok(())
                            })
                        })
                    },
                )
                .assume();

            if render.is_ok() {
                context.window().gl_swap_window();
                Ok(())
            } else {
                Err(())
            }
        };

        Self {
            camera: Camera::new(),
            render_fn: Box::new(render_fn),
            instances: Vec::new(),
            tex,
            sprite_sheets: Vec::new(),
            particles: Vec::new(),
        }
    }

    /// Queues the stamp for rendering.
    pub fn push<T: Stamp>(&mut self, stamp: T) {
        self.instances.push(stamp.stamp());
    }

    /// Queues the particle_systems for rendering.
    pub fn push_particle_system(&mut self, system: &ParticleSystem) {
        self.particles.push(system.freeze());
    }

    /// Takes the SpriteSheetBuilder and generates a new SpriteSheet.
    /// There's a hard limit on the number of SpriteSheets that can be
    /// added: see [SPRITE_SHEET_SIZE].
    pub fn add_sprite_sheet(&mut self, builder: SpriteSheetBuilder) -> SpriteSheet {
        let id = self.sprite_sheets.len();
        assert!((id as u32) < SPRITE_SHEET_SIZE[2]);

        self.tex
            .upload_part_raw(
                GenMipmaps::No,
                [0, 0, id as u32],
                [builder.image_dim.0 as u32, builder.image_dim.1 as u32, 1],
                &builder.image,
            )
            .unwrap();
        // Upload texture to slot
        let sheet = SpriteSheet {
            id,
            image_dim: builder.image_dim,
            tile_dim: builder.tile_dim,
        };
        self.sprite_sheets.push(sheet);
        sheet
    }

    pub fn render(&mut self, context: &mut GL33Surface) -> Result<(), ()> {
        let res = (*self.render_fn)(
            &self.instances,
            &self.particles,
            &mut self.tex,
            self.camera.matrix(),
            context,
        );
        self.instances.clear();
        self.particles.clear();
        res
    }
}
