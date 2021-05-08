use lingon::{Game, random::{Uniform, Distribute, NoDice}};
use lingon::renderer::{Rect, Sprite, Transform, Tint};
use std::sync::{Arc, Mutex};
use crate::{*, error::RuntimeError};
use crate::Value::*;
use crate as sylt;

// Errors are important, they should be easy to write!
macro_rules! error {
    ( $name:expr, $( $fmt:expr ),* ) => {
        Err(RuntimeError::ExternError($name.to_string(), format!( $( $fmt ),* )))
    }
}

fn unpack_int_int_tuple(value: &Value) -> (i64, i64) {
    if let Tuple(tuple) = value {
        if let (Some(Int(w)), Some(Int(h))) = (tuple.get(0), tuple.get(1)) {
            return (*w, *h);
        }
    };
    unreachable!("Expected tuple (int, int) but got '{:?}'", value);
}

fn parse_dist(name: &str) -> Option<Box<dyn lingon::random::Distribute>> {
    use lingon::random::*;

    Some(match name{
        "Square" => Box::new(Square),
        "ThreeDice" => Box::new(ThreeDice),
        "TwoDice" => Box::new(TwoDice),
        "Uniform" => Box::new(Uniform),
        "NoDice" => Box::new(NoDice),
        _ => { return None; }
    })
}

struct GG {
    pub game: Game<std::string::String>,
}


// If you see this, you should stop your inital instinct to puke.
//
// Luminance - the graphics API underneth - is helpfull and well written,
// it doesn't allow this, since GL-contexts cannot be passed between threads.
// It makes sense.
//
// So this is me promising that I won't pass it between threads.
// -- Ed
unsafe impl Send for GG {}
unsafe impl Sync for GG {}

lazy_static::lazy_static! {
    static ref GAME: Arc<Mutex<GG>> = new_game();
}

std::thread_local! {
    static PARTICLES: Mutex<Vec<lingon::renderer::ParticleSystem>> = Mutex::new(Vec::new());
}

fn new_game() -> Arc<Mutex<GG>> {
    // TODO(ed): Maybe make these settable from the game itself.
    Arc::new(Mutex::new(GG { game: Game::new("Ultimate Fishbee - Game of the Year Edition ", 900, 900) }))
}

macro_rules! game {
    () => {
        &mut GAME.lock().unwrap().game
    };
}

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_update
    "Updates the engine. Needs to be called once per frame"
    [] -> Type::Void => {
        // TODO(ed): Unused for now
        game!().update(0.0);
        Ok(Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_render
    "Draws all render calls to the screen. Needs to be called once per frame"
    [] -> Type::Void => {
        game!().draw().unwrap();
        Ok(Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_window_size
    "Returns the size of the game window"
    [] -> Type::Tuple(vec![Type::Int, Type::Int]) => {
        let (x, y) = game!().window_size();
        Ok(Value::Tuple(Rc::new(vec![Value::Int(x as i64), Value::Int(y as i64)])))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_set_window_size
    "Sets the dimension of the game window"
    [Two(Int(x), Int(y))] -> Type::Void => {
        game!().set_window_size(*x as u32, *y as u32).unwrap();
        Ok(Value::Nil)
    },
);

fn l_gfx_rect_internal(x: &f64, y: &f64, w: &f64, h: &f64, rot: &f64, r: &f64, g: &f64, b: &f64, a: &f64) {
    let mut rect = Rect::new();
    rect.at(*x as f32, *y as f32);
    rect.scale(*w as f32, *h as f32);
    rect.angle(*rot as f32);
    rect.rgba(*r as f32, *g as f32, *b as f32, *a as f32);

    game!().renderer.push(rect);
}

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_rect
    "Draws a rectangle on the screen, in many different ways"
    [One(Float(x)), One(Float(y)), One(Float(w)), One(Float(h))]
    -> Type::Void => {
        // x, y, w, h
        l_gfx_rect_internal(x, y, w, h, &0.0, &1.0, &1.0, &1.0, &1.0);
        Ok(Nil)
    },
    [Two(Float(x), Float(y)), Two(Float(w), Float(h))]
    -> Type::Void => {
        // (x, y), (w, h)
        l_gfx_rect_internal(x, y, w, h, &0.0, &1.0, &1.0, &1.0, &1.0);
        Ok(Nil)
    },
    [One(Float(x)), One(Float(y)), One(Float(w)), One(Float(h)), Three(Float(r), Float(g), Float(b))]
    -> Type::Void => {
        // x, y, w, h, (r, g, b)
        l_gfx_rect_internal(x, y, w, h, &0.0, r, g, b, &1.0);
        Ok(Nil)
    },
    [Two(Float(x), Float(y)), Two(Float(w), Float(h)), Three(Float(r), Float(g), Float(b))]
    -> Type::Void => {
        // (x, y), (w, h), (r, g, b)
        l_gfx_rect_internal(x, y, w, h, &0.0, r, g, b, &1.0);
        Ok(Nil)
    },
    [One(Float(x)), One(Float(y)), One(Float(w)), One(Float(h)), Four(Float(r), Float(g), Float(b), Float(a))]
    -> Type::Void => {
        // x, y, w, h, (r, g, b, a)
        l_gfx_rect_internal(x, y, w, h, &0.0, r, g, b, a);
        Ok(Nil)
    },
    [Two(Float(x), Float(y)), Two(Float(w), Float(h)), Four(Float(r), Float(g), Float(b), Float(a))]
    -> Type::Void => {
        // (x, y), (w, h), (r, g, b, a)
        l_gfx_rect_internal(x, y, w, h, &0.0, r, g, b, a);
        Ok(Nil)
    },

    [One(Float(x)), One(Float(y)), One(Float(w)), One(Float(h)), One(Float(rot))]
    -> Type::Void => {
        // x, y, w, h
        l_gfx_rect_internal(x, y, w, h, rot, &1.0, &1.0, &1.0, &1.0);
        Ok(Nil)
    },
    [Two(Float(x), Float(y)), Two(Float(w), Float(h)), One(Float(rot))]
    -> Type::Void => {
        // (x, y), (w, h)
        l_gfx_rect_internal(x, y, w, h, rot, &1.0, &1.0, &1.0, &1.0);
        Ok(Nil)
    },
    [One(Float(x)), One(Float(y)), One(Float(w)), One(Float(h)), One(Float(rot)), Three(Float(r), Float(g), Float(b))]
    -> Type::Void => {
        // x, y, w, h, (r, g, b)
        l_gfx_rect_internal(x, y, w, h, rot, r, g, b, &1.0);
        Ok(Nil)
    },
    [Two(Float(x), Float(y)), Two(Float(w), Float(h)), One(Float(rot)), Three(Float(r), Float(g), Float(b))]
    -> Type::Void => {
        // (x, y), (w, h), (r, g, b)
        l_gfx_rect_internal(x, y, w, h, rot, r, g, b, &1.0);
        Ok(Nil)
    },
    [One(Float(x)), One(Float(y)), One(Float(w)), One(Float(h)), One(Float(rot)), Four(Float(r), Float(g), Float(b), Float(a))]
    -> Type::Void => {
        // x, y, w, h, (r, g, b, a)
        l_gfx_rect_internal(x, y, w, h, rot, r, g, b, a);
        Ok(Nil)
    },
    [Two(Float(x), Float(y)), Two(Float(w), Float(h)), One(Float(rot)), Four(Float(r), Float(g), Float(b), Float(a))]
    -> Type::Void => {
        // (x, y), (w, h), (r, g, b, a)
        l_gfx_rect_internal(x, y, w, h, rot, r, g, b, a);
        Ok(Nil)
    },
);

fn l_gfx_sprite_internal(sprite: &i64, x: &f64, y: &f64, w: &f64, h: &f64, gx: &i64, gy: &i64, rot: &f64, r: &f64, g: &f64, b: &f64, a: &f64) -> Value {
    let sprite = game!().renderer.sprite_sheets[*sprite as usize].grid(*gx as usize, *gy as usize);
    let mut sprite = Sprite::new(sprite);
    sprite.at(*x as f32, *y as f32).scale(*w as f32, *h as f32);
    sprite.angle(*rot as f32);
    sprite.rgba(*r as f32, *g as f32, *b as f32, *a as f32);
    game!().renderer.push(sprite);
    Nil
}

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_sprite
    "Draws a sprite on the screen, in many different ways.
     Note that the first argument is a sprite id from <a href='#l_load_image'>l_load_image</a>"
    [Two(String(name), Int(sprite)), Two(Int(gx), Int(gy)), One(Float(x)), One(Float(y)), One(Float(w)), One(Float(h))] -> Type::Void => {
        // id, (gx, gy), (x), (y), (w), (h)
        if name.as_ref() != "image" {
            return error!("l_gfx_sprite", "Expected a sprite ID");
        }
        Ok(l_gfx_sprite_internal(sprite, x, y, w, h, gx, gy, &0.0, &1.0, &1.0, &1.0, &1.0))
    },
    [Two(String(name), Int(sprite)), Two(Int(gx), Int(gy)), Two(Float(x), Float(y)), Two(Float(w), Float(h))] -> Type::Void => {
        // id, (gx, gy), (x, y), (w, h)
        if name.as_ref() != "image" {
            return error!("l_gfx_sprite", "Expected a sprite ID");
        }
        Ok(l_gfx_sprite_internal(sprite, x, y, w, h, gx, gy, &0.0, &1.0, &1.0, &1.0, &1.0))
    },
    [Two(String(name), Int(sprite)), Two(Int(gx), Int(gy)), One(Float(x)), One(Float(y)), One(Float(w)), One(Float(h)), Three(Float(r), Float(g), Float(b))] -> Type::Void => {
        // id, (gx, gy), (x), (y), (w), (h), (r, g, b)
        if name.as_ref() != "image" {
            return error!("l_gfx_sprite", "Expected a sprite ID")
        }
        Ok(l_gfx_sprite_internal(sprite, x, y, w, h, gx, gy, &0.0, r, g, b, &1.0))
    },
    [Two(String(name), Int(sprite)), Two(Int(gx), Int(gy)), Two(Float(x), Float(y)), Two(Float(w), Float(h)), Three(Float(r), Float(g), Float(b))] -> Type::Void => {
        // id, (gx, gy), (x, y), (w), (h), (r, g, b)
        if name.as_ref() != "image" {
            return error!("l_gfx_sprite", "Expected a sprite ID")
        }
        Ok(l_gfx_sprite_internal(sprite, x, y, w, h, gx, gy, &0.0, r, g, b, &1.0))
    },
    [Two(String(name), Int(sprite)), Two(Int(gx), Int(gy)), One(Float(x)), One(Float(y)), One(Float(w)), One(Float(h)), Four(Float(r), Float(g), Float(b), Float(a))] -> Type::Void => {
        // id, (gx, gy), (x), (y), (w), (h), (r, g, b, a)
        if name.as_ref() != "image" {
            return error!("l_gfx_sprite", "Expected a sprite ID")
        }
        Ok(l_gfx_sprite_internal(sprite, x, y, w, h, gx, gy, &0.0, r, g, b, a))
    },
    [Two(String(name), Int(sprite)), Two(Int(gx), Int(gy)), Two(Float(x), Float(y)), Two(Float(w), Float(h)), Four(Float(r), Float(g), Float(b), Float(a))] -> Type::Void => {
        // id, (gx, gy), (x, y), (w), (h), (r, g, b, a)
        if name.as_ref() != "image" {
            return error!("l_gfx_sprite", "Expected a sprite ID")
        }
        Ok(l_gfx_sprite_internal(sprite, x, y, w, h, gx, gy, &0.0, r, g, b, a))
    },
    [Two(String(name), Int(sprite)), Two(Int(gx), Int(gy)), One(Float(x)), One(Float(y)), One(Float(w)), One(Float(h)), One(Float(rot))] -> Type::Void => {
        // id, (gx, gy), (x), (y), (w), (h)
        if name.as_ref() != "image" {
            return error!("l_gfx_sprite", "Expected a sprite ID");
        }
        Ok(l_gfx_sprite_internal(sprite, x, y, w, h, gx, gy, rot, &1.0, &1.0, &1.0, &1.0))
    },
    [Two(String(name), Int(sprite)), Two(Int(gx), Int(gy)), Two(Float(x), Float(y)), Two(Float(w), Float(h)), One(Float(rot))] -> Type::Void => {
        // id, (gx, gy), (x, y), (w, h)
        if name.as_ref() != "image" {
            return error!("l_gfx_sprite", "Expected a sprite ID");
        }
        Ok(l_gfx_sprite_internal(sprite, x, y, w, h, gx, gy, rot, &1.0, &1.0, &1.0, &1.0))
    },
    [Two(String(name), Int(sprite)), Two(Int(gx), Int(gy)), One(Float(x)), One(Float(y)), One(Float(w)), One(Float(h)), One(Float(rot)), Three(Float(r), Float(g), Float(b))] -> Type::Void => {
        // id, (gx, gy), (x), (y), (w), (h), (r, g, b)
        if name.as_ref() != "image" {
            return error!("l_gfx_sprite", "Expected a sprite ID")
        }
        Ok(l_gfx_sprite_internal(sprite, x, y, w, h, gx, gy, rot, r, g, b, &1.0))
    },
    [Two(String(name), Int(sprite)), Two(Int(gx), Int(gy)), Two(Float(x), Float(y)), Two(Float(w), Float(h)), One(Float(rot)), Three(Float(r), Float(g), Float(b))] -> Type::Void => {
        // id, (gx, gy), (x, y), (w), (h), (r, g, b)
        if name.as_ref() != "image" {
            return error!("l_gfx_sprite", "Expected a sprite ID")
        }
        Ok(l_gfx_sprite_internal(sprite, x, y, w, h, gx, gy, rot, r, g, b, &1.0))
    },
    [Two(String(name), Int(sprite)), Two(Int(gx), Int(gy)), One(Float(x)), One(Float(y)), One(Float(w)), One(Float(h)), One(Float(rot)), Four(Float(r), Float(g), Float(b), Float(a))] -> Type::Void => {
        // id, (gx, gy), (x), (y), (w), (h), (r, g, b, a)
        if name.as_ref() != "image" {
            return error!("l_gfx_sprite", "Expected a sprite ID")
        }
        Ok(l_gfx_sprite_internal(sprite, x, y, w, h, gx, gy, rot, r, g, b, a))
    },
    [Two(String(name), Int(sprite)), Two(Int(gx), Int(gy)), Two(Float(x), Float(y)), Two(Float(w), Float(h)), One(Float(rot)), Four(Float(r), Float(g), Float(b), Float(a))] -> Type::Void => {
        // id, (gx, gy), (x, y), (w), (h), (r, g, b, a)
        if name.as_ref() != "image" {
            return error!("l_gfx_sprite", "Expected a sprite ID")
        }
        Ok(l_gfx_sprite_internal(sprite, x, y, w, h, gx, gy, rot, r, g, b, a))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_camera_at
    "Gives out the position of the camera"
    [] -> Type::Tuple(vec![Type::Float, Type::Float]) => {
        let game = &mut game!().renderer.camera;
        let x = *game.x_mut();
        let y = *game.y_mut();
        Ok(Tuple(Rc::new(vec![Float(x as f64), Float(y as f64)])))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_camera_place
    "Positions the camera at a specific point in space"
    [Two(Float(x), Float(y))] -> Type::Void => {
        game!().renderer.camera.at(*x as f32, *y as f32);
        Ok(Nil)
    },
    [One(Float(x)), One(Float(y))] -> Type::Void => {
        game!().renderer.camera.at(*x as f32, *y as f32);
        Ok(Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_camera_angle
    "Sets the angle of the camera - in absolute terms"
    [One(Float(angle))] -> Type::Void => {
        game!().renderer.camera.angle(*angle as f32);
        Ok(Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_camera_rotate
    "Rotates the camera - relative to the current rotation"
    [One(Float(by))] -> Type::Void => {
        game!().renderer.camera.rotate(*by as f32);
        Ok(Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_camera_set_zoom
    "Specifies the zoom level"
    [One(Float(to))] -> Type::Void => {
        game!().renderer.camera.scale(*to as f32, *to as f32);
        Ok(Nil)
    },
    [One(Float(sx)), One(Float(sy))] -> Type::Void => {
        game!().renderer.camera.scale(*sx as f32, *sy as f32);
        Ok(Nil)
    },
    [Two(Float(sx), Float(sy))] -> Type::Void => {
        game!().renderer.camera.scale(*sx as f32, *sy as f32);
        Ok(Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_camera_zoom_by
    "Zoomes relative to the current zoom level"
    [One(Float(to))] -> Type::Void => {
        game!().renderer.camera.scale_by(*to as f32, *to as f32);
        Ok(Nil)
    },
    [One(Float(sx)), One(Float(sy))] -> Type::Void => {
        game!().renderer.camera.scale_by(*sx as f32, *sy as f32);
        Ok(Nil)
    },
    [Two(Float(sx), Float(sy))] -> Type::Void => {
        game!().renderer.camera.scale_by(*sx as f32, *sy as f32);
        Ok(Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_particle_new
    "Creates a new particle system. Note specially the return type. Don't edit the return value."
    [] -> Type::Tuple(vec![Type::String, Type::Int]) => {
        let slot = PARTICLES.with(|ps| {
            let mut ps = ps.lock().unwrap();
            let slot = ps.len();
            ps.push(lingon::renderer::ParticleSystem::new());
            slot
        });
        Ok(Tuple(Rc::new(vec![sylt_str("particle"), Int(slot as i64)])))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_particle_spawn
    "Spawn a new particle for the given particle system"
    [Two(String(name), Int(system))] -> Type::Void => {
        if name.as_ref() != "particle" {
            return error!("l_gfx_particle_spawn", "Expected a particle system ID");
        }
        PARTICLES.with(|ps| {
            ps.lock().unwrap()[*system as usize].spawn();
        });
        Ok(Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_particle_update
    "Updates the particle system, stepping it forward in time"
    [Two(String(name), Int(system)), One(Float(delta))] -> Type::Void => {
        if name.as_ref() != "particle" {
            return error!("l_gfx_particle_spawn", "Expected a particle system ID");
        }
        PARTICLES.with(|ps| {
            ps.lock().unwrap()[*system as usize].update(*delta as f32);
        });
        Ok(Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_particle_render
    "Renders the particle system, has to be called each frame"
    [Two(String(name), Int(system))] -> Type::Void => {
        if name.as_ref() != "particle" {
            return error!("l_gfx_particle_spawn", "Expected a particle system ID");
        }
        PARTICLES.with(|ps| {
            game!().renderer.push_particle_system(&ps.lock().unwrap()[*system as usize]);
        });
        Ok(Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_particle_add_sprite
    "Adds a sprite to the particle system as an alternative when spawning. If nothing is added it's colored rectangles all the way"
    [Two(String(s_name), Int(system)), Two(String(sp_name), Int(sprite)), Two(Int(gx), Int(gy))] -> Type::Void => {
        if s_name.as_ref() != "particle" {
            return error!("l_gfx_particle_spawn", "Expected a particle system ID");
        }
        if sp_name.as_ref() != "image" {
            return error!("l_gfx_sprite", "Expected a sprite ID");
        }

        let sprite = game!().renderer.sprite_sheets[*sprite as usize].grid(*gx as usize, *gy as usize);
        PARTICLES.with(|ps| {
            ps.lock().unwrap()[*system as usize].sprites.push(sprite);
        });
        Ok(Nil)
    },
);

macro_rules! particle_prop {
    { $name:ident, $prop:ident } => {
        sylt_macro::extern_function!(
            "sylt::lingon_sylt"
            $name
            "Sets the given particle prop"
            [Two(String(name), Int(system)), Two(Float(lo), Float(hi))] -> Type::Void => {
                if name.as_ref() != "particle" {
                    return error!("l_gfx_particle_spawn", "Expected a particle system ID");
                }
                let prop = lingon::random::RandomProperty::new(*lo as f32, *hi as f32, Box::new(Uniform));
                PARTICLES.with(|ps| {
                    ps.lock().unwrap()[*system as usize].$prop = prop;
                });
                Ok(Nil)
            },
            [Two(String(name), Int(system)), Two(Float(lo), Float(hi)), One(String(dist))] -> Type::Void => {
                if name.as_ref() != "particle" {
                    return error!("l_gfx_particle_spawn", "Expected a particle system ID");
                }
                if let Some(dist) = parse_dist(dist) {
                    let prop = lingon::random::RandomProperty::new(*lo as f32, *hi as f32, dist);
                    PARTICLES.with(|ps| {
                        ps.lock().unwrap()[*system as usize].$prop = prop;
                    });
                    Ok(Nil)
                } else {
                    error!(stringify!($name), "Failed to parse distribution '{}'", dist)
                }
            },
        );
    };
}

particle_prop! { l_gfx_particle_x, x }
particle_prop! { l_gfx_particle_y, y }

particle_prop! { l_gfx_particle_lifetime, lifetime }

particle_prop! { l_gfx_particle_vel_angle, vel_angle }
particle_prop! { l_gfx_particle_vel_magnitude, vel_magnitude }

particle_prop! { l_gfx_particle_acc_angle, acc_angle }
particle_prop! { l_gfx_particle_acc_magnitude, acc_magnitude }
particle_prop! { l_gfx_particle_drag, drag }

particle_prop! { l_gfx_particle_angle, angle }
particle_prop! { l_gfx_particle_angle_velocity, angle_velocity }
particle_prop! { l_gfx_particle_angle_drag, angle_drag }

particle_prop! { l_gfx_particle_start_sx, start_sx }
particle_prop! { l_gfx_particle_start_sy, start_sy }
particle_prop! { l_gfx_particle_end_sx, end_sx }
particle_prop! { l_gfx_particle_end_sy, end_sy }

particle_prop! { l_gfx_particle_start_red, start_red }
particle_prop! { l_gfx_particle_start_green, start_green }
particle_prop! { l_gfx_particle_start_blue, start_blue }
particle_prop! { l_gfx_particle_start_alpha, start_alpha }

particle_prop! { l_gfx_particle_end_red, end_red }
particle_prop! { l_gfx_particle_end_green, end_green }
particle_prop! { l_gfx_particle_end_blue, end_blue }
particle_prop! { l_gfx_particle_end_alpha, end_alpha }

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_particle_start_color
    "Sets the spawn color of the particles"
    [Two(String(name), Int(system)), Three(Float(r), Float(g), Float(b))] -> Type::Void => {
        if name.as_ref() != "particle" {
            return error!("l_gfx_particle_spawn", "Expected a particle system ID");
        }
        let r = lingon::random::RandomProperty::new(*r as f32, *r as f32, Box::new(NoDice));
        let g = lingon::random::RandomProperty::new(*g as f32, *g as f32, Box::new(NoDice));
        let b = lingon::random::RandomProperty::new(*b as f32, *b as f32, Box::new(NoDice));
        PARTICLES.with(|ps| {
            let mut ps = ps.lock().unwrap();
            ps[*system as usize].start_red = r;
            ps[*system as usize].start_green = g;
            ps[*system as usize].start_blue = b;
        });
        Ok(Nil)
    },
    [Two(String(name), Int(system)), Four(Float(r), Float(g), Float(b), Float(a))] -> Type::Void => {
        if name.as_ref() != "particle" {
            return error!("l_gfx_particle_spawn", "Expected a particle system ID");
        }
        let r = lingon::random::RandomProperty::new(*r as f32, *r as f32, Box::new(NoDice));
        let g = lingon::random::RandomProperty::new(*g as f32, *g as f32, Box::new(NoDice));
        let b = lingon::random::RandomProperty::new(*b as f32, *b as f32, Box::new(NoDice));
        let a = lingon::random::RandomProperty::new(*a as f32, *a as f32, Box::new(NoDice));
        PARTICLES.with(|ps| {
            let mut ps = ps.lock().unwrap();
            ps[*system as usize].start_red = r;
            ps[*system as usize].start_green = g;
            ps[*system as usize].start_blue = b;
            ps[*system as usize].start_alpha = a;
        });
        Ok(Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_particle_end_color
    "Sets the spawn color of the particles"
    [Two(String(name), Int(system)), Three(Float(r), Float(g), Float(b))] -> Type::Void => {
        if name.as_ref() != "particle" {
            return error!("l_gfx_particle_spawn", "Expected a particle system ID");
        }
        let r = lingon::random::RandomProperty::new(*r as f32, *r as f32, Box::new(NoDice));
        let g = lingon::random::RandomProperty::new(*g as f32, *g as f32, Box::new(NoDice));
        let b = lingon::random::RandomProperty::new(*b as f32, *b as f32, Box::new(NoDice));
        PARTICLES.with(|ps| {
            let mut ps = ps.lock().unwrap();
            ps[*system as usize].end_red = r;
            ps[*system as usize].end_green = g;
            ps[*system as usize].end_blue = b;
        });
        Ok(Nil)
    },
    [Two(String(name), Int(system)), Four(Float(r), Float(g), Float(b), Float(a))] -> Type::Void => {
        if name.as_ref() != "particle" {
            return error!("l_gfx_particle_spawn", "Expected a particle system ID");
        }
        let r = lingon::random::RandomProperty::new(*r as f32, *r as f32, Box::new(NoDice));
        let g = lingon::random::RandomProperty::new(*g as f32, *g as f32, Box::new(NoDice));
        let b = lingon::random::RandomProperty::new(*b as f32, *b as f32, Box::new(NoDice));
        let a = lingon::random::RandomProperty::new(*a as f32, *a as f32, Box::new(NoDice));
        PARTICLES.with(|ps| {
            let mut ps = ps.lock().unwrap();
            ps[*system as usize].end_red = r;
            ps[*system as usize].end_green = g;
            ps[*system as usize].end_blue = b;
            ps[*system as usize].end_alpha = a;
        });
        Ok(Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_delta
    "The time since last the frame in seconds"
    [] -> Type::Float => {
        let delta = game!().time_tick() as f64;
        Ok(Float(delta))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_time
    "An absolute time messurement, but the start time is ill defined"
    [] -> Type::Float => {
        let time = game!().total_time() as f64;
        Ok(Float(time))
    },
);


sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_random
    "Returns a uniformly sampled random float between 0 and 1"
    [] -> Type::Float => {
        Ok(Float(Uniform.sample().into()))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_random_range
    "Returns a randomized integer in the given range"
    [One(Int(lo)), One(Int(hi))] -> Type::Int => {
        Ok(Int(*lo + (Uniform.sample() * ((hi - lo + 1) as f32)) as i64))
    },
    [Two(Int(lo), Int(hi))] -> Type::Int => {
        Ok(Int(*lo + (Uniform.sample() * ((hi - lo + 1) as f32)) as i64))
    },
    [One(Float(lo)), One(Float(hi))] -> Type::Float => {
        Ok(Float(*lo + Uniform.sample() as f64 * (hi - lo)))
    },
    [Two(Float(lo), Float(hi))] -> Type::Float => {
        Ok(Float(*lo + Uniform.sample() as f64 * (hi - lo)))
    },
);


sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_bind_key
    "Binds a keyboard key to an input name"
    [One(String(key)), One(String(name))] -> Type::Void => {
        let key = if let Some(key) = Keycode::from_name(key) {
            key
        } else {
            return error!("l_bind_key", "'{}' is an invalid key", key);
        };

        use lingon::input::{Device::Key, Keycode};
        game!().input.bind(Key(key), std::string::String::clone(name));

        Ok(Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_bind_quit
    "Binds the windows quit action (pressing the X in the corner) - plus points if you make it jump"
    [One(String(name))] -> Type::Void => {
        use lingon::input::Device::Quit;
        game!().input.bind(Quit, std::string::String::clone(name));
        Ok(Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_bind_button
    "Binds a controller button to an input name"
    [One(Int(controller)), One(String(button)), One(String(name))] -> Type::Void => {
        use lingon::input::{Device, Button};
        let button = if let Some(button) = Button::from_string(button) {
            button
        } else {
            return error!("l_bind_button", "'{}' is an invalid button", button);
        };

        game!().input.bind(Device::Button(*controller as u32, button), std::string::String::clone(name));
        Ok(Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_bind_axis
    "Binds a controller axis to an input name"
    [One(Int(controller)), One(String(axis)), One(String(name))] -> Type::Void => {
        use lingon::input::{Device, Axis};
        let axis = if let Some(axis) = Axis::from_string(axis) {
            axis
        } else {
            return error!("l_bind_axis", "'{}' is an invalid axis", axis);
        };

        game!().input.bind(Device::Axis(*controller as u32, axis), std::string::String::clone(name));
        Ok(Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_bind_mouse
    "Binds a mouse button, allows the following keys: ['left', 'middle', 'right', 'x1', 'x2']"
    [One(String(button)), One(String(name))] -> Type::Void => {
        use lingon::input::{Device::Mouse, MouseButton::*};
        let button = match button.as_str() {
            "left" => Left,
            "middle" => Middle,
            "right" => Right,
            "x1" => X1,
            "x2" => X2,
            _ => { return error!("l_bind_mouse", "'{}' is an invalid mouse button", button); }
        };

        game!().input.bind(Mouse(button), std::string::String::clone(name));
        Ok(Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_input_down
    "Returns true if the input name is down this frame, e.g. pressed"
    [One(String(name))] -> Type::Bool => {
        Ok(Bool(game!().input.down(std::string::String::clone(name))))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_input_up
    "Returns true if the input name is up this frame, e.g. not pressed"
    [One(String(name))] -> Type::Bool => {
        Ok(Bool(game!().input.up(std::string::String::clone(name))))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_input_pressed
    "Returns true if the input name started being down this frame, e.g. a tap"
    [One(String(name))] -> Type::Bool => {
        Ok(Bool(game!().input.pressed(std::string::String::clone(name))))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_input_released
    "Returns true if the input name started being up this frame, e.g. a release"
    [One(String(name))] -> Type::Bool => {
        Ok(Bool(game!().input.released(std::string::String::clone(name))))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_input_value
    "Returns the float representation of the input name, usefull for reading controller inputs"
    [One(String(name))] -> Type::Float => {
        Ok(Float(game!().input.value(std::string::String::clone(name)) as f64))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_audio_play
    "Plays an audio source. Expects the first value to be a
     return value from <a href='#l_load_sound'>l_load_sound</a>"
    [Two(String(name), Int(sound)),
     One(Bool(looping)),
     One(Float(gain)),
     One(Float(pitch)),
    ] -> Type::Void => {
        if name.as_ref() != "audio" {
            return error!("l_audio_play", "");
        }

        let game = game!();
        let sound = &game.assets[unsafe { lingon::asset::AudioAssetID::from_usize(*sound as usize) }];
        let source = lingon::audio::AudioSource::new(sound)
            .looping(*looping)
            .gain(*gain as f32)
            .pitch(*pitch as f32);
        game.audio.lock().play(source);

        Ok(Nil)
    },
    [Two(String(name), Int(sound)),
     One(Bool(looping)),
     Two(Float(gain), Float(gain_variance)),
     Two(Float(pitch), Float(pitch_variance)),
    ] -> Type::Void => {
        if name.as_ref() != "audio" {
            return error!("l_audio_play", "");
        }

        let game = game!();
        let sound = &game.assets[unsafe { lingon::asset::AudioAssetID::from_usize(*sound as usize) }];
        let source = lingon::audio::AudioSource::new(sound)
            .looping(*looping)
            .gain(*gain as f32).gain_variance(*gain_variance as f32)
            .pitch(*pitch as f32).pitch_variance(*pitch_variance as f32);
        game.audio.lock().play(source);

        Ok(Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_audio_master_gain
    "Controls the master gain of the audio mixer"
    [One(Float(gain))] -> Type::Void => {
        *game!().audio.lock().gain_mut() = *gain as f32;
        Ok(Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_mouse
    "Gets the current mouse position"
    [] -> Type::Tuple(vec!(Type::Int, Type::Int)) => {
        let mouse = game!().input.mouse();
        Ok(Tuple(Rc::new(vec!(Int(mouse.0 as i64), Int(mouse.1 as i64)))))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_mouse_rel
    "Gets the relative mouse position since the last frame"
    [] -> Type::Tuple(vec!(Type::Int, Type::Int)) => {
        let mouse = game!().input.mouse_rel();
        Ok(Tuple(Rc::new(vec!(Int(mouse.0 as i64), Int(mouse.1 as i64)))))
    },
);

pub fn sylt_str(s: &str) -> Value {
    String(Rc::new(s.to_string()))
}

#[sylt_macro::sylt_doc(l_load_image, "Loads an image and turns it into a sprite sheet",
  [One(String(path))] Type::Tuple)]
#[sylt_macro::sylt_link(l_load_image, "sylt::lingon_sylt")]
pub fn l_load_image(values: &[Value], typecheck: bool) -> Result<Value, RuntimeError> {
    match (values, typecheck) {
        ([String(path), tilesize], false) => {
            let game = game!();
            let path = PathBuf::from(path.as_ref());
            let image = game.assets.load_image(path);
            let image = &game.assets[image];

            let dim = unpack_int_int_tuple(tilesize);
            let slot = game.renderer.add_sprite_sheet(image.clone(), (dim.0 as usize, dim.1 as usize));

            Ok(Tuple(Rc::new(vec![sylt_str("image"), Int(slot as i64)])))
        }
        ([String(_), tilesize], true) => {
            unpack_int_int_tuple(tilesize);
            Ok(Tuple(Rc::new(vec![sylt_str("image"), Int(0)])))
        }
        (values, _) => Err(RuntimeError::ExternTypeMismatch(
            "l_load_image".to_string(),
            values.iter().map(Type::from).collect(),
        )),
    }
}

#[sylt_macro::sylt_doc(l_load_image,
  "Loads a sound and lets you play it using <a href='l_audio_play'>l_audio_play</a>",
  [One(String(path))] Type::Tuple)]
#[sylt_macro::sylt_link(l_load_audio, "sylt::lingon_sylt")]
pub fn l_load_audio(values: &[Value], typecheck: bool) -> Result<Value, RuntimeError> {
    match (values, typecheck) {
        ([String(path)], false) => {
            let game = game!();
            let path = PathBuf::from(path.as_ref());
            let audio = game.assets.load_audio(path);
            Ok(Tuple(Rc::new(vec![sylt_str("audio"), Int(*audio as i64)])))
        }
        ([String(_)], true) => {
            Ok(Tuple(Rc::new(vec![sylt_str("audio"), Int(0)])))
        }
        (values, _) => Err(RuntimeError::ExternTypeMismatch(
            "l_load_image".to_string(),
            values.iter().map(Type::from).collect(),
        )),
    }
}

sylt_macro::sylt_link_gen!("sylt::lingon_sylt");
