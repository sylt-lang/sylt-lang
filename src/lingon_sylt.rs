use lingon::{Game, random::{Uniform, Distribute}};
use lingon::renderer::{Rect, Sprite, Transform, Tint};
use std::sync::{Arc, Mutex};
use crate::{*, error::RuntimeError};
use crate as sylt;

// Errors are important, they should be easy to write!
macro_rules! error {
    ( $name:expr, $( $fmt:expr ),* ) => {
        Err(RuntimeError::ExternError($name.to_string(), format!( $( $fmt ),* )))
    }
}

fn unpack_int_int_tuple(value: &Value) -> (i64, i64) {
    if let Value::Tuple(tuple) = value {
        if let (Some(Value::Int(w)), Some(Value::Int(h))) = (tuple.get(0), tuple.get(1)) {
            return (*w, *h);
        }
    };
    unreachable!("Expected tuple (int, int) but got '{:?}'", value);
}

fn unpack_float_float_tuple(value: &Value) -> (f64, f64) {
    if let Value::Tuple(tuple) = value {
        if let (Some(Value::Float(w)), Some(Value::Float(h))) = (tuple.get(0), tuple.get(1)) {
            return (*w, *h);
        }
    };
    unreachable!("Expected tuple (float, float) but got '{:?}'", value);
}

fn parse_dist(name: &String) -> Option<Box<dyn lingon::random::Distribute>> {
    use lingon::random::*;

    Some(match name.as_str() {
        "Square" => Box::new(Square),
        "ThreeDice" => Box::new(ThreeDice),
        "TwoDice" => Box::new(TwoDice),
        "Uniform" => Box::new(Uniform),
        "NoDice" => Box::new(NoDice),
        _ => { return None; }
    })
}

fn unpack_and_tint<T: Tint>(target: &mut T, tint: &Value) {
    if let Value::Tuple(tuple) = tint {
        match (tuple.get(0), tuple.get(1), tuple.get(2), tuple.get(3)) {
            (Some(Value::Float(r)), Some(Value::Float(g)), Some(Value::Float(b)), Some(Value::Float(a))) => {
                target.rgba(*r as f32, *g as f32, *b as f32, *a as f32);
                return;
            }

            (Some(Value::Float(r)), Some(Value::Float(g)), Some(Value::Float(b)), ..) => {
                target.rgb(*r as f32, *g as f32, *b as f32);
                return;
            }

            (Some(Value::Float(v)), ..) => {
                target.rgb(*v as f32, *v as f32, *v as f32);
                return;
            }

            _ => {}
        }
    }
    unreachable!("Expected tint tuple but got '{:?}'", tint);
}

// TODO(ed): These should accept an Rc<Vec<_>>.
fn unpack_sprite_id(sprite: &Value) -> usize {
    if let Value::Tuple(tuple) = sprite {
        match (tuple.get(0), tuple.get(1)) {
            (Some(Value::String(kind)), Some(Value::Int(id))) if kind.as_str() == "image" => {
                return *id as usize;
            }
            _ => {}
        }
    }
    unreachable!("Expected sprite id tuple but got '{:?}'", sprite);
}

fn unpack_audio_id(sprite: &Value) -> usize {
    if let Value::Tuple(tuple) = sprite {
        match (tuple.get(0), tuple.get(1)) {
            (Some(Value::String(kind)), Some(Value::Int(id))) if kind.as_str() == "audio" => {
                return *id as usize;
            }
            _ => {}
        }
    }
    unreachable!("Expected sprite id tuple but got '{:?}'", sprite);
}

fn unpack_particle_id(particle: &Value) -> usize {
    if let Value::Tuple(tuple) = particle {
        match (tuple.get(0), tuple.get(1)) {
            (Some(Value::String(kind)), Some(Value::Int(id))) if kind.as_str() == "particle" => {
                return *id as usize;
            }
            _ => {}
        }
    }
    unreachable!("Expected particle id tuple but got '{:?}'", particle);
}

struct GG {
    pub game: Game<String>,
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
    Arc::new(Mutex::new(GG { game: Game::new("Lingon - Sylt", 500, 500) }))
}

macro_rules! game {
    () => {
        &mut GAME.lock().unwrap().game
    };
}

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_update
    [] -> Type::Void => {
        // TODO(ed): Unused for now
        game!().update(0.0);
        Ok(Value::Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_render
    [] -> Type::Void => {
        game!().draw().unwrap();
        Ok(Value::Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_rect
    [Value::Float(x), Value::Float(y), Value::Float(w), Value::Float(h)] -> Type::Void => {
        game!().renderer.push(Rect::new().at(*x as f32, *y as f32).scale(*w as f32, *h as f32));
        Ok(Value::Nil)
    },
    [Value::Float(x), Value::Float(y), Value::Float(w), Value::Float(h), Value::Tuple(tint)] -> Type::Void => {
        let mut rect = Rect::new();
        unpack_and_tint(&mut rect, &Value::Tuple(tint.clone()));
        rect.at(*x as f32, *y as f32);
        rect.scale(*w as f32, *h as f32);

       game!().renderer.push(rect);
        Ok(Value::Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_sprite
    [Value::Tuple(sprite), Value::Tuple(grid),
     Value::Float(x), Value::Float(y),
     Value::Float(w), Value::Float(h)] -> Type::Void => {
        let grid = unpack_int_int_tuple(&Value::Tuple(grid.clone()));
        let sprite = unpack_sprite_id(&Value::Tuple(sprite.clone()));
        let sprite = game!().renderer.sprite_sheets[sprite].grid(grid.0 as usize, grid.1 as usize);
        let mut sprite = Sprite::new(sprite);

        sprite.at(*x as f32, *y as f32).scale(*w as f32, *h as f32);
        game!().renderer.push(sprite);
         Ok(Value::Nil)
    },
    [Value::Tuple(sprite), Value::Tuple(grid),
     Value::Float(x), Value::Float(y),
     Value::Float(w), Value::Float(h),
     Value::Tuple(tint)] -> Type::Void => {
        let grid = unpack_int_int_tuple(&Value::Tuple(grid.clone()));
        let sprite = unpack_sprite_id(&Value::Tuple(sprite.clone()));
        let sprite = game!().renderer.sprite_sheets[sprite].grid(grid.0 as usize, grid.1 as usize);
        let mut sprite = Sprite::new(sprite);

        unpack_and_tint(&mut sprite, &Value::Tuple(tint.clone()));
        sprite.at(*x as f32, *y as f32).scale(*w as f32, *h as f32);
        game!().renderer.push(sprite);
         Ok(Value::Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_camera_at
    [] -> Type::Tuple(vec![Type::Float, Type::Float]) => {
        let game = &mut game!().renderer.camera;
        let x = *game.x_mut();
        let y = *game.y_mut();
        Ok(Value::Tuple(Rc::new(vec![Value::Float(x as f64), Value::Float(y as f64)])))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_camera_place
    [Value::Tuple(at)] -> Type::Void => {
        let at = unpack_float_float_tuple(&Value::Tuple(at.clone()));
        game!().renderer.camera.at(at.0 as f32, at.1 as f32);
        Ok(Value::Nil)
    },
    [Value::Float(x), Value::Float(y)] -> Type::Void => {
        game!().renderer.camera.at(*x as f32, *y as f32);
        Ok(Value::Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_camera_angle
    [Value::Float(angle)] -> Type::Void => {
        game!().renderer.camera.angle(*angle as f32);
        Ok(Value::Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_camera_rotate
    [Value::Float(by)] -> Type::Void => {
        game!().renderer.camera.rotate(*by as f32);
        Ok(Value::Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_camera_set_zoom
    [Value::Float(to)] -> Type::Void => {
        game!().renderer.camera.scale(*to as f32, *to as f32);
        Ok(Value::Nil)
    },
    [Value::Float(sx), Value::Float(sy)] -> Type::Void => {
        game!().renderer.camera.scale(*sx as f32, *sy as f32);
        Ok(Value::Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_camera_zoom_by
    [Value::Float(to)] -> Type::Void => {
        game!().renderer.camera.scale_by(*to as f32, *to as f32);
        Ok(Value::Nil)
    },
    [Value::Float(sx), Value::Float(sy)] -> Type::Void => {
        game!().renderer.camera.scale_by(*sx as f32, *sy as f32);
        Ok(Value::Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_particle_new
    [] -> Type::Tuple(vec![Type::String, Type::Int]) => {
        let slot = PARTICLES.with(|ps| {
            let mut ps = ps.lock().unwrap();
            let slot = ps.len();
            ps.push(lingon::renderer::ParticleSystem::new());
            slot
        });
        Ok(Value::Tuple(Rc::new(vec![sylt_str("particle"), Value::Int(slot as i64)])))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_particle_spawn
    [Value::Tuple(system)] -> Type::Void => {
        let system = unpack_particle_id(&Value::Tuple(Rc::clone(system)));
        PARTICLES.with(|ps| {
            ps.lock().unwrap()[system].spawn();
        });
        Ok(Value::Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_particle_update
    [Value::Tuple(system), Value::Float(delta)] -> Type::Void => {
        let system = unpack_particle_id(&Value::Tuple(Rc::clone(system)));
        PARTICLES.with(|ps| {
            ps.lock().unwrap()[system].update(*delta as f32);
        });
        Ok(Value::Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_particle_render
    [Value::Tuple(system)] -> Type::Void => {
        let system = unpack_particle_id(&Value::Tuple(Rc::clone(system)));
        PARTICLES.with(|ps| {
            game!().renderer.push_particle_system(&ps.lock().unwrap()[system]);
        });
        Ok(Value::Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_gfx_particle_add_sprite
    [Value::Tuple(system), Value::Tuple(sprite), Value::Tuple(grid)] -> Type::Void => {
        let system = unpack_particle_id(&Value::Tuple(Rc::clone(system)));
        let sprite = unpack_sprite_id(&Value::Tuple(Rc::clone(sprite)));
        let grid = unpack_int_int_tuple(&Value::Tuple(Rc::clone(grid)));
        PARTICLES.with(|ps| {
            let sprite = game!().renderer.sprite_sheets[sprite].grid(grid.0 as usize, grid.1 as usize);
            ps.lock().unwrap()[system].sprites.push(sprite);
        });
        Ok(Value::Nil)
    },
);

macro_rules! particle_prop {
    { $name:ident, $prop:ident } => {
        sylt_macro::extern_function!(
            "sylt::lingon_sylt"
            $name
            [Value::Tuple(system), Value::Tuple(range), Value::String(dist)] -> Type::Void => {
                let system = unpack_particle_id(&Value::Tuple(Rc::clone(system)));
                let range = unpack_float_float_tuple(&Value::Tuple(Rc::clone(range)));
                if let Some(dist) = parse_dist(dist) {
                    PARTICLES.with(|ps| {
                        let prop = lingon::random::RandomProperty::new(range.0 as f32, range.1 as f32, dist);
                        ps.lock().unwrap()[system].$prop = prop;
                    });
                    Ok(Value::Nil)
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
    l_delta
    [] -> Type::Float => {
        let delta = game!().time_tick() as f64;
        Ok(Value::Float(delta))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_time
    [] -> Type::Float => {
        let time = game!().total_time() as f64;
        Ok(Value::Float(time))
    },
);


sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_random
    [] -> Type::Float => {
        Ok(Value::Float(Uniform.sample().into()))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_random_range
    [Value::Int(lo), Value::Int(hi)] -> Type::Int => {
        Ok(Value::Int(*lo + (Uniform.sample() * ((hi - lo) as f32)) as i64))
    },
);


sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_bind_key
    [Value::String(key), Value::String(name)] -> Type::Void => {
        let key = if let Some(key) = Keycode::from_name(key) {
            key
        } else {
            return error!("l_bind_key", "'{}' is an invalid key", key);
        };

        use lingon::input::{Device::Key, Keycode};
        game!().input.bind(Key(key), String::clone(name));

        Ok(Value::Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_bind_quit
    [Value::String(name)] -> Type::Void => {
        use lingon::input::Device::Quit;
        game!().input.bind(Quit, String::clone(name));
        Ok(Value::Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_bind_button
    [Value::Int(controller), Value::String(button), Value::String(name)] -> Type::Void => {
        use lingon::input::{Device, Button};
        let button = if let Some(button) = Button::from_string(button) {
            button
        } else {
            return error!("l_bind_button", "'{}' is an invalid button", button);
        };

        game!().input.bind(Device::Button(*controller as u32, button), String::clone(name));
        Ok(Value::Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_bind_axis
    [Value::Int(controller), Value::String(axis), Value::String(name)] -> Type::Void => {
        use lingon::input::{Device, Axis};
        let axis = if let Some(axis) = Axis::from_string(axis) {
            axis
        } else {
            return error!("l_bind_axis", "'{}' is an invalid axis", axis);
        };

        game!().input.bind(Device::Axis(*controller as u32, axis), String::clone(name));
        Ok(Value::Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_bind_mouse
    [Value::String(button), Value::String(name)] -> Type::Void => {
        use lingon::input::{Device::Mouse, MouseButton::*};
        let button = match button.as_str() {
            "left" => Left,
            "middle" => Middle,
            "right" => Right,
            "x1" => X1,
            "x2" => X2,
            _ => { return error!("l_bind_mouse", "'{}' is an invalid mouse button", button); }
        };

        game!().input.bind(Mouse(button), String::clone(name));
        Ok(Value::Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_input_down
    [Value::String(name)] -> Type::Bool => {
        Ok(Value::Bool(game!().input.down(String::clone(name))))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_input_up
    [Value::String(name)] -> Type::Bool => {
        Ok(Value::Bool(game!().input.up(String::clone(name))))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_input_pressed
    [Value::String(name)] -> Type::Bool => {
        Ok(Value::Bool(game!().input.pressed(String::clone(name))))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_input_released
    [Value::String(name)] -> Type::Bool => {
        Ok(Value::Bool(game!().input.released(String::clone(name))))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_input_value
    [Value::String(name)] -> Type::Float => {
        Ok(Value::Float(game!().input.value(String::clone(name)) as f64))
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_audio_play
    [Value::Tuple(audio_source),
     Value::Bool(looping),
     Value::Float(gain), Value::Float(gain_variance),
     Value::Float(pitch), Value::Float(pitch_variance),
    ] -> Type::Void => {
        let game = game!();
        let sound = unpack_audio_id(&Value::Tuple(audio_source.clone()));
        // SAFETY: unpack_audio_id checks that audio_source was previously received as an audio id
        let sound = &game.assets[unsafe { lingon::asset::AudioAssetID::from_usize(sound) }];
        let source = lingon::audio::AudioSource::new(sound)
            .looping(*looping)
            .gain(*gain as f32).gain_variance(*gain_variance as f32)
            .pitch(*pitch as f32).pitch_variance(*pitch_variance as f32);
        game.audio.lock().play(source);

        Ok(Value::Nil)
    },
);

sylt_macro::extern_function!(
    "sylt::lingon_sylt"
    l_audio_master_gain
    [Value::Float(gain)] -> Type::Void => {
        *game!().audio.lock().gain_mut() = *gain as f32;
        Ok(Value::Nil)
    },
);


pub fn sylt_str(s: &str) -> Value {
    Value::String(Rc::new(s.to_string()))
}

#[sylt_macro::sylt_link(l_load_image, "sylt::lingon_sylt")]
pub fn l_load_image(values: &[Value], typecheck: bool) -> Result<Value, RuntimeError> {
    match (values, typecheck) {
        ([Value::String(path), tilesize], false) => {
            let game = game!();
            let path = PathBuf::from(path.as_ref());
            let image = game.assets.load_image(path);
            let image = &game.assets[image];

            let dim = unpack_int_int_tuple(tilesize);
            let slot = game.renderer.add_sprite_sheet(image.clone(), (dim.0 as usize, dim.1 as usize));

            Ok(Value::Tuple(Rc::new(vec![sylt_str("image"), Value::Int(slot as i64)])))
        }
        ([Value::String(_), tilesize], true) => {
            unpack_int_int_tuple(tilesize);
            Ok(Value::Tuple(Rc::new(vec![sylt_str("image"), Value::Int(0)])))
        }
        (values, _) => Err(RuntimeError::ExternTypeMismatch(
            "l_load_image".to_string(),
            values.iter().map(Type::from).collect(),
        )),
    }
}

#[sylt_macro::sylt_link(l_load_audio, "sylt::lingon_sylt")]
pub fn l_load_audio(values: &[Value], typecheck: bool) -> Result<Value, RuntimeError> {
    match (values, typecheck) {
        ([Value::String(path)], false) => {
            let game = game!();
            let path = PathBuf::from(path.as_ref());
            let audio = game.assets.load_audio(path);
            Ok(Value::Tuple(Rc::new(vec![sylt_str("audio"), Value::Int(*audio as i64)])))
        }
        ([Value::String(_)], true) => {
            Ok(Value::Tuple(Rc::new(vec![sylt_str("audio"), Value::Int(0)])))
        }
        (values, _) => Err(RuntimeError::ExternTypeMismatch(
            "l_load_image".to_string(),
            values.iter().map(Type::from).collect(),
        )),
    }
}

sylt_macro::sylt_link_gen!("sylt::lingon_sylt");
