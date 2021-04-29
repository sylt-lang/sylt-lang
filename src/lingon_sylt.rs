use lingon::{Game, random::{Uniform, Distribute}};
use lingon::renderer::{Rect, Transform, Tint};
use std::sync::{Arc, Mutex};
use crate::{*, error::RuntimeError};
use crate as sylt;

// TODO(ed): Make the trait only clone, not copy.
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
    [Value::Float(x), Value::Float(y), Value::Float(w), Value::Float(h), Value::Tuple(value)] -> Type::Void => {
        let mut rect = Rect::new();
        match value.as_slice() {
            [Value::Float(r), Value::Float(g), Value::Float(b)] =>
                rect.rgb(*r as f32, *g as f32, *b as f32),
            [Value::Float(r), Value::Float(g), Value::Float(b), Value::Float(a)] =>
                rect.rgba(*r as f32, *g as f32, *b as f32, *a as f32),
            values => {
                return Err(RuntimeError::ExternTypeMismatch(
                    "l_gfx_rect - color argument".to_string(),
                    values.iter().map(Type::from).collect(),
                ))
            },
        };
        rect.at(*x as f32, *y as f32);
        rect.scale(*w as f32, *h as f32);

       game!().renderer.push(rect);
        Ok(Value::Nil)
    },
);

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
    l_bind_key
    [Value::String(key), Value::String(name)] -> Type::Void => {
        let key = if let Some(key) = Keycode::from_name(key) {
            key
        } else {
            return Err(RuntimeError::ExternTypeMismatch(
                    format!("l_bind_key - invalid key: '{}'", key),
                    Vec::new(),
            ))
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
            return Err(RuntimeError::ExternTypeMismatch(
                    format!("l_bind_key - invalid button: '{}'", button),
                    Vec::new(),
            ))
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
            return Err(RuntimeError::ExternTypeMismatch(
                    format!("l_bind_key - invalid axis: '{}'", axis),
                    Vec::new(),
            ))
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
            x => return Err(RuntimeError::ExternTypeMismatch(
                    format!("l_bind_key - invalid mouse button: '{}'", x),
                    Vec::new(),
            ))
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

sylt_macro::sylt_link_gen!("sylt::lingon_sylt");
