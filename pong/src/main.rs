use macroquad::{Camera2D, DARKPURPLE, KeyCode, SKYBLUE, clear_background, draw_rectangle, get_frame_time, is_key_down, next_frame, set_camera, vec2};
use std::path::Path;
use tihdy::{Type, Value};
use tihdy_derive::extern_function;

const SCREEN_WIDTH: f32 = 20.0;
const SCREEN_HEIGHT: f32 = 20.0;

extern_function!(log
    [Value::Float(f1), Value::Float(f2)] -> Type::Void => {
        println!("({}, {})", f1, f2);
        Ok(Value::Nil)
    },
);

extern_function!(get_delta
    [] -> Type::Float => {
        Ok(Value::Float(get_frame_time() as f64))
    },
);

extern_function!(key_down
    [Value::String(s)] -> Type::Bool => {
        let s: &str = s;
        Ok(Value::Bool(match s {
            "w" => is_key_down(KeyCode::W),
            "s" => is_key_down(KeyCode::S),
            "i" => is_key_down(KeyCode::I),
            "k" => is_key_down(KeyCode::K),
            _ => false,
        }))
    },
);

extern_function!(my_next_frame
    [] -> Type::Void => {
        tokio::spawn(async {
            next_frame().await
        });
        Ok(Value::Nil)
    },
);

extern_function!(my_draw_rectangle
    [Value::Float(x), Value::Float(y), Value::Float(w), Value::Float(h)] -> Type::Void => {
        println!("Drawing rectangle {} {} {} {}", x, y, w, h);
        draw_rectangle(*x as f32, *y as f32, *w as f32, *h as f32, DARKPURPLE);
        Ok(Value::Nil)
    },
);

extern_function!(clear
    [] -> Type::Void => {
        clear_background(SKYBLUE);
        Ok(Value::Nil)
    },
);

#[macroquad::main("Pong")]
async fn main() {
    set_camera(Camera2D {
        zoom: vec2(1. / SCREEN_WIDTH * 2., -1. / SCREEN_HEIGHT * 2.),
        target: vec2(SCREEN_WIDTH / 2., SCREEN_HEIGHT / 2.),
        ..Default::default()
    });

    let rt = tokio::runtime::Runtime::new().unwrap();

    let functions: Vec<(String, tihdy::RustFunction)> = vec![
        ("log".to_string(), log),
        ("get_delta".to_string(), get_delta),
        ("key_down".to_string(), key_down),
        ("next_frame".to_string(), my_next_frame),
        ("draw_rectangle".to_string(), my_draw_rectangle),
        ("clear".to_string(), clear),
    ];

    let _guard = rt.enter();  // so we can async { next_frame().await }
    if let Err(errs) = tihdy::run_file(Path::new("pong.tdy"), false, functions) {
        for err in errs {
            println!("{}", err);
        }
    }
}
