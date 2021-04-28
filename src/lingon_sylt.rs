use lingon::{Game, random::{Uniform, Distribute}};
use std::sync::{Arc, Mutex};
use crate::*;
use crate as sylt;

// TODO(ed): Make the trait only clone, not copy.
struct GG {
    pub game: Game<i64>,
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
        {
            let mutex: &Mutex<GG> = Arc::borrow(&GAME);
            &mut mutex.lock().unwrap().game
        }
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
    l_draw
    [] -> Type::Void => {
        game!().draw().unwrap();
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
    l_random
    [] -> Type::Float => {
        Ok(Value::Float(Uniform.sample().into()))
    },
);


sylt_macro::sylt_link_gen!("sylt::lingon_sylt");
