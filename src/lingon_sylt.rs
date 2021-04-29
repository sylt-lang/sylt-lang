use lingon::{Game, random::{Uniform, Distribute}};
use lingon::renderer::{Rect, Transform, Tint};
use std::sync::{Arc, Mutex};
use crate::{*, error::RuntimeError};
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

sylt_macro::sylt_link_gen!("sylt::lingon_sylt");

//
// Bellow here is where the boilerplate goes.
//

// Shamelessly stolen from rust-sdl2
fn string_to_sdl_scancode(key: &String) -> Option<lingon::input::Keycode> {
    use lingon::input::Keycode::*;
    Some( match key.as_str() {
        "BACKSPACE"           => Backspace,
        "TAB"                 => Tab,
        "RETURN"              => Return,
        "ESCAPE"              => Escape,
        "SPACE"               => Space,
        "EXCLAIM"             => Exclaim,
        "QUOTEDBL"            => Quotedbl,
        "HASH"                => Hash,
        "DOLLAR"              => Dollar,
        "PERCENT"             => Percent,
        "AMPERSAND"           => Ampersand,
        "QUOTE"               => Quote,
        "LEFTPAREN"           => LeftParen,
        "RIGHTPAREN"          => RightParen,
        "ASTERISK"            => Asterisk,
        "PLUS"                => Plus,
        "COMMA"               => Comma,
        "MINUS"               => Minus,
        "PERIOD"              => Period,
        "SLASH"               => Slash,
        "0"                   => Num0,
        "1"                   => Num1,
        "2"                   => Num2,
        "3"                   => Num3,
        "4"                   => Num4,
        "5"                   => Num5,
        "6"                   => Num6,
        "7"                   => Num7,
        "8"                   => Num8,
        "9"                   => Num9,
        "COLON"               => Colon,
        "SEMICOLON"           => Semicolon,
        "LESS"                => Less,
        "EQUALS"              => Equals,
        "GREATER"             => Greater,
        "QUESTION"            => Question,
        "AT"                  => At,
        "LEFTBRACKET"         => LeftBracket,
        "BACKSLASH"           => Backslash,
        "RIGHTBRACKET"        => RightBracket,
        "CARET"               => Caret,
        "UNDERSCORE"          => Underscore,
        "BACKQUOTE"           => Backquote,
        "a"                   => A,
        "b"                   => B,
        "c"                   => C,
        "d"                   => D,
        "e"                   => E,
        "f"                   => F,
        "g"                   => G,
        "h"                   => H,
        "i"                   => I,
        "j"                   => J,
        "k"                   => K,
        "l"                   => L,
        "m"                   => M,
        "n"                   => N,
        "o"                   => O,
        "p"                   => P,
        "q"                   => Q,
        "r"                   => R,
        "s"                   => S,
        "t"                   => T,
        "u"                   => U,
        "v"                   => V,
        "w"                   => W,
        "x"                   => X,
        "y"                   => Y,
        "z"                   => Z,
        "DELETE"              => Delete,
        "CAPSLOCK"            => CapsLock,
        "F1"                  => F1,
        "F2"                  => F2,
        "F3"                  => F3,
        "F4"                  => F4,
        "F5"                  => F5,
        "F6"                  => F6,
        "F7"                  => F7,
        "F8"                  => F8,
        "F9"                  => F9,
        "F10"                 => F10,
        "F11"                 => F11,
        "F12"                 => F12,
        "PRINTSCREEN"         => PrintScreen,
        "SCROLLLOCK"          => ScrollLock,
        "PAUSE"               => Pause,
        "INSERT"              => Insert,
        "HOME"                => Home,
        "PAGEUP"              => PageUp,
        "END"                 => End,
        "PAGEDOWN"            => PageDown,
        "RIGHT"               => Right,
        "LEFT"                => Left,
        "DOWN"                => Down,
        "UP"                  => Up,
        "NUMLOCKCLEAR"        => NumLockClear,
        "KP_DIVIDE"           => KpDivide,
        "KP_MULTIPLY"         => KpMultiply,
        "KP_MINUS"            => KpMinus,
        "KP_PLUS"             => KpPlus,
        "KP_ENTER"            => KpEnter,
        "KP_1"                => Kp1,
        "KP_2"                => Kp2,
        "KP_3"                => Kp3,
        "KP_4"                => Kp4,
        "KP_5"                => Kp5,
        "KP_6"                => Kp6,
        "KP_7"                => Kp7,
        "KP_8"                => Kp8,
        "KP_9"                => Kp9,
        "KP_0"                => Kp0,
        "KP_PERIOD"           => KpPeriod,
        "APPLICATION"         => Application,
        "POWER"               => Power,
        "KP_EQUALS"           => KpEquals,
        "F13"                 => F13,
        "F14"                 => F14,
        "F15"                 => F15,
        "F16"                 => F16,
        "F17"                 => F17,
        "F18"                 => F18,
        "F19"                 => F19,
        "F20"                 => F20,
        "F21"                 => F21,
        "F22"                 => F22,
        "F23"                 => F23,
        "F24"                 => F24,
        "EXECUTE"             => Execute,
        "HELP"                => Help,
        "MENU"                => Menu,
        "SELECT"              => Select,
        "STOP"                => Stop,
        "AGAIN"               => Again,
        "UNDO"                => Undo,
        "CUT"                 => Cut,
        "COPY"                => Copy,
        "PASTE"               => Paste,
        "FIND"                => Find,
        "MUTE"                => Mute,
        "VOLUMEUP"            => VolumeUp,
        "VOLUMEDOWN"          => VolumeDown,
        "KP_COMMA"            => KpComma,
        "KP_EQUALSAS400"      => KpEqualsAS400,
        "ALTERASE"            => AltErase,
        "SYSREQ"              => Sysreq,
        "CANCEL"              => Cancel,
        "CLEAR"               => Clear,
        "PRIOR"               => Prior,
        "RETURN2"             => Return2,
        "SEPARATOR"           => Separator,
        "OUT"                 => Out,
        "OPER"                => Oper,
        "CLEARAGAIN"          => ClearAgain,
        "CRSEL"               => CrSel,
        "EXSEL"               => ExSel,
        "KP_00"               => Kp00,
        "KP_000"              => Kp000,
        "THOUSANDSSEPARATOR"  => ThousandsSeparator,
        "DECIMALSEPARATOR"    => DecimalSeparator,
        "CURRENCYUNIT"        => CurrencyUnit,
        "CURRENCYSUBUNIT"     => CurrencySubUnit,
        "KP_LEFTPAREN"        => KpLeftParen,
        "KP_RIGHTPAREN"       => KpRightParen,
        "KP_LEFTBRACE"        => KpLeftBrace,
        "KP_RIGHTBRACE"       => KpRightBrace,
        "KP_TAB"              => KpTab,
        "KP_BACKSPACE"        => KpBackspace,
        "KP_A"                => KpA,
        "KP_B"                => KpB,
        "KP_C"                => KpC,
        "KP_D"                => KpD,
        "KP_E"                => KpE,
        "KP_F"                => KpF,
        "KP_XOR"              => KpXor,
        "KP_POWER"            => KpPower,
        "KP_PERCENT"          => KpPercent,
        "KP_LESS"             => KpLess,
        "KP_GREATER"          => KpGreater,
        "KP_AMPERSAND"        => KpAmpersand,
        "KP_DBLAMPERSAND"     => KpDblAmpersand,
        "KP_VERTICALBAR"      => KpVerticalBar,
        "KP_DBLVERTICALBAR"   => KpDblVerticalBar,
        "KP_COLON"            => KpColon,
        "KP_HASH"             => KpHash,
        "KP_SPACE"            => KpSpace,
        "KP_AT"               => KpAt,
        "KP_EXCLAM"           => KpExclam,
        "KP_MEMSTORE"         => KpMemStore,
        "KP_MEMRECALL"        => KpMemRecall,
        "KP_MEMCLEAR"         => KpMemClear,
        "KP_MEMADD"           => KpMemAdd,
        "KP_MEMSUBTRACT"      => KpMemSubtract,
        "KP_MEMMULTIPLY"      => KpMemMultiply,
        "KP_MEMDIVIDE"        => KpMemDivide,
        "KP_PLUSMINUS"        => KpPlusMinus,
        "KP_CLEAR"            => KpClear,
        "KP_CLEARENTRY"       => KpClearEntry,
        "KP_BINARY"           => KpBinary,
        "KP_OCTAL"            => KpOctal,
        "KP_DECIMAL"          => KpDecimal,
        "KP_HEXADECIMAL"      => KpHexadecimal,
        "LCTRL"               => LCtrl,
        "LSHIFT"              => LShift,
        "LALT"                => LAlt,
        "LGUI"                => LGui,
        "RCTRL"               => RCtrl,
        "RSHIFT"              => RShift,
        "RALT"                => RAlt,
        "RGUI"                => RGui,
        "MODE"                => Mode,
        "AUDIONEXT"           => AudioNext,
        "AUDIOPREV"           => AudioPrev,
        "AUDIOSTOP"           => AudioStop,
        "AUDIOPLAY"           => AudioPlay,
        "AUDIOMUTE"           => AudioMute,
        "MEDIASELECT"         => MediaSelect,
        "WWW"                 => Www,
        "MAIL"                => Mail,
        "CALCULATOR"          => Calculator,
        "COMPUTER"            => Computer,
        "AC_SEARCH"           => AcSearch,
        "AC_HOME"             => AcHome,
        "AC_BACK"             => AcBack,
        "AC_FORWARD"          => AcForward,
        "AC_STOP"             => AcStop,
        "AC_REFRESH"          => AcRefresh,
        "AC_BOOKMARKS"        => AcBookmarks,
        "BRIGHTNESSDOWN"      => BrightnessDown,
        "BRIGHTNESSUP"        => BrightnessUp,
        "DISPLAYSWITCH"       => DisplaySwitch,
        "KBDILLUMTOGGLE"      => KbdIllumToggle,
        "KBDILLUMDOWN"        => KbdIllumDown,
        "KBDILLUMUP"          => KbdIllumUp,
        "EJECT"               => Eject,
        "SLEEP"               => Sleep,
        _                     => return None
    })
}

