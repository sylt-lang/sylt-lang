use luminance_sdl2::sdl2;
use sdl2::event::{Event, WindowEvent};
use std::collections::HashMap;

pub use sdl2::{GameControllerSubsystem, Sdl};
pub use sdl2::controller::{Axis, Button, GameController};
pub use sdl2::keyboard::Keycode;
pub use sdl2::mouse::MouseButton;

#[derive(Hash, Copy, Clone, Debug, Eq, PartialEq)]
pub enum Device {
    Quit,
    Key(Keycode),
    Mouse(MouseButton),
    Button(u32, Button),
    Axis(u32, Axis),
}

#[derive(Hash, Copy, Clone, Debug, Eq, PartialEq)]
pub enum Name {
    Left,
    Right,
    Up,
    Down,
    Quit,
}

#[derive(Copy, Clone, Debug)]
pub enum KeyState {
    Down(usize),
    Up(usize),
    Analog(f32),
}

pub struct InputManager {
    frame: usize,
    controllers: GameControllerSubsystem,
    physical_inputs: HashMap<Device, Name>,
    virtual_inputs: HashMap<Name, KeyState>,
    opened_controllers: HashMap<u32, GameController>,
}

fn remap(value: i16) -> f32 {
    // MIN has a larger absolute value,
    // this garantees that the values in [-1, 1).
    -(value as f32) / (i16::MIN as f32)
}

const TRIGGER_LIMIT: f32 = 0.1;

impl InputManager {
    pub fn new(sdl: &Sdl) -> Self {
        let controllers = sdl.game_controller().unwrap();
        controllers.set_event_state(true);

        Self {
            physical_inputs: HashMap::new(),
            virtual_inputs: HashMap::new(),
            frame: 0,
            controllers: controllers.clone(),
            opened_controllers: HashMap::new(),
        }
    }

    pub fn bind(&mut self, device: Device, name: Name) {
        self.physical_inputs.insert(device, name);
        self.virtual_inputs.insert(name, KeyState::Up(0));
    }

    #[allow(dead_code)]
    pub fn down(&self, name: Name) -> bool {
        match self.virtual_inputs.get(&name) {
            Some(KeyState::Down(_)) => true,
            Some(KeyState::Up(_)) => false,
            Some(KeyState::Analog(v)) => v.abs() > TRIGGER_LIMIT,
            None => {
                // TODO(ed): I don't like this... but it's here now.
                false
            }
        }
    }

    #[allow(dead_code)]
    pub fn up(&self, name: Name) -> bool {
        match self.virtual_inputs.get(&name) {
            Some(KeyState::Down(_)) => false,
            Some(KeyState::Up(_)) => true,
            Some(KeyState::Analog(v)) => v.abs() < TRIGGER_LIMIT,
            None => {
                // TODO(ed): I don't like this... but it's here now.
                false
            }
        }
    }

    pub fn pressed(&self, name: Name) -> bool {
        match self.virtual_inputs.get(&name) {
            Some(KeyState::Down(frame)) => self.frame == *frame,
            _ => {
                // TODO(ed): I don't like this... but it's here now.
                false
            }
        }
    }

    #[allow(dead_code)]
    pub fn released(&self, name: Name) -> bool {
        match self.virtual_inputs.get(&name) {
            Some(KeyState::Up(frame)) => self.frame == *frame,
            _ => {
                // TODO(ed): I don't like this... but it's here now.
                false
            }
        }
    }

    pub fn value(&self, name: Name) -> f32 {
        match self.virtual_inputs.get(&name) {
            Some(KeyState::Up(_)) => 0.0,
            Some(KeyState::Down(_)) => 1.0,
            Some(KeyState::Analog(v)) => *v,
            _ => {
                // TODO(ed): I don't like this... but it's here now.
                0.0
            }
        }
    }

    pub fn rumble(&mut self, controller: u32, lo: f32, hi: f32, time: f32) -> Result<(), ()> {
        if let Some(controller) = self.opened_controllers.get_mut(&controller) {
            let lo = (lo * (u16::MAX as f32)) as u16;
            let hi = (hi * (u16::MAX as f32)) as u16;
            controller.set_rumble(lo, hi, (time * 1000.0) as u32).unwrap();
            Ok(())
        } else {
            Err(())
        }
    }

    pub fn poll(&mut self, sdl: &sdl2::Sdl) {
        self.frame += 1;
        let frame = self.frame;
        for event in sdl.event_pump().unwrap().poll_iter() {
            let (input, down) = match event {
                Event::Quit { .. } => (Device::Quit, KeyState::Down(frame)),
                Event::Window {
                    win_event: WindowEvent::Close,
                    ..
                } => (Device::Quit, KeyState::Down(frame)),
                Event::KeyDown {
                    keycode: Some(keycode),
                    ..
                } => (Device::Key(keycode), KeyState::Down(frame)),
                Event::KeyUp {
                    keycode: Some(keycode),
                    ..
                } => (Device::Key(keycode), KeyState::Up(frame)),
                Event::ControllerDeviceAdded {
                    which,
                    ..
                } => {
                    let controller = self.controllers.open(which).unwrap();
                    self.opened_controllers.insert(which, controller);
                    continue;
                }
                Event::ControllerDeviceRemoved {
                    which,
                    ..
                } => {
                    self.opened_controllers.remove(&which).unwrap();
                    continue;
                }
                Event::ControllerAxisMotion {
                    which, axis, value, ..
                } => {
                    let value = remap(value);
                    (Device::Axis(which, axis), KeyState::Analog(value))
                }
                Event::ControllerButtonDown { which, button, .. } => {
                    (Device::Button(which, button), KeyState::Down(frame))
                }
                Event::ControllerButtonUp { which, button, .. } => {
                    (Device::Button(which, button), KeyState::Up(frame))
                }
                Event::MouseButtonDown { mouse_btn, .. } => {
                    (Device::Mouse(mouse_btn), KeyState::Down(frame))
                }
                Event::MouseButtonUp { mouse_btn, .. } => {
                    (Device::Mouse(mouse_btn), KeyState::Up(frame))
                }
                Event::MouseMotion { .. } => {
                    // TODO
                    continue;
                }
                _ => {
                    continue;
                }
            };

            if let Some(slot) = self.physical_inputs.get(&input) {
                self.virtual_inputs.insert(*slot, down);
            }
        }
    }
}
