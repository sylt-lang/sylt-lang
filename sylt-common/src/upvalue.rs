use serde::{Deserialize, Serialize};

use crate::value::Value;

#[derive(Debug)]
#[derive(Deserialize, Serialize)]
pub struct UpValue {
    pub slot: usize,
    pub value: Value,
}

impl UpValue {
    pub fn new(slot: usize) -> Self {
        Self {
            slot,
            value: Value::Nil,
        }
    }

    pub fn get(&self, stack: &[Value]) -> Value {
        if self.is_closed() {
            self.value.clone()
        } else {
            stack[self.slot].clone()
        }
    }

    pub fn set(&mut self, stack: &mut [Value], value: Value) {
        if self.is_closed() {
            self.value = value;
        } else {
            stack[self.slot] = value;
        }
    }

    pub fn is_closed(&self) -> bool {
        self.slot == 0
    }

    pub fn close(&mut self, value: Value) {
        self.slot = 0;
        self.value = value;
    }
}
