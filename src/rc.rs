use std::fmt;

pub struct Rc<T>(*mut (usize, T));

impl<T> Rc<T> {
    pub fn new(data: T) -> Self {
        Self(Box::into_raw(Box::new((1, data))))
    }
}

impl<T> Drop for Rc<T> {
    fn drop(&mut self) {
        unsafe {
            if (*self.0).0 == 1 {
                drop(self.0);
                return;
            }
            (*self.0).0 -= 1;
        }
    }
}

impl<T> Clone for Rc<T> {
    fn clone(&self) -> Self {
        unsafe {
            (*self.0).0 += 1;
        }
        Self(self.0)
    }
}

impl<T> From<T> for Rc<T> {
    fn from(t: T) -> Self {
        Self::new(t)
    }
}

impl<T> AsRef<T> for Rc<T> {
    fn as_ref(&self) -> &T {
        unsafe {
            &(*self.0).1
        }
    }
}

impl<T> std::ops::Deref for Rc<T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe {
            &(*self.0).1
        }
    }
}

impl<T: std::cmp::PartialEq> std::cmp::PartialEq for Rc<T> {
    fn eq(&self, other: &Self) -> bool {
        unsafe {
            (*self.0).1.eq(&(*other.0).1)
        }
    }
}

impl<T: std::cmp::Eq> std::cmp::Eq for Rc<T> {}

impl<T: std::cmp::PartialOrd> std::cmp::PartialOrd for Rc<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        unsafe {
            (*self.0).1.partial_cmp(&(*other.0).1)
        }
    }
}

impl<T: std::cmp::Ord> std::cmp::Ord for Rc<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        unsafe {
            (*self.0).1.cmp(&(*other.0).1)
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Rc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unsafe {
            (*self.0).1.fmt(f)
        }
    }
}

impl<T: fmt::Display> fmt::Display for Rc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unsafe {
            (*self.0).1.fmt(f)
        }
    }
}
