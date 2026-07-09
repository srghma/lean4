impl BaseMutex {
    pub fn new() -> Self {
        Self {
            locked: Mutex::new(false),
            changed: Condvar::new(),
        }
    }

    pub fn lock(&self) {
        let mut locked = self.locked.lock().unwrap();
        while *locked {
            locked = self.changed.wait(locked).unwrap();
        }
        *locked = true;
    }

    pub fn try_lock(&self) -> bool {
        let mut locked = self.locked.lock().unwrap();
        if *locked {
            false
        } else {
            *locked = true;
            true
        }
    }

    pub fn unlock(&self) {
        let mut locked = self.locked.lock().unwrap();
        *locked = false;
        self.changed.notify_one();
    }
}
