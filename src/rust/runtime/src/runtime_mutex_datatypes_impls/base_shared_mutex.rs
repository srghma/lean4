impl BaseSharedMutex {
    pub fn new() -> Self {
        Self {
            state: Mutex::new(SharedState {
                readers: 0,
                writer: false,
            }),
            changed: Condvar::new(),
        }
    }

    pub fn write(&self) {
        let mut state = self.state.lock().unwrap();
        while state.writer || state.readers != 0 {
            state = self.changed.wait(state).unwrap();
        }
        state.writer = true;
    }

    pub fn try_write(&self) -> bool {
        let mut state = self.state.lock().unwrap();
        if state.writer || state.readers != 0 {
            false
        } else {
            state.writer = true;
            true
        }
    }

    pub fn unlock_write(&self) {
        let mut state = self.state.lock().unwrap();
        state.writer = false;
        self.changed.notify_all();
    }

    pub fn read(&self) {
        let mut state = self.state.lock().unwrap();
        while state.writer {
            state = self.changed.wait(state).unwrap();
        }
        state.readers += 1;
    }

    pub fn try_read(&self) -> bool {
        let mut state = self.state.lock().unwrap();
        if state.writer {
            false
        } else {
            state.readers += 1;
            true
        }
    }

    pub fn unlock_read(&self) {
        let mut state = self.state.lock().unwrap();
        if state.readers > 0 {
            state.readers -= 1;
            if state.readers == 0 {
                self.changed.notify_all();
            }
        }
    }
}
