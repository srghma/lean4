impl BaseRecMutex {
    pub fn new() -> Self {
        Self {
            state: Mutex::new(RecState {
                owner: None,
                depth: 0,
            }),
            changed: Condvar::new(),
        }
    }

    pub fn lock(&self) {
        let current = std::thread::current().id();
        let mut state = self.state.lock().unwrap();
        loop {
            match state.owner {
                None => {
                    state.owner = Some(current);
                    state.depth = 1;
                    return;
                }
                Some(owner) if owner == current => {
                    state.depth += 1;
                    return;
                }
                _ => {
                    state = self.changed.wait(state).unwrap();
                }
            }
        }
    }

    pub fn try_lock(&self) -> bool {
        let current = std::thread::current().id();
        let mut state = self.state.lock().unwrap();
        match state.owner {
            None => {
                state.owner = Some(current);
                state.depth = 1;
                true
            }
            Some(owner) if owner == current => {
                state.depth += 1;
                true
            }
            _ => false,
        }
    }

    pub fn unlock(&self) {
        let current = std::thread::current().id();
        let mut state = self.state.lock().unwrap();
        if state.owner == Some(current) {
            state.depth -= 1;
            if state.depth == 0 {
                state.owner = None;
                self.changed.notify_one();
            }
        }
    }
}
