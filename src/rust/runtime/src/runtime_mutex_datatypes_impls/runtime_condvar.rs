impl RuntimeCondvar {
    pub fn new() -> Self {
        Self {
            condvar: Condvar::new(),
        }
    }

    pub fn wait(&self, mutex: &BaseMutex) {
        let mut locked = mutex.locked.lock().unwrap();
        *locked = false;
        mutex.changed.notify_one();
        locked = self.condvar.wait(locked).unwrap();
        while *locked {
            locked = mutex.changed.wait(locked).unwrap();
        }
        *locked = true;
    }
}
