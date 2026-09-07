use std::rc::{Rc, Weak};
use std::cell::RefCell;

#[derive(Debug)]
enum RcOrWeak<T> {
    None,
    Strong(Rc<T>),
    Weak(Weak<T>),
}

struct Node {
    value: i32,
    next: RefCell<RcOrWeak<Node>>,
}

impl Drop for Node {
    fn drop(&mut self) {
        println!("\n--- Dropping Node ---");
        println!("Value: {}", self.value);

        match &*self.next.borrow() {
            RcOrWeak::None => println!("Next: None"),
            RcOrWeak::Strong(rc) => println!("Next: Strong → Node with value {}", rc.value),
            RcOrWeak::Weak(weak) => match weak.upgrade() {
                Some(rc) => println!("Next: Weak → Node with value {}", rc.value),
                None => println!("Next: Weak → Already dropped"),
            },
        }

        println!("----------------------\n");
    }
}

pub fn main() {
    let a = Rc::new(Node {
        value: 1,
        next: RefCell::new(RcOrWeak::None),
    });

    let b = Rc::new(Node {
        value: 2,
        next: RefCell::new(RcOrWeak::Strong(a.clone())),
    });

    // Create a cycle: a => b -> a (=> is strong connection, -> is weak connection)
    *a.next.borrow_mut() = RcOrWeak::Weak(Rc::downgrade(&b));

    println!("a strong = {}, weak = {}", Rc::strong_count(&a), Rc::weak_count(&a)); // 2, 0
    println!("b strong = {}, weak = {}", Rc::strong_count(&b), Rc::weak_count(&b)); // 1, 1

    drop(b);
    println!("drop b finished"); // strong = 2, weak = 0

    println!("a strong = {}, weak = {}", Rc::strong_count(&a), Rc::weak_count(&a)); // 2, 0
}

// 👇 Let's inspect a:
// Rc::new(...) → 1 strong
// Rc::downgrade(&a) → +1 weak

// 👇 Now inspect b:
// Rc::new(...) → 1 strong
// Some(b.clone()) (stored in a.next) → +1 strong

// A => B => C => A - leak, A => B => C -> A - no leak

// Example: A ⇄ B ⇄ C
