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
        // println!("Dropping Node with value {}", self.value);
        // *self.next.borrow_mut() = RcOrWeak::None;

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
    let c = Rc::new(Node {
        value: 3,
        next: RefCell::new(RcOrWeak::None),
    });

    let b = Rc::new(Node {
        value: 2,
        next: RefCell::new(RcOrWeak::Strong(c.clone())), // b → c (strong)
    });

    let a = Rc::new(Node {
        value: 1,
        next: RefCell::new(RcOrWeak::Strong(b.clone())), // a → b (strong)
    });


    // Create a cycle: a => b => c -> a (=> is strong connection, -> is weak connection)
    *c.next.borrow_mut() = RcOrWeak::Weak(Rc::downgrade(&a)); // c → a (weak)

    // Reference count breakdown:
    //
    // a:
    //   - strong = 1 (from `let a = Rc::new(...)`)
    //   - weak = 1 (from `c.next = Weak(a)`)
    //
    // b:
    //   - strong = 2 (from `let b = Rc::new(...)` and `a.next = Rc(b)`)
    //   - weak = 0
    //
    // c:
    //   - strong = 2 (from `let c = Rc::new(...)` and `b.next = Rc(c)`)
    //   - weak = 0

    println!("a strong = {}, weak = {}", Rc::strong_count(&a), Rc::weak_count(&a)); // 1, 1
    println!("b strong = {}, weak = {}", Rc::strong_count(&b), Rc::weak_count(&b)); // 2, 0
    println!("c strong = {}, weak = {}", Rc::strong_count(&c), Rc::weak_count(&c)); // 2, 0

    // *b.next.borrow_mut() = RcOrWeak::None;
    *a.next.borrow_mut() = RcOrWeak::None;
    println!("a strong = {}, weak = {}", Rc::strong_count(&a), Rc::weak_count(&a)); // 1, 1
    println!("b strong = {}, weak = {}", Rc::strong_count(&b), Rc::weak_count(&b)); // 2, 0
    println!("c strong = {}, weak = {}", Rc::strong_count(&c), Rc::weak_count(&c)); // 1, 0

    // drop(b); // Drop one strong reference to `b` (from the `b` variable). `a.next` still holds one strong Rc to `b`.
    drop_and_verify(b, "b"); // if *a.next.borrow_mut() = RcOrWeak::None; was not called before - throws
    println!("drop b finished");

    println!("a strong = {}, weak = {}", Rc::strong_count(&a), Rc::weak_count(&a)); // 1, 1
    println!("c strong = {}, weak = {}", Rc::strong_count(&c), Rc::weak_count(&c)); // 1, 0
}

// Custom drop function that checks if drop was ignored
fn drop_and_verify<T>(rc: Rc<T>, name: &str) {
    let strong_count_before = Rc::strong_count(&rc);
    let weak_count_before = Rc::weak_count(&rc);

    println!("→ Calling drop({}) - strong_count: {}, weak_count: {}",
             name, strong_count_before, weak_count_before);

    // Check if this is the last strong reference
    let is_last_strong_ref = strong_count_before == 1;

    drop(rc);

    if is_last_strong_ref {
        println!("✓ drop({}) should have executed Drop::drop (was last strong reference)", name);
    } else {
        panic!("❌ drop({}) was ignored! There are still {} other strong references preventing Drop::drop execution",
               name, strong_count_before - 1);
    }
}
