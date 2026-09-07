use std::rc::{Rc, Weak};
use std::cell::RefCell;

struct Node {
    value: i32,
    next: RefCell<Option<Rc<Node>>>, // better use next: Enum either Rc or Weak
    prev: RefCell<Option<Weak<Node>>>, // <- Use Weak here
}

impl Drop for Node {
    fn drop(&mut self) {
        println!("\n--- Dropping Node ---");
        println!("Value: {}", self.value);

        // Display information about next
        match &*self.next.borrow() {
            Some(next) => println!("Next: Node with value {}", next.value),
            None => println!("Next: None"),
        }

        // Display information about prev
        // Weak::upgrade() tries to convert a Weak<T> into an Rc<T>. It returns:
        //   Some(Rc<T>) if the value still exists (i.e., at least one Rc<T> is alive).
        //   None if all Rc<T>s have been dropped, and the value has been deallocated.

        match &*self.prev.borrow() {
            Some(prev_weak) => match prev_weak.upgrade() {
                Some(prev_rc) => println!("Prev: value is some but was not dropped yet (ref.value = {})", prev_rc.value),
                None => println!("Prev: value is some but was dropped already, upgrade gave None"),
            },
            None => println!("Prev: value is None"),
        }

        println!("----------------------\n");
    }
}
pub fn main() {
    let a = Rc::new(Node {
        value: 1,
        next: RefCell::new(None),
        prev: RefCell::new(None),
    });

    let b = Rc::new(Node {
        value: 2,
        next: RefCell::new(Some(a.clone())),
        // next: RefCell::new(None),
        prev: RefCell::new(None),
    });

    // Create a cycle: a → b → a (but use Weak for b → a)
    *a.next.borrow_mut() = Some(b.clone()); // +1 strong for b
    *b.prev.borrow_mut() = Some(Rc::downgrade(&a)); // +1 weak for a
    *b.next.borrow_mut() = None; // <- This breaks the strong cycle

    println!("a strong = {}, weak = {}", Rc::strong_count(&a), Rc::weak_count(&a)); // strong = 1, weak = 1
    println!("b strong = {}, weak = {}", Rc::strong_count(&b), Rc::weak_count(&b)); // strong = 2, weak = 0

    println!("Dropping b manually (removing a.next)");
    *a.next.borrow_mut() = None; // Remove b from a.next
    println!("Dropping b manually (removing a.next finished)");
    println!("a strong = {}, weak = {}", Rc::strong_count(&a), Rc::weak_count(&a)); // strong = 1, weak = 1
    println!("b strong = {}, weak = {}", Rc::strong_count(&b), Rc::weak_count(&b)); // strong = 1, weak = 0
    drop(b);
    println!("drop b finished"); // strong = 2, weak = 0

    // Both a and b will never be freed, even when main ends
}

// 👇 Let's inspect a:
// Rc::new(...) → 1 strong
// Rc::downgrade(&a) → +1 weak

// 👇 Now inspect b:
// Rc::new(...) → 1 strong
// Some(b.clone()) (stored in a.next) → +1 strong
