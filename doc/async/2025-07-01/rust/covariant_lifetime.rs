#[allow(unused_variables)]
fn covariant_example<'short, 'long: 'short>() {
    let long: &'long str = "I live longer";
    // println!("long: {:p}", long);
    // println!("&long: {:p}", &long);
    // println!("&&long: {:p}", &&long);

    let short: &'short str = long;
    // println!("short: {:p}", short);
    // println!("&short: {:p}", &short);
    // println!("&&short: {:p}", &&short);
    // let _S: &'static str = long; // NOT OK anything

    // let _S: &'static str = "I live longer";
    // let _short2: &'short str = _S;

    /////////////////////////////
    // let ll_ref: &'long &'long str = &long;
    // let ss_ref: &'short &'short str = &long;
    // let sl_ref: &'long &'short str = &long;
    // let ls_ref: &'short &'long str = &long;

    // let Ss_ref: &'static &'short str = &long;
    // let sS_ref: &'short &'static str = &long;
    // let Sl_ref: &'static &'long str = &long;
    // let lS_ref: &'long &'static str = &long;

    // // local temporary lifetime
    // let Ls_ref: &'_ &'short str = &long; // ok
    // let sL_ref: &'short &'_ str = &long;
    // let Ll_ref: &'_ &'long str = &long; // ok
    // let lL_ref: &'long &'_ str = &long;

    ////////////////////////////
    // let ll_ref_s: &'long &'long str = &short;
    // let ss_ref_s: &'short &'short str = &short;
    // let sl_ref_s: &'long &'short str = &short;
    // let ls_ref_s: &'short &'long str = &short;

    // let Ss_ref_s: &'static &'short str = &short;
    // let sS_ref_s: &'short &'static str = &short;
    // let Sl_ref_s: &'static &'long str = &short;
    // let lS_ref_s: &'long &'static str = &short;

    // // local temporary lifetime
    // let Ls_ref_s: &'_ &'short str = &short; // ok
    // let sL_ref_s: &'short &'_ str = &short;
    // let Ll_ref_s: &'_ &'long str = &short; // NOT ok
    // let lL_ref_s: &'long &'_ str = &short;


    // let llref: &'long &'long str = ll_ref;
    // let ssref: &'short &'short str = ll_ref;
    // let lsref: &'long &'short str = ll_ref;
    // let slref: &'short &'long str = ll_ref;
    // let lSref: &'long &'static str = ll_ref;
    // let Slref: &'static &'long str = ll_ref;
    // let Ssref: &'static &'short str = ll_ref;
    // let sSref: &'short &'static str = ll_ref;
}

// fn invariant_example<'short, 'long: 'short>() {
//     let mut x: i32 = 5;
//     let long: &'long mut i32 = &mut x;

//     // let short: &'short mut i32 = long; // ❌ Error: can't coerce
//     // Reason: &mut T is invariant in T
// }

// fn accepts_str(s: &str) {}
// fn accepts_static_str(s: &'static str) {}

// fn contravariant_example() {
//     let f1: fn(&'static str) -> () = accepts_str; // ✅ OK: accepts_str: fn(&str) -> ()
//     // Because &str :> &'static str (i.e. &'static str is subtype of &str)
// }

pub fn main() {
    covariant_example();
}
