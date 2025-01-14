#[doc(hidden)]
#[macro_export]
macro_rules! count {
    (@subst $($x:tt)*) => (());
    ($($rest:expr),*) => (<[()]>::len(&[$($crate::count!(@subst $rest)),*]) as i32);
}

/// Creates a [`JanetTuple`] containing the arguments.
///
/// `tuple!` allows [`JanetTuple`]s to be defined with the same syntax as Rust array
/// expressions. There are 2 forms of this macro:
///  * Create a [`JanetTuple`] containing a given list of elements
/// ```
/// use janetrs::{tuple, Janet};
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let t = tuple![3, true, "hey"];
///
/// assert_eq!(t[0], &Janet::integer(3));
/// assert_eq!(t[1], &Janet::boolean(true));
/// assert_eq!(t[2], &Janet::from("hey"));
/// ```
///  * Create a [`JanetTuple`] from a given element and size
/// ```
/// use janetrs::{Janet, tuple};
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let t = tuple!["123"; 3];
///
/// assert_eq!(t[0], &Janet::from("123"));
/// assert_eq!(t[1], &Janet::from("123"));
/// assert_eq!(t[2], &Janet::from("123"));
/// ```
///
/// Note that unlike `vec!` from the Rust standard library, this macro doesn't try to
/// clone the elements passed.
///
/// Also note that this macro builds the tuples converting the passed elements to
/// [`Janet`] using the [`From`] trait, so if you want for a type defined by you to be
/// used in this macro, implement the [`From`] trait to convert from you type to
/// [`Janet`] or transform to [`Janet`] beforehand.
///
/// [`Janet`]: ./types/struct.Janet.html
/// [`JanetTuple`]: ./types/tuple/struct.JanetTuple.html
#[macro_export]
macro_rules! tuple {
    ($elem:expr; $n:expr) => {$crate::JanetTuple::with_default_elem($crate::Janet::from($elem), $n)};

    ($($val:expr),* $(,)?) => {{
        const LEN: i32 = $crate::count!($($val),*);
        $crate::JanetTuple::builder(LEN)
            $(.put($crate::Janet::from($val)))*
            .finalize()
    }};
}

/// Creates a [`JanetArray`] containing the arguments.
///
/// `tuple!` allows [`JanetArray`]s to be defined with the same syntax as Rust array
/// expressions. There are 2 forms of this macro:
///  * Create a [`JanetArray`] containing a given list of elements
/// ```
/// use janetrs::{array, Janet};
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let arr = array![3, true, "hey"];
///
/// assert_eq!(arr[0], &Janet::integer(3));
/// assert_eq!(arr[1], &Janet::boolean(true));
/// assert_eq!(arr[2], &Janet::from("hey"));
/// ```
///  * Create a [`JanetArray`] from a given element and size
/// ```
/// use janetrs::{Janet, array};
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let arr = array!["123"; 3];
///
/// assert_eq!(arr[0], &Janet::from("123"));
/// assert_eq!(arr[1], &Janet::from("123"));
/// assert_eq!(arr[2], &Janet::from("123"));
/// ```
///
/// Note that unlike `vec!` from the Rust standard library, this macro doesn't try to
/// clone the elements passed.
///
/// Also note that this macro builds the array converting the passed elements to
/// [`Janet`] using the [`From`] trait, so if you want for a type defined by you to be
/// used in this macro, implement the [`From`] trait to convert from you type to
/// [`Janet`] or transform to [`Janet`] beforehand.
///
/// [`Janet`]: ./types/struct.Janet.html
/// [`JanetArray`]: ./types/tuple/struct.JanetArray.html
#[macro_export]
macro_rules! array {
    () => { $crate::JanetArray::new() };

    ($elem:expr; $n:expr) => {{
        let mut arr = $crate::JanetArray::with_capacity($n);
        (0..$n).for_each(|_| arr.push($crate::Janet::from($elem)));
        arr
    }};

    ($($val:expr),* $(,)?) => {{
        const LEN: i32 = $crate::count!($($val),*);
        let mut arr = $crate::JanetArray::with_capacity(LEN);
        $(arr.push($crate::Janet::from($val));)*
        arr
    }};
}

/// Creates a [`JanetStruct`] containing the arguments key-value pairs.
///
/// `structs!` allows [`JanetStruct`]s to be defined with a syntax that have key-value
/// pairs as the items of the struct.
///
/// ```
/// use janetrs::{structs, Janet};
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let st = structs! {
///     1 => "one",
///     true => 1,
/// };
///
/// assert_eq!(st.len(), 2);
/// assert_eq!(st.get(1), Some(&Janet::from("one")));
/// assert_eq!(st.get(true), Some(&Janet::integer(1)));
/// ```
///
/// Note that this macro builds the struct converting the passed elements to
/// [`Janet`] using the [`From`] trait, so if you want for a type defined by you to be
/// used in this macro, implement the [`From`] trait to convert from you type to
/// [`Janet`] or transform to [`Janet`] beforehand.
///
/// [`Janet`]: ./types/struct.Janet.html
/// [`JanetStruct`]: ./types/tuple/struct.JanetStruct.html
#[macro_export]
macro_rules! structs {
    ($($key:expr => $value:expr),* $(,)?) => {{
        const LEN: i32 = $crate::count!($($key),*);
        $crate::JanetStruct::builder(LEN)
            $(.put($crate::Janet::from($key), $crate::Janet::from($value)))*
            .finalize()
    }};
}

/// Creates a [`JanetTable`] containing the arguments key-value pairs.
///
/// `table!` allows [`JanetTable`]s to be defined with a syntax that have key-value
/// pairs as the items of the struct.
///
/// ```
/// use janetrs::{table, Janet};
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let table = table! {
///     1 => "one",
///     true => 1,
/// };
///
/// assert_eq!(table.len(), 2);
/// assert_eq!(table.get(1), Some(&Janet::from("one")));
/// assert_eq!(table.get(true), Some(&Janet::integer(1)));
/// ```
///
/// Note that this macro builds the struct converting the passed elements to
/// [`Janet`] using the [`From`] trait, so if you want for a type defined by you to be
/// used in this macro, implement the [`From`] trait to convert from you type to
/// [`Janet`] or transform to [`Janet`] beforehand.
///
/// [`Janet`]: ./types/struct.Janet.html
/// [`JanetTable`]: ./types/tuple/struct.JanetTable.html
#[macro_export]
macro_rules! table {
    () => ($crate::JanetTable::new());

    ($($key:expr => $value:expr),* $(,)?) => {{
        const LEN: i32 = $crate::count!($($key),*);
        let mut table = $crate::JanetTable::with_capacity(LEN);
        $(let _ = table.insert($crate::Janet::from($key), $crate::Janet::from($value));)*

        table
    }};
}

/// A macro to make life easier creating modules for Janet from Rust.
///
/// ## The syntax:
/// `janet_mod!(<Janet Module Name (string literal)>; <{<Janet Function Name ((string
/// literal))>, <function pointer>, <Janet documentation string (string literal)>},
/// ...>);` ¹ Items inside `<>` means mandatory
/// ² `...` means one or more
///
/// # Examples
/// ```
/// use janetrs::{janet_mod, Janet, janet_fn};
///
/// #[janet_fn(arity(fix(0)))]
/// fn rust_hello(args: &mut [Janet]) -> Janet {
///     println!("Hello from Rust!");
///     Janet::nil()
/// }
///
/// #[janet_fn(arity(fix(0)))]
/// fn hi(args: &mut [Janet]) -> Janet {
///     Janet::from("Hi! My name is GrayJack!")
/// }
///
/// janet_mod!("rust";
///     {"hello", rust_hello, "(rust/hello)\n\nRust say hello"},
///     {"hi", hi, "(rust/hi)\n\nHi! My name is..."}
/// );
/// ```
#[deprecated(since = "0.4.0", note = "use `declare_janet_mod` instead")]
#[macro_export]
macro_rules! janet_mod {
    ($mod_name:literal; $({$fn_name:literal, $fn:expr, $fn_doc:literal}),* $(,)?) => {
        #[no_mangle]
        pub unsafe extern "C-unwind" fn _janet_mod_config() -> $crate::lowlevel::JanetBuildConfig {
            $crate::lowlevel::JanetBuildConfig {
                major: $crate::lowlevel::JANET_VERSION_MAJOR,
                minor: $crate::lowlevel::JANET_VERSION_MINOR,
                patch: $crate::lowlevel::JANET_VERSION_PATCH,
                bits:  $crate::lowlevel::JANET_CURRENT_CONFIG_BITS,
            }
        }

        #[no_mangle]
        pub unsafe extern "C-unwind" fn _janet_init(env: *mut $crate::lowlevel::JanetTable) {
            $crate::lowlevel::janet_cfuns(env, concat!($mod_name, "\0").as_ptr() as *const _, [
                $(
                    $crate::lowlevel::JanetReg {
                        name: concat!($fn_name, "\0").as_ptr() as *const _,
                        cfun: Some($fn),
                        documentation: concat!($fn_doc, "\0").as_ptr() as *const _,
                    },
                )*

                $crate::lowlevel::JanetReg {
                    name: std::ptr::null(),
                    cfun: None,
                    documentation: std::ptr::null(),
                },
            ].as_ptr())
        }
    };
}

/// Causes a panic in the Janet side (exception). Differently of the Rust `panic!` macro,
/// this macro does **not** terminate the current thread. Instead, it sends a error signal
/// with the passed message where the Janet runtime takes care to properly exit.
///
/// # Examples
/// ```ignore
/// use janetrs::jpanic;
/// # let _client = janetrs::client::JanetClient::init().unwrap();
/// jpanic!();
/// jpanic!("this is a terrible mistake!");
/// jpanic!(4); // In simple cases you can use any type that Janet implements From trait
/// jpanic!("this is a {} {message}", "fancy", message = "message");
/// ```
#[cfg(not(feature = "std"))]
#[macro_export]
macro_rules! jpanic {
    () => {
        $crate::util::_panic($crate::Janet::from("explicit panic"))
    };
    ($($arg:tt)+) => {
        $crate::util::_panic($crate::Janet::from(::alloc::format!($($arg)+).as_str()))
    };
}

/// Causes a panic in the Janet side (exception). Differently of the Rust `panic!` macro,
/// this macro does **not** terminate the current thread. Instead, it sends a error signal
/// with the passed message where the Janet runtime takes care to properly exit.
///
/// # Examples
/// ```ignore
/// use janetrs::jpanic;
/// # let _client = janetrs::client::JanetClient::init().unwrap();
/// jpanic!();
/// jpanic!("this is a terrible mistake!");
/// jpanic!(4); // In simple cases you can use any type that Janet implements From trait
/// jpanic!("this is a {} {message}", "fancy", message = "message");
/// ```
#[cfg(feature = "std")]
#[macro_export]
macro_rules! jpanic {
    () => {
        $crate::util::_panic($crate::Janet::from("explicit panic"))
    };
    ($($arg:tt)+) => {
        $crate::util::_panic($crate::Janet::from(::std::format!($($arg)+).as_str()))
    };
}

/// A macro helper to use the default message when getting the wrong types in the function
/// argument when the situations that are more complex than the ones handled in
/// [`JanetArgs`](crate::JanetArgs), like multiple accepted types.
///
/// # Examples
///
/// ```
/// use janetrs::{bad_slot, janet_fn, Janet, TaggedJanet};
///
/// #[janet_fn(arity(fix(1)))]
/// fn hi(args: &mut [Janet]) -> Janet {
///     match args[1].unwrap() {
///         TaggedJanet::Buffer(name) => println!("Hi, {}", name),
///         TaggedJanet::String(name) => println!("Hi, {}", name),
///         _ => bad_slot!(args, 0, "string|buffer"),
///     }
///     Janet::nil()
/// }
/// ```
#[macro_export]
macro_rules! bad_slot {
    ($args:ident, $index:expr, $expected:expr) => {
        $crate::jpanic!(
            "bad slot #{}, expected {}, got {}",
            $index,
            $expected,
            $args[$index].kind()
        )
    };
}

/// Execute a function ([`JanetCFunction`], Rust function or extern C function) and catch
/// any janet panic that may happen as a [`Result`].
///
/// # Examples
/// ```rust, ignore
/// use janetrs::{jcatch, jpanic, Janet};
///
/// fn panic_fn() {
///     jpanic!("Help!");
/// }
///
/// #[janet_fn]
/// fn test(args: &mut [Janet]) -> Janet {
///     let res = jcatch!(panic_fn());
///     dbg!(res);
///     Janet::nil()
/// }
/// ```
///
/// [`JanetCFunction`]: crate::JanetCFunction
#[crate::cjvg("1.12.2")]
#[macro_export]
macro_rules! jcatch {
    ($e:expr) => {{
        let mut state = $crate::function::JanetTryState::init();

        if let Some(signal) = state.signal() {
            if matches!(
                signal,
                $crate::JanetSignal::Ok | $crate::JanetSignal::Yield | $crate::JanetSignal::User9
            ) {
                Ok($e)
            } else {
                Err(state.payload())
            }
        } else {
            Err($crate::Janet::from("No fiber to run."))
        }
    }};
}

/// Macro that tries to run a expression, and if it panics in the Rust side, it tries to
/// recover from that and pass the Rust panic string to a Janet Panic.
///
/// This uses the [`catch_unwind`] function, and therefore have the same guarantees as it.
///
/// # Examples
/// ```ignore
/// # #![allow(unconditional_panic)]
/// use janetrs::jtry;
/// # let _client = janetrs::client::JanetClient::init().unwrap();
///
/// let arr = [10; 5];
/// let val_index_2 = jtry!(arr[2]); // Not going to panic
/// let val_index_20 = jtry!(arr[20]); // Index out bounds
/// ```
///
/// [`catch_unwind`]: https://doc.rust-lang.org/std/panic/fn.catch_unwind.html
#[cfg(feature = "std")]
#[cfg_attr(_doc, doc(cfg(feature = "std")))]
#[macro_export]
macro_rules! jtry {
    ($e:expr) => {{
        ::std::panic::catch_unwind(|| $e).unwrap_or_else(|err| {
            if let Some(err) = err.downcast_ref::<String>() {
                $crate::jpanic!("{}", err);
            } else {
                $crate::jpanic!();
            }
        })
    }};
}

/// Like [`assert_eq`], but using [`deep_eq`]` internally instead.
///
/// Unlike the other macros, this use uses the Rust-panic mechanic, because this must be
/// used to assert values in Rust tests, that detects Rust-panics only.
///
/// It is safe to use this macros in janet exposed code, since we are using "C-unwind"
/// extern blocks internally, but it is not interesting to Janet libraries authors when it
/// is a recoverable error, as Janet also uses it's Janet-panics to throw recoverable
/// exception errors.
///
/// [`deep_eq`]: crate::DeepEq::deep_eq
#[macro_export]
macro_rules! assert_deep_eq {
    ($left:expr, $right:expr $(,)?) => {{
        use $crate::DeepEq;
        match (&$left, &$right) {
            (left_val, right_val) => {
                if !(left_val.deep_eq(right_val)) {
                    // The reborrows below are intentional. Without them, the stack slot for the
                    // borrow is initialized even before the values are compared, leading to a
                    // noticeable slow down.
                    $crate::util::assert_deep_inner("==", &*left_val, &*right_val, ::core::option::Option::None);
                }
            }
        }
    }};
    ($left:expr, $right:expr, $($arg:tt)+) => {{
        match (&$left, &$right) {
            (left_val, right_val) => {
                if !(left_val.deep_eq(right_val)) {
                    // The reborrows below are intentional. Without them, the stack slot for the
                    // borrow is initialized even before the values are compared, leading to a
                    // noticeable slow down.
                    $crate::util::assert_deep_inner("==", &*left_val, &*right_val, ::core::option::Option::Some(::core::format_args!($($arg)+)));
                }
            }
        }
    }};
}

/// Like [`assert_ne`], but using [`deep_ne`]` internally instead.
///
/// Unlike the other macros, this use uses the Rust-panic mechanic, because this must be
/// used to assert values in Rust tests, that detects Rust-panics only.
///
/// It is safe to use this macros in janet exposed code, since we are using "C-unwind"
/// extern blocks internally, but it is not interesting to Janet libraries authors when it
/// is a recoverable error, as Janet also uses it's Janet-panics to throw recoverable
/// exception errors.
///
/// [`deep_ne`]: crate::DeepEq::deep_ne
#[macro_export]
macro_rules! assert_deep_ne {
    ($left:expr, $right:expr $(,)?) => {{
        use $crate::DeepEq;
        match (&$left, &$right) {
            (left_val, right_val) => {
                if !(left_val.deep_ne(right_val)) {
                    // The reborrows below are intentional. Without them, the stack slot for the
                    // borrow is initialized even before the values are compared, leading to a
                    // noticeable slow down.
                    $crate::util::assert_deep_inner("!=", &*left_val, &*right_val, ::core::option::Option::None);
                }
            }
        }
    }};
    ($left:expr, $right:expr, $($arg:tt)+) => {{
        match (&$left, &$right) {
            (left_val, right_val) => {
                if !(left_val.deep_ne(right_val)) {
                    // The reborrows below are intentional. Without them, the stack slot for the
                    // borrow is initialized even before the values are compared, leading to a
                    // noticeable slow down.
                    $crate::util::assert_deep_inner("!=", &*left_val, &*right_val, ::core::option::Option::Some(::core::format_args!($($arg)+)));
                }
            }
        }
    }};
}

#[cfg(all(test, any(feature = "amalgation", feature = "link-system")))]
mod tests {
    // use super::*;
    use crate::types::Janet;

    #[test]
    fn tuple0() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;

        let t = tuple![0, 1, 2, 3, true, "hey"];

        assert_eq!(t.len(), 6);
        assert_eq!(t[0], &Janet::integer(0));
        assert_eq!(t[1], &Janet::integer(1));
        assert_eq!(t[2], &Janet::integer(2));
        assert_eq!(t[3], &Janet::integer(3));
        assert_eq!(t[4], &Janet::boolean(true));
        assert_eq!(t[5], &Janet::from("hey"));

        Ok(())
    }

    #[test]
    fn tuple1() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;

        let t = tuple!["123"; 3];

        assert_eq!(t.len(), 3);
        assert_eq!(t[0], &Janet::from("123"));
        assert_eq!(t[1], &Janet::from("123"));
        assert_eq!(t[2], &Janet::from("123"));

        Ok(())
    }

    #[test]
    fn array0() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;

        let arr = array![];
        assert!(arr.is_empty());

        Ok(())
    }

    #[test]
    fn array1() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;

        let arr = array![0; 5];
        assert_eq!(arr.len(), 5);

        assert_eq!(arr[0], &Janet::integer(0));
        assert_eq!(arr[1], &Janet::integer(0));
        assert_eq!(arr[2], &Janet::integer(0));
        assert_eq!(arr[3], &Janet::integer(0));
        assert_eq!(arr[4], &Janet::integer(0));

        Ok(())
    }

    #[test]
    fn array2() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;

        let arr = array![0, 10.0, 15.5, true, "abc"];
        assert_eq!(arr.len(), 5);

        assert_eq!(arr[0], &Janet::integer(0));
        assert_eq!(arr[1], &Janet::number(10.0));
        assert_eq!(arr[2], &Janet::number(15.5));
        assert_eq!(arr[3], &Janet::boolean(true));
        assert_eq!(arr[4], &Janet::from("abc"));

        Ok(())
    }

    #[test]
    fn structs() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;

        let st = structs! {
            1 => "one",
            true => 1,
        };

        assert_eq!(st.len(), 2);
        assert_eq!(st.get(1), Some(&Janet::from("one")));
        assert_eq!(st.get(true), Some(&Janet::integer(1)));

        Ok(())
    }

    #[test]
    fn table() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;

        let table = table! {};
        assert!(table.is_empty());

        let table = table! {
            1 => "one",
            true => 1,
        };

        assert_eq!(table.len(), 2);
        assert_eq!(table.get(1), Some(&Janet::from("one")));
        assert_eq!(table.get(true), Some(&Janet::integer(1)));

        Ok(())
    }

    #[test]
    fn empty() -> Result<(), crate::client::Error> {
        let _client = crate::client::JanetClient::init()?;

        let arr = array![];
        let tup = tuple![];
        let stru = structs! {};
        let tab = table! {};

        assert!(arr.is_empty());
        assert!(tup.is_empty());
        assert!(stru.is_empty());
        assert!(tab.is_empty());

        Ok(())
    }
}
