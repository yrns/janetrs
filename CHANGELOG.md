# Changelog

All notable changes to the library should be put here

## Unreleased

- **Breaking** Refactor: Rename `JanetArgs::get_unwrapped` to `JanetArgs::try_get`
- **Breaking** Refactor: Rename `JanetArgs::get_panic` to `JanetArgs::get_or_panic`
- **Breaking** Refactor: Turn `JanetConversionError` into a enum
- **Breaking** Refactor: Refactor `CFunOptions` to use `CStr` instead of `str`
- Feat: Add `Janet::dynamic_from_cstr` constructor
- Feat: Add `JanetArgs::get_value` and `JanetArgs::get_tagged` trait methods
- Feat: Add `JanetArgs::get_or_default` trait method
- Feat: Add `JanetArgs::get_or_else` trait method
- Feat: Add `JanetArgs::get_matches` and `JanetArgs::get_tagged_matches`
- Feat: Add `JanetArray::pop_if` method
- Feat: Add `JanetArray::push_within_capacity` method
- Feat: Add `JanetArray::extract_if` method
- Feat: Add `JanetArray::split_off` method
- Feat: Add `JanetArray::swap_unchecked` method
- Feat: Add `JanetArray::retain` and `JanetArray::retain_mut` methods
- Feat: Add `JanetArray::get_range`, `JanetArray::get_range_mut`, `JanetArray::get_range_unchecked` and , `JanetArray::get_range_unchecked_mut` methods
- Feat: Add `JanetArray::weak` and `JanetArray::weak_with_capacity` constructors
- Feat: Add `JanetBuffer::push_janet_string` method
- Feat: Add `assert_deep_eq!` macro
- Feat: Add `assert_deep_ne!` macro
- Feat: Add `env::set_dynamic` function
- Feat: Implement `JanetArgs` for `[Janet; N]`
- Perf: Avoid allocation in `Janet::dynamic` if the passed argument is already null terminated
- Refactor: Use default implementation on `JanetArgs` trait for most methods
- Refactor: Simplify `jpanic!` macro
- Refactor: janetrs_macros 0.7.0 — Update `syn` crate to 2.0
- Fix: janetrs_macros 0.7.1 — Fix `janet_fn` attribute macro not generating Janet docstring correctly

## 0.7.0

- **BREAKING:** Refactor: Rename `JanetArgs::get_unwraped` to `JanetArgs::get_unwrapped`
- **BREAKING:** Refactor: Rename `FileFlags::is_serializeble` to `FileFlags::is_serializable`
- Feat: Add `JanetAbstract::take` method
- Feat: Add `JanetAbstract::into_inner` method
- Feat: Add `JanetTuple::{sourcemap, set_sourcemap}` methods
- Refactor: Simplify `JanetAbstract::new`
- Fix: Fix undefined behavior in `JanetArray::as_{ref,mut}` methods
- Fix: Fix clippy lints
- docs: Update a few documentation comments

## 0.6.0

- **BREAKING:** Feat: Conditionally expose `JanetFile` "piped" flag (PIPED was removed in Janet 1.22.0)
- **BREAKING:** Refactor: Changed definition of `IsJanetAbstract` trait
- **BREAKING:** Refactor: Changed the return type of `JanetAbstract::get{_mut, _unchecked, _unchecked_mut}`
- **BREAKING:** Feat: Move everything possible to `C-unwind`
- **BREAKING:** Up Minimum Rust version to 1.71.0
- Feat: Add additional implementation of `From` implementation for
    `JanetBuffer`, `JanetArray` and `JanetTable`
- Feat: Expose `JanetBuffer` methods that use `CStr` on no_std environment
- Feat: Expose `JanetFile` "update" flag
- Feat: Expose more of the String-like types API on no_std environment
- Feat: Add method `can_resume` for `JanetFiber`
- Refactor: Simplify the `tuple!` and `structs!` macros
- Refactor: Simplify a few `PartialEq` implementations
- Refactor: Simplify `JanetStruct` implementation of `Clone`
- Refactor: Adapt lifetimes to changes on bstr crate
- Refactor: Modernize format strings
- Fix: Fix compilation when `unicode` feature os off
- Fix: Fix `check_mut_ref` on `janet_fn` attribute macro
- Fix: Fix linking on non x86_64 targets
- Docs: Improve documentation flags
- Docs: Simplify links
- CI: Many CI improvements

## 0.5.0

- **BREAKING:** Rename `JanetClient::with_default_env` ->
    `JanetClient::load_env_default`
- **BREAKING:** Rename `JanetClient::with_replacements` ->
    `JanetClient::load_env_replacements`
- Add `catch` arg to `janet_fn` attribute macro that adds code to catch Rust
    panics and transform them into Janet panics
- Add two new functions to initialize `JanetClient`:
    `JanetClient::init_with_replacements` and `JanetClient::init_with_default_env`
- Add `JanetFile::temp`
- Fix `tuple::{IntoIter, Iter}::size_hint` implementation
- Migrate to Rust 2021

## 0.4.1

- Add the trait `JanetArgs` that extend functionality of `[Janet]` used in Rust
    defined Janet functions
- Add the trait `JanetTypeName` that defines the name of the types displayed
    janet messages
- Add `bad_slot!` macro to shorten and help developing Rust defined Janet
    functions

## 0.4.0

- **BREAKING:** Make `JanetGc::collect` an unsafe function
- **BREAKING:** Remove `JanetEnvironment::add_def_with_doc`,
    `JanetEnvironment::add_var_with_doc`, `JanetEnvironment::add_c_func_with_doc`
    and `JanetClient` functions with the same names
- **BREAKING:** Remove `util::def`, `util::var`, `util::c_func`
- **BREAKING:** Rename `JanetEnviornment::add_c_func` to
    `JanetEnvironment::add_c_fn` `JanetEnvironment::add_c_fn`
- Add `JanetFile` type
- Add `JanetRng` type
- Add `JanetTable::try_insert` and related error type
- Add `DefOptions`, `VarOptions`, `CFunOptions` to interact with the Janet
    environment
- Add `declare_janet_mod` macro to generate the machinery that Janet requires do
    create a Janet native module
  - It satisfies the same purpose as `janet_mod`, but it can get the
        documentation string from the function doc-comments and, for Janet versions
        above 1.17.0, it also add source map information for Janet
- Add `janet_abstract::register` function to register an abstract type.
- Add option to `janet_fn` attribute macro to include arity checks
- Add `Janet::unwrap_or`, `Janet::unwrap_or_else` and `Janet::unwrap_or_default`
- Implement `Display` for `TaggedJanet` and defer the `Janet` display
    implementation to that
- Improve error report of attribute macros
- Refactor the `janet_fn` attribute macro parameter parsing
- Refactor the `JanetEnvironment` and `JanetClient` API
- `janet_fn` now emits code with the function documentation and source map
    information as constants to be used by another macro `declare_janet_mod`
- Fix compilation when no_std and with unicode feature enabled

## 0.3.2

- Add `JanetTable::clear` in Janet version below 1.10.1

## 0.3.1

### Fixes

- Fix compiler complaining about alloc crate when `std` feature is active while
    using a macro

## 0.3.0

### Changes

- **BREAKING:** Rename `as_ptr_mut` to `as_mut_ptr`
- **BREAKING:** Rename `as_raw_mut` to `as_mut_raw`
- **BREAKING:** `JanetAbstract::new` now takes a value
- **BREAKING:** Make the `janetrs::types` module private and export everything
    inside it in the upper module
- **BREAKING:** Modify `From<&str>` for `Janet` to return a Janet keyword if
    `&str` starts with `:`
- **BREAKING:** Modify `CallError::stacktrace` function.
- Add ability to change some Janet behavior using the `amalgation` feature using
    environment variables
- Add `DeepEq` trait
- Add `dedup`, `dedup_by` and `dedup_by_key` for `JanetArray`
- Add `get_unchecked` and `get_unchecked_mut` for `JanetArray`
- Add `get_unchecked` for `JanetTuple`
- Add `get_method` and `has_method` to `Janet`
- Add `prototype`, `set_prototype` and `with_prototype` methods for `JanetTable`
- Add `get_key_value_proto{_mut}` and `get_proto{_mut}` methods for `JanetTable`
- Add `JanetGc` and `JanetGcLockGuard` types to access some Janet GC operations
- Add `JanetGcRootGuard` and the functions `JanetGc::root` and `JanetGc::unroot`
    to root a Janet object to the GC
- Add functions to get reference to a `JanetAbstract` data safely
- Add `JanetAbstract::is`
- Add `Janet::int64`
- Add `Janet::uint64`
- Create `janetrs_version` crate to use as common code used by `janet_version`
    macro and `janetrs::util` module
- Implement `DeepEq` for most types
- Implement `Debug` and `Display` for `JanetSymbol`
- Implement `Debug` and `Display` for `JanetKeyword`
- Implement `IsJanetAbstract` for i64 and u64
- Implement `PartialEq`, `Eq`, `PartialOrd` and `Ord` for `JanetAbstract`
- Implement `PartialEq`, `Eq`, `PartialOrd` and `Ord` for `JanetFunction`
- Implement `PartialOrd` and `Ord` for `JanetFiber`
- Implement `From` and `TryFrom` between `i64` and `Janet`
- Implement `From` and `TryFrom` between `u64` and `Janet`
- Include "@" before the debug representation of Janet mutable types
- Refactor `Debug` implementation of `Janet` type
- Refactor `Display` implementation of `Janet` type
- Refactor some implementations of `From` and `TryFrom` related to `Janet` type
- Reduce code duplication in `JanetAbstract` functions

### Fixes

- **BREAKING:** Change definition of `IsJanetAbstract` trait
- Expose `jcatch!` macro only if Janet version supports the underlying mechanism
- Fix some clippy lints
- Fix compilation on no_std environment.
- Make some functions const if using a recent enough Rust version

## 0.2.0

### Changes

- **BREAKING:** Add `Janet::unwrap` that return `TaggedJanet`
- **BREAKING:** Rename `Janet::unwrap` to `Janet::try_unwrap`
- Add `JanetEnvironment` type
- Add `janet_version`/`cjvg` attribute macros for conditional compilation of
    Janet versions
- Add split iterator for `JanetBuffer` and `JanetString`
- Add `jcatch` declarative macro
- Refactor `JanetClient` in terms of `JanetEnvironment`
- Implement `TaggetJanet` type
- Implement `JanetAbstract` type
- Implement `JanetPointer` type
- Implement `JanetTryState` for Janet "exception" recovery
- Implement `PartialEq`, `Eq`, `PartialOrd` and `Ord` for several Janet types
- `janet_fn` now can accept a parameter `check_mut_ref` that checks if the
    function received more than one `*mut` pointer as parameter (not the default
    because Janet types are like interior mutability types)
- More methods added for several types and improvements to the docs

### Bug Fixes

- Fix change in behavior in `JanetBuffer` since Janet 1.13.0 and also enforce
    that on earlier versions
- Fix UB in `JanetTryState` safe API
- Fix `Default` implementation for `JanetEnvironment`
- Fix `JanetTuple` implementation of `PartialEq` to match the Janet
    implementation

## 0.1.2

### Changes

- Implement Display for `JanetType`

### Bug Fixes

- Fix `From<char>` for `JanetString` not considering that char can be
    represented with more than 1 byte in UTF-8

## 0.1.0 ~ 0.1.1

### Changes

- Basic Janet types manipulation
- A way to run the Janet runtime
- Macros to create Janet collections
- Macro to cause Janet Panics
- Macro to catch Rust Panic and transform to Janet Panic
