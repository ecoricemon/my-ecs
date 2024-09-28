#[macro_export]
macro_rules! type_name {
    ($e:expr) => {{
        fn name<T: ?Sized>(_t: &T) -> &str {
            let name = std::any::type_name::<T>();
            if matches!(name.chars().next(), Some(c) if c == '&') {
                &name[1..]
            } else {
                name
            }
        }
        name(&$e)
    }};
}

#[macro_export]
macro_rules! panic_if_called_twice {
    ($($msg: tt)*) => {
        use std::sync::atomic::{AtomicU8, Ordering};
        static mut ONCE: AtomicU8 = AtomicU8::new(0);
        let old = unsafe { ONCE.fetch_add(1, Ordering::Relaxed) };
        assert!(old == 0, $($msg)*);
    };
}

#[macro_export]
macro_rules! debug_format {
    ($($t:tt)*) => {{
        #[cfg(debug_assertions)]
        {
            format!($($t)*)
        }
        #[cfg(not(debug_assertions))]
        {
            String::new()
        }
    }};
}

/// Implements [`From`] and [`TryFrom`] for the enum.
///
/// # Examples
///
/// ```
/// # use my_ecs::impl_from_for_enum;
///
/// struct AA;
/// struct BB;
/// enum MyEnum {
///     A(AA),
///     B(BB),
/// }
///
/// impl_from_for_enum!(MyEnum, A, AA);
/// impl_from_for_enum!(MyEnum, B, BB);
/// ```
#[macro_export]
macro_rules! impl_from_for_enum {
    ($enum:ident, $var_outer:ident, $var_inner:ty) => {
        impl From<$var_inner> for $enum {
            fn from(value: $var_inner) -> Self {
                Self::$var_outer(value)
            }
        }

        impl TryFrom<$enum> for $var_inner {
            type Error = ();

            fn try_from(value: $enum) -> Result<Self, Self::Error> {
                if let $enum::$var_outer(inner) = value {
                    Ok(inner)
                } else {
                    Err(())
                }
            }
        }

        impl<'a> TryFrom<&'a mut $enum> for &'a mut $var_inner {
            type Error = ();

            fn try_from(value: &'a mut $enum) -> Result<Self, Self::Error> {
                if let $enum::$var_outer(inner) = value {
                    Ok(inner)
                } else {
                    Err(())
                }
            }
        }

        impl<'a> TryFrom<&'a $enum> for &'a $var_inner {
            type Error = ();

            fn try_from(value: &'a $enum) -> Result<Self, Self::Error> {
                if let $enum::$var_outer(inner) = value {
                    Ok(inner)
                } else {
                    Err(())
                }
            }
        }
    };
}

#[macro_export]
macro_rules! log {
    ($($t:tt)*) => {
        #[cfg(target_arch = "wasm32")]
        {
            $crate::util::macros::console_log(format!($($t)*))
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            println!($($t)*)
        }
    }
}

#[cfg(target_arch = "wasm32")]
pub fn console_log(s: String) {
    web_sys::console::log_1(&s.into());
}

/// Sometimes, we want exiting early in a function due to deeply nested statements.
/// In that case, you can use this macro to hide boilerplate code.
//
// TODO: I heard Rust made something like this...
#[macro_export]
macro_rules! unwrap_or {
    ($rhs:expr) => {
        if let Some(x) = $rhs {
            x
        } else {
            return;
        }
    };
    ($rhs:expr => $($else:tt)*) => {
        if let Some(x) = $rhs {
            x
        } else {
            $($else)*
        }
    };
}
