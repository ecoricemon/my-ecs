use crate::ds::prelude::*;

/// Granular data such as position, speed, and something like that.
pub trait Component: 'static {
    /// Provided.
    fn key() -> ComponentKey {
        ComponentKey::of::<Self>()
    }
}

pub trait Components: 'static {
    type Output: IntoIterator<Item = ComponentKey>;

    fn keys() -> Self::Output;
}

#[macro_export]
macro_rules! impl_components {
    ($n:expr, $($i:expr),*) => {const _: () = {
        #[allow(unused_imports)]
        use $crate::ecs::ent::component::{Component, Components, ComponentKey};
        use paste::paste;

        paste! {
            #[allow(unused_parens)]
            impl<$([<A $i>]: Component),*> Components for ( $([<A $i>]),* ) {
                type Output = [ComponentKey; $n];

                fn keys() -> Self::Output {
                    [
                        $([<A $i>]::key()),*
                    ]
                }
            }
        }
    };};
}
impl_components!(0,);
impl_components!(1, 0);
impl_components!(2, 0, 1);
impl_components!(3, 0, 1, 2);
impl_components!(4, 0, 1, 2, 3);
impl_components!(5, 0, 1, 2, 3, 4);
impl_components!(6, 0, 1, 2, 3, 4, 5);
impl_components!(7, 0, 1, 2, 3, 4, 5, 6);
impl_components!(8, 0, 1, 2, 3, 4, 5, 6, 7);

/// [`TypeId`](std::any::TypeId) of a component.
pub type ComponentKey = ATypeId<ComponentKey_>;
pub struct ComponentKey_;
