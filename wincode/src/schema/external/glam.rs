use {
    crate::{
        config::ConfigCore,
        error::{ReadResult, WriteResult},
        io::{Reader, Writer},
        schema::{SchemaRead, SchemaWrite, TypeMeta},
    },
    core::mem::MaybeUninit,
};

macro_rules! impl_glam_array_type {
    ($ty:ty, $wire:ty, $to_wire:expr, $from_wire:expr) => {
        unsafe impl<'de, C: ConfigCore> SchemaRead<'de, C> for $ty {
            type Dst = $ty;

            const TYPE_META: TypeMeta =
                <$wire as SchemaRead<'de, C>>::TYPE_META.keep_zero_copy(false);

            #[inline]
            fn read(reader: impl Reader<'de>, dst: &mut MaybeUninit<Self::Dst>) -> ReadResult<()> {
                let wire = <$wire as SchemaRead<'de, C>>::get(reader)?;
                dst.write(($from_wire)(wire));
                Ok(())
            }
        }

        unsafe impl<C: ConfigCore> SchemaWrite<C> for $ty {
            type Src = $ty;

            const TYPE_META: TypeMeta = <$wire as SchemaWrite<C>>::TYPE_META.keep_zero_copy(false);

            #[inline]
            fn size_of(src: &Self::Src) -> WriteResult<usize> {
                if let TypeMeta::Static { size, .. } = <Self as SchemaWrite<C>>::TYPE_META {
                    return Ok(size);
                }
                let wire = ($to_wire)(src);
                <$wire as SchemaWrite<C>>::size_of(&wire)
            }

            #[inline]
            fn write(writer: impl Writer, src: &Self::Src) -> WriteResult<()> {
                let wire = ($to_wire)(src);
                <$wire as SchemaWrite<C>>::write(writer, &wire)
            }
        }
    };
}

macro_rules! impl_glam_vec_types {
    ($scalar:ty, $vec2:ty, $vec3:ty, $vec4:ty) => {
        impl_glam_array_type!($vec2, [$scalar; 2], <$vec2>::to_array, <$vec2>::from_array);
        impl_glam_array_type!($vec3, [$scalar; 3], <$vec3>::to_array, <$vec3>::from_array);
        impl_glam_array_type!($vec4, [$scalar; 4], <$vec4>::to_array, <$vec4>::from_array);
    };
}

macro_rules! impl_glam_float_types {
    ($scalar:ty, $vec2:ty, $vec3:ty, $vec4:ty, $quat:ty, $mat2:ty, $mat3:ty, $mat4:ty, $affine2:ty, $affine3:ty) => {
        impl_glam_vec_types!($scalar, $vec2, $vec3, $vec4);
        impl_glam_array_type!($quat, [$scalar; 4], <$quat>::to_array, <$quat>::from_array);
        impl_glam_array_type!($mat2, [$scalar; 4], <$mat2>::to_cols_array, |wire| {
            <$mat2>::from_cols_array(&wire)
        });
        impl_glam_array_type!($mat3, [$scalar; 9], <$mat3>::to_cols_array, |wire| {
            <$mat3>::from_cols_array(&wire)
        });
        impl_glam_array_type!($mat4, [$scalar; 16], <$mat4>::to_cols_array, |wire| {
            <$mat4>::from_cols_array(&wire)
        });
        impl_glam_array_type!($affine2, [$scalar; 6], <$affine2>::to_cols_array, |wire| {
            <$affine2>::from_cols_array(&wire)
        });
        impl_glam_array_type!($affine3, [$scalar; 12], <$affine3>::to_cols_array, |wire| {
            <$affine3>::from_cols_array(&wire)
        });
    };
}

impl_glam_float_types!(
    f32,
    ::glam::Vec2,
    ::glam::Vec3,
    ::glam::Vec4,
    ::glam::Quat,
    ::glam::Mat2,
    ::glam::Mat3,
    ::glam::Mat4,
    ::glam::Affine2,
    ::glam::Affine3
);
impl_glam_array_type!(
    ::glam::Vec3A,
    [f32; 3],
    ::glam::Vec3A::to_array,
    ::glam::Vec3A::from_array
);
impl_glam_array_type!(
    ::glam::Mat3A,
    [f32; 9],
    ::glam::Mat3A::to_cols_array,
    |wire| ::glam::Mat3A::from_cols_array(&wire)
);
impl_glam_array_type!(
    ::glam::Affine3A,
    [f32; 12],
    ::glam::Affine3A::to_cols_array,
    |wire| ::glam::Affine3A::from_cols_array(&wire)
);

impl_glam_float_types!(
    f64,
    ::glam::DVec2,
    ::glam::DVec3,
    ::glam::DVec4,
    ::glam::DQuat,
    ::glam::DMat2,
    ::glam::DMat3,
    ::glam::DMat4,
    ::glam::DAffine2,
    ::glam::DAffine3
);

impl_glam_vec_types!(i8, ::glam::I8Vec2, ::glam::I8Vec3, ::glam::I8Vec4);
impl_glam_vec_types!(i16, ::glam::I16Vec2, ::glam::I16Vec3, ::glam::I16Vec4);
impl_glam_vec_types!(i32, ::glam::IVec2, ::glam::IVec3, ::glam::IVec4);
impl_glam_vec_types!(i64, ::glam::I64Vec2, ::glam::I64Vec3, ::glam::I64Vec4);
impl_glam_vec_types!(
    isize,
    ::glam::ISizeVec2,
    ::glam::ISizeVec3,
    ::glam::ISizeVec4
);
impl_glam_vec_types!(u8, ::glam::U8Vec2, ::glam::U8Vec3, ::glam::U8Vec4);
impl_glam_vec_types!(u16, ::glam::U16Vec2, ::glam::U16Vec3, ::glam::U16Vec4);
impl_glam_vec_types!(u32, ::glam::UVec2, ::glam::UVec3, ::glam::UVec4);
impl_glam_vec_types!(u64, ::glam::U64Vec2, ::glam::U64Vec3, ::glam::U64Vec4);
impl_glam_vec_types!(
    usize,
    ::glam::USizeVec2,
    ::glam::USizeVec3,
    ::glam::USizeVec4
);

impl_glam_array_type!(
    ::glam::BVec2,
    [bool; 2],
    |value: &::glam::BVec2| [value.x, value.y],
    ::glam::BVec2::from_array
);
impl_glam_array_type!(
    ::glam::BVec3,
    [bool; 3],
    |value: &::glam::BVec3| [value.x, value.y, value.z],
    ::glam::BVec3::from_array
);
impl_glam_array_type!(
    ::glam::BVec4,
    [bool; 4],
    |value: &::glam::BVec4| [value.x, value.y, value.z, value.w],
    ::glam::BVec4::from_array
);
impl_glam_array_type!(
    ::glam::BVec3A,
    [bool; 3],
    |value: &::glam::BVec3A| [value.test(0), value.test(1), value.test(2)],
    ::glam::BVec3A::from_array
);
// BVec4A is intentionally omitted until glam's serde representation preserves all four lanes.

#[cfg(all(test, feature = "alloc"))]
mod tests {
    use {
        crate::{
            SchemaRead, SchemaWrite, TypeMeta, config::DefaultConfig, deserialize, serialize,
            serialized_size,
        },
        alloc::vec,
        core::fmt::Debug,
        serde::{Serialize, de::DeserializeOwned},
    };

    fn assert_bincode_compat<T>(value: T)
    where
        T: Clone
            + Debug
            + PartialEq
            + Serialize
            + DeserializeOwned
            + SchemaWrite<DefaultConfig, Src = T>
            + for<'de> SchemaRead<'de, DefaultConfig, Dst = T>,
    {
        let wincode_bytes = serialize(&value).unwrap();
        let bincode_bytes = bincode::serialize(&value).unwrap();
        assert_eq!(bincode_bytes, wincode_bytes);
        assert_eq!(
            serialized_size(&value).unwrap() as usize,
            wincode_bytes.len()
        );

        let wincode_deserialized = deserialize::<T>(&wincode_bytes).unwrap();
        let bincode_deserialized = bincode::deserialize::<T>(&wincode_bytes).unwrap();
        let bincode_bytes_deserialized = deserialize::<T>(&bincode_bytes).unwrap();
        assert_eq!(value, wincode_deserialized);
        assert_eq!(value, bincode_deserialized);
        assert_eq!(value, bincode_bytes_deserialized);
    }

    #[test]
    fn test_glam_f32_types_match_bincode() {
        assert_bincode_compat(::glam::Vec2::new(1.0, -2.5));
        assert_bincode_compat(::glam::Vec3::new(1.0, -2.5, 3.25));
        assert_bincode_compat(::glam::Vec3A::new(1.0, -2.5, 3.25));
        assert_bincode_compat(::glam::Vec4::new(1.0, -2.5, 3.25, 4.5));
        assert_bincode_compat(::glam::Quat::from_array([0.0, 0.25, -0.5, 1.0]));
        assert_bincode_compat(::glam::Mat2::from_cols_array(&[1.0, 2.0, 3.0, 4.0]));
        assert_bincode_compat(::glam::Mat3::from_cols_array(&[
            1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0,
        ]));
        assert_bincode_compat(::glam::Mat3A::from_cols_array(&[
            1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0,
        ]));
        assert_bincode_compat(::glam::Mat4::from_cols_array(&[
            1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0, 11.0, 12.0, 13.0, 14.0, 15.0, 16.0,
        ]));
        assert_bincode_compat(::glam::Affine2::from_cols_array(&[
            1.0, 2.0, 3.0, 4.0, 5.0, 6.0,
        ]));
        assert_bincode_compat(::glam::Affine3::from_cols_array(&[
            1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0, 11.0, 12.0,
        ]));
        assert_bincode_compat(::glam::Affine3A::from_cols_array(&[
            1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0, 11.0, 12.0,
        ]));
    }

    #[test]
    fn test_glam_f64_types_match_bincode() {
        assert_bincode_compat(::glam::DVec2::new(1.0, -2.5));
        assert_bincode_compat(::glam::DVec3::new(1.0, -2.5, 3.25));
        assert_bincode_compat(::glam::DVec4::new(1.0, -2.5, 3.25, 4.5));
        assert_bincode_compat(::glam::DQuat::from_array([0.0, 0.25, -0.5, 1.0]));
        assert_bincode_compat(::glam::DMat2::from_cols_array(&[1.0, 2.0, 3.0, 4.0]));
        assert_bincode_compat(::glam::DMat3::from_cols_array(&[
            1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0,
        ]));
        assert_bincode_compat(::glam::DMat4::from_cols_array(&[
            1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0, 11.0, 12.0, 13.0, 14.0, 15.0, 16.0,
        ]));
        assert_bincode_compat(::glam::DAffine2::from_cols_array(&[
            1.0, 2.0, 3.0, 4.0, 5.0, 6.0,
        ]));
        assert_bincode_compat(::glam::DAffine3::from_cols_array(&[
            1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0, 11.0, 12.0,
        ]));
    }

    #[test]
    fn test_glam_integer_types_match_bincode() {
        assert_bincode_compat(::glam::I8Vec2::new(-1, 2));
        assert_bincode_compat(::glam::I8Vec3::new(-1, 2, -3));
        assert_bincode_compat(::glam::I8Vec4::new(-1, 2, -3, 4));
        assert_bincode_compat(::glam::I16Vec2::new(-1, 2));
        assert_bincode_compat(::glam::I16Vec3::new(-1, 2, -3));
        assert_bincode_compat(::glam::I16Vec4::new(-1, 2, -3, 4));
        assert_bincode_compat(::glam::IVec2::new(-1, 2));
        assert_bincode_compat(::glam::IVec3::new(-1, 2, -3));
        assert_bincode_compat(::glam::IVec4::new(-1, 2, -3, 4));
        assert_bincode_compat(::glam::I64Vec2::new(-1, 2));
        assert_bincode_compat(::glam::I64Vec3::new(-1, 2, -3));
        assert_bincode_compat(::glam::I64Vec4::new(-1, 2, -3, 4));
        assert_bincode_compat(::glam::ISizeVec2::new(-1, 2));
        assert_bincode_compat(::glam::ISizeVec3::new(-1, 2, -3));
        assert_bincode_compat(::glam::ISizeVec4::new(-1, 2, -3, 4));
        assert_bincode_compat(::glam::U8Vec2::new(1, 2));
        assert_bincode_compat(::glam::U8Vec3::new(1, 2, 3));
        assert_bincode_compat(::glam::U8Vec4::new(1, 2, 3, 4));
        assert_bincode_compat(::glam::U16Vec2::new(1, 2));
        assert_bincode_compat(::glam::U16Vec3::new(1, 2, 3));
        assert_bincode_compat(::glam::U16Vec4::new(1, 2, 3, 4));
        assert_bincode_compat(::glam::UVec2::new(1, 2));
        assert_bincode_compat(::glam::UVec3::new(1, 2, 3));
        assert_bincode_compat(::glam::UVec4::new(1, 2, 3, 4));
        assert_bincode_compat(::glam::U64Vec2::new(1, 2));
        assert_bincode_compat(::glam::U64Vec3::new(1, 2, 3));
        assert_bincode_compat(::glam::U64Vec4::new(1, 2, 3, 4));
        assert_bincode_compat(::glam::USizeVec2::new(1, 2));
        assert_bincode_compat(::glam::USizeVec3::new(1, 2, 3));
        assert_bincode_compat(::glam::USizeVec4::new(1, 2, 3, 4));
    }

    #[test]
    fn test_glam_bool_types_match_bincode() {
        assert_bincode_compat(::glam::BVec2::new(true, false));
        assert_bincode_compat(::glam::BVec3::new(true, false, true));
        assert_bincode_compat(::glam::BVec4::new(true, false, true, false));
        assert_bincode_compat(::glam::BVec3A::new(true, false, true));
    }

    #[test]
    fn test_glam_sequences_match_bincode() {
        assert_bincode_compat(vec![
            ::glam::Vec3A::new(1.0, 2.0, 3.0),
            ::glam::Vec3A::new(4.0, 5.0, 6.0),
        ]);
        assert_bincode_compat(vec![
            ::glam::Mat4::from_cols_array(&[
                1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0, 10.0, 11.0, 12.0, 13.0, 14.0, 15.0,
                16.0,
            ]),
            ::glam::Mat4::IDENTITY,
        ]);
        assert_bincode_compat(vec![
            ::glam::BVec3A::new(true, false, true),
            ::glam::BVec3A::new(false, true, false),
        ]);
    }

    #[test]
    fn test_glam_types_are_static_but_not_zero_copy() {
        assert_eq!(
            <::glam::Vec3A as SchemaWrite<DefaultConfig>>::TYPE_META,
            TypeMeta::Static {
                size: size_of::<[f32; 3]>(),
                zero_copy: false,
            }
        );
        assert_eq!(
            <::glam::Mat4 as SchemaWrite<DefaultConfig>>::TYPE_META,
            TypeMeta::Static {
                size: size_of::<[f32; 16]>(),
                zero_copy: false,
            }
        );
        assert_eq!(
            <::glam::BVec3A as SchemaWrite<DefaultConfig>>::TYPE_META,
            TypeMeta::Static {
                size: size_of::<[bool; 3]>(),
                zero_copy: false,
            }
        );
    }
}
