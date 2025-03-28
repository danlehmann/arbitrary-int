#![no_main]
#![allow(warnings)]

use arbitrary_int::*;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: Numbers| {
    // We only test the arbitrary implementation can yield values without panicking
    let _ = data;
});

#[derive(Copy, Clone, Debug, arbitrary::Arbitrary)]
enum Numbers {
    U8(StorageU8),
    I8(StorageI8),
    U16(StorageU16),
    I16(StorageI16),
    U32(StorageU32),
    I32(StorageI32),
    U64(StorageU64),
    I64(StorageI64),
    U128(StorageU128),
    I128(StorageI128),
}

seq_macro::seq!(
    N in 1..=7 {
        #[derive(Copy, Clone, Debug, arbitrary::Arbitrary)]
        enum StorageU8 {
            #(
                U~N(u~N),
            )*
        }
    }
);

seq_macro::seq!(
    N in 1..=7 {
        #[derive(Copy, Clone, Debug, arbitrary::Arbitrary)]
        enum StorageI8 {
            #(
                I~N(i~N),
            )*
        }
    }
);

seq_macro::seq!(
    N in 7..=15 {
        #[derive(Copy, Clone, Debug, arbitrary::Arbitrary)]
        enum StorageU16 {
            #(
                U~N(u~N),
            )*
        }
    }
);

seq_macro::seq!(
    N in 7..=15 {
        #[derive(Copy, Clone, Debug, arbitrary::Arbitrary)]
        enum StorageI16 {
            #(
                I~N(i~N),
            )*
        }
    }
);

seq_macro::seq!(
    N in 15..=31 {
        #[derive(Copy, Clone, Debug, arbitrary::Arbitrary)]
        enum StorageU32 {
            #(
                U~N(u~N),
            )*
        }
    }
);

seq_macro::seq!(
    N in 15..=31 {
        #[derive(Copy, Clone, Debug, arbitrary::Arbitrary)]
        enum StorageI32 {
            #(
                I~N(i~N),
            )*
        }
    }
);

seq_macro::seq!(
    N in 31..=63 {
        #[derive(Copy, Clone, Debug, arbitrary::Arbitrary)]
        enum StorageU64 {
            #(
                U~N(u~N),
            )*
        }
    }
);

seq_macro::seq!(
    N in 31..=63 {
        #[derive(Copy, Clone, Debug, arbitrary::Arbitrary)]
        enum StorageI64 {
            #(
                I~N(i~N),
            )*
        }
    }
);

seq_macro::seq!(
    N in 63..=127 {
        #[derive(Copy, Clone, Debug, arbitrary::Arbitrary)]
        enum StorageU128 {
            #(
                U~N(u~N),
            )*
        }
    }
);

seq_macro::seq!(
    N in 63..=127 {
        #[derive(Copy, Clone, Debug, arbitrary::Arbitrary)]
        enum StorageI128 {
            #(
                I~N(i~N),
            )*
        }
    }
);
