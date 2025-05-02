use arbitrary_int::prelude::*;

fn test_sum<'a, T, I>(iter: I, expected: T)
where
    T: core::iter::Sum<T> + core::iter::Sum<&'a T> + std::fmt::Debug + Copy + PartialEq + 'a,
    I: IntoIterator<Item = &'a T> + Clone,
{
    // Test with an iterator yielding references
    assert_eq!(iter.clone().into_iter().sum::<T>(), expected);
    // Test with an iterator yielding owned values
    assert_eq!(iter.into_iter().copied().sum::<T>(), expected);
}

#[test]
pub fn sum_unsigned() {
    test_sum(&[u7::new(0); 4], u7::new(0));
    test_sum(&[u7::new(1); 4], u7::new(4));
    test_sum(&[u7::new(2); 4], u7::new(8));
    test_sum(&[u7::new(4); 4], u7::new(16));
    test_sum(&[u7::new(1); 127], u7::new(127));

    test_sum(
        &[u7::new(1), u7::new(2), u7::new(3), u7::new(4)],
        u7::new(10),
    );
}

#[test]
pub fn sum_signed() {
    test_sum(&[i7::new(0); 4], i7::new(0));

    test_sum(&[i7::new(1); 4], i7::new(4));
    test_sum(&[i7::new(-1); 4], i7::new(-4));

    test_sum(&[i7::new(2); 4], i7::new(8));
    test_sum(&[i7::new(-2); 4], i7::new(-8));

    test_sum(&[i7::new(4); 4], i7::new(16));
    test_sum(&[i7::new(-4); 4], i7::new(-16));

    test_sum(&[i7::new(1); 63], i7::new(63));
    test_sum(&[i7::new(-1); 64], i7::new(-64));

    test_sum(
        &[i7::new(1), i7::new(2), i7::new(3), i7::new(4)],
        i7::new(10),
    );

    test_sum(
        &[i7::new(-1), i7::new(-2), i7::new(-3), i7::new(-4)],
        i7::new(-10),
    );

    test_sum(
        &[i7::new(1), i7::new(-2), i7::new(3), i7::new(-4)],
        i7::new(-2),
    );
}

#[cfg(not(debug_assertions))]
#[test]
pub fn sum_overflow_wraps_unsigned() {
    test_sum(&[u7::new(1); 128], u7::new(0));
    test_sum(&[u7::new(8); 16], u7::new(0));
    test_sum(&[u7::new(9); 16], u7::new(16));
}

#[cfg(not(debug_assertions))]
#[test]
pub fn sum_overflow_wraps_signed() {
    test_sum(&[i7::new(1); 64], i7::new(-64));
    test_sum(&[i7::new(-1); 65], i7::new(63));

    test_sum(&[i7::new(8); 8], i7::new(-64));
    test_sum(&[i7::new(-8); 9], i7::new(56));
}

#[cfg(debug_assertions)]
#[test]
#[should_panic]
pub fn sum_overflow_panic_unsigned() {
    let _ = [u7::new(1); 128].iter().sum::<u7>();
}

#[cfg(debug_assertions)]
#[test]
#[should_panic]
pub fn sum_overflow_upper_panic_signed() {
    let _ = [i7::new(1); 64].iter().sum::<i7>();
}

#[cfg(debug_assertions)]
#[test]
#[should_panic]
pub fn sum_overflow_lower_panic_signed() {
    let _ = [i7::new(-1); 65].iter().sum::<i7>();
}
