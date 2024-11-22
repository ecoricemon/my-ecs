/// ref: https://en.wikipedia.org/wiki/Plotting_algorithms_for_the_Mandelbrot_set
use my_ecs::prelude::*;
use std::{array, ops, slice, sync::LazyLock};

const MAX_ITER: u32 = 100;

static PALETTE: LazyLock<[u32; MAX_ITER as usize + 1]> = LazyLock::new(|| {
    let mut colors = array::from_fn(|i| {
        let (r, g, b) = iter_to_rgb(i as u32);
        if is_little_endian() {
            255 << 24 | ((b as u32) << 16) | ((g as u32) << 8) | ((r as u32) << 0)
        } else {
            (r as u32) << 24 | (g as u32) << 16 | (b as u32) << 8 | 255
        }
    });

    // black
    colors[MAX_ITER as usize] = if is_little_endian() { 255 << 24 } else { 255 };

    colors
});

pub(super) fn calc(args: Args, buf: &mut [u8]) {
    assert!(args.width * args.height * 4 <= buf.len() as u32);
    let buf = unsafe { slice::from_raw_parts_mut(buf.as_mut_ptr() as *mut u32, buf.len() / 4) };
    let iter = (0..args.width * args.height).into_par_iter().zip(buf);
    EcsPar(iter).for_each(|(i, pixel)| {
        let x = i % args.width;
        let y = i / args.width;
        let iter = calc_pixel(x, y, args);
        *pixel = PALETTE[iter as usize];
    });
}

fn is_little_endian() -> bool {
    u16::from_ne_bytes([1, 0]) == u16::from_le_bytes([1, 0])
}

fn calc_pixel(x: u32, y: u32, args: Args) -> u32 {
    let c = Complex {
        r: scale(x, args.width, args.x_range.0, args.x_range.1),
        i: scale(y, args.height, args.y_range.0, args.y_range.1),
    };
    let mut z = Complex { r: 0.0, i: 0.0 };
    let mut iter = 0;
    while iter < MAX_ITER && z.norm_sqr() < 4.0 {
        z = z * z + c;
        iter += 1;
    }
    iter
}

fn scale(val: u32, val_limit: u32, low: f64, high: f64) -> f64 {
    (val as f64 / val_limit as f64) * (high - low) + low
}

fn iter_to_rgb(i: u32) -> (u8, u8, u8) {
    let h = scale(i, MAX_ITER, 0.0, 360.0);
    let s = 0.6;
    let v = scale(i, MAX_ITER, 0.0, 1.0);
    hsv_to_rgb(h, s, v)
}

// h: [0, 360), s: [0, 1], v: [0, 1]
fn hsv_to_rgb(h: f64, s: f64, v: f64) -> (u8, u8, u8) {
    let c = v * s;
    let x = c * (1.0 - ((h / 60.0) % 2.0 - 1.0).abs());
    let m = v - c;

    let (r, g, b) = match h as u32 {
        0..=59 => (c, x, 0.0),
        60..=119 => (x, c, 0.0),
        120..=179 => (0.0, c, x),
        180..=239 => (0.0, x, c),
        240..=299 => (x, 0.0, c),
        _ => (c, 0.0, x),
    };

    (
        ((r + m) * 255.0) as u8,
        ((g + m) * 255.0) as u8,
        ((b + m) * 255.0) as u8,
    )
}

#[derive(Clone, Copy)]
pub(super) struct Args {
    width: u32,
    height: u32,
    x_range: (f64, f64),
    y_range: (f64, f64),
}

impl Args {
    pub(super) const fn new() -> Self {
        Self {
            width: 0,
            height: 0,
            x_range: (0.0, 0.0),
            y_range: (0.0, 0.0),
        }
    }

    pub(super) fn set_size(&mut self, width: u32, height: u32) {
        self.width = width;
        self.height = height;
    }

    pub(super) fn set_plot_range(&mut self, x_range: (f64, f64), y_range: (f64, f64)) {
        self.x_range = x_range;
        self.y_range = y_range;
    }
}

#[derive(Clone, Copy)]
struct Complex {
    r: f64,
    i: f64,
}

impl Complex {
    fn norm_sqr(self) -> f64 {
        self.r * self.r + self.i * self.i
    }
}

impl ops::Add for Complex {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            r: self.r + rhs.r,
            i: self.i + rhs.i,
        }
    }
}

impl ops::Mul for Complex {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self {
            r: self.r * rhs.r - self.i * rhs.i,
            i: self.r * rhs.i + self.i * rhs.r,
        }
    }
}
