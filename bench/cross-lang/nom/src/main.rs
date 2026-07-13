use nom::{
    branch::alt,
    bytes::complete::{tag, take_while},
    character::complete::multispace0,
    combinator::recognize,
    multi::fold_many0,
    sequence::{delimited, preceded, separated_pair, tuple},
    IResult,
};
use std::hint::black_box;
use std::time::Instant;

// ---------------------------------------------------------------------------
// Whitespace
// ---------------------------------------------------------------------------

#[inline]
fn ws(input: &[u8]) -> IResult<&[u8], &[u8]> {
    multispace0(input)
}

// ---------------------------------------------------------------------------
// String: naive — `"` then bytes up to next `"` (no escape handling needed)
// ---------------------------------------------------------------------------

#[inline]
fn json_string(input: &[u8]) -> IResult<&[u8], &[u8]> {
    let (input, _) = tag(b"\"" as &[u8])(input)?;
    let (input, body) = take_while(|b| b != b'"')(input)?;
    let (input, _) = tag(b"\"" as &[u8])(input)?;
    Ok((input, body))
}

// ---------------------------------------------------------------------------
// Number: optional minus, digits, optional fraction/exponent
// ---------------------------------------------------------------------------

#[inline]
fn is_digit(b: u8) -> bool {
    b.is_ascii_digit()
}

fn json_number(input: &[u8]) -> IResult<&[u8], &[u8]> {
    recognize(tuple((
        // optional minus
        nom::combinator::opt(tag(b"-" as &[u8])),
        // integer part: 0 | [1-9][0-9]*
        alt((
            tag(b"0" as &[u8]),
            recognize(tuple((
                nom::bytes::complete::take_while1(|b: u8| b.is_ascii_digit() && b != b'0'),
                take_while(is_digit),
            ))),
        )),
        // optional fraction
        nom::combinator::opt(recognize(tuple((
            tag(b"." as &[u8]),
            nom::bytes::complete::take_while1(is_digit),
        )))),
        // optional exponent
        nom::combinator::opt(recognize(tuple((
            alt((tag(b"e" as &[u8]), tag(b"E" as &[u8]))),
            nom::combinator::opt(alt((tag(b"+" as &[u8]), tag(b"-" as &[u8])))),
            nom::bytes::complete::take_while1(is_digit),
        )))),
    )))(input)
}

// ---------------------------------------------------------------------------
// Value — returns the leaf count contributed by this value
// ---------------------------------------------------------------------------

fn json_value(input: &[u8]) -> IResult<&[u8], usize> {
    let (input, _) = ws(input)?;
    alt((
        // object → sum of child values (keys not counted)
        json_object,
        // array → sum of child values
        json_array,
        // string leaf → 1
        |i| {
            let (i, _) = json_string(i)?;
            Ok((i, 1usize))
        },
        // number leaf → 1
        |i| {
            let (i, _) = json_number(i)?;
            Ok((i, 1usize))
        },
        // true → 1
        |i| {
            let (i, _) = tag(b"true" as &[u8])(i)?;
            Ok((i, 1usize))
        },
        // false → 1
        |i| {
            let (i, _) = tag(b"false" as &[u8])(i)?;
            Ok((i, 1usize))
        },
        // null → 1
        |i| {
            let (i, _) = tag(b"null" as &[u8])(i)?;
            Ok((i, 1usize))
        },
    ))(input)
}

// ---------------------------------------------------------------------------
// Object: { key: value, ... }  — keys are strings and NOT counted
// ---------------------------------------------------------------------------

fn json_object(input: &[u8]) -> IResult<&[u8], usize> {
    let (input, _) = ws(input)?;
    let (input, _) = tag(b"{" as &[u8])(input)?;
    let (input, _) = ws(input)?;

    // Check for empty object
    if input.first() == Some(&b'}') {
        let (input, _) = tag(b"}" as &[u8])(input)?;
        return Ok((input, 0));
    }

    // First key-value pair (no leading comma)
    let (input, first_count) = json_kv(input)?;

    // Subsequent key-value pairs (comma-separated)
    let (input, rest_count) = fold_many0(
        preceded(tuple((ws, tag(b"," as &[u8]), ws)), json_kv),
        || 0usize,
        |acc, c| acc + c,
    )(input)?;

    let (input, _) = ws(input)?;
    let (input, _) = tag(b"}" as &[u8])(input)?;

    Ok((input, first_count + rest_count))
}

// A single key-value pair; returns count from value only (key is NOT counted)
fn json_kv(input: &[u8]) -> IResult<&[u8], usize> {
    let (input, (_, count)) = separated_pair(
        delimited(ws, json_string, ws),
        tag(b":" as &[u8]),
        json_value,
    )(input)?;
    Ok((input, count))
}

// ---------------------------------------------------------------------------
// Array: [ value, ... ]
// ---------------------------------------------------------------------------

fn json_array(input: &[u8]) -> IResult<&[u8], usize> {
    let (input, _) = ws(input)?;
    let (input, _) = tag(b"[" as &[u8])(input)?;
    let (input, _) = ws(input)?;

    // Check for empty array
    if input.first() == Some(&b']') {
        let (input, _) = tag(b"]" as &[u8])(input)?;
        return Ok((input, 0));
    }

    // First element (no leading comma)
    let (input, first_count) = json_value(input)?;

    // Subsequent elements (comma-separated)
    let (input, rest_count) = fold_many0(
        preceded(tuple((ws, tag(b"," as &[u8]))), json_value),
        || 0usize,
        |acc, c| acc + c,
    )(input)?;

    let (input, _) = ws(input)?;
    let (input, _) = tag(b"]" as &[u8])(input)?;

    Ok((input, first_count + rest_count))
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

fn parse_count(input: &[u8]) -> usize {
    let (remaining, count) = json_value(input).expect("parse failed");
    // consume any trailing whitespace
    let remaining = remaining
        .iter()
        .copied()
        .skip_while(|b| b.is_ascii_whitespace())
        .collect::<Vec<_>>();
    assert!(
        remaining.is_empty(),
        "trailing bytes: {:?}",
        &remaining[..remaining.len().min(20)]
    );
    count
}

fn main() {
    let path = "/Users/jonaprieto/research/grip/bench/data/canada.json";
    let data = std::fs::read(path).expect("cannot read file");

    const RUNS: usize = 20;
    let mut best = f64::MAX;
    let mut final_count = 0usize;

    for _ in 0..RUNS {
        let t0 = Instant::now();
        let count = parse_count(black_box(&data));
        let elapsed = t0.elapsed();
        let ms = elapsed.as_secs_f64() * 1000.0;
        if ms < best {
            best = ms;
        }
        final_count = count;
    }

    println!("count={}", final_count);
    println!("best_ms={:.3}", best);
}
