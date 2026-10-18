use std::process::Command;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT_SCRIPT: AtomicUsize = AtomicUsize::new(0);
static RUN_LOCK: Mutex<()> = Mutex::new(());

fn run(source: &str) -> std::process::Output {
    let _guard = RUN_LOCK.lock().expect("serialize JIT processes");
    let directory = std::env::temp_dir().join(format!(
        "napalm-date-{}-{}",
        std::process::id(),
        NEXT_SCRIPT.fetch_add(1, Ordering::Relaxed),
    ));
    std::fs::create_dir(&directory).expect("create date test directory");
    let entry = directory.join("main.napalm");
    std::fs::write(&entry, source).expect("write date test");
    let output = Command::new(env!("CARGO_BIN_EXE_Napalm"))
        .arg(&entry)
        .output();
    std::fs::remove_file(&entry).expect("remove date test");
    std::fs::remove_dir(&directory).expect("remove empty date test directory");
    output.expect("execute Napalm")
}

fn stdout_of(source: &str) -> String {
    let output = run(source);
    assert!(
        output.status.success(),
        "exit {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).replace("\r\n", "\n")
}

fn assert_output(source: &str, expected: &str) {
    assert_eq!(stdout_of(source), expected);
}

#[test]
fn date_example() {
    // Line 6 prints `toString()` of a local date, which depends on the host timezone.
    let out = stdout_of(include_str!("../scripts/date.napalm"));
    let lines: Vec<&str> = out.lines().collect();
    assert!(lines[5].starts_with("\"Wed Jan 31 2024 09:30:00 GMT"), "{}", lines[5]);
    let rest: Vec<&str> = lines
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != 5)
        .map(|(_, l)| *l)
        .collect();
    assert_eq!(
        rest.join("\n"),
        [
            "\"1970-01-01T00:00:00.000Z\"",
            "1709214330250",
            "\"2024-02-29T13:45:30.250Z\"",
            "\"Thu, 29 Feb 2024 13:45:30 GMT\"",
            "\"2024-1-31\"",
            "\"2024-03-06T00:00:00.000Z\"",
            "[2024, 1, 29, 4, 13, 45, 30, 250]",
            "\"2020-12-25T18:30:00.000Z\"",
            "\"2021-01-04T18:30:00.000Z\"",
            "\"1970-01-02T00:00:00.000Z\"",
            "1709634030123",
            "1709596800000",
            "1709634030000",
            "1709634030000",
            "true",
            "true",
            "-1",
            "\"-000001-01-01T00:00:00.000Z\"",
            "\"+275760-09-13T00:00:00.000Z\"",
            "NaN",
            "\"Invalid Date\"",
            "null",
            "\"RangeError: Invalid time value\"",
            "365",
            "true",
        ]
        .join("\n")
    );
}

#[test]
fn static_methods() {
    assert_output(
        r#"
print(Date.UTC(2024));
print(Date.UTC(2024, 1, 29, 23, 59, 59, 999));
print(Date.UTC(99, 0));
print(Date.UTC());
print(Date.UTC(2024, 0, 1, 0, 0, 0, 0) == Date.UTC(2024, 0));
print(Date.parse("2024-03-05T10:20:30.123Z"));
print(Date.parse("2024-03-05T10:20Z"));
print(Date.parse("2024-03"));
print(Date.parse("2024"));
print(Date.parse("+002024-03-05T00:00:00.000Z"));
print(Date.parse("-000001-01-01T00:00:00Z"));
print(Date.parse("2024-03-05T12:20:30.5+02:00"));
print(Date.parse("Tue, 05 Mar 2024 10:20:30 GMT"));
print(Date.parse("Tue Mar 05 2024 11:20:30 GMT+0100"));
print(Date.parse("2024-13-01"));
print(Date.parse("2024-02-30"));
print(Date.parse("garbage"));
print(Date.now() > 1700000000000);
"#,
        "1704067200000\n1709251199999\n915148800000\nNaN\ntrue\n1709634030123\n\
1709634000000\n1709251200000\n1704067200000\n1709596800000\n-62198755200000\n\
1709634030500\n1709634030000\n1709634030000\nNaN\nNaN\nNaN\ntrue\n",
    );
}

#[test]
fn utc_getters_setters_and_formatting() {
    assert_output(
        r#"
let d = new Date(Date.UTC(2024, 6, 4, 15, 5, 9, 7));
print([d.getUTCFullYear(), d.getUTCMonth(), d.getUTCDate(), d.getUTCDay(),
       d.getUTCHours(), d.getUTCMinutes(), d.getUTCSeconds(), d.getUTCMilliseconds()]);
print(d.valueOf() == d.getTime());
print(d.toJSON());
print(d.toGMTString());
d.setUTCFullYear(2025, 1, 30);
print(d.toISOString());
d.setUTCHours(25);
print(d.toISOString());
d.setUTCMinutes(0, 0, 0);
print(d.toISOString());
d.setUTCSeconds(-1);
print(d.toISOString());
d.setUTCMilliseconds(1001);
print(d.toISOString());
d.setUTCMonth(0);
print(d.toISOString());
d.setUTCDate(0);
print(d.toISOString());
print(d.setTime(0));
print(d.toISOString());
let copy = new Date(d);
copy.setTime(1);
print([d.getTime(), copy.getTime()]);
print(new Date(Date.UTC(2023, 13, 35)).toISOString());
print(new Date(-1).toISOString());
print(new Date(-62198755200000).toISOString());
print(new Date(8640000000000000).toISOString());
print(new Date(8640000000000001).getTime());
print(new Date("2024-03-05T10:20:30Z").getTime());
"#,
        "[2024, 6, 4, 4, 15, 5, 9, 7]\ntrue\n\"2024-07-04T15:05:09.007Z\"\n\
\"Thu, 04 Jul 2024 15:05:09 GMT\"\n\"2025-03-02T15:05:09.007Z\"\n\
\"2025-03-03T01:05:09.007Z\"\n\"2025-03-03T01:00:00.000Z\"\n\
\"2025-03-03T00:59:59.000Z\"\n\"2025-03-03T01:00:00.001Z\"\n\
\"2025-01-03T01:00:00.001Z\"\n\"2024-12-31T01:00:00.001Z\"\n0\n\
\"1970-01-01T00:00:00.000Z\"\n[0, 1]\n\"2024-03-06T00:00:00.000Z\"\n\
\"1969-12-31T23:59:59.999Z\"\n\"-000001-01-01T00:00:00.000Z\"\n\
\"+275760-09-13T00:00:00.000Z\"\nNaN\n1709634030000\n",
    );
}

#[test]
fn local_time_is_consistent_with_timezone_offset() {
    assert_output(
        r#"
let d = new Date(2024, 6, 4, 15, 5, 9, 7);
print([d.getFullYear(), d.getMonth(), d.getDate(), d.getDay(),
       d.getHours(), d.getMinutes(), d.getSeconds(), d.getMilliseconds()]);
print(d.getTime() == Date.UTC(2024, 6, 4, 15, 5, 9, 7) + d.getTimezoneOffset() * 60000);
print(d.toDateString());
print(d.toLocaleDateString());
print(d.toLocaleTimeString());
print(d.toLocaleString());
d.setHours(23, 59, 59, 999);
d.setMinutes(61);
print([d.getDate(), d.getHours(), d.getMinutes()]);
d.setFullYear(2025, 1, 30);
print([d.getFullYear(), d.getMonth(), d.getDate()]);
d.setMonth(0);
d.setDate(0);
print(d.toDateString());
d.setSeconds(5, 500);
d.setMilliseconds(1500);
print([d.getSeconds(), d.getMilliseconds()]);
let e = new Date("2024-07-04T15:05:09");
print([e.getHours(), e.getMinutes(), e.getSeconds()]);
print(Date.parse(e.toString()) == e.getTime());
print(new Date(2024, 6).getDate());
print(new Date(99, 0).getFullYear());
"#,
        "[2024, 6, 4, 4, 15, 5, 9, 7]\ntrue\n\"Thu Jul 04 2024\"\n\"7/4/2024\"\n\
\"3:05:09 PM\"\n\"7/4/2024, 3:05:09 PM\"\n[5, 0, 1]\n[2025, 2, 2]\n\
\"Tue Dec 31 2024\"\n[6, 500]\n[15, 5, 9]\ntrue\n1\n1999\n",
    );
}

#[test]
fn invalid_dates() {
    assert_output(
        r#"
let bad = new Date("not a date");
print(bad.getTime());
print(bad.getFullYear());
print(bad.toString());
print(bad.toUTCString());
print(bad.toJSON());
try {
    bad.toISOString();
} catch (e) {
    print(e);
}
bad.setUTCHours(1);
print(bad.getTime());
bad.setTime(0);
print(bad.toISOString());
"#,
        "NaN\nNaN\n\"Invalid Date\"\n\"Invalid Date\"\nnull\n\
\"RangeError: Invalid time value\"\nNaN\n\"1970-01-01T00:00:00.000Z\"\n",
    );
}

#[test]
fn explicit_imports_typing_and_shadowing() {
    assert_output(
        r#"
import * as D from "napalm:date";
fn year(d: Date): number { return d.getUTCFullYear(); }
print(year(new Date(0)));
print(new D.Date(5).getTime());
"#,
        "1970\n5\n",
    );
    assert_output(
        r#"
class Date { constructor() { this.x = 42; } }
print(new Date().x);
"#,
        "42\n",
    );
}
