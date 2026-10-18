//! OS clock and time-zone access for the `Date` standard module
//! (`src/stdlib/date.napalm`). All calendar logic lives in that module and is
//! compiled by the JIT; these are the only facts it cannot compute itself.

use crate::value::{BoxedF64, NULL, ObjHeader, TAG_BOXED_F64, is_imm, make_smi, smi_to_i64};

fn number_arg(v: i64) -> Option<f64> {
    if is_imm(v) {
        return Some(smi_to_i64(v) as f64);
    }
    if v == NULL || (v & 0b111) != 0 {
        return None;
    }
    unsafe {
        if (*(v as *const ObjHeader)).tag == TAG_BOXED_F64 {
            Some((*(v as *const BoxedF64)).val)
        } else {
            None
        }
    }
}

/// Milliseconds since the Unix epoch (`Date.now()`).
#[unsafe(no_mangle)]
pub extern "C" fn wir_date_now() -> i64 {
    let ms = match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
        Ok(d) => d.as_millis() as i64,
        Err(e) => -(e.duration().as_millis() as i64),
    };
    make_smi(ms)
}

/// Offset of local time from UTC, in minutes east of Greenwich, at the UTC
/// instant `t` (milliseconds since the epoch). Non-numbers and NaN yield 0.
#[unsafe(no_mangle)]
pub extern "C" fn wir_date_local_offset(t: i64) -> i64 {
    let minutes = match number_arg(t) {
        Some(ms) if ms.is_finite() => local_offset_minutes((ms / 1000.0).floor() as i64),
        _ => 0,
    };
    make_smi(minutes)
}

/// Proleptic Gregorian (year, month 1-12, day) of a day count since 1970-01-01.
fn civil_from_days(z: i64) -> (i64, i64, i64) {
    let z = z + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    (yoe + era * 400 + i64::from(m <= 2), m, d)
}

#[cfg(windows)]
fn local_offset_minutes(secs: i64) -> i64 {
    use windows_sys::Win32::Foundation::SYSTEMTIME;
    use windows_sys::Win32::System::Time::SystemTimeToTzSpecificLocalTime;

    // SYSTEMTIME covers years 1601..=30827; outside that range the offset of
    // the same wall-clock moment in the nearest supported year is used.
    let (year, month, day) = civil_from_days(secs.div_euclid(86_400));
    let clamped = year.clamp(1601, 30_827);
    let day = if clamped != year && month == 2 && day == 29 { 28 } else { day };
    let tod = secs.rem_euclid(86_400);
    let utc = SYSTEMTIME {
        wYear: clamped as u16,
        wMonth: month as u16,
        wDayOfWeek: 0,
        wDay: day as u16,
        wHour: (tod / 3600) as u16,
        wMinute: (tod / 60 % 60) as u16,
        wSecond: (tod % 60) as u16,
        wMilliseconds: 0,
    };
    let mut local: SYSTEMTIME = unsafe { std::mem::zeroed() };
    if unsafe { SystemTimeToTzSpecificLocalTime(std::ptr::null(), &utc, &mut local) } == 0 {
        return 0;
    }
    let minutes_of = |t: &SYSTEMTIME| {
        let days = days_from_civil(t.wYear as i64, t.wMonth as i64, t.wDay as i64);
        days * 1440 + t.wHour as i64 * 60 + t.wMinute as i64
    };
    minutes_of(&local) - minutes_of(&utc)
}

#[cfg(windows)]
fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = y.div_euclid(400);
    let yoe = y - era * 400;
    let doy = (153 * ((m + 9) % 12) + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146_097 + doe - 719_468
}

#[cfg(unix)]
fn local_offset_minutes(secs: i64) -> i64 {
    let t = secs as libc::time_t;
    let mut tm: libc::tm = unsafe { std::mem::zeroed() };
    if unsafe { libc::localtime_r(&t, &mut tm) }.is_null() {
        return 0;
    }
    tm.tm_gmtoff as i64 / 60
}

#[cfg(not(any(windows, unix)))]
fn local_offset_minutes(_secs: i64) -> i64 {
    0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn civil_round_trips() {
        assert_eq!(civil_from_days(0), (1970, 1, 1));
        assert_eq!(civil_from_days(19_787), (2024, 3, 5));
        assert_eq!(civil_from_days(-1), (1969, 12, 31));
        assert_eq!(civil_from_days(-719_468), (0, 3, 1));
    }

    #[test]
    fn offset_is_whole_minutes_within_a_day() {
        for secs in [0, 1_700_000_000, -5_000_000_000, 40_000_000_000_000] {
            assert!(local_offset_minutes(secs).abs() < 1440);
        }
    }
}
