// kpoc_charger.rs: Standalone offline charging service (KPOC) written from
// scratch in Rust for Transsion MediaTek devices without external dependencies.
//
// Renderer: Direct Linux DRM/KMS on /dev/dri/card0 using dumb buffers.
//
// Battery and input plumbing:
//   - Battery state: Linux Netlink KOBJECT_UEVENT socket for real-time capacity,
//     temperature, and charging status without sysfs dependency.
//   - Power key: evdev (/dev/input/event*) for short-press screen toggle
//     and long-press OS reboot.
//   - Backlight: sysfs backlight control on resume and blanking on suspend.
//   - Assets: MTK compressed ARGB8888 zlib streams decoded directly from
//     the logo partition.

use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::os::raw::{c_int, c_long, c_ulong, c_void};
use std::os::unix::fs::OpenOptionsExt;
use std::os::unix::io::AsRawFd;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Mutex;

// ------------------------------------------------------------------ //
// Layout and animation constants                                     //
// ------------------------------------------------------------------ //

const DIGIT_W: usize = 42; // white digit glyph, entries 4..13
const DIGIT_H: usize = 60;
const PCT_W: usize = 48; // '%' glyph, entry 14
const PCT_H: usize = 60;

const DIGIT1_X: usize = 474;
const DIGIT_Y: usize = 873;
const DIGIT2_X: usize = 516;
const PCT_X: usize = 558;

// Centered single digit when cap < 10
const DIGIT_SINGLE_X: usize = 495;
const PCT_SINGLE_X: usize = 537;

const LOGO_FULL: usize = 1; // 100% full screen
#[allow(dead_code)]
const LOGO_LOW: usize = 2; // low battery warning icon
const LOGO_OVTEMP: usize = 3; // over temperature warning icon
const LOGO_DIGIT0: usize = 4; // digits 0..9 (entries 4..=13)
const LOGO_PCT: usize = 14; // '%'
const LOGO_WAVE_FIRST: usize = 15; // wave crests (entries 15..=24)
const LOGO_WAVE_LAST: usize = 24;
const LOGO_GREEN_BASE: usize = 35; // chassis, cable, battery well
const LOGO_GREEN_ROW: usize = 36; // 224x1 green bar

const WELL_X: usize = 427;
const WELL_W: usize = 224;
const WELL_Y_TOP: usize = 1030;
const WELL_Y_BOT: usize = 1366;
const WELL_H: usize = 337;
const WAVE_W: usize = 224;
const WAVE_H: usize = 12;

const OVERTEMP_DEG_C: i32 = 600;

const POLL_MS: i32 = 500;
const KEY_POLL_MS: i32 = 100;
const STATE_POLL_DIV: u32 = 4; // sysfs poll = 4 * POLL_MS = 2 s
const UNPLUG_TRIP: u32 = 3; // consecutive no-charger reads -> power off
const SCREEN_TIMEOUT_MS: i64 = 10_000; // auto-blank panel after 10 s of inactivity

/// Animation frame period: 200 ms (5 fps).
const ANIM_FRAME_MS: i64 = 200;

/// Poll interval for the input path: fast cadence while a key is held,
/// idle interval otherwise.
fn key_poll_ms(held: bool) -> i32 {
    if held {
        KEY_POLL_MS
    } else {
        POLL_MS
    }
}

/// A kernel event timestamp more than this far behind the clock it belongs
/// to is a replay of buffered history, not a live press. The threshold sits
/// orders of magnitude above any plausible queue delay (bounded by POLL_MS
/// plus one draw) and far below the 1909 s old replay observed on hardware, so
/// a real press is never filtered out by it.
const KEV_STALE_MS: i64 = 600_000;

/// Timestamps at or above this are wall-clock (ms since the epoch); below
/// it, monotonic. The two domains are orders of magnitude apart on any real
/// device, so the split is unambiguous.
const KEV_REALTIME_FLOOR_MS: i64 = 100_000_000_000;

/// Tolerance for a stamp that looks like it is from the future, e.g. after
/// the clock was stepped. Such a stamp carries no usable age.
const KEV_CLOCK_SLACK_MS: i64 = 300_000;

/// both kernel clocks in milliseconds. The kernel stamps input_event.time
/// with one of them and which one is not knowable from userspace, so
/// staleness has to be judged against both.
fn kernel_clocks_ms() -> (i64, i64) {
    unsafe {
        let mut rt = TimeSpec {
            tv_sec: 0,
            tv_nsec: 0,
        };
        let mut mo = TimeSpec {
            tv_sec: 0,
            tv_nsec: 0,
        };
        clock_gettime(CLOCK_REALTIME, &mut rt);
        clock_gettime(CLOCK_MONOTONIC, &mut mo);
        (
            rt.tv_sec * 1000 + rt.tv_nsec / 1_000_000,
            mo.tv_sec * 1000 + mo.tv_nsec / 1_000_000,
        )
    }
}

/// one input_event's kernel timestamp in ms, or None when it carries no
/// usable stamp. A zero stamp is the "no information" case and the event
/// must be kept.
fn ev_ts_ms(buf: &[u8], o: usize) -> Option<i64> {
    let sec = i64::from_le_bytes([
        buf[o], buf[o + 1], buf[o + 2], buf[o + 3], buf[o + 4], buf[o + 5], buf[o + 6], buf[o + 7],
    ]);
    let usec = i64::from_le_bytes([
        buf[o + 8], buf[o + 9], buf[o + 10], buf[o + 11], buf[o + 12], buf[o + 13], buf[o + 14],
        buf[o + 15],
    ]);
    if sec <= 0 {
        return None;
    }
    Some(sec * 1000 + usec / 1000)
}

/// how old this stamp is, in the clock domain it belongs to. None when the
/// domain cannot be decided, which keeps the event rather than guessing.
///
/// The kernel stamps with one of the two clocks and userspace cannot know
/// which, so the domain is decided by magnitude: a wall-clock stamp is
/// orders of magnitude above a monotonic one on any real device. A stamp
/// from the future is not judgeable either. When the realtime clock is not
/// a usable wall clock at all, a small stamp cannot be told apart from a
/// broken realtime stamp, so it is kept.
fn ev_age_ms(ts: i64, now: (i64, i64)) -> Option<i64> {
    let (rt, mo) = now;
    if ts >= KEV_REALTIME_FLOOR_MS {
        if ts > rt + KEV_CLOCK_SLACK_MS {
            return None;
        }
        Some(rt - ts)
    } else if rt < KEV_REALTIME_FLOOR_MS {
        None
    } else if ts > mo + KEV_CLOCK_SLACK_MS {
        None
    } else {
        Some(mo - ts)
    }
}

/// is this event a replay of buffered history rather than a live press?
///
/// The MTK kernel keeps power-key history behind its pwrkey_sync handler
/// and flushes it to a reader when a new press arrives, so a reader sees a
/// burst of old press/release pairs stamped at the moment they were
/// buffered. On target hardware one flush handed a reader four pairs 1909 s old, all
/// sharing a single timestamp, and `feed()` collapsed them into one panel
/// toggle the user never asked for. Only a stamp that is impossibly old is
/// dropped, so a real press survives every clock domain and every
/// clock-step case.
fn ev_is_stale(buf: &[u8], o: usize, now: (i64, i64)) -> bool {
    match ev_ts_ms(buf, o) {
        None => false,
        Some(ts) => match ev_age_ms(ts, now) {
            None => false,
            Some(age) => age > KEV_STALE_MS,
        },
    }
}

// The panel backlight is a standalone LED-class device on this platform
// (there is no /sys/class/backlight). It reads 0 whenever the composer HAL
// is not running, i.e. exactly in charger mode, so a perfectly correct
// render comes out as a black screen unless it is raised explicitly.
const BL_CLASS: &str = "/sys/class/leds/lcd-backlight";

const WAKELOCK_NAME: &[u8] = b"kpoc_anim";
const PS_CLASS: &str = "/sys/class/power_supply";

const LOGO_MAGIC_HDR: u32 = 0x5888_1688;
const LOGO_MAGIC_TBL: u32 = 0x5889_1689; // at 0x30 in the header
const LOGO_TBL_OFF: u64 = 0x200;
const LOGO_MAX_ENTRIES: usize = 512;

// reboot(2) syscall constants
const __NR_REBOOT: c_long = 142; // aarch64, confirmed in NDK sysroot
const __NR_SOCKET: c_long = 198;
const __NR_BIND: c_long = 200;
const __NR_RECVFROM: c_long = 207;
const __NR_CLOSE: c_long = 57;
const REBOOT_MAGIC1: c_ulong = 0xfee1_dead;
const REBOOT_MAGIC2: c_ulong = 672_274_793;
const REBOOT_CMD_RESTART: c_ulong = 0x0123_4567;
const REBOOT_CMD_POWER_OFF: c_ulong = 0x4321_fedc;

// DRM/KMS ioctls, aarch64 _IOWR('d', nr, sizeof(struct)):
//   GETRESOURCES 0xa0 card_res(64)   GETCRTC 0xa1 crtc(104)
//   SETCRTC      0xa2 crtc(104)      GETENCODER 0xa6 get_encoder(20)
//   GETCONNECTOR 0xa7 get_connector(80)
//   CREATE_DUMB  0xb2 create_dumb(32) MAP_DUMB 0xb3 map_dumb(16)
//   ADDFB2       0xb8 fb_cmd2(104)   SET_MASTER _IO('d',0x1e)
const DRM_SET_MASTER: c_ulong = 0x641e;
const DRM_GETRESOURCES: c_ulong = 0xc040_64a0;
const DRM_GETCRTC: c_ulong = 0xc068_64a1;
const DRM_SETCRTC: c_ulong = 0xc068_64a2;
const DRM_GETENCODER: c_ulong = 0xc014_64a6;
const DRM_GETCONNECTOR: c_ulong = 0xc050_64a7;
const DRM_CREATE_DUMB: c_ulong = 0xc020_64b2;
const DRM_MAP_DUMB: c_ulong = 0xc010_64b3;
const DRM_ADDFB2: c_ulong = 0xc068_64b8;

const DRM_MODE_CONNECTED: u32 = 1;
const DRM_FORMAT_XRGB8888: u32 = 0x3432_5258; // 'XR24' little-endian

const PROT_READ_WRITE: c_int = 3;
const MAP_SHARED: c_int = 1;
const O_NONBLOCK: c_int = 0o4000;

// input
const EV_KEY: u16 = 0x01;
const KEY_POWER: u16 = 116;
const INPUT_EV_SIZE: usize = 24; // struct input_event on aarch64

// poll
const POLLIN: i16 = 0x001;

// zlib
const Z_OK: c_int = 0;
const Z_STREAM_END: c_int = 1;
const Z_FINISH: c_int = 4;
const Z_BUF_ERROR: c_int = -5;

// ------------------------------------------------------------------ //
// klog: direct /dev/kmsg writes                                       //
// ------------------------------------------------------------------ //

static KMSG: Mutex<Option<File>> = Mutex::new(None);

fn klog(level: &str, args: std::fmt::Arguments) {
    let line = format!("<{}>kpoc: {}\n", level, args);
    #[cfg(test)]
    if std::env::var_os("KPOC_TEST_LOG").is_some() {
        eprint!("{}", line);
    }
    if let Ok(mut g) = KMSG.lock() {
        if let Some(f) = g.as_mut() {
            let _ = f.write_all(line.as_bytes());
        }
    }
}

macro_rules! logi {
    ($($a:tt)*) => { klog("6", format_args!($($a)*)) };
}
macro_rules! loge {
    ($($a:tt)*) => { klog("3", format_args!($($a)*)) };
}

/// report a replayed-history drop once. A charger-mode service logs for
/// hours and the kernel replays on every new press, so a per-event line
/// would flood the kernel log; the count is what matters for diagnosis.
fn log_stale_drop(n: usize) {
    static LOGGED: AtomicBool = AtomicBool::new(false);
    if LOGGED.swap(true, Ordering::Relaxed) {
        return;
    }
    logi!(
        "keys: dropped {} replayed power-key events (older than {} ms)",
        n,
        KEV_STALE_MS
    );
}

fn errno_str() -> std::io::Error {
    std::io::Error::last_os_error()
}

// ------------------------------------------------------------------ //
// hand-declared libc bits (bionic, statically linked)                 //
// ------------------------------------------------------------------ //

#[repr(C)]
struct PollFd {
    fd: c_int,
    events: i16,
    revents: i16,
}

/// struct timespec, for reading the kernel clocks
#[repr(C)]
struct TimeSpec {
    tv_sec: i64,
    tv_nsec: i64,
}

const CLOCK_REALTIME: c_int = 0;
const CLOCK_MONOTONIC: c_int = 1;

extern "C" {
    fn ioctl(fd: c_int, request: c_ulong, ...) -> c_int;
    fn mmap(
        addr: *mut c_void,
        length: usize,
        prot: c_int,
        flags: c_int,
        fd: c_int,
        offset: i64,
    ) -> *mut c_void;
    fn munmap(addr: *mut c_void, length: usize) -> c_int;
    fn poll(fds: *mut PollFd, nfds: c_ulong, timeout: c_int) -> c_int;
    fn clock_gettime(clk: c_int, tp: *mut TimeSpec) -> c_int;
    fn syscall(number: c_long, ...) -> c_long;
    fn sync();
    fn recvfrom(
        fd: c_int,
        buf: *mut c_void,
        len: usize,
        flags: c_int,
        src_addr: *mut c_void,
        addrlen: *mut usize,
    ) -> isize;
}

// Linux netlink uevent socket (NETLINK_KOBJECT_UEVENT = 15).
// Delivers live battery and charger events directly without depending on sysfs access.
const AF_NETLINK: c_long = 16;
const SOCK_DGRAM: c_int = 2; // NDK sys/socket.h: SOCK_STREAM=1, SOCK_DGRAM=2
const SOCK_CLOEXEC: c_int = 0o2000000; // O_CLOEXEC
const NETLINK_KOBJECT_UEVENT: c_long = 15;
const MSG_DONTWAIT: c_int = 0x40;

fn do_reboot(cmd: c_ulong) {
    unsafe {
        syscall(
            __NR_REBOOT,
            REBOOT_MAGIC1 as c_long,
            REBOOT_MAGIC2 as c_long,
            cmd as c_long,
            0usize,
        );
    }
}

// ------------------------------------------------------------------ //
// zlib FFI: statically linked from the toolchain sysroot              //
// ------------------------------------------------------------------ //

#[repr(C)]
struct ZStream {
    next_in: *const u8,
    avail_in: u32,
    total_in: u64,
    next_out: *mut u8,
    avail_out: u32,
    total_out: u64,
    msg: *const u8,
    state: *mut c_void,
    zalloc: *mut c_void,
    zfree: *mut c_void,
    opaque: *mut c_void,
    data_type: c_int,
    adler: u64,
    reserved: u64,
}

#[link(name = "z")]
extern "C" {
    fn inflateInit_(strm: *mut ZStream, version: *const u8, stream_size: c_int) -> c_int;
    fn inflate(strm: *mut ZStream, flush: c_int) -> c_int;
    fn inflateEnd(strm: *mut ZStream) -> c_int;
}

/// inflate one zlib stream, growing the output as needed (same loop as the
/// C `load_entry`). `hint` = expected inflated size.
unsafe fn zlib_inflate(raw: &[u8], hint: usize) -> Option<Vec<u8>> {
    let mut cap = if hint > 0 { hint } else { 1 << 20 };
    let mut out = vec![0u8; cap];
    let mut zs: ZStream = std::mem::zeroed();
    zs.next_in = raw.as_ptr();
    zs.avail_in = raw.len() as u32;
    zs.next_out = out.as_mut_ptr();
    zs.avail_out = out.len() as u32;
    if inflateInit_(
        &mut zs,
        // zlib only checks version[0] == '1' and stream_size
        b"1\0".as_ptr(),
        std::mem::size_of::<ZStream>() as c_int,
    ) != Z_OK
    {
        return None;
    }
    let mut rc = inflate(&mut zs, Z_FINISH);
    while (rc == Z_BUF_ERROR || rc == Z_OK) && zs.avail_out == 0 {
        let used = out.len() - zs.avail_out as usize;
        cap *= 2;
        out.resize(cap, 0);
        zs.next_out = out.as_mut_ptr().add(used);
        zs.avail_out = (cap - used) as u32;
        rc = inflate(&mut zs, Z_FINISH);
    }
    let outlen = out.len() - zs.avail_out as usize;
    inflateEnd(&mut zs);
    if rc != Z_STREAM_END {
        return None;
    }
    out.truncate(outlen);
    Some(out)
}

// ------------------------------------------------------------------ //
// Framebuffer: DRM/KMS                                                //
// ------------------------------------------------------------------ //

// ---- uapi/linux/drm_mode.h structs, v5.10 (sizes cross-checked) ------ //

#[repr(C)]
#[derive(Clone, Copy)]
struct ModeInfo {
    clock: u32,
    hdisplay: u16,
    hsync_start: u16,
    hsync_end: u16,
    htotal: u16,
    hskew: u16,
    vdisplay: u16,
    vsync_start: u16,
    vsync_end: u16,
    vtotal: u16,
    vscan: u16,
    vrefresh: u32,
    flags: u32,
    ty: u32,
    name: [u8; 32],
} // 68 bytes

#[repr(C)]
struct CardRes {
    fb_id_ptr: u64,
    crtc_id_ptr: u64,
    connector_id_ptr: u64,
    encoder_id_ptr: u64,
    count_fbs: u32,
    count_crtcs: u32,
    count_connectors: u32,
    count_encoders: u32,
    min_width: u32,
    max_width: u32,
    min_height: u32,
    max_height: u32,
} // 64 bytes

#[repr(C)]
struct GetConnector {
    encoders_ptr: u64,
    modes_ptr: u64,
    props_ptr: u64,
    prop_values_ptr: u64,
    count_modes: u32,
    count_props: u32,
    count_encoders: u32,
    encoder_id: u32,
    connector_id: u32,
    connector_type: u32,
    connector_type_id: u32,
    connection: u32,
    mm_width: u32,
    mm_height: u32,
    subpixel: u32,
    pad: u32,
} // 80 bytes

#[repr(C)]
struct GetEncoder {
    encoder_id: u32,
    encoder_type: u32,
    crtc_id: u32,
    possible_crtcs: u32,
    possible_clones: u32,
} // 20 bytes

#[repr(C)]
struct CreateDumb {
    height: u32,
    width: u32,
    bpp: u32,
    flags: u32,
    handle: u32,
    pitch: u32,
    size: u64,
} // 32 bytes

#[repr(C)]
struct MapDumb {
    handle: u32,
    pad: u32,
    offset: u64,
} // 16 bytes

#[repr(C)]
struct FbCmd2 {
    fb_id: u32,
    width: u32,
    height: u32,
    pixel_format: u32,
    flags: u32,
    handles: [u32; 4],
    pitches: [u32; 4],
    offsets: [u32; 4],
    modifier: [u64; 4],
} // 104 bytes

#[repr(C)]
struct Crtc {
    set_connectors_ptr: u64,
    count_connectors: u32,
    crtc_id: u32,
    fb_id: u32,
    x: u32,
    y: u32,
    gamma_size: u32,
    mode_valid: u32,
    mode: ModeInfo,
} // 104 bytes

// geometry of a mapped framebuffer surface. `row_bytes` is the KMS pitch,
// which is >= w*4 when the driver pads rows; every blit offsets by it.
#[derive(Clone, Copy)]
struct Surf {
    row_bytes: usize,
    w: usize,
    h: usize,
}

impl Surf {
    fn frame_bytes(&self) -> usize {
        self.w * self.h * 4
    }
}

// One live KMS output: a dumb buffer that IS the crtc framebuffer, so
// writes through the mmap land on the scanned-out surface with no extra
// ioctl (verified live: the second blit showed up immediately).
struct Screen {
    file: File,
    mem: *mut u8,
    mem_len: usize,
    surf: Surf,
    crtc_id: u32,
    /// kept so the crtc can be re-enabled after a short-press suspend
    conn_id: u32,
    fb_id: u32,
    mode: ModeInfo,
}

impl Screen {
    /// the mapped surface as one mutable slice; callers blit into it
    fn buf(&mut self) -> &mut [u8] {
        unsafe { std::slice::from_raw_parts_mut(self.mem, self.mem_len) }
    }
}

impl Drop for Screen {
    fn drop(&mut self) {
        unsafe { munmap(self.mem as *mut c_void, self.mem_len) };
    }
}

fn drm_open() -> Option<Screen> {
    let mut file: Option<File> = None;
    for dev in ["/dev/dri/card0", "/dev/dri/card1"] {
        match OpenOptions::new().read(true).write(true).open(dev) {
            Ok(f) => {
                file = Some(f);
                break;
            }
            Err(e) => loge!("drm: open {} failed: {}", dev, e),
        }
    }
    let file = file?;
    let fd = file.as_raw_fd();

    // The composer HAL holds DRM master in a normal boot; in charger mode
    // nothing does, but taking it explicitly is what makes this work when
    // the service is started by hand for validation.
    if unsafe { ioctl(fd, DRM_SET_MASTER, 0usize) } < 0 {
        loge!("drm: SET_MASTER failed: {}", errno_str());
        return None;
    }
    logi!("drm: SET_MASTER ok");

    let mut res: CardRes = unsafe { std::mem::zeroed() };
    if unsafe { ioctl(fd, DRM_GETRESOURCES, &mut res) } < 0 {
        loge!("drm: GETRESOURCES failed: {}", errno_str());
        return None;
    }
    let n_conn = res.count_connectors as usize;
    let n_crtc = res.count_crtcs as usize;
    let n_enc = res.count_encoders as usize;
    if n_conn == 0 || n_crtc == 0 {
        loge!("drm: {} crtcs / {} connectors", n_crtc, n_conn);
        return None;
    }
    let mut conns = vec![0u32; n_conn];
    let mut crtcs = vec![0u32; n_crtc];
    let mut encs = vec![0u32; n_enc.max(1)];
    let mut fbs = vec![0u32; (res.count_fbs as usize).max(1)];
    res.fb_id_ptr = fbs.as_mut_ptr() as u64;
    res.crtc_id_ptr = crtcs.as_mut_ptr() as u64;
    res.connector_id_ptr = conns.as_mut_ptr() as u64;
    res.encoder_id_ptr = encs.as_mut_ptr() as u64;
    if unsafe { ioctl(fd, DRM_GETRESOURCES, &mut res) } < 0 {
        loge!("drm: GETRESOURCES(2) failed: {}", errno_str());
        return None;
    }
    logi!(
        "drm: {} crtcs, {} connectors, {} encoders, {} fbs",
        n_crtc,
        n_conn,
        n_enc,
        res.count_fbs
    );

    // first connected connector that actually has modes
    let mut conn_id = 0u32;
    let mut enc_id = 0u32;
    let mut mode: ModeInfo = unsafe { std::mem::zeroed() };
    for i in 0..n_conn {
        let mut gc: GetConnector = unsafe { std::mem::zeroed() };
        gc.connector_id = conns[i];
        if unsafe { ioctl(fd, DRM_GETCONNECTOR, &mut gc) } < 0 {
            loge!("drm: GETCONNECTOR({}) failed: {}", conns[i], errno_str());
            continue;
        }
        if gc.connection != DRM_MODE_CONNECTED || gc.count_modes == 0 {
            logi!(
                "drm: conn {} type={} connection={} modes={}, skipped",
                conns[i],
                gc.connector_type,
                gc.connection,
                gc.count_modes
            );
            continue;
        }
        let nmode = gc.count_modes as usize;
        let nenc = (gc.count_encoders as usize).max(1);
        let mut ms = vec![
            ModeInfo {
                clock: 0,
                hdisplay: 0,
                hsync_start: 0,
                hsync_end: 0,
                htotal: 0,
                hskew: 0,
                vdisplay: 0,
                vsync_start: 0,
                vsync_end: 0,
                vtotal: 0,
                vscan: 0,
                vrefresh: 0,
                flags: 0,
                ty: 0,
                name: [0; 32],
            };
            nmode
        ];
        let mut es = vec![0u32; nenc];
        let mut g2: GetConnector = unsafe { std::mem::zeroed() };
        g2.connector_id = conns[i];
        g2.modes_ptr = ms.as_mut_ptr() as u64;
        g2.count_modes = gc.count_modes;
        g2.encoders_ptr = es.as_mut_ptr() as u64;
        g2.count_encoders = gc.count_encoders;
        if unsafe { ioctl(fd, DRM_GETCONNECTOR, &mut g2) } < 0 {
            loge!("drm: GETCONNECTOR({},2) failed: {}", conns[i], errno_str());
            continue;
        }
        conn_id = conns[i];
        enc_id = if g2.count_encoders > 0 { es[0] } else { 0 };
        mode = ms[0];
        logi!(
            "drm: conn {} type={} enc={} mode {}x{}@{}Hz",
            conn_id,
            gc.connector_type,
            enc_id,
            mode.hdisplay,
            mode.vdisplay,
            mode.vrefresh
        );
        break;
    }
    if conn_id == 0 {
        loge!("drm: no connected connector with modes");
        return None;
    }

    // encoder -> crtc: prefer the one already bound, else the first
    // possible_crtcs bit (e.g. bit 0 for crtc 70)
    let mut crtc_id = 0u32;
    if enc_id != 0 {
        let mut ge: GetEncoder = unsafe { std::mem::zeroed() };
        ge.encoder_id = enc_id;
        if unsafe { ioctl(fd, DRM_GETENCODER, &mut ge) } == 0 {
            crtc_id = ge.crtc_id;
            if crtc_id == 0 {
                for b in 0..n_crtc {
                    if ge.possible_crtcs & (1u32 << b) != 0 {
                        crtc_id = crtcs[b];
                        break;
                    }
                }
            }
        } else {
            loge!("drm: GETENCODER({}) failed: {}", enc_id, errno_str());
        }
    }
    if crtc_id == 0 {
        loge!("drm: no crtc for encoder {}", enc_id);
        return None;
    }
    logi!("drm: crtc_id={} encoder={}", crtc_id, enc_id);

    let mut cd: CreateDumb = unsafe { std::mem::zeroed() };
    cd.width = mode.hdisplay as u32;
    cd.height = mode.vdisplay as u32;
    cd.bpp = 32;
    if unsafe { ioctl(fd, DRM_CREATE_DUMB, &mut cd) } < 0 {
        loge!("drm: CREATE_DUMB failed: {}", errno_str());
        return None;
    }
    let mut md: MapDumb = unsafe { std::mem::zeroed() };
    md.handle = cd.handle;
    if unsafe { ioctl(fd, DRM_MAP_DUMB, &mut md) } < 0 {
        loge!("drm: MAP_DUMB failed: {}", errno_str());
        return None;
    }
    let mem = unsafe {
        mmap(
            std::ptr::null_mut(),
            cd.size as usize,
            PROT_READ_WRITE,
            MAP_SHARED,
            fd,
            md.offset as i64,
        )
    };
    if mem == usize::MAX as *mut c_void {
        loge!("drm: mmap failed: {}", errno_str());
        return None;
    }
    logi!(
        "drm: dumb {}x{} pitch={} size={}",
        mode.hdisplay,
        mode.vdisplay,
        cd.pitch,
        cd.size
    );

    let mut fc: FbCmd2 = unsafe { std::mem::zeroed() };
    fc.width = mode.hdisplay as u32;
    fc.height = mode.vdisplay as u32;
    fc.pixel_format = DRM_FORMAT_XRGB8888;
    fc.handles[0] = cd.handle;
    fc.pitches[0] = cd.pitch;
    fc.offsets[0] = 0;
    if unsafe { ioctl(fd, DRM_ADDFB2, &mut fc) } < 0 {
        loge!("drm: ADDFB2 failed: {}", errno_str());
        return None;
    }
    logi!("drm: ADDFB2 ok fb_id={} fmt=XRGB8888", fc.fb_id);

    let mut sc: Crtc = unsafe { std::mem::zeroed() };
    sc.crtc_id = crtc_id;
    sc.fb_id = fc.fb_id;
    sc.x = 0;
    sc.y = 0;
    sc.set_connectors_ptr = &conn_id as *const u32 as u64;
    sc.count_connectors = 1;
    sc.mode = mode;
    sc.mode_valid = 1;
    if unsafe { ioctl(fd, DRM_SETCRTC, &mut sc) } < 0 {
        loge!("drm: SETCRTC failed: {}", errno_str());
        return None;
    }
    let mut chk: Crtc = unsafe { std::mem::zeroed() };
    chk.crtc_id = crtc_id;
    if unsafe { ioctl(fd, DRM_GETCRTC, &mut chk) } == 0 {
        logi!(
            "drm: SETCRTC ok: readback fb_id={} mode_valid={} {}x{}",
            chk.fb_id,
            chk.mode_valid,
            chk.mode.hdisplay,
            chk.mode.vdisplay
        );
    }

    let w = mode.hdisplay as usize;
    let h = mode.vdisplay as usize;
    Some(Screen {
        file,
        mem: mem as *mut u8,
        mem_len: cd.size as usize,
        surf: Surf {
            row_bytes: cd.pitch as usize,
            w,
            h,
        },
        crtc_id,
        conn_id,
        fb_id: fc.fb_id,
        mode,
    })
}

/// blank the output and drop the crtc; used before RB_POWER_OFF so the
/// panel does not hold the last frame. mode_valid=0 REQUIRES
/// count_connectors=0, otherwise drm_mode_setcrtc() returns EINVAL.
/// returns false when the crtc could not be stopped
fn drm_disable(scr: &Screen) -> bool {
    let fd = scr.file.as_raw_fd();
    let mut off: Crtc = unsafe { std::mem::zeroed() };
    off.crtc_id = scr.crtc_id;
    off.fb_id = 0;
    off.mode_valid = 0;
    off.set_connectors_ptr = 0;
    off.count_connectors = 0;
    if unsafe { ioctl(fd, DRM_SETCRTC, &mut off) } < 0 {
        loge!("drm: disable failed: {}", errno_str());
        false
    } else {
        logi!("drm: crtc {} disabled", scr.crtc_id);
        true
    }
}

/// Re-attach the framebuffer and the mode to a crtc that `drm_disable` dropped.
/// A full SETCRTC restores the scanout surface.
/// Returns false when the crtc did not come back up.
fn drm_enable(scr: &Screen) -> bool {
    let fd = scr.file.as_raw_fd();
    let mut on: Crtc = unsafe { std::mem::zeroed() };
    on.crtc_id = scr.crtc_id;
    on.fb_id = scr.fb_id;
    on.x = 0;
    on.y = 0;
    on.set_connectors_ptr = &scr.conn_id as *const u32 as u64;
    on.count_connectors = 1;
    on.mode = scr.mode;
    on.mode_valid = 1;
    if unsafe { ioctl(fd, DRM_SETCRTC, &mut on) } < 0 {
        loge!("drm: enable failed: {}", errno_str());
        false
    } else {
        logi!("drm: crtc {} enabled fb={}", scr.crtc_id, scr.fb_id);
        true
    }
}

/// write one row of an XRGB8888 source into the surface at (x,y)
fn blit_row(dst: &mut [u8], s: &Surf, y: usize, x: usize, src: &[u8], w: usize) {
    let pxsz = 4usize;
    if x * pxsz >= s.row_bytes || y >= s.h {
        return;
    }
    let max_w = (s.row_bytes - x * pxsz) / pxsz;
    let w = w.min(max_w).min(s.w.saturating_sub(x));
    if w == 0 {
        return;
    }
    let off = y * s.row_bytes + x * pxsz;
    dst[off..off + w * pxsz].copy_from_slice(&src[..w * pxsz]);
}

/// blit a full XRGB8888 frame sized exactly like the surface
fn blit_frame(dst: &mut [u8], s: &Surf, src: &[u8]) {
    if src.len() < s.frame_bytes() {
        loge!("blit_frame: src {} < fb {}, skipped", src.len(), s.frame_bytes());
        return;
    }
    for y in 0..s.h {
        blit_row(dst, s, y, 0, &src[y * s.w * 4..], s.w);
    }
}

/// blit a small XRGB8888 glyph (w x h) at (x, y)
fn blit_glyph(dst: &mut [u8], s: &Surf, src: &[u8], x: usize, y: usize, w: usize, h: usize) {
    if x + w > s.w || y + h > s.h {
        loge!(
            "glyph ({},{} {}x{}) out of fb {}x{}, skipped",
            x, y, w, h, s.w, s.h
        );
        return;
    }
    if src.len() < w * h * 4 {
        loge!("glyph src {} < {}, skipped", src.len(), w * h * 4);
        return;
    }
    for r in 0..h {
        blit_row(dst, s, y + r, x, &src[r * w * 4..], w);
    }
}

fn fill_black(dst: &mut [u8], s: &Surf) {
    // a short framebuffer must not take the service down: a panic in
    // charger mode is a crash loop, and the panel is already dark
    if dst.len() < s.row_bytes.saturating_mul(s.h) {
        loge!(
            "fill_black: fb {} < {}, skipped",
            dst.len(),
            s.row_bytes.saturating_mul(s.h)
        );
        return;
    }
    for y in 0..s.h {
        let off = y * s.row_bytes;
        let end = (off + s.w * 4).min(dst.len());
        if off >= end {
            break;
        }
        dst[off..end].fill(0);
    }
}

// ---- backlight ------------------------------------------------------ //

/// Panel backlight level: set to a fixed comfortable brightness on resume, or 0 on suspend.
/// A missing or unwritable node is non-fatal: it is logged and skipped.
const BACKLIGHT_ON: i32 = 255;

fn backlight_set(on: bool) {
    let max = read_int_file(&format!("{}/max_brightness", BL_CLASS));
    let cur = read_int_file(&format!("{}/brightness", BL_CLASS));
    let m = match max {
        Some(m) if m > 0 => m,
        _ => {
            loge!("backlight: max={:?} cur={:?}, skipped", max, cur);
            return;
        }
    };
    let want = if on { m.min(BACKLIGHT_ON) } else { 0 };
    // Always write on resume: panel power-on can reset internal backlight state
    // even if sysfs still reports the previous value.
    match OpenOptions::new()
        .write(true)
        .open(format!("{}/brightness", BL_CLASS))
        .and_then(|mut f| f.write_all(want.to_string().as_bytes()))
    {
        Ok(()) => logi!("backlight: {:?} -> {} (max {})", cur, want, m),
        Err(e) => loge!("backlight: write {} failed: {}", want, e),
    }
}

/// raise the panel to maximum at startup
fn backlight_setup() {
    backlight_set(true);
}

// ------------------------------------------------------------------ //
// logo table                                                          //
// ------------------------------------------------------------------ //

struct LogoTable {
    count: usize,
    entries: Vec<Option<Vec<u8>>>, // inflated ARGB8888
    fb_bytes: usize,
}

impl LogoTable {
    fn have(&self, idx: usize) -> bool {
        idx < self.count && self.entries[idx].is_some()
    }
}

fn read_at(f: &mut File, off: u64, buf: &mut [u8]) -> std::io::Result<()> {
    f.seek(SeekFrom::Start(off))?;
    f.read_exact(buf)
}

fn should_load_entry(idx: usize) -> bool {
    matches!(idx, LOGO_FULL..=LOGO_WAVE_LAST | LOGO_GREEN_BASE | LOGO_GREEN_ROW)
}

fn expected_entry_bytes(idx: usize, fb_bytes: usize) -> usize {
    match idx {
        1 | 2 | 3 | LOGO_GREEN_BASE => fb_bytes,
        4..=13 => DIGIT_W * DIGIT_H * 4,
        LOGO_PCT => PCT_W * PCT_H * 4,
        LOGO_WAVE_FIRST..=LOGO_WAVE_LAST => WAVE_W * WAVE_H * 4,
        LOGO_GREEN_ROW => WELL_W * 4,
        _ => fb_bytes,
    }
}

fn load_entry(f: &mut File, t: &mut LogoTable, idx: usize, start: u64, end: u64) {
    let len = (end - start) as usize;
    if len == 0 || len > (64 << 20) {
        loge!("logo[{}]: bad length {}", idx, len);
        return;
    }
    let mut raw = vec![0u8; len];
    if let Err(e) = read_at(f, LOGO_TBL_OFF + start, &mut raw) {
        loge!("logo[{}]: read failed: {}", idx, e);
        return;
    }
    let hint = expected_entry_bytes(idx, t.fb_bytes);
    match unsafe { zlib_inflate(&raw, hint) } {
        Some(out) => {
            if out.len() == t.fb_bytes {
                logi!("logo[{}]: full frame {} bytes", idx, out.len());
            } else {
                logi!("logo[{}]: {} bytes", idx, out.len());
            }
            t.entries[idx] = Some(out);
        }
        None => loge!("logo[{}]: inflate failed", idx),
    }
}

fn table_load(fb_bytes: usize) -> Option<LogoTable> {
    // never hardcode logo_a as the only alternative: with A/B slots the live
    // partition can be logo, logo_a or logo_b depending on the active slot
    table_load_from(
        &[
            "/dev/block/by-name/logo",
            "/dev/block/by-name/logo_a",
            "/dev/block/by-name/logo_b",
        ],
        fb_bytes,
    )
}

fn table_load_from(parts: &[&str], fb_bytes: usize) -> Option<LogoTable> {
    for part in parts {
        let mut f = match File::open(part) {
            Ok(f) => f,
            Err(e) => {
                loge!("logo: open {} failed: {}", part, e);
                continue;
            }
        };
        logi!("logo: using {}", part);

        // Header: magic1 at 0x00, magic2 at 0x30; table offset is 0x200.
        let mut hdr = [0u8; 0x40];
        if let Err(e) = read_at(&mut f, 0, &mut hdr) {
            loge!("logo: header read failed on {}: {}, trying next", part, e);
            continue;
        }
        let m0 = u32::from_le_bytes(hdr[0..4].try_into().unwrap());
        let m1 = u32::from_le_bytes(hdr[0x30..0x34].try_into().unwrap());
        if m0 != LOGO_MAGIC_HDR || m1 != LOGO_MAGIC_TBL {
            loge!("logo: {} bad magics {:08x} {:08x}, trying next", part, m0, m1);
            continue;
        }

        let mut meta = [0u8; 8];
        if let Err(e) = read_at(&mut f, LOGO_TBL_OFF, &mut meta) {
            loge!("logo: table meta read failed on {}: {}, trying next", part, e);
            continue;
        }
        let count = u32::from_le_bytes(meta[0..4].try_into().unwrap()) as usize;
        let total_len = u32::from_le_bytes(meta[4..8].try_into().unwrap());
        if count == 0 || count > LOGO_MAX_ENTRIES || total_len == 0 {
            loge!(
                "logo: {} bad count={} total_len={}, trying next",
                part, count, total_len
            );
            continue;
        }
        logi!("logo: {} entries, table span {}", count, total_len);

        // Cumulative starts at 0x208+4i; entry i ends at start[i+1]; the last
        // ends at total_len (data spans 0x200 .. 0x200+total_len)
        let mut starts = vec![0u8; (count + 1) * 4];
        if let Err(e) = read_at(&mut f, LOGO_TBL_OFF + 8, &mut starts) {
            loge!("logo: start table read failed on {}: {}, trying next", part, e);
            continue;
        }
        let mut t = LogoTable {
            count,
            entries: vec![None; count],
            fb_bytes,
        };
        for i in 0..count {
            if !should_load_entry(i) {
                continue;
            }
            let s = u32::from_le_bytes(starts[i * 4..i * 4 + 4].try_into().unwrap());
            let e = if i + 1 < count {
                u32::from_le_bytes(starts[(i + 1) * 4..(i + 1) * 4 + 4].try_into().unwrap())
            } else {
                total_len
            };
            if e <= s {
                loge!("logo[{}]: empty entry (start={} end={})", i, s, e);
                continue;
            }
            load_entry(&mut f, &mut t, i, s as u64, e as u64);
        }
        return Some(t);
    }
    None
}

// ------------------------------------------------------------------ //
// rendering                                                           //
// ------------------------------------------------------------------ //

/// which screen the current (cap, temp) state maps to
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
enum UiMode {
    /// one static full-frame entry (ovtemp / low battery / 100% / unknown)
    Static(usize),
    /// the flowing-fill animation, digits drawn on top
    Anim,
}

/// the frame range an animation mode cycles through. Static modes have
/// no range and return None.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct AnimRange {
    first: usize,
    last: usize,
}

fn anim_range(mode: UiMode) -> Option<AnimRange> {
    match mode {
        UiMode::Anim => Some(AnimRange {
            first: 0,
            last: 9,
        }),
        UiMode::Static(_) => None,
    }
}

fn ui_mode(cap: i32, temp: i32, tab: &LogoTable) -> UiMode {
    if temp >= OVERTEMP_DEG_C && tab.have(LOGO_OVTEMP) {
        return UiMode::Static(LOGO_OVTEMP);
    }
    // a full battery is the full-green screen
    if cap >= 100 && tab.have(LOGO_FULL) {
        return UiMode::Static(LOGO_FULL);
    }
    if (0..=99).contains(&cap) && tab.have(LOGO_GREEN_BASE) && tab.have(LOGO_GREEN_ROW) {
        return UiMode::Anim;
    }
    // cap < 0: capacity still unknown; fall back to the plain base frame
    UiMode::Static(LOGO_GREEN_BASE)
}

fn draw_full(dst: &mut [u8], s: &Surf, tab: &LogoTable, idx: usize) {
    if !tab.have(idx) {
        loge!("draw_full: entry {} missing", idx);
        return;
    }
    let e = tab.entries[idx].as_ref().unwrap();
    if e.len() != s.frame_bytes() {
        loge!(
            "draw_full: entry {} size {} != fb {}, skipped",
            idx,
            e.len(),
            s.frame_bytes()
        );
        return;
    }
    blit_frame(dst, s, e);
}

fn draw_digit(dst: &mut [u8], s: &Surf, tab: &LogoTable, d: usize, x: usize) {
    let idx = LOGO_DIGIT0 + d;
    if !tab.have(idx) {
        loge!("draw_digit: entry {} missing", idx);
        return;
    }
    let want = DIGIT_W * DIGIT_H * 4;
    let e = tab.entries[idx].as_ref().unwrap();
    if e.len() != want {
        loge!("draw_digit: entry {} size {} != {}, skipped", idx, e.len(), want);
        return;
    }
    blit_glyph(dst, s, e, x, DIGIT_Y, DIGIT_W, DIGIT_H);
}

fn draw_pct(dst: &mut [u8], s: &Surf, tab: &LogoTable, x: usize) {
    if !tab.have(LOGO_PCT) {
        return;
    }
    let want = PCT_W * PCT_H * 4;
    let e = tab.entries[LOGO_PCT].as_ref().unwrap();
    if e.len() != want {
        loge!("pct: entry {} size {} != {}, skipped", LOGO_PCT, e.len(), want);
        return;
    }
    blit_glyph(dst, s, e, x, DIGIT_Y, PCT_W, PCT_H);
}

/// the white "NN%" block, drawn over whichever frame is underneath.
/// cap >= 100 never reaches here: entry 1 already carries a baked "100%".
fn draw_percent(dst: &mut [u8], s: &Surf, tab: &LogoTable, cap: i32) {
    if cap < 0 || cap > 99 {
        return;
    }
    if cap <= 9 {
        draw_digit(dst, s, tab, cap as usize, DIGIT_SINGLE_X);
        draw_pct(dst, s, tab, PCT_SINGLE_X);
    } else {
        draw_digit(dst, s, tab, (cap / 10) as usize, DIGIT1_X);
        draw_digit(dst, s, tab, (cap % 10) as usize, DIGIT2_X);
        draw_pct(dst, s, tab, PCT_X);
    }
}

fn draw_black(dst: &mut [u8], s: &Surf) {
    fill_black(dst, s);
}

/// Fill the charging battery well (entry 35 base + entry 36 green row)
/// upward to match `cap` (0..=99%), with an animated 12px wave crest (entries 15..=24)
/// at the top surface cycling every 200 ms.
fn draw_anim_normal(dst: &mut [u8], s: &Surf, tab: &LogoTable, frame: usize, cap: i32) {
    if !tab.have(LOGO_GREEN_BASE) || !tab.have(LOGO_GREEN_ROW) {
        loge!("draw_anim_normal: base or row missing");
        return;
    }
    let base = tab.entries[LOGO_GREEN_BASE].as_ref().unwrap();
    let row = tab.entries[LOGO_GREEN_ROW].as_ref().unwrap();
    if base.len() != s.frame_bytes() || row.len() != WELL_W * 4 {
        loge!("draw_anim_normal: bad base or row size");
        return;
    }
    // 1. Offscreen scratch buffer for atomic presentation without black-flash tearing
    let mut scratch = base.clone();

    // 2. Static fill height for the battery capacity (no synthetic oscillating delta)
    let fill_y = (WELL_Y_BOT as i32 - (WELL_H as i32 * cap.clamp(0, 100)) / 100)
        .clamp(WELL_Y_TOP as i32, WELL_Y_BOT as i32) as usize;

    // 3. Fill solid green rows from fill_y down to the bottom of the well
    if cap > 0 {
        for y in fill_y..=WELL_Y_BOT {
            if y >= s.h || WELL_X + WELL_W > s.w {
                break;
            }
            let d_off = y * s.row_bytes + WELL_X * 4;
            scratch[d_off..d_off + WELL_W * 4].copy_from_slice(row);
        }
    }

    // 4. Wave crest at surface: cycle entries 15..=24 (224x12) when cap <= 90
    if cap <= 90 {
        let wave_idx = LOGO_WAVE_FIRST + (frame % 10);
        if tab.have(wave_idx) {
            let wave = tab.entries[wave_idx].as_ref().unwrap();
            if wave.len() == WAVE_W * WAVE_H * 4 {
                let wave_y = fill_y.saturating_sub(WAVE_H).max(WELL_Y_TOP);
                for r in 0..WAVE_H {
                    let y = wave_y + r;
                    if y >= s.h || WELL_X + WAVE_W > s.w {
                        break;
                    }
                    let d_off = y * s.row_bytes + WELL_X * 4;
                    let w_off = r * WAVE_W * 4;
                    scratch[d_off..d_off + WAVE_W * 4].copy_from_slice(&wave[w_off..w_off + WAVE_W * 4]);
                }
            }
        }
    }

    // 5. Draw live battery percent
    draw_percent(&mut scratch, s, tab, cap);

    // 6. Blit finished frame into dst atomically
    dst.copy_from_slice(&scratch);
}

/// Update only the 12-row wave crest (224x12) directly in the active framebuffer.
/// Leaves the background, green well fill, and digits untouched, eliminating redraw
/// flicker / tearing on a single dumb buffer.
fn draw_anim_wave_only(dst: &mut [u8], s: &Surf, tab: &LogoTable, frame: usize, cap: i32) {
    if cap > 90 || !tab.have(LOGO_GREEN_BASE) || !tab.have(LOGO_GREEN_ROW) {
        return;
    }
    let fill_y = (WELL_Y_BOT as i32 - (WELL_H as i32 * cap.clamp(0, 100)) / 100)
        .clamp(WELL_Y_TOP as i32, WELL_Y_BOT as i32) as usize;
    let wave_idx = LOGO_WAVE_FIRST + (frame % 10);
    if tab.have(wave_idx) {
        let wave = tab.entries[wave_idx].as_ref().unwrap();
        if wave.len() == WAVE_W * WAVE_H * 4 {
            let wave_y = fill_y.saturating_sub(WAVE_H).max(WELL_Y_TOP);
            for r in 0..WAVE_H {
                let y = wave_y + r;
                if y >= s.h || WELL_X + WAVE_W > s.w {
                    break;
                }
                let d_off = y * s.row_bytes + WELL_X * 4;
                let w_off = r * WAVE_W * 4;
                dst[d_off..d_off + WAVE_W * 4].copy_from_slice(&wave[w_off..w_off + WAVE_W * 4]);
            }
        }
    }
}

/// repaint whatever the current state calls for
fn draw_ui(dst: &mut [u8], s: &Surf, tab: &LogoTable, mode: UiMode, frame: usize, cap: i32) {
    match mode {
        UiMode::Static(idx) => draw_full(dst, s, tab, idx),
        UiMode::Anim => draw_anim_normal(dst, s, tab, frame, cap),
    }
}

/// has the composed image changed since the last paint? Temperature is
/// deliberately not an input: it selects the mode (over-temperature) but
/// never reaches the picture directly, and in Anim mode the frame advances
/// every tick anyway. Treating a 0.1 degC flicker as a change costs a full
/// 10 MB blit twice a second for an identical image.
fn needs_redraw(mode: UiMode, new_mode: UiMode, cap: i32, last_cap: i32) -> bool {
    new_mode != mode || cap != last_cap
}

/// advance the flowing-fill cycle within its own range: 0 -> 1 -> ... -> 9 -> 0.
fn anim_next(frame: usize, r: AnimRange) -> usize {
    if frame < r.first || frame >= r.last {
        r.first
    } else {
        frame + 1
    }
}

// ------------------------------------------------------------------ //
// sysfs state                                                         //
// ------------------------------------------------------------------ //

/// like strtol: parse the leading integer of a file's first line
fn read_int_file(path: &str) -> Option<i32> {
    let s = std::fs::read_to_string(path).ok()?;
    let t = s.trim_start();
    let end = t
        .find(|c: char| !(c.is_ascii_digit() || c == '-' || c == '+'))
        .unwrap_or(t.len());
    let tok = &t[..end];
    if tok.is_empty() || tok == "-" || tok == "+" {
        return None;
    }
    tok.parse::<i32>().ok()
}

// ------------------------------------------------------------------ //
// Live battery state: kernel uevents                                 //
// ------------------------------------------------------------------ //

struct PsState {
    cap: Option<i32>,
    temp: Option<i32>,
    volt_uv: Option<i32>,
    charging: Option<bool>,
    online: Option<bool>,
    ivolt_mv: Option<i32>,
    ilim_ma: Option<i32>,
    c_max_ua: Option<i32>,
    ps_type: Option<String>,
    updates: u64,
}

static PS: Mutex<PsState> = Mutex::new(PsState {
    cap: None,
    temp: None,
    volt_uv: None,
    charging: None,
    online: None,
    ivolt_mv: None,
    ilim_ma: None,
    c_max_ua: None,
    ps_type: None,
    updates: 0,
});

/// one parsed power_supply uevent
struct UevInfo {
    name: String,
    cap: Option<i32>,
    temp: Option<i32>,
    voltage_uv: Option<i32>,
    status: Option<String>,
    online: Option<i32>,
    ivolt_mv: Option<i32>,
    ilim_ma: Option<i32>,
    c_max_ua: Option<i32>,
    ps_type: Option<String>,
}

/// parse a kernel uevent datagram: NUL-separated
/// "change@/devices/.../power_supply/battery\0KEY=VAL\0KEY=VAL\0..."
fn parse_uevent(buf: &[u8]) -> Option<UevInfo> {
    let mut info = UevInfo {
        name: String::new(),
        cap: None,
        temp: None,
        voltage_uv: None,
        status: None,
        online: None,
        ivolt_mv: None,
        ilim_ma: None,
        c_max_ua: None,
        ps_type: None,
    };
    for field in buf.split(|&b| b == 0) {
        if field.is_empty() {
            continue;
        }
        let s = String::from_utf8_lossy(field);
        if let Some(v) = s.strip_prefix("POWER_SUPPLY_NAME=") {
            info.name = v.to_string();
        } else if let Some(v) = s.strip_prefix("POWER_SUPPLY_CAPACITY=") {
            info.cap = v.trim().parse().ok();
        } else if let Some(v) = s.strip_prefix("POWER_SUPPLY_TEMP=") {
            info.temp = v.trim().parse().ok();
        } else if let Some(v) = s.strip_prefix("POWER_SUPPLY_VOLTAGE_NOW=") {
            // microvolts, as the power_supply sysfs ABI defines it
            info.voltage_uv = v.trim().parse().ok();
        } else if let Some(v) = s.strip_prefix("POWER_SUPPLY_STATUS=") {
            info.status = Some(v.to_string());
        } else if let Some(v) = s.strip_prefix("POWER_SUPPLY_ONLINE=") {
            info.online = v.trim().parse().ok();
        // the negotiated charger capability. Only the `charger` supply
        // carries these; the battery supply does not.
        } else if let Some(v) = s.strip_prefix("POWER_SUPPLY_INPUT_VOLTAGE_LIMIT=") {
            info.ivolt_mv = v.trim().parse().ok();
        } else if let Some(v) = s.strip_prefix("POWER_SUPPLY_INPUT_CURRENT_LIMIT=") {
            info.ilim_ma = v.trim().parse().ok();
        } else if let Some(v) = s.strip_prefix("POWER_SUPPLY_CURRENT_MAX=") {
            info.c_max_ua = v.trim().parse().ok();
        } else if let Some(v) = s.strip_prefix("POWER_SUPPLY_TYPE=") {
            info.ps_type = Some(v.to_string());
        }
    }
    if info.name.is_empty() {
        return None;
    }
    Some(info)
}

/// apply one parsed uevent to the battery state
/// which supplies may answer "is a cable connected"?
///
/// The name list covers the conventional Android supplies. The type test
/// covers the MediaTek reality on target hardware, where the only supply that reports
/// cable presence is named `charger` and typed USB_DCP, and no usb, ac or
/// wireless supply exists at all. A name-only list therefore left `online`
/// permanently None, which made the unplug power-off path unreachable:
/// the decision needs charging==false AND online==false, and online could
/// never become Some(false).
///
/// `usb_switch` is deliberately excluded. It is typed Mains and reports
/// online=0 on this device while a cable is plugged in and charging, so
/// accepting it would put a supply that reads "cable out" while the cable
/// is in straight into the decision, leaving the battery status as the
/// only thing between that and a power-off during a charge-phase
/// transition.
fn online_source(name: &str, ps_type: Option<&str>) -> bool {
    if matches!(name, "usb" | "ac" | "wireless" | "charger") {
        return true;
    }
    matches!(ps_type, Some(t) if t.starts_with("USB"))
}

fn ps_apply(ps: &mut PsState, info: &UevInfo) {
    if let Some(c) = info.cap {
        if (0..=100).contains(&c) {
            // count only real changes, exactly as the C reference does
            if ps.cap != Some(c) {
                ps.updates += 1;
            }
            ps.cap = Some(c);
        }
    }
    if let Some(t) = info.temp {
        if ps.temp != Some(t) {
            ps.updates += 1;
        }
        ps.temp = Some(t);
    }
    if let Some(s) = &info.status {
        let chg = s.starts_with("Charging") || s.starts_with("Full");
        if ps.charging != Some(chg) {
            ps.updates += 1;
        }
        ps.charging = Some(chg);
    }
    if let Some(o) = info.online {
        if online_source(&info.name, info.ps_type.as_deref()) {
            if ps.online != Some(o > 0) {
                ps.updates += 1;
            }
            ps.online = Some(o > 0);
        }
    }
    // The charger node re-emits its full property set on every change, so
    // whatever it does not carry this time is absent.
    if info.name == "charger" {
        ps.ivolt_mv = info.ivolt_mv;
        ps.ilim_ma = info.ilim_ma;
        ps.c_max_ua = info.c_max_ua;
        ps.ps_type = info.ps_type.clone();
    }
    // Only the battery supply's voltage gates a boot. A partial uevent
    // that omits the key must not wipe a good reading, so this is an
    // update-on-present, not an overwrite.
    if info.name == "battery" {
        if let Some(uv) = info.voltage_uv {
            if uv > 0 {
                ps.volt_uv = Some(uv);
            }
        }
    }
}

fn uev_apply(msg: &[u8]) {
    let info = match parse_uevent(msg) {
        Some(i) => i,
        None => return,
    };
    if let Ok(mut ps) = PS.lock() {
        ps_apply(&mut ps, &info);
    }
}

/// bind the netlink KOBJECT_UEVENT multicast socket
fn uev_open() -> Option<c_int> {
    let fd = unsafe {
        syscall(
            __NR_SOCKET,
            AF_NETLINK,
            SOCK_DGRAM | SOCK_CLOEXEC,
            NETLINK_KOBJECT_UEVENT,
        )
    };
    if fd < 0 {
        loge!("uevent: socket failed: {}", errno_str());
        return None;
    }
    // sockaddr_nl { nl_family u16; nl_pad u16; nl_pid u32; nl_groups u32 }
    let mut sa = [0u8; 16];
    sa[0] = AF_NETLINK as u8;
    sa[8] = 1; // nl_groups = 1: kernel uevent multicast group
    if unsafe { syscall(__NR_BIND, fd, sa.as_ptr(), sa.len()) } < 0 {
        loge!("uevent: bind failed: {}", errno_str());
        unsafe { syscall(__NR_CLOSE, fd) };
        return None;
    }
    logi!("uevent: netlink KOBJECT_UEVENT fd={}", fd);
    Some(fd as c_int)
}

/// drain pending uevent datagrams; returns how many were parsed
fn uev_drain(fd: c_int) -> usize {
    let mut buf = [0u8; 16 * 1024];
    let mut n = 0usize;
    for _ in 0..64 {
        let r = unsafe {
            recvfrom(
                fd,
                buf.as_mut_ptr() as *mut c_void,
                buf.len(),
                MSG_DONTWAIT,
                std::ptr::null_mut(),
                std::ptr::null_mut(),
            )
        };
        if r <= 0 {
            break;
        }
        uev_apply(&buf[..r as usize]);
        n += 1;
    }
    n
}

/// wait up to `ms` for the first battery uevent, so the initial frame
/// already shows the percent (charger-mode boot: the first
/// power_supply change lands within a couple of seconds)
fn uev_wait_first(fd: c_int, ms: i32) -> bool {
    let mut waited = 0;
    while waited < ms {
        let mut pfd = [PollFd {
            fd,
            events: POLLIN,
            revents: 0,
        }];
        let n = unsafe { poll(pfd.as_mut_ptr(), 1, 50) };
        waited += 50;
        if n <= 0 {
            continue;
        }
        if pfd[0].revents & POLLIN != 0 && uev_drain(fd) > 0 {
            if let Ok(ps) = PS.lock() {
                if ps.cap.is_some() {
                    return true;
                }
            }
        }
    }
    false
}

/// Battery capacity: reads sysfs where available, falling back to uevents.
fn read_capacity() -> Option<i32> {
    if let Some(v) = read_int_file(&format!("{}/battery/capacity", PS_CLASS)) {
        if (0..=100).contains(&v) {
            return Some(v);
        }
    }
    PS.lock().ok()?.cap
}

/// temperature in 0.1 degC units
fn read_temp() -> Option<i32> {
    if let Some(v) = read_int_file(&format!("{}/battery/temp", PS_CLASS)) {
        return Some(v);
    }
    PS.lock().ok()?.temp
}

/// Battery voltage in mV. Reads sysfs if available, falling back to uevents.
fn battery_voltage_mv() -> Option<i32> {
    if let Some(uv) = read_int_file(&format!("{}/battery/voltage_now", PS_CLASS)) {
        if uv > 0 {
            return Some(uv / 1000);
        }
    }
    if let Ok(ps) = PS.lock() {
        if let Some(uv) = ps.volt_uv {
            if uv > 0 {
                return Some(uv / 1000);
            }
        }
    }
    None
}

/// true when the device reports a charger attached
/// is the cable still in, given what the two data sources said?
///
/// When sysfs reads are restricted, only the uevent state is available.
/// A positive uevent proves the cable is connected, whereas confirming unplug
/// requires agreeing negative uevents to prevent accidental shutdown.
fn charger_present_decision(sysfs_any: bool, charging: Option<bool>, online: Option<bool>) -> bool {
    if charging == Some(true) || online == Some(true) {
        return true;
    }
    if sysfs_any {
        return false;
    }
    if charging == Some(false) && online == Some(false) {
        return false;
    }
    true
}

fn charger_present() -> bool {
    // 1) sysfs: works wherever the domain may read power_supply files
    let mut sysfs_any = false;
    for src in ["usb/online", "ac/online", "battery/online", "wireless/online"] {
        if let Some(v) = read_int_file(&format!("{}/{}", PS_CLASS, src)) {
            sysfs_any = true;
            if v > 0 {
                return true;
            }
        }
    }
    if let Ok(s) = std::fs::read_to_string(format!("{}/battery/status", PS_CLASS)) {
        sysfs_any = true;
        if s.starts_with("Charging") || s.starts_with("Full") {
            return true;
        }
    }
    // 2) the pure decision over sysfs authority plus the uevent state.
    //    The lock is taken once: between the two reads in the old code a
    //    uevent could land and change the answer mid-function.
    if let Ok(ps) = PS.lock() {
        return charger_present_decision(sysfs_any, ps.charging, ps.online);
    }
    // 3) if the lock is poisoned, return true to stay alive
    true
}

// ------------------------------------------------------------------ //
// Charger input calculation                                           //
// ------------------------------------------------------------------ //

#[cfg(test)]
fn input_watts(ivolt_mv: Option<i32>, ilim_ma: Option<i32>, c_max_ua: Option<i32>) -> Option<i32> {
    let v = ivolt_mv?;
    if v <= 0 {
        return None;
    }
    let mut best: Option<i64> = None;
    if let Some(i) = ilim_ma {
        if i > 0 {
            let w = v as i64 * i as i64 / 1_000_000;
            best = Some(best.map_or(w, |b| b.max(w)));
        }
    }
    if let Some(i) = c_max_ua {
        if i > 0 {
            let w = v as i64 * i as i64 / 1_000_000_000;
            best = Some(best.map_or(w, |b| b.max(w)));
        }
    }
    best.map(|w| w as i32)
}

// ------------------------------------------------------------------ //
// Power key handling                                                  //
// ------------------------------------------------------------------ //

// A hold past KEY_LONG_MS boots to OS; a short press toggles the panel.
const KEY_LONG_MS: u64 = 1200;

/// Minimum battery voltage required to permit booting to OS (3400 mV).
const BOOT_VMIN_MV: i32 = 3400;

// Optional RT_Monitor watchdog tick on screen toggle.
const RT_MONITOR_DEV: &str = "/dev/RT_Monitor";
const RT_MONITOR_TICK: c_ulong = 0x8004_700a;
const RT_MONITOR_TICK_MS: usize = 300;
static RT_MONITOR_OK: AtomicBool = AtomicBool::new(true);

fn rt_monitor_tick() {
    if !RT_MONITOR_OK.load(Ordering::Relaxed) {
        return;
    }
    let f = match OpenOptions::new().read(true).write(true).open(RT_MONITOR_DEV) {
        Ok(f) => f,
        Err(_) => {
            RT_MONITOR_OK.store(false, Ordering::Relaxed);
            return;
        }
    };
    let r = unsafe { ioctl(f.as_raw_fd(), RT_MONITOR_TICK, RT_MONITOR_TICK_MS) };
    if r != 0 {
        loge!("set tick time failed, ret={}, errno={}", r, errno_str());
    }
}

/// one key edge. Autorepeat (value 2) is deliberately not an edge: it must
/// not restart the long-press clock.
#[derive(PartialEq, Eq, Clone, Copy, Debug)]
enum KeyEv {
    None,
    Press,
    Release,
}

/// max key edges carried in one poll batch
const KEY_BATCH_MAX: usize = 16;

/// the power-key edges seen in one poll batch, in arrival order. A fixed
/// array so the key path never allocates.
#[derive(Clone, Copy)]
struct KeyBatch {
    ev: [KeyEv; KEY_BATCH_MAX],
    n: usize,
}

impl KeyBatch {
    fn new() -> Self {
        KeyBatch {
            ev: [KeyEv::None; KEY_BATCH_MAX],
            n: 0,
        }
    }
    fn push(&mut self, e: KeyEv) {
        if self.n < KEY_BATCH_MAX {
            self.ev[self.n] = e;
            self.n += 1;
        }
    }
    fn is_empty(&self) -> bool {
        self.n == 0
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
enum KeyAction {
    None,
    /// short press: toggle the panel
    ToggleScreen,
    /// long press: boot to the OS
    BootOs,
}

/// power-key state. Single instance, owned by main.
struct PowerKey {
    /// when the current press started; None while the key is up
    press: Option<std::time::Instant>,
    /// panel state, so a short press always toggles rather than always
    /// blanking
    screen_on: bool,
}

impl PowerKey {
    fn new() -> Self {
        PowerKey {
            press: None,
            screen_on: true,
        }
    }

    /// feed one poll batch in arrival order; returns the action to take.
    /// The action belongs to the LAST press the batch completed, and a
    /// batch that ends mid-press leaves that press pending for the next
    /// one instead of dropping it.
    fn feed(&mut self, b: &KeyBatch) -> KeyAction {
        if b.is_empty() {
            return KeyAction::None;
        }
        let mut act = KeyAction::None;
        for i in 0..b.n {
            match b.ev[i] {
                KeyEv::Press => {
                    self.press = Some(std::time::Instant::now());
                }
                KeyEv::Release => act = self.release_action(),
                KeyEv::None => {}
            }
        }
        act
    }

    /// what a key release means for the press it ends
    fn release_action(&mut self) -> KeyAction {
        match self.press.take() {
            None => KeyAction::None,
            Some(t0) => {
                if t0.elapsed() >= std::time::Duration::from_millis(KEY_LONG_MS) {
                    KeyAction::BootOs
                } else {
                    KeyAction::ToggleScreen
                }
            }
        }
    }

    /// A key held past the threshold boots without waiting for release.
    fn held_long_enough(&self) -> bool {
        matches!(self.press, Some(t0)
            if t0.elapsed() >= std::time::Duration::from_millis(KEY_LONG_MS))
    }

    /// drop a pending press whose action has already been taken
    fn cancel(&mut self) {
        self.press = None;
    }

    /// Validates whether the battery voltage permits OS boot.
    /// If voltage is unreadable, boot is permitted to avoid trapping the device.
    fn vbat_allows_boot(mv: Option<i32>) -> bool {
        match mv {
            Some(v) => v > BOOT_VMIN_MV,
            None => true,
        }
    }
}

/// Screen toggle state follows the CRTC result, not the request.
/// A failed SETCRTC leaves the state unchanged to keep subsequent keypresses in sync.
fn screen_state_after(drm_ok: bool, was_on: bool, suspending: bool) -> bool {
    if !drm_ok {
        return was_on;
    }
    !suspending
}

fn screen_suspend(scr: &mut Screen, pkey: &mut PowerKey) {
    logi!("power key short press / timeout: panel off");
    backlight_set(false);
    let ok = drm_disable(scr);
    pkey.screen_on = screen_state_after(ok, pkey.screen_on, true);
}

/// short press with the panel dark: draw the frame first so the buffer is
/// ready before scanout starts, re-attach the CRTC, then restore backlight.
fn screen_resume(scr: &mut Screen, pkey: &mut PowerKey, tab: &LogoTable, mode: UiMode, frame: usize, cap: i32) {
    logi!("power key short press: panel on");
    let surf = scr.surf;
    draw_ui(scr.buf(), &surf, tab, mode, frame, cap);
    let ok = drm_enable(scr);
    pkey.screen_on = screen_state_after(ok, pkey.screen_on, false);
    if ok {
        backlight_set(true);
    }
}

// ------------------------------------------------------------------ //
// input                                                               //
// ------------------------------------------------------------------ //

struct Keys {
    fds: Vec<File>,
}

impl Keys {
    /// Discard whatever is already queued on every node.
    /// Draining at open time avoids acting on stale keypresses queued during boot.
    fn drain(&mut self) {
        let mut buf = [0u8; 16 * INPUT_EV_SIZE];
        let mut dropped = 0usize;
        for f in self.fds.iter_mut() {
            for _ in 0..64 {
                match f.read(&mut buf) {
                    Ok(0) => break,
                    Ok(r) => dropped += r,
                    Err(_) => break,
                }
            }
        }
        if dropped > 0 {
            logi!("keys: dropped {} stale bytes at startup", dropped);
        }
    }
}

fn keys_open() -> Keys {
    let mut fds = Vec::new();
    if let Ok(rd) = std::fs::read_dir("/dev/input") {
        for e in rd.flatten() {
            let name = e.file_name();
            let name = name.to_string_lossy();
            if !name.starts_with("event") {
                continue;
            }
            if let Ok(f) = OpenOptions::new()
                .read(true)
                .custom_flags(O_NONBLOCK)
                .open(e.path())
            {
                fds.push(f);
            }
        }
    }
    logi!("keys: {} input devices", fds.len());
    Keys { fds }
}

/// poll the key devices and the uevent socket. Returns the key edges
/// seen in this batch (in arrival order) and whether a battery uevent
/// landed. An unreadable device is skipped rather than fatal: the input
/// node set differs between platforms and charger mode must survive it.
fn input_poll(keys: &mut Keys, uev_fd: Option<c_int>, timeout_ms: i32) -> (KeyBatch, bool) {
    let mut pfds: Vec<PollFd> = keys
        .fds
        .iter()
        .map(|f| PollFd {
            fd: f.as_raw_fd(),
            events: POLLIN,
            revents: 0,
        })
        .collect();
    let uev_idx = if let Some(fd) = uev_fd {
        pfds.push(PollFd {
            fd,
            events: POLLIN,
            revents: 0,
        });
        Some(pfds.len() - 1)
    } else {
        None
    };
    if pfds.is_empty() {
        return (KeyBatch::new(), false);
    }
    let n = unsafe { poll(pfds.as_mut_ptr(), pfds.len() as c_ulong, timeout_ms) };
    if n <= 0 {
        return (KeyBatch::new(), false);
    }
    // Process uevents first to update live battery state before input handling.
    let mut uev_seen = false;
    if let Some(i) = uev_idx {
        if pfds[i].revents & POLLIN != 0 && uev_drain(pfds[i].fd) > 0 {
            uev_seen = true;
        }
    }
    let mut kb = KeyBatch::new();
    // one clock read per batch: the kernel stamps every event of a flush
    // with the same value, so a per-event read would only add syscalls
    let now = kernel_clocks_ms();
    let mut stale_dropped = 0usize;
    for i in 0..keys.fds.len() {
        if pfds[i].revents & POLLIN == 0 {
            continue;
        }
        let mut buf = [0u8; 16 * INPUT_EV_SIZE];
        let r = keys.fds[i].read(&mut buf).unwrap_or(0);
        if r == 0 {
            continue;
        }
        for k in 0..r / INPUT_EV_SIZE {
            let o = k * INPUT_EV_SIZE;
            let ty = u16::from_le_bytes([buf[o + 16], buf[o + 17]]);
            let code = u16::from_le_bytes([buf[o + 18], buf[o + 19]]);
            let val = i32::from_le_bytes([buf[o + 20], buf[o + 21], buf[o + 22], buf[o + 23]]);
            if ty != EV_KEY || code != KEY_POWER {
                continue;
            }
            // 1 = press, 0 = release, 2 = autorepeat. Only the edges
            // matter; a repeat must not restart the long-press clock.
            let edge = match val {
                1 => KeyEv::Press,
                0 => KeyEv::Release,
                _ => continue,
            };
            // a flush of buffered history would otherwise reach feed() as
            // a run of pairs and blank the panel for no reason
            if ev_is_stale(&buf, o, now) {
                stale_dropped += 1;
                continue;
            }
            kb.push(edge);
        }
    }
    if stale_dropped > 0 {
        log_stale_drop(stale_dropped);
    }
    (kb, uev_seen)
}

// ------------------------------------------------------------------ //
// power actions                                                       //
// ------------------------------------------------------------------ //

fn hold_wakelock() {
    if let Err(e) = File::create("/sys/power/wake_lock")
        .and_then(|mut f| f.write_all(WAKELOCK_NAME))
    {
        loge!("wake_lock failed: {}", e);
    }
}

fn release_wakelock() {
    let _ = File::create("/sys/power/wake_unlock")
        .and_then(|mut f| f.write_all(WAKELOCK_NAME));
}

/// Reboot to OS on long power-key press, gated by battery voltage.
/// Returns false if battery voltage is too low to boot, falling back to screen toggle.
fn boot_to_os(_scr: &mut Screen) -> bool {
    let mv = battery_voltage_mv();
    if !PowerKey::vbat_allows_boot(mv) {
        logi!(
            "charger: VBAT <= {}: holding in charger mode ({} mV)",
            BOOT_VMIN_MV,
            mv.unwrap_or(0)
        );
        return false;
    }
    logi!(
        "power key long press: rebooting to OS (vbat {} mV)",
        mv.unwrap_or(0)
    );
    release_wakelock();
    unsafe { sync() };
    // the crtc is left running: the composer reconfigures KMS on the way up
    do_reboot(REBOOT_CMD_RESTART);
    loge!("reboot failed: {}", errno_str());
    true
}

fn power_off(scr: &mut Screen) {
    logi!("charger removed, powering off");
    let surf = scr.surf;
    draw_black(scr.buf(), &surf);
    drm_disable(scr);
    release_wakelock();
    unsafe { sync() };
    do_reboot(REBOOT_CMD_POWER_OFF);
    loge!("poweroff failed: {}", errno_str());
}

// ------------------------------------------------------------------ //

fn idle_forever(why: &str) -> ! {
    loge!("{}: idling (no crash loop)", why);
    // hold the wakelock and do nothing; a crash loop here would reboot-loop
    // the whole charger mode
    loop {
        std::thread::sleep(std::time::Duration::from_secs(3600));
    }
}

fn main() {
    // Rust ignores SIGPIPE by default; open kmsg for direct logging
    if let Ok(f) = OpenOptions::new()
        .write(true)
        .append(true)
        .open("/dev/kmsg")
    {
        // a poisoned mutex here would abort the process; the log is
        // optional, the charger is not
        if let Ok(mut g) = KMSG.lock() {
            *g = Some(f);
        }
    }

    logi!("kpoc_charger (static rebuild, rust) starting, pid={}", std::process::id());

    hold_wakelock();

    let mut scr = match drm_open() {
        Some(s) => s,
        None => idle_forever("no DRM output"),
    };
    let tab = match table_load(scr.surf.frame_bytes()) {
        Some(t) => t,
        None => idle_forever("no logo table"),
    };
    let mut keys = keys_open();
    keys.drain();
    let uev_fd = uev_open();

    let mut cap = read_capacity().unwrap_or(-1);
    let mut temp = read_temp().unwrap_or(-1);
    if cap < 0 {
        // If initial capacity is unknown, wait briefly for the first battery uevent.
        if let Some(fd) = uev_fd {
            if uev_wait_first(fd, 2500) {
                cap = read_capacity().unwrap_or(-1);
                temp = read_temp().unwrap_or(-1);
            }
        }
    }
    logi!("initial cap={} temp={}", cap, temp);

    let mut mode = ui_mode(cap, temp, &tab);
    let mut frame = anim_range(mode).map_or(0, |r| r.first);
    let surf = scr.surf;
    draw_ui(scr.buf(), &surf, &tab, mode, frame, cap);
    backlight_setup();
    let mut last_cap = cap;
    let mut last_temp = temp;
    let mut no_charger_reads: u32 = 0;
    let mut pkey = PowerKey::new();

    let mut tick: u32 = 0;
    // wall-clock deadline (monotonic ms) for the next animation frame;
    // 0 means "due now", so the first frame lands on the first loop pass
    let mut next_frame_ms: i64 = 0;
    let mut screen_on_since: i64 = kernel_clocks_ms().1;
    loop {
        // While a key is held, the poll interval drops to KEY_POLL_MS
        // to measure hold duration accurately. When the screen is on, the
        // timeout is also capped at the time remaining to the next frame.
        let poll_ms = if pkey.screen_on {
            let now_mo = kernel_clocks_ms().1;
            let due_ms = (next_frame_ms - now_mo).clamp(0, POLL_MS as i64) as i32;
            key_poll_ms(pkey.press.is_some()).min(due_ms)
        } else {
            key_poll_ms(pkey.press.is_some())
        };
        let (kbatch, uev_seen) = input_poll(&mut keys, uev_fd, poll_ms);
        let mut action = pkey.feed(&kbatch);
        // Trigger boot as soon as threshold is exceeded, without waiting for release.
        if action == KeyAction::None && pkey.held_long_enough() {
            pkey.cancel();
            action = KeyAction::BootOs;
        }
        match action {
            KeyAction::BootOs => {
                if !boot_to_os(&mut scr) {
                    // Battery too low to boot: fall through to screen toggle.
                    rt_monitor_tick();
                    if pkey.screen_on {
                        screen_suspend(&mut scr, &mut pkey);
                    } else {
                        screen_resume(&mut scr, &mut pkey, &tab, mode, frame, cap);
                        if pkey.screen_on {
                            screen_on_since = kernel_clocks_ms().1;
                            next_frame_ms = screen_on_since + ANIM_FRAME_MS;
                        }
                    }
                }
            }
            KeyAction::ToggleScreen => {
                // Notify RT_Monitor watchdog on screen toggle.
                rt_monitor_tick();
                if pkey.screen_on {
                    screen_suspend(&mut scr, &mut pkey);
                } else {
                    screen_resume(&mut scr, &mut pkey, &tab, mode, frame, cap);
                    if pkey.screen_on {
                        screen_on_since = kernel_clocks_ms().1;
                        next_frame_ms = screen_on_since + ANIM_FRAME_MS;
                    }
                }
            }
            KeyAction::None => {}
        }

        // Auto-dismiss charging screen after SCREEN_TIMEOUT_MS of inactivity.
        let now_frame = kernel_clocks_ms().1;
        if pkey.screen_on && now_frame - screen_on_since >= SCREEN_TIMEOUT_MS {
            screen_suspend(&mut scr, &mut pkey);
        }

        tick = tick.wrapping_add(1);
        let now_frame = kernel_clocks_ms().1;
        if now_frame >= next_frame_ms {
            // while the panel is dark nothing is blitted, but the state
            // poll below still runs every pass: an unplug must still
            // power the device off.
            if pkey.screen_on {
                if let Some(r) = anim_range(mode) {
                    frame = anim_next(frame, r);
                    draw_anim_wave_only(scr.buf(), &surf, &tab, frame, cap);
                }
            }
            next_frame_ms = now_frame + ANIM_FRAME_MS;
        }

        if tick % STATE_POLL_DIV != 0 && !uev_seen {
            continue;
        }

        cap = read_capacity().unwrap_or(-1);
        temp = read_temp().unwrap_or(-1);
        let chg = charger_present();

        if !chg {
            no_charger_reads += 1;
            if no_charger_reads >= UNPLUG_TRIP {
                power_off(&mut scr);
                continue; // unreachable if reboot works
            }
        } else {
            no_charger_reads = 0;
        }

        let new_mode = ui_mode(cap, temp, &tab);
        // redraw only when the composed image changes: mode or cap
        if needs_redraw(mode, new_mode, cap, last_cap) {
            logi!(
                "state change: cap={} temp={} mode={:?} (was cap={} temp={} mode={:?})",
                cap,
                temp,
                new_mode,
                last_cap,
                last_temp,
                mode
            );
            mode = new_mode;
            frame = anim_range(mode).map_or(0, |r| r.first);
            if pkey.screen_on {
                draw_ui(scr.buf(), &surf, &tab, mode, frame, cap);
            }
            last_cap = cap;
            last_temp = temp;
        }
    }
}

// ------------------------------------------------------------------ //
// Tests: run on host via: rustc --test --edition 2021 kpoc_charger.rs //
// ------------------------------------------------------------------ //

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn netlink_constants() {
        assert_eq!(AF_NETLINK, 16); // 2 is AF_INET
        assert_eq!(SOCK_DGRAM, 2); // SOCK_STREAM is 1; SOCK_DGRAM is 2
        assert_eq!(SOCK_CLOEXEC, 0x80000);
        assert_eq!(NETLINK_KOBJECT_UEVENT, 15);
        assert_eq!(__NR_SOCKET, 198);
        assert_eq!(__NR_BIND, 200);
        assert_eq!(__NR_RECVFROM, 207);
        assert_eq!(__NR_CLOSE, 57);
    }

    // the pixel format the KMS path blits in: 'XR24' little-endian
    #[test]
    fn drm_constants() {
        assert_eq!(DRM_FORMAT_XRGB8888, 0x3432_5258);
        assert_eq!(DRM_MODE_CONNECTED, 1);
        assert_eq!(DRM_SET_MASTER, 0x641e);
    }

    #[test]
    fn strtol_like_parsing() {
        let dir = std::env::temp_dir();
        let mk = |name: &str, content: &str| {
            let p = dir.join(name);
            std::fs::write(&p, content).unwrap();
            p
        };
        let cases: &[(&str, &str, Option<i32>)] = &[
            ("int_a", "81\n", Some(81)),
            ("int_b", "  4500\n", Some(4500)),
            ("int_c", "-12\n", Some(-12)),
            ("int_d", "\n", None),
            ("int_e", "abc\n", None),
            ("int_f", "", None),
        ];
        for (name, content, want) in cases {
            let p = mk(name, content);
            assert_eq!(read_int_file(&p.to_string_lossy()), *want, "case {}", name);
        }
    }

    fn mk_uevent(fields: &[&str]) -> Vec<u8> {
        let mut v = Vec::new();
        for f in fields {
            v.extend_from_slice(f.as_bytes());
            v.push(0);
        }
        v
    }

    #[test]
    fn uevent_battery_parsing() {
        let msg = mk_uevent(&[
            "change@/devices/platform/soc/1000d000.pwrap/1000d000.pwrap:mt6358-pmic/mt6358-gauge/power_supply/battery",
            "SUBSYSTEM=power_supply",
            "POWER_SUPPLY_NAME=battery",
            "POWER_SUPPLY_STATUS=Charging",
            "POWER_SUPPLY_CAPACITY=57",
            "POWER_SUPPLY_TEMP=305",
            "POWER_SUPPLY_VOLTAGE_NOW=4123000",
        ]);
        let info = parse_uevent(&msg).expect("must parse");
        assert_eq!(info.name, "battery");
        assert_eq!(info.cap, Some(57));
        assert_eq!(info.temp, Some(305));
        assert_eq!(info.status.as_deref(), Some("Charging"));
        assert_eq!(info.online, None);
    }

    #[test]
    fn uevent_ps_apply_semantics() {
        let mut ps = PsState {
            cap: None,
            temp: None,
            volt_uv: None,
            charging: None,
            online: None,
            ivolt_mv: None,
            ilim_ma: None,
            c_max_ua: None,
            ps_type: None,
            updates: 0,
        };
        // usb online
        let usb = mk_uevent(&[
            "change@/devices/platform/x/power_supply/usb",
            "POWER_SUPPLY_NAME=usb",
            "POWER_SUPPLY_ONLINE=1",
        ]);
        ps_apply(&mut ps, &parse_uevent(&usb).unwrap());
        assert_eq!(ps.online, Some(true));
        // battery charging with capacity + temp
        let bat = mk_uevent(&[
            "change@/devices/platform/x/power_supply/battery",
            "POWER_SUPPLY_NAME=battery",
            "POWER_SUPPLY_STATUS=Charging",
            "POWER_SUPPLY_CAPACITY=42",
            "POWER_SUPPLY_TEMP=311",
        ]);
        ps_apply(&mut ps, &parse_uevent(&bat).unwrap());
        assert_eq!(ps.cap, Some(42));
        assert_eq!(ps.temp, Some(311));
        assert_eq!(ps.charging, Some(true));
        // out-of-range capacity is ignored
        let bad = mk_uevent(&[
            "change@/devices/platform/x/power_supply/battery",
            "POWER_SUPPLY_NAME=battery",
            "POWER_SUPPLY_CAPACITY=200",
        ]);
        ps_apply(&mut ps, &parse_uevent(&bad).unwrap());
        assert_eq!(ps.cap, Some(42));
        // a non-power_supply event parses to None (no NAME key)
        assert!(parse_uevent(b"add@/devices/platform/foo\0ACTION=add\0").is_none());
        // unplugged: battery Discharging + usb offline
        let off = mk_uevent(&[
            "change@/devices/platform/x/power_supply/battery",
            "POWER_SUPPLY_NAME=battery",
            "POWER_SUPPLY_STATUS=Discharging",
            "POWER_SUPPLY_CAPACITY=41",
        ]);
        ps_apply(&mut ps, &parse_uevent(&off).unwrap());
        assert_eq!(ps.charging, Some(false));
        assert_eq!(ps.cap, Some(41));
    }

    // a table that claims to have everything, so ui_mode's `have()` guards
    // never fall through to LOGO_BASE while we test the mapping itself
    fn full_table() -> LogoTable {
        LogoTable {
            count: 61,
            entries: vec![Some(Vec::new()); 61],
            fb_bytes: 1080 * 2400 * 4,
        }
    }

    #[test]
    fn ui_mode_mapping() {
        let t = full_table();
        // over temperature wins over everything
        assert_eq!(
            ui_mode(55, OVERTEMP_DEG_C, &t),
            UiMode::Static(LOGO_OVTEMP)
        );
        // 0% to 99% animates
        for cap in 0..=99 {
            assert_eq!(ui_mode(cap, 300, &t), UiMode::Anim, "cap {}", cap);
        }
        // 100% is the static full screen
        assert_eq!(ui_mode(100, 300, &t), UiMode::Static(LOGO_FULL));
        assert_eq!(ui_mode(101, 300, &t), UiMode::Static(LOGO_FULL));
        // capacity still unknown: plain base frame, no digits
        assert_eq!(ui_mode(-1, 300, &t), UiMode::Static(LOGO_GREEN_BASE));
    }

    #[test]
    fn ui_mode_degrades_when_entries_missing() {
        // an empty table must never be claimed to have a screen
        let t = LogoTable {
            count: 0,
            entries: Vec::new(),
            fb_bytes: 0,
        };
        for cap in [-1, 0, 15, 50, 99, 100] {
            assert_eq!(
                ui_mode(cap, 300, &t),
                UiMode::Static(LOGO_GREEN_BASE),
                "cap {}",
                cap
            );
        }
        // over temperature with no ovtemp entry falls through, not crashes
        assert_eq!(
            ui_mode(50, OVERTEMP_DEG_C + 5, &t),
            UiMode::Static(LOGO_GREEN_BASE)
        );
    }

    #[test]
    fn redraw_ignores_temperature_noise() {
        // same mode and same capacity: nothing on screen changed, however
        // far the temperature moved
        for t in [300, 599, 600, 601, 900] {
            assert!(
                !needs_redraw(UiMode::Static(1), UiMode::Static(1), 100, 100),
                "temp {} must not force a repaint",
                t
            );
            assert!(
                !needs_redraw(UiMode::Anim, UiMode::Anim, 42, 42),
                "temp {} must not force a repaint",
                t
            );
        }
        // a capacity change does, in both modes
        assert!(needs_redraw(UiMode::Static(1), UiMode::Static(1), 99, 100));
        assert!(needs_redraw(UiMode::Anim, UiMode::Anim, 43, 42));
        // and so does a mode change at constant capacity
        assert!(needs_redraw(UiMode::Static(1), UiMode::Static(2), 100, 100));
        assert!(needs_redraw(UiMode::Static(2), UiMode::Anim, 50, 50));
        assert!(needs_redraw(UiMode::Anim, UiMode::Static(2), 50, 50));
    }

    #[test]
    fn anim_next_cycles_0_to_9() {
        let r = anim_range(UiMode::Anim).expect("Anim must have a range");
        assert_eq!((r.first, r.last), (0, 9));
        let mut f = 0;
        let mut seen = Vec::new();
        for _ in 0..12 {
            f = anim_next(f, r);
            seen.push(f);
            assert!(f <= 9, "frame {} out of range", f);
        }
        assert_eq!(seen, vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2]);
        assert_eq!(anim_next(9, r), 0);
        assert_eq!(anim_next(10, r), 0);
    }

    #[test]
    fn anim_range_static_modes_have_none() {
        for m in [
            UiMode::Static(LOGO_GREEN_BASE),
            UiMode::Static(LOGO_FULL),
            UiMode::Static(LOGO_LOW),
            UiMode::Static(LOGO_OVTEMP),
        ] {
            assert_eq!(anim_range(m), None, "{:?} must not animate", m);
        }
    }

    // ------------------------------------------------------------------ //
    // super charge                                                        //
    // ------------------------------------------------------------------ //

    #[test]
    fn input_watts_math() {
        // the device's current cable: 4600 mV x 1200 mA = 5.52 W -> 5 W
        assert_eq!(input_watts(Some(4600), Some(1200), None), Some(5));
        // a 45 W VOOC/Warp-class supply: 5 V x 9 A
        assert_eq!(input_watts(Some(5000), Some(9000), None), Some(45));
        // 10 V x 4.5 A
        assert_eq!(input_watts(Some(10000), Some(4500), None), Some(45));
        // CURRENT_MAX is in uA: 4600 mV x 4 500 000 uA = 20 W
        assert_eq!(input_watts(Some(4600), None, Some(4_500_000)), Some(20));
        // the larger of the two estimates wins: INPUT_CURRENT_LIMIT lags
        // during ramp-up, CURRENT_MAX is the adapter's own ceiling
        assert_eq!(input_watts(Some(5000), Some(1000), Some(9_000_000)), Some(45));
        assert_eq!(input_watts(Some(5000), Some(9000), Some(1_000_000)), Some(45));
        // nothing usable -> None, never a bogus zero that reads as "no charge"
        assert_eq!(input_watts(None, Some(9000), None), None);
        assert_eq!(input_watts(Some(5000), None, None), None);
        assert_eq!(input_watts(Some(0), Some(9000), None), None);
        assert_eq!(input_watts(Some(-5000), Some(9000), None), None);
        assert_eq!(input_watts(Some(5000), Some(0), None), None);
        assert_eq!(input_watts(Some(5000), Some(-9000), None), None);
        // overflow: 20 V x 5 A in i64 before the divide, no wrap
        assert_eq!(input_watts(Some(20000), Some(5000), None), Some(100));
    }

    #[test]
    fn logo_partition_fallback_chain() {
        // first path missing -> falls through to the real logo file
        let path = match std::env::var("KPOC_TEST_LOGO") {
            Ok(p) => p,
            Err(_) => return,
        };
        let t = table_load_from(&["/dev/does/not/exist", &path], 1080 * 2400 * 4)
            .expect("must fall back to the second path");
        assert!(t.have(LOGO_GREEN_BASE));
        assert_eq!(
            t.entries[LOGO_GREEN_BASE].as_ref().unwrap().len(),
            1080 * 2400 * 4
        );
    }

    #[test]
    fn fallback_survives_a_candidate_that_opens_but_is_garbage() {
        // logo, logo_a and logo_b are all plausible on an A/B device; a
        // partition that opens but is not a logo table must not abort the
        // whole chain
        let dir = std::env::temp_dir();
        let junk = dir.join("kpoc_junk_logo.bin");
        std::fs::write(&junk, vec![0x5au8; 4096]).unwrap();
        let path = match std::env::var("KPOC_TEST_LOGO") {
            Ok(p) => p,
            Err(_) => return,
        };
        let t = table_load_from(
            &[junk.to_str().unwrap(), "/dev/null", &path],
            1080 * 2400 * 4,
        )
        .expect("must skip the junk candidates");
        assert_eq!(t.count, 61);
    }

    // the exact geometry the KMS path blits into, matching a 1080x2400 panel
    fn panel_surf() -> Surf {
        Surf {
            row_bytes: 1080 * 4,
            w: 1080,
            h: 2400,
        }
    }

    fn px(dst: &[u8], s: &Surf, x: usize, y: usize) -> [u8; 4] {
        let o = y * s.row_bytes + x * 4;
        dst[o..o + 4].try_into().unwrap()
    }

    /// true inside the three digit boxes the percent block occupies
    fn in_digit_box(x: usize, y: usize) -> bool {
        if y < DIGIT_Y || y >= DIGIT_Y + DIGIT_H {
            return false;
        }
        (x >= DIGIT1_X && x < DIGIT1_X + DIGIT_W)
            || (x >= DIGIT2_X && x < DIGIT2_X + DIGIT_W)
            || (x >= PCT_X && x < PCT_X + PCT_W)
    }

    #[test]
    fn blit_respects_a_padded_pitch() {
        // a driver may pad rows; the blit must stride by row_bytes, not w*4
        let s = Surf {
            row_bytes: 8 * 4 + 16,
            w: 8,
            h: 4,
        };
        let mut dst = vec![0xaau8; s.row_bytes * s.h];
        let src: Vec<u8> = (0..(8 * 4 * 4)).map(|i| (i % 251) as u8).collect();
        blit_frame(&mut dst, &s, &src);
        for y in 0..s.h {
            // the pixel area matches the source row exactly
            assert_eq!(&dst[y * s.row_bytes..y * s.row_bytes + 8 * 4], &src[y * 8 * 4..(y + 1) * 8 * 4]);
            // the 16 pad bytes are left untouched
            assert!(dst[y * s.row_bytes + 8 * 4..y * s.row_bytes + 8 * 4 + 16].iter().all(|&b| b == 0xaa));
        }
    }

    #[test]
    fn anim_frame_composition_is_pixel_exact() {
        let path = match std::env::var("KPOC_TEST_LOGO") {
            Ok(p) => p,
            Err(_) => return,
        };
        let s = panel_surf();
        let t = table_load_from(&[&path], s.frame_bytes()).expect("table must load");

        // cap=42: two digits + '%' over LOGO_GREEN_BASE + green well fill
        let cap = 42;
        let mut dst = vec![0u8; s.row_bytes * s.h];
        draw_ui(&mut dst, &s, &t, UiMode::Anim, 0, cap);

        let base = t.entries[LOGO_GREEN_BASE].as_ref().unwrap();
        let glyphs: [(usize, usize, &Vec<u8>); 3] = [
            (DIGIT1_X, DIGIT_W, t.entries[LOGO_DIGIT0 + cap as usize / 10].as_ref().unwrap()),
            (DIGIT2_X, DIGIT_W, t.entries[LOGO_DIGIT0 + cap as usize % 10].as_ref().unwrap()),
            (PCT_X, PCT_W, t.entries[LOGO_PCT].as_ref().unwrap()),
        ];

        let in_well = |x: usize, y: usize| {
            x >= WELL_X && x < WELL_X + WELL_W && y >= WELL_Y_TOP && y <= WELL_Y_BOT
        };
        for y in 0..s.h {
            for x in 0..s.w {
                if in_digit_box(x, y) || in_well(x, y) {
                    continue;
                }
                let want = &base[y * s.w * 4 + x * 4..y * s.w * 4 + x * 4 + 4];
                assert_eq!(px(&dst, &s, x, y), <[u8; 4]>::try_from(want).unwrap(), "({},{})", x, y);
            }
        }
        // at 99% the well is filled with green nearly to the top
        let mut dst99 = vec![0u8; s.row_bytes * s.h];
        draw_ui(&mut dst99, &s, &t, UiMode::Anim, 0, 99);
        let p99 = px(&dst99, &s, WELL_X + WELL_W / 2, WELL_Y_TOP + 10);
        assert!(p99[1] > 150 && p99[2] < 100, "99% must be green near top, got {:?}", p99);

        // at 0% '0%' is drawn centered
        let mut dst0 = vec![0u8; s.row_bytes * s.h];
        draw_ui(&mut dst0, &s, &t, UiMode::Anim, 0, 0);
        let g0 = t.entries[LOGO_DIGIT0].as_ref().unwrap();
        let g_pct = t.entries[LOGO_PCT].as_ref().unwrap();
        for r in 0..DIGIT_H {
            for c in 0..DIGIT_W {
                let src = &g0[r * DIGIT_W * 4 + c * 4..r * DIGIT_W * 4 + c * 4 + 4];
                assert_eq!(px(&dst0, &s, DIGIT_SINGLE_X + c, DIGIT_Y + r), <[u8; 4]>::try_from(src).unwrap());
            }
            for c in 0..PCT_W {
                let src = &g_pct[r * PCT_W * 4 + c * 4..r * PCT_W * 4 + c * 4 + 4];
                assert_eq!(px(&dst0, &s, PCT_SINGLE_X + c, DIGIT_Y + r), <[u8; 4]>::try_from(src).unwrap());
            }
        }

        // every pixel inside a digit box is the untouched glyph
        for (gx, gw, g) in glyphs {
            for r in 0..DIGIT_H {
                for c in 0..gw {
                    let src = &g[r * gw * 4 + c * 4..r * gw * 4 + c * 4 + 4];
                    assert_eq!(
                        px(&dst, &s, gx + c, DIGIT_Y + r),
                        <[u8; 4]>::try_from(src).unwrap(),
                        "glyph at x={} ({},{})",
                        gx, c, r
                    );
                }
            }
        }
    }

    #[test]
    fn anim_wave_crest_cycles_cleanly() {
        let path = match std::env::var("KPOC_TEST_LOGO") {
            Ok(p) => p,
            Err(_) => return,
        };
        let s = panel_surf();
        let t = table_load_from(&[&path], s.frame_bytes()).expect("table must load");
        let r = anim_range(UiMode::Anim).unwrap();

        let cap = 50;
        let mut wave_pixel_samples = Vec::new();
        let mut f = r.first;
        for _ in 0..=r.last {
            let mut dst = vec![0u8; s.row_bytes * s.h];
            draw_ui(&mut dst, &s, &t, UiMode::Anim, f, cap);
            let fill_y = (WELL_Y_BOT as i32 - (WELL_H as i32 * cap) / 100) as usize;
            let sample_y = fill_y - 6;
            let sample = px(&dst, &s, WELL_X + 20, sample_y);
            wave_pixel_samples.push(sample);

            let bot_sample = px(&dst, &s, WELL_X + 50, WELL_Y_BOT - 10);
            assert!(bot_sample[1] > 150 && bot_sample[2] < 100);

            f = anim_next(f, r);
        }
        assert!(wave_pixel_samples.windows(2).any(|w| w[0] != w[1]));
    }

    #[test]
    fn anim_wave_only_preserves_surroundings() {
        let path = match std::env::var("KPOC_TEST_LOGO") {
            Ok(p) => p,
            Err(_) => return,
        };
        let s = panel_surf();
        let t = table_load_from(&[&path], s.frame_bytes()).expect("table must load");
        let cap = 50;
        let mut full = vec![0u8; s.row_bytes * s.h];
        draw_ui(&mut full, &s, &t, UiMode::Anim, 0, cap);

        let mut step = full.clone();
        draw_anim_wave_only(&mut step, &s, &t, 1, cap);

        let fill_y = (WELL_Y_BOT as i32 - (WELL_H as i32 * cap) / 100) as usize;
        let wave_y = fill_y.saturating_sub(WAVE_H).max(WELL_Y_TOP);

        let wave_start_byte = wave_y * s.row_bytes;
        let wave_end_byte = (wave_y + WAVE_H) * s.row_bytes;
        assert_eq!(&step[..wave_start_byte], &full[..wave_start_byte], "pixels above wave changed");
        assert_eq!(&step[wave_end_byte..], &full[wave_end_byte..], "pixels below wave changed");
        assert_ne!(
            &step[wave_start_byte..wave_end_byte],
            &full[wave_start_byte..wave_end_byte],
            "wave crest was not updated"
        );
    }

    #[test]
    fn real_logo_table() {
        let path = match std::env::var("KPOC_TEST_LOGO") {
            Ok(p) => p,
            Err(_) => return,
        };
        let fb_bytes = 1080usize * 2400 * 4;
        let t = table_load_from(&[&path], fb_bytes).expect("table must load");
        assert_eq!(t.count, 61, "logo table has 61 entries");

        // Selective loading: full frames
        for i in [LOGO_LOW, LOGO_OVTEMP, LOGO_FULL, LOGO_GREEN_BASE] {
            assert!(t.have(i), "entry {} missing", i);
            assert_eq!(
                t.entries[i].as_ref().unwrap().len(),
                fb_bytes,
                "entry {} not a full frame",
                i
            );
        }
        // digits 0..9: 42x60 ARGB
        for d in 0..10 {
            assert!(t.have(LOGO_DIGIT0 + d), "digit {} missing", d);
            assert_eq!(
                t.entries[LOGO_DIGIT0 + d].as_ref().unwrap().len(),
                DIGIT_W * DIGIT_H * 4,
                "digit {} wrong size",
                d
            );
        }
        // '%' glyph: 48x60 ARGB
        assert_eq!(
            t.entries[LOGO_PCT].as_ref().unwrap().len(),
            PCT_W * PCT_H * 4
        );
        // wave crests: 224x12 ARGB (entries 15..=24)
        for w in LOGO_WAVE_FIRST..=LOGO_WAVE_LAST {
            assert!(t.have(w), "wave entry {} missing", w);
            assert_eq!(
                t.entries[w].as_ref().unwrap().len(),
                WAVE_W * WAVE_H * 4
            );
        }
        // green row: 224x1 ARGB
        assert_eq!(
            t.entries[LOGO_GREEN_ROW].as_ref().unwrap().len(),
            WELL_W * 4
        );
    }

    // ---- power key --------------------------------------------------------

    /// build a batch out of a plain edge list, e.g. &["P", "R"]
    fn mk_batch(edges: &[u8]) -> KeyBatch {
        let mut b = KeyBatch::new();
        for e in edges {
            match e {
                b'P' => b.push(KeyEv::Press),
                b'R' => b.push(KeyEv::Release),
                _ => b.push(KeyEv::None),
            }
        }
        b
    }

    #[test]
    fn keybatch_overflow_is_dropped_not_fatal() {
        let mut b = KeyBatch::new();
        for _ in 0..KEY_BATCH_MAX * 4 {
            b.push(KeyEv::Press);
        }
        assert_eq!(b.n, KEY_BATCH_MAX, "batch must clamp, not grow or panic");
    }

    #[test]
    fn powerkey_short_press_toggles_the_panel() {
        let mut k = PowerKey::new();
        assert!(k.screen_on, "charger mode starts with the panel live");
        assert_eq!(k.feed(&mk_batch(b"P")), KeyAction::None);
        // released immediately: a short press
        assert_eq!(k.feed(&mk_batch(b"R")), KeyAction::ToggleScreen);
        assert!(k.press.is_none(), "the press must be consumed");
        // ...and the next short press toggles back rather than blanking again
        assert_eq!(k.feed(&mk_batch(b"P")), KeyAction::None);
        assert_eq!(k.feed(&mk_batch(b"R")), KeyAction::ToggleScreen);
    }

    #[test]
    fn powerkey_long_press_boots() {
        let mut k = PowerKey::new();
        k.feed(&mk_batch(b"P"));
        // Hold past the threshold without a release: triggers boot directly
        std::thread::sleep(std::time::Duration::from_millis(KEY_LONG_MS + 40));
        assert!(k.held_long_enough());
        assert_eq!(k.feed(&mk_batch(b"R")), KeyAction::BootOs);
        assert!(k.press.is_none());
    }

    #[test]
    fn powerkey_release_without_press_is_ignored() {
        let mut k = PowerKey::new();
        // a stray release (or a release read before its press) must not
        // reboot the device
        assert_eq!(k.feed(&mk_batch(b"R")), KeyAction::None);
        assert_eq!(k.feed(&mk_batch(b"R")), KeyAction::None);
        assert!(k.screen_on);
    }

    #[test]
    fn powerkey_press_release_press_keeps_the_action_and_the_press() {
        let mut k = PowerKey::new();
        // a fast double tap inside one poll batch: the first press is
        // completed, the second is left pending for the next batch
        assert_eq!(k.feed(&mk_batch(b"PRP")), KeyAction::ToggleScreen);
        assert!(k.press.is_some(), "the trailing press must stay pending");
    }

    #[test]
    fn powerkey_autorepeat_does_not_restart_the_clock() {
        let mut k = PowerKey::new();
        k.feed(&mk_batch(b"P"));
        // evdev value 2 is never translated into an edge, so the only way
        // the clock can restart is a real press
        let b = mk_batch(b"");
        assert_eq!(b.n, 0);
        std::thread::sleep(std::time::Duration::from_millis(KEY_LONG_MS + 40));
        assert!(k.held_long_enough());
        assert_eq!(k.feed(&mk_batch(b"R")), KeyAction::BootOs);
    }

    #[test]
    fn powerkey_cancel_drops_the_pending_press() {
        let mut k = PowerKey::new();
        k.feed(&mk_batch(b"P"));
        k.cancel();
        assert!(!k.held_long_enough());
        // the release that follows a boot must not queue a second action
        assert_eq!(k.feed(&mk_batch(b"R")), KeyAction::None);
    }

    #[test]
    fn powerkey_empty_batch_is_a_no_op() {
        let mut k = PowerKey::new();
        assert_eq!(k.feed(&KeyBatch::new()), KeyAction::None);
    }

    #[test]
    fn boot_guard_allows_a_healthy_battery_and_an_unknown_one() {
        // An unreadable voltage must never block a real boot
        assert!(PowerKey::vbat_allows_boot(Some(4123)));
        assert!(PowerKey::vbat_allows_boot(Some(BOOT_VMIN_MV + 1)));
        assert!(PowerKey::vbat_allows_boot(None));
    }

    #[test]
    fn boot_guard_blocks_a_flat_battery() {
        assert!(!PowerKey::vbat_allows_boot(Some(3200)));
        assert!(!PowerKey::vbat_allows_boot(Some(BOOT_VMIN_MV)));
    }

    #[test]
    fn rt_monitor_tick_without_the_node_is_silent() {
        // /dev/RT_Monitor does not exist on the host; the call must
        // disable itself and return instead of panicking
        RT_MONITOR_OK.store(true, Ordering::Relaxed);
        rt_monitor_tick();
        assert!(!RT_MONITOR_OK.load(Ordering::Relaxed));
        // a second call is a no-op, not a retry storm
        rt_monitor_tick();
        RT_MONITOR_OK.store(true, Ordering::Relaxed);
    }

    #[test]
    fn rt_monitor_constants() {
        assert_eq!(RT_MONITOR_TICK, 0x8004_700a);
        assert_eq!(RT_MONITOR_TICK_MS, 300);
        assert_eq!(RT_MONITOR_DEV, "/dev/RT_Monitor");
    }

    #[test]
    fn backlight_set_without_the_node_does_not_panic() {
        // no /sys/class/leds/lcd-backlight on the host: the function must
        // log and return, leaving the caller to carry on
        backlight_set(true);
        backlight_set(false);
    }

    // ---- voltage plumbing -------------------------------------------------

    #[test]
    fn uevent_battery_voltage_is_parsed() {
        let msg = mk_uevent(&[
            "change@/devices/platform/soc/1000d000.pwrap/power_supply/battery",
            "POWER_SUPPLY_NAME=battery",
            "POWER_SUPPLY_VOLTAGE_NOW=4123000",
        ]);
        let info = parse_uevent(&msg).expect("must parse");
        assert_eq!(info.voltage_uv, Some(4123000));
    }

    #[test]
    fn uevent_voltage_reaches_ps_state() {
        let mut ps = PsState {
            cap: None,
            temp: None,
            volt_uv: None,
            charging: None,
            online: None,
            ivolt_mv: None,
            ilim_ma: None,
            c_max_ua: None,
            ps_type: None,
            updates: 0,
        };
        let batt = mk_uevent(&[
            "change@/devices/platform/soc/power_supply/battery",
            "POWER_SUPPLY_NAME=battery",
            "POWER_SUPPLY_VOLTAGE_NOW=3980000",
        ]);
        ps_apply(&mut ps, &parse_uevent(&batt).unwrap());
        assert_eq!(ps.volt_uv, Some(3980000));

        // a partial uevent that omits the key must not wipe the reading
        let bare = mk_uevent(&[
            "change@/devices/platform/soc/power_supply/battery",
            "POWER_SUPPLY_NAME=battery",
            "POWER_SUPPLY_CAPACITY=61",
        ]);
        ps_apply(&mut ps, &parse_uevent(&bare).unwrap());
        assert_eq!(ps.volt_uv, Some(3980000), "a good reading must survive");

        // a garbage value must be ignored, not stored as 0
        let bad = mk_uevent(&[
            "change@/devices/platform/soc/power_supply/battery",
            "POWER_SUPPLY_NAME=battery",
            "POWER_SUPPLY_VOLTAGE_NOW=0",
        ]);
        ps_apply(&mut ps, &parse_uevent(&bad).unwrap());
        assert_eq!(ps.volt_uv, Some(3980000));
    }

    #[test]
    fn uevent_voltage_from_another_supply_is_ignored() {
        let mut ps = PsState {
            cap: None,
            temp: None,
            volt_uv: None,
            charging: None,
            online: None,
            ivolt_mv: None,
            ilim_ma: None,
            c_max_ua: None,
            ps_type: None,
            updates: 0,
        };
        // the `charger` supply reports the bus voltage, which says nothing
        // about whether the battery can run the OS
        let chg = mk_uevent(&[
            "change@/devices/platform/soc/power_supply/charger",
            "POWER_SUPPLY_NAME=charger",
            "POWER_SUPPLY_VOLTAGE_NOW=9000000",
        ]);
        ps_apply(&mut ps, &parse_uevent(&chg).unwrap());
        assert_eq!(ps.volt_uv, None);
    }

    #[test]
    fn fill_black_with_a_short_framebuffer_is_safe() {
        // a short fb must not panic: in charger mode a panic is a crash loop
        let s = Surf {
            row_bytes: 64,
            w: 16,
            h: 16,
        };
        let mut short = vec![0u8; 8];
        fill_black(&mut short, &s);
        assert!(short.iter().all(|&b| b == 0));
        // the exact-size buffer still works
        let mut exact = vec![0xffu8; s.row_bytes * s.h];
        fill_black(&mut exact, &s);
        assert!(exact.iter().all(|&b| b == 0));
    }

    // ---- stale input replay ----------------------------------------------

    #[test]
    fn keys_drain_empties_the_queue() {
        // the MTK pwrkey_sync buffer hands a late reader the press/release
        // pairs queued before it existed; drain must leave nothing behind
        let dir = std::env::temp_dir();
        let path = dir.join("kpoc_drain_probe.bin");
        // two full stale pairs, exactly the shape the kernel replays
        std::fs::write(&path, vec![0xa5u8; 4 * INPUT_EV_SIZE]).unwrap();
        let f = OpenOptions::new().read(true).open(&path).unwrap();
        let mut k = Keys { fds: vec![f] };
        k.drain();
        // nothing is left: a second read hits EOF rather than replaying
        let mut buf = [0u8; 64];
        let n = k.fds[0].read(&mut buf).unwrap();
        assert_eq!(n, 0, "drain must consume the whole stale queue");
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn keys_drain_on_an_empty_queue_is_a_no_op() {
        let dir = std::env::temp_dir();
        let path = dir.join("kpoc_drain_empty.bin");
        std::fs::write(&path, b"").unwrap();
        let f = OpenOptions::new().read(true).open(&path).unwrap();
        let mut k = Keys { fds: vec![f] };
        k.drain();
        let mut buf = [0u8; 64];
        assert_eq!(k.fds[0].read(&mut buf).unwrap(), 0);
        std::fs::remove_file(&path).ok();
    }

    #[test]
    fn stale_replay_run_becomes_one_toggle_not_many() {
        // the documented kernel behaviour: four stale pairs in one batch
        // must produce exactly one toggle, and must never boot
        let mut k = PowerKey::new();
        let b = mk_batch(b"PRPRPRPR");
        assert_eq!(k.feed(&b), KeyAction::ToggleScreen);
        assert!(k.press.is_none(), "no press may be left pending");
        assert!(!k.held_long_enough());
    }

    // ---- kernel-timestamp staleness (replayed input history) ------------

    /// build one input_event with an explicit kernel timestamp in ms
    fn mk_ev(ty: u16, code: u16, val: i32, ts_ms: i64) -> [u8; INPUT_EV_SIZE] {
        let mut b = [0u8; INPUT_EV_SIZE];
        b[0..8].copy_from_slice(&(ts_ms / 1000).to_le_bytes());
        b[8..16].copy_from_slice(&((ts_ms % 1000) * 1000).to_le_bytes());
        b[16..18].copy_from_slice(&ty.to_le_bytes());
        b[18..20].copy_from_slice(&code.to_le_bytes());
        b[20..24].copy_from_slice(&val.to_le_bytes());
        b
    }

    /// decode a raw evdev buffer the way input_poll does, minus the fd
    fn decode_live_edges(buf: &[u8], now: (i64, i64)) -> KeyBatch {
        let mut kb = KeyBatch::new();
        for k in 0..buf.len() / INPUT_EV_SIZE {
            let o = k * INPUT_EV_SIZE;
            if ev_is_stale(buf, o, now) {
                continue;
            }
            let ty = u16::from_le_bytes([buf[o + 16], buf[o + 17]]);
            let code = u16::from_le_bytes([buf[o + 18], buf[o + 19]]);
            let val = i32::from_le_bytes([buf[o + 20], buf[o + 21], buf[o + 22], buf[o + 23]]);
            if ty != EV_KEY || code != KEY_POWER {
                continue;
            }
            match val {
                1 => kb.push(KeyEv::Press),
                0 => kb.push(KeyEv::Release),
                _ => {}
            }
        }
        kb
    }

    /// the exact shape observed on device: realtime clock now, and a flush
    /// of four press/release pairs all stamped 1909 s ago
    const PROBE_NOW: (i64, i64) = (1_794_504_283_108, 3_063_697);
    const PROBE_STALE: i64 = 1_794_502_374_068; // 1909 s behind PROBE_NOW.0

    #[test]
    fn a_replayed_flush_produces_no_action_at_all() {
        // four pairs, one frozen timestamp: what the kernel handed a
        // reader on device. Before the filter, feed() collapsed them into
        // one panel toggle the user never asked for.
        let mut buf = Vec::new();
        for _ in 0..4 {
            buf.extend_from_slice(&mk_ev(EV_KEY, KEY_POWER, 1, PROBE_STALE));
            buf.extend_from_slice(&mk_ev(EV_KEY, KEY_POWER, 0, PROBE_STALE));
        }
        let kb = decode_live_edges(&buf, PROBE_NOW);
        assert!(kb.is_empty(), "a replayed flush must not reach feed()");
        let mut k = PowerKey::new();
        assert_eq!(k.feed(&kb), KeyAction::None);
    }

    #[test]
    fn a_live_press_still_reaches_feed() {
        // the same decode with a current timestamp must keep both edges
        let mut buf = Vec::new();
        buf.extend_from_slice(&mk_ev(EV_KEY, KEY_POWER, 1, PROBE_NOW.0 - 20));
        buf.extend_from_slice(&mk_ev(EV_KEY, KEY_POWER, 0, PROBE_NOW.0 - 5));
        let kb = decode_live_edges(&buf, PROBE_NOW);
        assert_eq!(kb.n, 2, "a live press must survive the filter");
        let mut k = PowerKey::new();
        assert_eq!(k.feed(&kb), KeyAction::ToggleScreen);
    }

    #[test]
    fn a_live_monotonic_stamp_is_kept() {
        // a kernel that stamps CLOCK_MONOTONIC must not be filtered
        let mut buf = Vec::new();
        buf.extend_from_slice(&mk_ev(EV_KEY, KEY_POWER, 1, PROBE_NOW.1 - 50));
        buf.extend_from_slice(&mk_ev(EV_KEY, KEY_POWER, 0, PROBE_NOW.1 - 10));
        let kb = decode_live_edges(&buf, PROBE_NOW);
        assert_eq!(kb.n, 2, "a monotonic stamp is a live press");
    }

    #[test]
    fn an_unset_stamp_is_kept() {
        // a zero timestamp is the "no information" case, never stale
        let mut buf = Vec::new();
        buf.extend_from_slice(&mk_ev(EV_KEY, KEY_POWER, 1, 0));
        buf.extend_from_slice(&mk_ev(EV_KEY, KEY_POWER, 0, 0));
        let kb = decode_live_edges(&buf, PROBE_NOW);
        assert_eq!(kb.n, 2, "an unset stamp must not be treated as stale");
    }

    #[test]
    fn a_future_stamp_is_kept() {
        // the clock was stepped forward: the event is not judgeable
        let mut buf = Vec::new();
        buf.extend_from_slice(&mk_ev(EV_KEY, KEY_POWER, 1, PROBE_NOW.0 + 400_000));
        let kb = decode_live_edges(&buf, PROBE_NOW);
        assert_eq!(kb.n, 1, "a stamp beyond the slack must be kept");
    }

    #[test]
    fn a_replay_below_the_threshold_is_kept() {
        // only an impossibly old stamp is dropped; a merely delayed one
        // (still far beyond any real queue delay) must survive
        let mut buf = Vec::new();
        buf.extend_from_slice(&mk_ev(EV_KEY, KEY_POWER, 1, PROBE_NOW.0 - 60_000));
        let kb = decode_live_edges(&buf, PROBE_NOW);
        assert_eq!(kb.n, 1, "60 s is inside the threshold");
    }

    #[test]
    fn ev_ts_ms_reads_the_timeval() {
        let b = mk_ev(EV_KEY, KEY_POWER, 1, 1_794_502_374_068);
        assert_eq!(ev_ts_ms(&b, 0), Some(1_794_502_374_068));
    }

    #[test]
    fn ev_ts_ms_reports_none_when_unset() {
        let b = [0u8; INPUT_EV_SIZE];
        assert_eq!(ev_ts_ms(&b, 0), None);
    }

    #[test]
    fn ev_age_ms_splits_the_clock_domains_by_magnitude() {
        // wall-clock domain
        assert_eq!(ev_age_ms(PROBE_NOW.0 - 20, PROBE_NOW), Some(20));
        // monotonic domain
        assert_eq!(ev_age_ms(PROBE_NOW.1 - 20, PROBE_NOW), Some(20));
    }

    #[test]
    fn ev_age_ms_keeps_a_stamp_when_realtime_is_unusable() {
        // a realtime clock that is not a wall clock at all: a small stamp
        // cannot be told apart from a broken realtime stamp, so it is kept
        let broken = (1_000i64, 3_063_697i64);
        assert_eq!(ev_age_ms(500, broken), None);
    }

    #[test]
    fn key_poll_ms_is_responsive_only_while_held() {
        assert_eq!(key_poll_ms(false), POLL_MS);
        assert_eq!(key_poll_ms(true), KEY_POLL_MS);
        assert!(
            KEY_POLL_MS < POLL_MS,
            "the held interval must be the tighter one"
        );
    }

    // ---- screen toggle state follows the crtc, not the request --------

    #[test]
    fn a_successful_suspend_blanks_the_panel() {
        assert!(!screen_state_after(true, true, true));
        assert!(screen_state_after(true, false, true) == false);
    }

    #[test]
    fn a_successful_resume_lights_the_panel() {
        assert!(screen_state_after(true, false, false));
        assert!(!screen_state_after(true, true, false) == false);
    }

    #[test]
    fn a_failed_suspend_leaves_the_state_alone() {
        // the crtc never stopped: the panel is still lit, so the state
        // must stay "on" or the next press blanks an already-blank panel
        assert!(screen_state_after(false, true, true));
        // and the reverse: already blank, failed suspend, still blank
        assert!(!screen_state_after(false, false, true));
    }

    #[test]
    fn a_failed_resume_leaves_the_state_alone() {
        // the crtc never came up: the panel is still dark, so the state
        // must stay "off" and the next press retries the resume
        assert!(!screen_state_after(false, false, false));
        assert!(screen_state_after(false, true, false));
    }

    #[test]
    fn the_toggle_round_trips_through_both_directions() {
        // on -> off -> on, all ioctls succeeding
        let mut on = true;
        on = screen_state_after(true, on, true);
        assert!(!on, "first press must blank");
        on = screen_state_after(true, on, false);
        assert!(on, "second press must light");
    }

    #[test]
    fn a_failed_resume_needs_exactly_one_more_press() {
        // resume fails once: the state stays "off", so one more press
        // retries. Without this rule the state would read "on" and the
        // extra press would blank the panel instead.
        let mut on = false;
        on = screen_state_after(false, on, false);
        assert!(!on, "failed resume must not claim the panel is up");
        on = screen_state_after(true, on, false);
        assert!(on, "the retry must succeed and light the panel");
    }

    // ---- charger_present_decision: the unplug safety property ---------
    //
    // This is the one decision that can power the device off, so the
    // asymmetry matters: a positive uevent proves the cable is in, but
    // only two agreeing negative uevents prove it is out. Every "cannot
    // tell" case must answer "present" and keep the service alive.

    #[test]
    fn a_charging_uevent_alone_keeps_the_device_on() {
        assert!(charger_present_decision(false, Some(true), None));
    }

    #[test]
    fn an_online_uevent_alone_keeps_the_device_on() {
        assert!(charger_present_decision(false, None, Some(true)));
    }

    #[test]
    fn both_uevents_positive_keeps_the_device_on() {
        assert!(charger_present_decision(false, Some(true), Some(true)));
    }

    #[test]
    fn a_positive_uevent_beats_a_denied_sysfs() {
        // the real domain's condition: every sysfs read denied, and the
        // uevent feed is the only live source
        assert!(charger_present_decision(false, Some(true), Some(false)));
    }

    #[test]
    fn two_agreeing_negative_uevents_power_the_device_off() {
        // both signals say the cable is out: this is the real unplug
        assert!(!charger_present_decision(false, Some(false), Some(false)));
    }

    #[test]
    fn a_single_spurious_discharging_does_not_power_off() {
        // charging says no but online still says yes: disagreeing
        // signals must not shut the device down
        assert!(charger_present_decision(false, Some(false), Some(true)));
        assert!(charger_present_decision(false, None, Some(false)));
        assert!(charger_present_decision(false, Some(false), None));
    }

    #[test]
    fn no_uevent_yet_does_not_power_off() {
        // startup race: the uevent has not arrived, sysfs is denied
        assert!(charger_present_decision(false, None, None));
    }

    #[test]
    fn sysfs_authority_powers_off_on_a_real_negative() {
        // sysfs answered and reported no charger: that answer is
        // authoritative even with no uevent at all
        assert!(!charger_present_decision(true, None, None));
        assert!(!charger_present_decision(true, Some(false), Some(false)));
    }

    #[test]
    fn sysfs_authority_never_overrides_a_positive_uevent() {
        // a positive uevent wins over sysfs, because the uevent feed is
        // the live source and sysfs can lag a hotplug
        assert!(charger_present_decision(true, Some(true), Some(true)));
        assert!(charger_present_decision(true, None, Some(true)));
    }

    #[test]
    fn the_decision_never_powers_off_on_missing_data() {
        // exhaustive: for every combination where nothing is known, the
        // answer must be "present". A false "no charger" here shuts the
        // device down while it is charging.
        for chg in [None, Some(true), Some(false)] {
            for on in [None, Some(true), Some(false)] {
                let r = charger_present_decision(false, chg, on);
                let known_out = chg == Some(false) && on == Some(false);
                assert_eq!(
                    r, !known_out,
                    "sysfs denied, charging={:?} online={:?}",
                    chg, on
                );
            }
        }
    }

    // ---- online_source: which supplies may answer "is a cable in?" -----
    //
    // Ground truth captured on device by forcing a synthetic uevent on
    // every supply under /sys/class/power_supply. The supplies are
    // battery, charger, mtk-gauge, mtk-master-charger, mtk-mst-div-chg,
    // mtk-slave-charger, mtk-slv-div-chg, mtk_charger_type, tran-auto-test
    // and usb_switch. None is named usb, ac or wireless.

    #[test]
    fn the_conventional_supply_names_are_still_accepted() {
        assert!(online_source("usb", None));
        assert!(online_source("ac", None));
        assert!(online_source("wireless", None));
        assert!(online_source("charger", None));
    }

    #[test]
    fn a_usb_typed_supply_is_accepted_whatever_it_is_named() {
        // the type is the semantic rule, so a supply named after its
        // driver still counts
        assert!(online_source("mt6360_chg", Some("USB_DCP")));
        assert!(online_source("anything", Some("USB_PD")));
        assert!(online_source("anything", Some("USB")));
        assert!(online_source("anything", Some("USB_HVDCP")));
    }

    #[test]
    fn usb_switch_is_not_an_online_source() {
        // it is typed Mains and reports online=0 while a cable is plugged
        // in and charging, so it must never reach the decision
        assert!(!online_source("usb_switch", Some("Mains")));
        assert!(!online_source("usb_switch", None));
    }

    #[test]
    fn the_mtk_internal_supplies_are_not_online_sources() {
        for (name, ty) in [
            ("mtk-gauge", "Unknown"),
            ("mtk-master-charger", "Unknown"),
            ("mtk-mst-div-chg", "Unknown"),
            ("mtk-slave-charger", "Unknown"),
            ("mtk-slv-div-chg", "Unknown"),
            ("mtk_charger_type", "Unknown"),
        ] {
            assert!(
                !online_source(name, Some(ty)),
                "{} must not answer for cable presence",
                name
            );
        }
    }

    #[test]
    fn a_battery_supply_is_not_an_online_source() {
        // battery and tran-auto-test are typed Battery and carry no
        // ONLINE property at all
        assert!(!online_source("battery", Some("Battery")));
        assert!(!online_source("tran-auto-test", Some("Battery")));
    }

    #[test]
    fn the_devices_actual_supply_set_yields_exactly_one_online_source() {
        // every supply the target device registers, with the type and the online value
        // each reports while a cable is plugged in and charging
        let supplies = [
            ("battery", "Battery"),
            ("charger", "USB_DCP"),
            ("mtk-gauge", "Unknown"),
            ("mtk-master-charger", "Unknown"),
            ("mtk-mst-div-chg", "Unknown"),
            ("mtk-slave-charger", "Unknown"),
            ("mtk-slv-div-chg", "Unknown"),
            ("mtk_charger_type", "Unknown"),
            ("tran-auto-test", "Battery"),
            ("usb_switch", "Mains"),
        ];
        let accepted: Vec<&str> = supplies
            .iter()
            .filter(|(name, ty)| online_source(name, Some(ty)))
            .map(|(name, _)| *name)
            .collect();
        assert_eq!(
            accepted,
            vec!["charger"],
            "exactly the charger supply must answer for cable presence"
        );
    }

    #[test]
    fn the_devices_charger_uevent_sets_online_and_charging() {
        // the exact payload captured from
        // /devices/platform/soc/11f00000.i2c/i2c-5/5-0034/mt6360_chg.2.auto/
        // power_supply/charger on device, with the header line the kernel
        // prepends left in place
        let raw: &[u8] = b"change@/devices/platform/soc/11f00000.i2c/i2c-5/5-0034/mt6360_chg.2.auto/power_supply/charger\0ACTION=change\0POWER_SUPPLY_NAME=charger\0POWER_SUPPLY_TYPE=USB_DCP\0POWER_SUPPLY_ONLINE=1\0POWER_SUPPLY_STATUS=Full\0POWER_SUPPLY_CURRENT_MAX=0\0";
        let info = parse_uevent(raw).expect("charger uevent must parse");
        assert_eq!(info.name, "charger");
        assert_eq!(info.online, Some(1));
        assert_eq!(info.ps_type.as_deref(), Some("USB_DCP"));

        let mut ps = PsState {
            cap: None,
            temp: None,
            volt_uv: None,
            charging: None,
            online: None,
            ivolt_mv: None,
            ilim_ma: None,
            c_max_ua: None,
            ps_type: None,
            updates: 0,
        };
        ps_apply(&mut ps, &info);
        assert_eq!(ps.online, Some(true));
        assert_eq!(ps.charging, Some(true));
        // plugged in, so the device must stay on
        assert!(charger_present_decision(false, ps.charging, ps.online));
    }

    #[test]
    fn the_devices_charger_uevent_going_offline_reaches_the_unplug_path() {
        // the same supply after the cable comes out: online drops to 0 and
        // the battery reports Discharging. Both signals must now say out,
        // which is what makes the power-off reachable at all.
        let raw: &[u8] = b"change@/devices/platform/soc/11f00000.i2c/i2c-5/5-0034/mt6360_chg.2.auto/power_supply/charger\0POWER_SUPPLY_NAME=charger\0POWER_SUPPLY_TYPE=USB_DCP\0POWER_SUPPLY_ONLINE=0\0POWER_SUPPLY_STATUS=Discharging\0";
        let info = parse_uevent(raw).expect("charger uevent must parse");
        assert_eq!(info.online, Some(0));

        let mut ps = PsState {
            cap: None,
            temp: None,
            volt_uv: None,
            charging: None,
            online: None,
            ivolt_mv: None,
            ilim_ma: None,
            c_max_ua: None,
            ps_type: None,
            updates: 0,
        };
        ps_apply(&mut ps, &info);
        assert_eq!(ps.online, Some(false));
        assert_eq!(ps.charging, Some(false));
        assert!(!charger_present_decision(false, ps.charging, ps.online));
    }

    #[test]
    fn a_usb_switch_uevent_must_not_clear_online() {
        // usb_switch reports online=0 while the cable is in. Feeding it in
        // must leave online untouched, so it cannot drag the decision
        // toward a power-off.
        let mut ps = PsState {
            cap: None,
            temp: None,
            volt_uv: None,
            charging: None,
            online: Some(true),
            ivolt_mv: None,
            ilim_ma: None,
            c_max_ua: None,
            ps_type: None,
            updates: 0,
        };
        let raw: &[u8] = b"change@/devices/platform/odm/odm:usb_switch/power_supply/usb_switch\0POWER_SUPPLY_NAME=usb_switch\0POWER_SUPPLY_TYPE=Mains\0POWER_SUPPLY_ONLINE=0\0";
        let info = parse_uevent(raw).expect("usb_switch uevent must parse");
        ps_apply(&mut ps, &info);
        assert_eq!(ps.online, Some(true), "usb_switch must not clear online");
        assert!(charger_present_decision(false, ps.charging, ps.online));
    }
}
