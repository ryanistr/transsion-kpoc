# transsion-kpoc

Standalone off-mode charging service (KPOC) written from scratch in Rust for Transsion MediaTek devices (Infinix, Tecno, itel) without external runtime dependencies.

## Overview

When an Android device powers off and connects to a charger, the kernel enters offline charging mode (`kpoc_charger`).

This project provides a standalone, fully static replacement service that runs directly on Linux DRM/KMS. It renders charging animations, monitors battery state in real time, and responds to power key input.

## Features

- **Direct DRM/KMS Renderer**: Operates directly on `/dev/dri/card0` dumb buffers via native DRM ioctls (`SET_MASTER`, `GETRESOURCES`, `CREATE_DUMB`, `MAP_DUMB`, `ADDFB2`, `SETCRTC`). Does not depend on legacy fbdev (`/dev/fb0`) or userspace graphics HALs.
- **Transsion Logo Asset Parser**: Decodes charging assets and font glyphs directly from the MediaTek `logo` partition (`/dev/block/by-name/logo`) using raw zlib streams.
- **Kernel Netlink Battery Telemetry**: Listens to `NETLINK_KOBJECT_UEVENT` multicast sockets for battery capacity, temperature, and charger hotplug events. Operates cleanly even when SELinux restricts direct `/sys/class/power_supply` file reads.
- **Zero External Dependencies**: Implemented in standard Rust using handwritten system bindings (DRM, Netlink, evdev, zlib FFI). Compiles to a self-contained static binary with zero dynamic library dependencies (`DT_NEEDED`).
- **Power Key and Power Management**: Debounces `/dev/input/event*` power key events: short presses toggle the display panel on or off, while a sustained hold past 1.2 seconds reboots the device into Android OS. Holds `kpoc_anim` wakelock to prevent kernel sleep while charging.

## Building

### Device Binary (aarch64 Android)

Building requires a working `rustc` with the `aarch64-linux-android` target installed and an Android NDK toolchain:

```sh
rustup target add aarch64-linux-android
export ANDROID_NDK_ROOT=/path/to/android-ndk
./build.sh
```

The script builds a stripped, fully static binary at `./kpoc_charger`.

### Unit Tests (Host)

The test suite exercises DRM ioctl structures, netlink uevent message parsers, wattage calculations, and power key state machines:

```sh
rustc --test --edition 2021 kpoc_charger.rs -o kpoc_test
./kpoc_test
```

To test against an extracted Transsion `logo.img`:

```sh
KPOC_TEST_LOGO=/path/to/logo.img ./kpoc_test
```

## License

MIT
