#!/bin/sh
set -e

NDK="${ANDROID_NDK_ROOT:-/home/ryanistr/android-ndk-r27c}"
TOOLCHAIN="$NDK/toolchains/llvm/prebuilt/linux-x86_64"
CC="$TOOLCHAIN/bin/aarch64-linux-android35-clang"
STRIP="$TOOLCHAIN/bin/llvm-strip"

if [ ! -x "$CC" ]; then
    echo "Error: Clang not found at $CC. Set ANDROID_NDK_ROOT to your NDK path." >&2
    exit 1
fi

echo "Building kpoc_charger for aarch64-linux-android..."
rustc --target aarch64-linux-android --edition 2021 -O \
    -C linker="$CC" \
    -C target-feature=+crt-static \
    -C relocation-model=static \
    -C link-arg=-static \
    -C panic=abort \
    kpoc_charger.rs -o kpoc_charger

if [ -x "$STRIP" ]; then
    "$STRIP" kpoc_charger
fi

ls -lh kpoc_charger
file kpoc_charger
