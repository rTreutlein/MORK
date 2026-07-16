FROM rust:1.88.0-bookworm

ARG RUST_TOOLCHAIN=nightly-2026-07-15

RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt-get install --yes --no-install-recommends \
        build-essential \
        ca-certificates \
        clang \
        cmake \
        git \
        libclang-dev \
        pkg-config \
    && rm -rf /var/lib/apt/lists/* \
    && rustup toolchain install "${RUST_TOOLCHAIN}" --profile minimal \
    && rustup default "${RUST_TOOLCHAIN}" \
    && mkdir -p /usr/local/cargo/registry /usr/local/cargo/git /var/cache/mork/target \
    && chmod 1777 /usr/local/cargo/registry /usr/local/cargo/git /var/cache/mork/target

ENV CARGO_TARGET_DIR=/var/cache/mork/target
