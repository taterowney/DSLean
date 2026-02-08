FROM debian:bookworm

ARG DEBIAN_FRONTEND=noninteractive
ARG GAPPA_VERSION=1.4.1-1
ARG SAGEMATH_VERSION=9.5-6
ARG MACAULAY2_VERSION=1.21+ds-3+b1

RUN apt-get update \
  && apt-get install -y --no-install-recommends \
    ca-certificates \
    curl \
    git \
    xz-utils \
    python3 \
    gappa=${GAPPA_VERSION} \
    sagemath=${SAGEMATH_VERSION} \
    macaulay2=${MACAULAY2_VERSION} \
  && rm -rf /var/lib/apt/lists/*

RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"

WORKDIR /workspace

COPY lean-toolchain lakefile.toml lake-manifest.json Main.lean DSLean.lean ./
COPY DSLean ./DSLean

RUN elan toolchain install "$(cat lean-toolchain)" \
  && elan default "$(cat lean-toolchain)" \
  && lake exe cache get \
  && lake build DSLean.Demos

COPY scripts ./scripts

ENV DSLEAN_GAPPA_BIN=/usr/bin/gappa
ENV DSLEAN_SAGE_BIN=/usr/bin/sage
ENV DSLEAN_TMP_DIR=/tmp/dslean

CMD ["bash"]
