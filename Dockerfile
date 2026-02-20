FROM debian:bookworm

ARG DEBIAN_FRONTEND=noninteractive

# ── System dependencies & external solvers ────────────────────────────
RUN apt-get update \
 && apt-get install -y --no-install-recommends \
      ca-certificates curl git xz-utils python3 \
      gappa sagemath macaulay2 \
 && rm -rf /var/lib/apt/lists/*

# ── Lean / elan ───────────────────────────────────────────────────────
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"

# ── Project source ────────────────────────────────────────────────────
WORKDIR /workspace

# Copy dependency metadata first for better layer caching
COPY lean-toolchain lakefile.toml lake-manifest.json ./
RUN elan toolchain install "$(cat lean-toolchain)" \
 && elan default "$(cat lean-toolchain)"

# Fetch Mathlib cache before copying our source (cache-friendly)
COPY Main.lean DSLean.lean ./
COPY DSLean ./DSLean
RUN lake exe cache get && lake build

# ── Environment ───────────────────────────────────────────────────────
# These match the env vars checked by the tactics:
#   Gappa.lean   → DSLEAN_GAPPA_PATH  (default: "gappa")
#   LeanM2.lean  → DSLEAN_M2_PATH     (default: "M2")
#   Desolve.lean → DSLEAN_SAGE_PATH   (default: "sage")
# The apt packages put binaries on PATH, so defaults already work.
# We set them explicitly anyway for discoverability.
ENV DSLEAN_GAPPA_PATH=/usr/bin/gappa
ENV DSLEAN_M2_PATH=/usr/bin/M2
ENV DSLEAN_SAGE_PATH=/usr/bin/sage

CMD ["bash"]