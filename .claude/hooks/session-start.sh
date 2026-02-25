#!/bin/bash
set -euo pipefail

# Only run in Claude Code remote environments
if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

###############################################################################
# Catalia SessionStart hook
# Installs: z3, Java (OpenJDK 21), Eldarica, and builds the Rust project
###############################################################################

ELDARICA_VERSION="2.2.1"
ELDARICA_URL="https://github.com/uuverifiers/eldarica/releases/download/v${ELDARICA_VERSION}/eldarica-bin-${ELDARICA_VERSION}.zip"
ELDARICA_DIR="/usr/local/eldarica"

# --- Z3 (via apt, idempotent) ---
if ! command -v z3 &>/dev/null; then
  apt-get update -qq
  apt-get install -y -qq z3
fi

# --- Java (required by Eldarica) ---
if ! command -v java &>/dev/null; then
  apt-get update -qq
  apt-get install -y -qq openjdk-21-jdk-headless
fi

# --- Eldarica ---
if ! command -v eld &>/dev/null; then
  tmpdir="$(mktemp -d)"
  wget -q "${ELDARICA_URL}" -O "${tmpdir}/eld.zip"
  unzip -q "${tmpdir}/eld.zip" -d "${tmpdir}"
  rm -rf "${ELDARICA_DIR}"
  mv "${tmpdir}"/eldarica-* "${ELDARICA_DIR}"
  chmod +x "${ELDARICA_DIR}/eld"
  ln -sf "${ELDARICA_DIR}/eld" /usr/local/bin/eld
  rm -rf "${tmpdir}"
fi

# --- Rust build (uses cached target/ when available) ---
cd "${CLAUDE_PROJECT_DIR}"
cargo build 2>/dev/null

# --- Set environment for Eldarica-based CEX (more stable than Spacer) ---
echo 'export HOICE_USE_ELDARICA_CEX=1' >> "$CLAUDE_ENV_FILE"
