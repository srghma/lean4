#!/usr/bin/env bash

# Find where the active node binary's directory is, resolving symlinks
NODE_DIR=$(dirname "$(readlink -f "$(which node)" 2>/dev/null || which node)")

bwrap \
  --ro-bind /nix /nix \
  --ro-bind /etc /etc \
  --ro-bind /usr /usr \
  --ro-bind /bin /bin \
  --ro-bind-try /lib /lib \
  --ro-bind-try /lib64 /lib64 \
  --ro-bind /run /run \
  --proc /proc \
  --dev /dev \
  --tmpfs /tmp \
  --tmpfs /home \
  --ro-bind /home/srghma/.local/share/pnpm /home/srghma/.local/share/pnpm \
  --ro-bind-try /home/srghma/.nix-profile /home/srghma/.nix-profile \
  --bind "$PWD" "$PWD" \
  --chdir "$PWD" \
  --setenv HOME "$PWD/.mimo-home" \
  --setenv PATH "/run/current-system/sw/bin:/home/srghma/.nix-profile/bin:/bin:/usr/bin:$NODE_DIR" \
  --unshare-all \
  --share-net \
  /home/srghma/.local/share/pnpm/bin/mimo "$@"
