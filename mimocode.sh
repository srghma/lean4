#!/usr/bin/env bash

MHOME="$PWD/.mimo-home"

bwrap \
  --ro-bind /nix /nix \
  --ro-bind /etc /etc \
  --ro-bind /usr /usr \
  --ro-bind /bin /bin \
  --ro-bind /lib /lib \
  --ro-bind /lib64 /lib64 \
  --ro-bind /run /run \
  --proc /proc \
  --dev /dev \
  --tmpfs /tmp \
  --tmpfs /home \
  --bind "$PWD" "$PWD" \
  --ro-bind /home/srghma/.local/share/pnpm /home/srghma/.local/share/pnpm \
  --ro-bind /home/srghma/.nix-profile /home/srghma/.nix-profile \
  --ro-bind /home/srghma/.elan /home/srghma/.elan \
  --ro-bind /home/srghma/.dotfiles/nvim "$MHOME/.config/nvim" \
  --chdir "$PWD" \
  --setenv HOME "$MHOME" \
  --setenv PATH "/run/current-system/sw/bin:/home/srghma/.nix-profile/bin:/bin:/usr/bin" \
  --unshare-all \
  --share-net \
  bash
  # /home/srghma/.local/share/pnpm/bin/mimo "$@"
