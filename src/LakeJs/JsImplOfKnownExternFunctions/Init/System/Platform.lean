export function lean_system_platform_windows() {
  if (typeof process !== 'undefined' && process.platform === 'win32') {
    return true;
  }
  if (typeof navigator !== 'undefined' && /Win/.test(navigator.platform)) {
    return true;
  }
  return false;
}

export function lean_system_platform_osx() {
  if (typeof process !== 'undefined' && (process.platform === 'darwin')) {
    return true;
  }
  if (typeof navigator !== 'undefined' && /Mac/.test(navigator.platform)) {
    return true;
  }
  return false;
}

export function lean_system_platform_emscripten() {
  // In a pure JS environment, we are not "Emscripten" unless running in that specific shell
  return false;
}

export function lean_system_platform_javascript() {
  return true; // If this code is running, we are in a JS environment
}

export function lean_system_platform_target() {
  if (typeof process !== 'undefined' && process.arch) {
    return `${process.platform}-${process.arch}-unknown`;
  }
  return "javascript-unknown-unknown";
}
