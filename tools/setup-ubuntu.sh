#!/usr/bin/env bash
set -euo pipefail
qsym_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd "$qsym_root"
[[ ${qsym_root##*/} == qsym ]] || { echo 'Checkout directory must be named qsym.' >&2; exit 1; }
[[ $(uname -s) == Linux && $(uname -m) == x86_64 ]] || { echo 'This setup requires Linux x86_64.' >&2; exit 1; }
for qsym_command in git curl tar xz zstd make gcc python3; do
	command -v "$qsym_command" >/dev/null || { echo "Missing dependency: $qsym_command" >&2; exit 1; }
done
[[ -f deps/util/package.d ]] || git submodule update --init -- deps/util
qsym_ldc=1.42.0
qsym_toolchain=$(<lean/lean-toolchain)
[[ $qsym_toolchain == leanprover/lean4:v* ]] || { echo 'Unsupported Lean toolchain.' >&2; exit 1; }
qsym_lean=${qsym_toolchain#leanprover/lean4:v}
[[ $qsym_lean =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]] || { echo 'Expected a stable Lean release.' >&2; exit 1; }
qsym_tools="$qsym_root/.toolchains"
mkdir -p "$qsym_tools/tmp" "$qsym_tools/mathlib-cache"
qsym_fetch(){
	local url=$1 archive=$2
	if [[ ! -s $archive ]]; then
		curl --fail --location --retry 3 --output "$archive.part" "$url"
		mv -- "$archive.part" "$archive"
	fi
}
if [[ ! -x $qsym_tools/ldc2-$qsym_ldc-linux-x86_64/bin/ldc2 ]]; then
	qsym_fetch "https://github.com/ldc-developers/ldc/releases/download/v$qsym_ldc/ldc2-$qsym_ldc-linux-x86_64.tar.xz" "$qsym_tools/ldc-$qsym_ldc.tar.xz"
	tar -xJf "$qsym_tools/ldc-$qsym_ldc.tar.xz" -C "$qsym_tools"
fi
if [[ ! -x $qsym_tools/lean-$qsym_lean-linux/bin/lean ]]; then
	qsym_fetch "https://github.com/leanprover/lean4/releases/download/v$qsym_lean/lean-$qsym_lean-linux.tar.zst" "$qsym_tools/lean-$qsym_lean.tar.zst"
	tar --zstd -xf "$qsym_tools/lean-$qsym_lean.tar.zst" -C "$qsym_tools"
fi
{
	printf 'export PATH=%q:%q:$PATH\n' "$qsym_tools/ldc2-$qsym_ldc-linux-x86_64/bin" "$qsym_tools/lean-$qsym_lean-linux/bin"
	printf 'export TMPDIR=%q\n' "$qsym_tools/tmp"
	printf 'export MATHLIB_CACHE_DIR=%q\n' "$qsym_tools/mathlib-cache"
	printf 'export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-1}\n'
} > "$qsym_tools/env.sh"
source "$qsym_tools/env.sh"
ldc2 --version
lean --version
python3 - <<'PY'
import pathlib,re,subprocess
root=pathlib.Path.cwd()/"lean"
modules=sorted({name for file in (root/"QSym").rglob("*.lean")
	for name in re.findall(r"^import (Mathlib\.[\w.]+)",file.read_text(),re.M)})
subprocess.run(["lake","exe","cache","get",*modules],cwd=root,check=True)
PY
printf '\nsource .toolchains/env.sh\nmake verify VERIFYFLAGS=\x27--jobs 2 --batch-size 16\x27\n'
