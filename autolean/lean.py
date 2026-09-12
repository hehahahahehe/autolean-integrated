from __future__ import annotations

import os
import signal
import subprocess
import time
from dataclasses import dataclass, asdict
from pathlib import Path


@dataclass
class CompileResult:
    success: bool
    returncode: int
    stdout: str
    stderr: str
    elapsed_seconds: float
    command: list[str]

    def to_dict(self) -> dict:
        return asdict(self)


def workspace_for(project_root: Path, source: str) -> Path:
    mapping = {
        "minif2f": project_root / "external" / "minif2f",
        "proofnet_verified": project_root / "external" / "proofnet_verified",
        "putnambench": project_root / "external" / "putnambench" / "lean4",
    }
    try:
        return mapping[source]
    except KeyError as exc:
        raise ValueError(f"unsupported benchmark source: {source}") from exc


def local_toolchain_commands(workspace: Path) -> tuple[str, str]:
    """Prefer an installed toolchain directly, avoiding elan update checks."""
    if os.name != "nt":
        return "lake", "lean"
    spec = (workspace / "lean-toolchain").read_text(encoding="utf-8").strip()
    folder = spec.replace("/", "--").replace(":", "---")
    toolchain = Path(os.environ["USERPROFILE"]) / ".elan" / "toolchains" / folder / "bin"
    lake = toolchain / "lake.exe"
    lean = toolchain / "lean.exe"
    if lake.exists() and lean.exists():
        return str(lake), str(lean)
    return "lake", "lean"


def compile_statement(project_root: Path, problem: dict, statement: str, timeout: int = 180) -> CompileResult:
    workspace = workspace_for(project_root, problem["source"])
    if not (workspace / "lakefile.lean").exists():
        raise FileNotFoundError(f"Lean workspace is not initialized: {workspace}")
    temp_dir = workspace / ".autolean_tmp"
    temp_dir.mkdir(exist_ok=True)
    lean_file = temp_dir / f"{problem['problem_id']}.lean"
    lean_file.write_text(statement.rstrip() + "\n", encoding="utf-8")
    lake, lean = local_toolchain_commands(workspace)
    command = [lake, "env", lean, str(lean_file)]
    env = os.environ.copy()
    # Codex/CI may execute Python under a sandbox account while the cloned
    # dependencies are owned by the desktop user. Scope the Git exception to
    # this child process so Lake can inspect its package checkouts.
    env["GIT_CONFIG_COUNT"] = "1"
    env["GIT_CONFIG_KEY_0"] = "safe.directory"
    env["GIT_CONFIG_VALUE_0"] = "*"
    started = time.perf_counter()
    try:
        flags = subprocess.CREATE_NEW_PROCESS_GROUP if os.name == "nt" else 0
        process = subprocess.Popen(
            command,
            cwd=workspace,
            env=env,
            text=True,
            encoding="utf-8",
            errors="replace",
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            creationflags=flags,
        )
        stdout, stderr = process.communicate(timeout=timeout)
        return CompileResult(
            success=process.returncode == 0,
            returncode=process.returncode,
            stdout=stdout,
            stderr=stderr,
            elapsed_seconds=time.perf_counter() - started,
            command=command,
        )
    except subprocess.TimeoutExpired as exc:
        if os.name == "nt":
            subprocess.run(
                ["taskkill", "/PID", str(process.pid), "/T", "/F"],
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                check=False,
            )
        else:
            os.killpg(os.getpgid(process.pid), signal.SIGKILL)
        stdout, stderr = process.communicate()
        return CompileResult(
            success=False,
            returncode=124,
            stdout=stdout or exc.stdout or "",
            stderr=(stderr or exc.stderr or "") + f"\nTimed out after {timeout}s",
            elapsed_seconds=time.perf_counter() - started,
            command=command,
        )
