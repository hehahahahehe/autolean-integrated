from __future__ import annotations

import argparse
import csv
import json
import subprocess
import time
from pathlib import Path

from autolean.lean import compile_statement
from autolean.prompts import initial_prompt
from autolean.runner import clean_proof, render_proof


DEFAULT_MODELS = [
    "gpt-6-astra",
    "gpt-5.6-sol",
    "gpt-5.6-terra",
    "gpt-5.6-luna",
    "gpt-5.5",
]

DEFAULT_PROBLEMS = [
    "minif2f_mathd_algebra_182",
    "proofnet_2_Artin_exercise_2_4_19",
    "putnambench_putnam_1962_a6",
]


def load_problems(path: Path) -> dict[str, dict]:
    rows = [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]
    return {row["problem_id"]: row for row in rows}


def run_model(project: Path, model: str, problem: dict, run_dir: Path, timeout: int, skip_compile: bool = False) -> dict:
    stem = f"{model}__{problem['problem_id']}"
    response_path = run_dir / f"{stem}.txt"
    log_path = run_dir / f"{stem}.log"
    prompt = (
        initial_prompt(problem)
        + "\n\nThis is a closed-book benchmark. Do not inspect files or run commands. "
        "Solve from the statement alone and output only the complete `by ...` proof."
    )
    command = [
        "codex", "exec", "--ephemeral", "--ignore-user-config",
        "--sandbox", "read-only", "--skip-git-repo-check",
        "-m", model, "-c", 'model_reasoning_effort="medium"',
        "-o", str(response_path), prompt,
    ]
    started = time.perf_counter()
    try:
        completed = subprocess.run(
            command,
            cwd=project,
            text=True,
            encoding="utf-8",
            errors="replace",
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
        )
        model_elapsed = time.perf_counter() - started
        log_path.write_text(completed.stdout + "\n" + completed.stderr, encoding="utf-8")
        response = response_path.read_text(encoding="utf-8") if response_path.exists() else ""
        result = {
            "model": model,
            "problem_id": problem["problem_id"],
            "source": problem["source"],
            "model_returncode": completed.returncode,
            "generation_seconds": model_elapsed,
            "response": response,
        }
    except subprocess.TimeoutExpired as exc:
        log_path.write_text((exc.stdout or "") + "\n" + (exc.stderr or ""), encoding="utf-8")
        return {
            "model": model,
            "problem_id": problem["problem_id"],
            "source": problem["source"],
            "model_returncode": 124,
            "generation_seconds": time.perf_counter() - started,
            "success": False,
            "failure": f"model timed out after {timeout}s",
            "response": "",
        }

    if result["model_returncode"] != 0:
        result.update(success=False, failure="model invocation failed")
        return result
    if skip_compile:
        result.update(generated=True, success=None)
        return result
    try:
        proof = clean_proof(response)
        candidate = render_proof(problem["formal_statement"], proof)
        compiled = compile_statement(project, problem, candidate, timeout=timeout)
        result.update(proof=proof, success=compiled.success, compile=compiled.to_dict())
        if not compiled.success:
            result["failure"] = "Lean compilation failed"
    except (ValueError, FileNotFoundError) as exc:
        result.update(success=False, failure=str(exc))
    return result


def write_summary(results: list[dict], output_dir: Path) -> None:
    fields = ["model", "problem_id", "source", "success", "generation_seconds", "compile_seconds", "failure"]
    with (output_dir / "codex-lean-pilot.csv").open("w", encoding="utf-8-sig", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for row in results:
            writer.writerow({
                "model": row["model"],
                "problem_id": row["problem_id"],
                "source": row["source"],
                "success": row.get("success", False),
                "generation_seconds": round(row.get("generation_seconds", 0), 2),
                "compile_seconds": round(row.get("compile", {}).get("elapsed_seconds", 0), 2),
                "failure": row.get("failure", ""),
            })

    models = list(dict.fromkeys(row["model"] for row in results))
    lines = [
        "# Codex 模型 Lean 能力分层试测",
        "",
        "测试口径：每个模型对同三道题单次生成；reasoning effort=medium；无编译器反馈、无修复轮；以 Lean 实际编译成功为唯一通过标准。",
        "",
        "| 模型 | 通过/3 | miniF2F | ProofNet | PutnamBench |",
        "|---|---:|---:|---:|---:|",
    ]
    for model in models:
        subset = [row for row in results if row["model"] == model]
        by_source = {row["source"]: "✓" if row.get("success") else "✗" for row in subset}
        lines.append(
            f"| {model} | {sum(bool(row.get('success')) for row in subset)}/3 | "
            f"{by_source.get('minif2f', '—')} | {by_source.get('proofnet_verified', '—')} | "
            f"{by_source.get('putnambench', '—')} |"
        )
    lines += ["", "## 逐题结果", ""]
    for row in results:
        status = "通过" if row.get("success") else "失败"
        detail = row.get("failure", "Lean 编译通过")
        lines.append(f"- {row['model']} / {row['problem_id']}: **{status}** — {detail}")
    (output_dir / "codex-lean-pilot-report.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--models", nargs="+", default=DEFAULT_MODELS)
    parser.add_argument("--problems", nargs="+", default=DEFAULT_PROBLEMS)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--skip-compile", action="store_true")
    parser.add_argument("--result-prefix", default="codex-lean-pilot")
    args = parser.parse_args()

    project = Path(__file__).resolve().parents[1]
    args.output_dir.mkdir(parents=True, exist_ok=True)
    run_dir = args.output_dir / f"{args.result_prefix}-raw"
    run_dir.mkdir(exist_ok=True)
    catalog = load_problems(project / "benchmark" / "dev.jsonl")
    results_path = args.output_dir / f"{args.result_prefix}.jsonl"
    existing = []
    if results_path.exists():
        existing = [json.loads(line) for line in results_path.read_text(encoding="utf-8").splitlines() if line.strip()]
    completed_keys = {(row["model"], row["problem_id"]) for row in existing}
    results = list(existing)
    for model in args.models:
        for problem_id in args.problems:
            if (model, problem_id) in completed_keys:
                continue
            result = run_model(project, model, catalog[problem_id], run_dir, args.timeout, args.skip_compile)
            results.append(result)
            with results_path.open("a", encoding="utf-8") as handle:
                handle.write(json.dumps(result, ensure_ascii=False) + "\n")
            print(f"{model} {problem_id}: {'PASS' if result.get('success') else 'FAIL'}", flush=True)
            if not args.skip_compile:
                write_summary(results, args.output_dir)
    if not args.skip_compile:
        write_summary(results, args.output_dir)


if __name__ == "__main__":
    main()
