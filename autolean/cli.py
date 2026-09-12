from __future__ import annotations

import argparse
import json
from pathlib import Path

from .benchmark import find_problem, load_jsonl
from .lean import compile_statement
from .providers import MockProvider, OpenAIProvider
from .runner import append_result, run_problem


def project_root() -> Path:
    return Path(__file__).resolve().parents[1]


def default_benchmark(root: Path) -> Path:
    return root / "benchmark" / "dev.jsonl"


def provider_from_name(name: str):
    return OpenAIProvider() if name == "openai" else MockProvider()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="autolean")
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("info", help="show installation status")
    check = sub.add_parser("check", help="compile a benchmark statement with its existing sorry")
    check.add_argument("--problem-id", required=True)
    check.add_argument("--benchmark")
    check.add_argument("--timeout", type=int, default=180)
    run = sub.add_parser("run", help="run one proving/repair job")
    run.add_argument("--problem-id", required=True)
    run.add_argument("--benchmark")
    run.add_argument("--provider", choices=["openai", "mock"], default="openai")
    run.add_argument("--max-repairs", type=int, default=5)
    run.add_argument("--timeout", type=int, default=180)
    batch = sub.add_parser("batch", help="run all benchmark problems")
    batch.add_argument("--benchmark")
    batch.add_argument("--provider", choices=["openai", "mock"], default="openai")
    batch.add_argument("--max-repairs", type=int, default=5)
    batch.add_argument("--timeout", type=int, default=180)
    batch.add_argument("--results", default="runs/results.jsonl")
    batch.add_argument("--resume", action="store_true")
    args = parser.parse_args(argv)
    root = project_root()
    bench_path = Path(getattr(args, "benchmark", None) or default_benchmark(root))
    if args.command == "info":
        problems = load_jsonl(default_benchmark(root))
        counts = {source: sum(p["source"] == source for p in problems) for source in sorted({p["source"] for p in problems})}
        print(json.dumps({"project_root": str(root), "problems": len(problems), "sources": counts}, indent=2))
        return 0
    problems = load_jsonl(bench_path)
    if args.command == "check":
        problem = find_problem(problems, args.problem_id)
        result = compile_statement(root, problem, problem["formal_statement"], timeout=args.timeout)
        print(json.dumps(result.to_dict(), ensure_ascii=False, indent=2))
        return 0 if result.success else 1
    provider = provider_from_name(args.provider)
    if args.command == "run":
        result = run_problem(root, find_problem(problems, args.problem_id), provider, args.max_repairs, args.timeout)
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0 if result["success"] else 1
    output = root / args.results
    completed = set()
    if args.resume and output.exists():
        completed = {row["problem_id"] for row in load_jsonl(output)}
    for problem in problems:
        if problem["problem_id"] in completed:
            continue
        result = run_problem(root, problem, provider, args.max_repairs, args.timeout)
        append_result(output, result)
        print(f"{problem['problem_id']}: {'success' if result['success'] else 'failed'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
