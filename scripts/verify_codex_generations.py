from __future__ import annotations

import argparse
import json
from pathlib import Path

from autolean.lean import compile_statement
from autolean.runner import clean_proof, render_proof


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--generations", type=Path, required=True)
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--sources", nargs="+")
    parser.add_argument("--timeout", type=int, default=180)
    args = parser.parse_args()
    project = Path(__file__).resolve().parents[1]
    catalog = {r["problem_id"]: r for r in read_jsonl(project / "benchmark" / "dev.jsonl")}
    generations = read_jsonl(args.generations)
    existing = read_jsonl(args.results) if args.results.exists() else []
    done = {(r["model"], r["problem_id"]) for r in existing}
    args.results.parent.mkdir(parents=True, exist_ok=True)

    for row in generations:
        key = (row["model"], row["problem_id"])
        if key in done or (args.sources and row["source"] not in args.sources):
            continue
        result = {k: row[k] for k in ("model", "problem_id", "source", "generation_seconds")}
        try:
            proof = clean_proof(row["response"])
            statement = render_proof(catalog[row["problem_id"]]["formal_statement"], proof)
            compiled = compile_statement(project, catalog[row["problem_id"]], statement, timeout=args.timeout)
            status = "pass" if compiled.success else ("timeout" if compiled.returncode == 124 else "fail")
            result.update(status=status, proof=proof, compile=compiled.to_dict())
        except (ValueError, FileNotFoundError) as exc:
            result.update(status="invalid", failure=str(exc))
        with args.results.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(result, ensure_ascii=False) + "\n")
        print(f"{result['model']} {result['problem_id']}: {result['status'].upper()}", flush=True)


if __name__ == "__main__":
    main()
