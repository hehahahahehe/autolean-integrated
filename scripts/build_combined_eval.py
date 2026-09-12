from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

from autolean.runner import clean_proof, render_proof


def rows(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--generations", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    project = Path(__file__).resolve().parents[1]
    catalog = {r["problem_id"]: r for r in rows(project / "benchmark" / "dev.jsonl")}
    grouped: dict[str, list[dict]] = {}
    for row in rows(args.generations):
        grouped.setdefault(row["problem_id"], []).append(row)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    manifest = []
    for problem_id, attempts in grouped.items():
        problem = catalog[problem_id]
        source_lines = problem["formal_statement"].splitlines()
        imports = [line for line in source_lines if line.startswith("import ")]
        body = "\n".join(line for line in source_lines if not line.startswith("import ")).strip()
        parts = imports + [""]
        for attempt in attempts:
            namespace = "Eval_" + re.sub(r"\W", "_", attempt["model"])
            proof = clean_proof(attempt["response"])
            rendered = render_proof(body, proof)
            start = len(parts) + 2
            parts += [f"namespace {namespace}", rendered, f"end {namespace}", ""]
            manifest.append({
                "problem_id": problem_id,
                "source": problem["source"],
                "model": attempt["model"],
                "namespace": namespace,
                "start_line": start,
                "proof": proof,
            })
        (args.output_dir / f"{problem_id}.lean").write_text("\n".join(parts), encoding="utf-8")
    (args.output_dir / "manifest.json").write_text(json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8")


if __name__ == "__main__":
    main()
