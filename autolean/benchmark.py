from __future__ import annotations

import json
from pathlib import Path


def load_jsonl(path: str | Path) -> list[dict]:
    with Path(path).open(encoding="utf-8") as handle:
        return [json.loads(line) for line in handle if line.strip()]


def find_problem(problems: list[dict], problem_id: str) -> dict:
    for problem in problems:
        if problem["problem_id"] == problem_id:
            return problem
    raise KeyError(f"unknown problem id: {problem_id}")
