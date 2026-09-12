from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
rows = [json.loads(line) for line in (ROOT / "benchmark" / "dev.jsonl").read_text(encoding="utf-8").splitlines() if line]
ids = [row["problem_id"] for row in rows]
assert len(rows) == 30
assert len(set(ids)) == 30
assert all(row["formal_statement"].count("sorry") == 1 for row in rows)
assert all("formal_proof" not in row for row in rows)
print(f"30 problems\n{dict(Counter(row['source'] for row in rows))}\nduplicate IDs: 0\nproof leakage: 0")
