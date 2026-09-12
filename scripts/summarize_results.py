from __future__ import annotations

import json
import sys
from pathlib import Path

rows = [json.loads(line) for line in Path(sys.argv[1]).read_text(encoding="utf-8").splitlines() if line]
successes = sum(bool(row.get("success")) for row in rows)
print(f"completed: {len(rows)}\nsuccess: {successes}\nfailed: {len(rows) - successes}\nsuccess rate: {successes / len(rows):.1%}" if rows else "completed: 0")
