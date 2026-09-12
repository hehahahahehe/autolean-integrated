from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def record(problem_id: str, source: str, statement: str, original_file: Path) -> dict:
    return {
        "problem_id": problem_id,
        "source": source,
        "formal_statement": statement.rstrip() + "\n",
        "original_file": str(original_file.relative_to(ROOT)).replace("\\", "/"),
    }


def mini_records() -> list[dict]:
    path = ROOT / "external" / "minif2f" / "MiniF2F" / "Valid.lean"
    text = path.read_text(encoding="utf-8")
    header = (
        "import Mathlib\n"
        "import FormalConjecturesForMathlib.Analysis.SpecialFunctions.NthRoot\n"
        "import FormalConjectures.Util.Answer\n\n"
        "open scoped Real Nat Topology Polynomial\n\n"
    )
    matches = re.findall(r"(?ms)^theorem\s+.*? := by\s*\n\s+sorry\s*$", text)
    rows = []
    for theorem in matches[:10]:
        name = re.match(r"theorem\s+([^\s(]+)", theorem).group(1)
        rows.append(record(f"minif2f_{name}", "minif2f", header + theorem, path))
    return rows


def proofnet_records() -> list[dict]:
    root = ROOT / "external" / "proofnet_verified"
    data = root / "data" / "proofnet-verified.jsonl"
    rows = []
    with data.open(encoding="utf-8") as handle:
        for line in handle:
            item = json.loads(line)
            statement = "\n".join(part for part in [item.get("header", ""), item.get("helper", ""), item["formal_stmt"]] if part)
            if statement.count("sorry") == 1:
                original = root / "proofnet-verified" / f"proofnet-{item['index']}.lean"
                rows.append(record(f"proofnet_{item['index']}_{item['name']}", "proofnet_verified", statement, original))
            if len(rows) == 10:
                break
    return rows


def putnam_records() -> list[dict]:
    src = ROOT / "external" / "putnambench" / "lean4" / "src"
    rows = []
    for path in sorted(src.glob("putnam_*.lean")):
        statement = path.read_text(encoding="utf-8")
        if statement.count("sorry") != 1:
            continue
        name = path.stem
        rows.append(record(f"putnambench_{name}", "putnambench", statement, path))
        if len(rows) == 10:
            break
    return rows


def main() -> None:
    rows = mini_records() + proofnet_records() + putnam_records()
    if len(rows) != 30:
        raise RuntimeError(f"expected 30 problems, found {len(rows)}")
    output = ROOT / "benchmark"
    output.mkdir(exist_ok=True)
    with (output / "dev.jsonl").open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(json.dumps(row, ensure_ascii=False) + "\n")
    (output / "selection_ids.json").write_text(
        json.dumps([row["problem_id"] for row in rows], ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    print("30 problems: minif2f=10, proofnet_verified=10, putnambench=10")


if __name__ == "__main__":
    main()
