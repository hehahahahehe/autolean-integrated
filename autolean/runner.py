from __future__ import annotations

import json
import re
from pathlib import Path

from .lean import compile_statement
from .prompts import initial_prompt, repair_prompt

FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|native_decide)\b")


def clean_proof(text: str) -> str:
    text = text.strip()
    match = re.search(r"```(?:lean)?\s*(.*?)```", text, re.DOTALL | re.IGNORECASE)
    if match:
        text = match.group(1).strip()
    start = text.find("by")
    if start < 0:
        raise ValueError("provider response does not contain a `by` proof")
    return text[start:].strip()


def render_proof(statement: str, proof: str) -> str:
    if statement.count("sorry") != 1:
        raise ValueError("formal statement must contain exactly one sorry")
    if FORBIDDEN.search(proof):
        raise ValueError("generated proof contains a forbidden escape")
    tactic_hole = re.compile(r"\bby\s*\n\s*sorry\b")
    if tactic_hole.search(statement):
        return tactic_hole.sub(lambda _: proof, statement, count=1)
    return statement.replace("sorry", proof, 1)


def run_problem(project_root: Path, problem: dict, provider, max_repairs: int = 5, timeout: int = 180) -> dict:
    attempts = []
    prompt = initial_prompt(problem)
    last_proof = ""
    for index in range(max_repairs + 1):
        response = provider.complete(prompt)
        attempt = {"attempt": index, "prompt": prompt, "response": response}
        try:
            proof = clean_proof(response)
            candidate = render_proof(problem["formal_statement"], proof)
            compiled = compile_statement(project_root, problem, candidate, timeout=timeout)
            attempt["proof"] = proof
            attempt["compile"] = compiled.to_dict()
            attempts.append(attempt)
            if compiled.success:
                return {"problem_id": problem["problem_id"], "success": True, "repair_rounds": index, "attempts": attempts}
            last_proof = proof
            diagnostic = (compiled.stdout + "\n" + compiled.stderr).strip()
        except ValueError as exc:
            attempt["error"] = str(exc)
            attempts.append(attempt)
            diagnostic = str(exc)
        prompt = repair_prompt(problem, last_proof, diagnostic)
    return {"problem_id": problem["problem_id"], "success": False, "repair_rounds": max_repairs, "attempts": attempts}


def append_result(path: Path, result: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(result, ensure_ascii=False) + "\n")
