from __future__ import annotations


def initial_prompt(problem: dict) -> str:
    return (
        "Fill the single Lean proof hole below. Return only a `by ...` proof. "
        "Do not use sorry, admit, axioms, or native_decide.\n\n"
        + problem["formal_statement"]
    )


def repair_prompt(problem: dict, proof: str, diagnostic: str) -> str:
    return (
        "Repair this Lean proof using the compiler diagnostic. Return only a complete `by ...` proof. "
        "Do not use sorry, admit, axioms, or native_decide.\n\n"
        f"STATEMENT:\n{problem['formal_statement']}\n\n"
        f"FAILED PROOF:\n{proof}\n\nDIAGNOSTIC:\n{diagnostic}"
    )
