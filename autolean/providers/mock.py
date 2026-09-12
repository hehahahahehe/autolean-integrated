from __future__ import annotations


class MockProvider:
    def __init__(self, responses: list[str] | None = None):
        self.responses = list(responses or ["by\n  exact True.intro"])

    def complete(self, prompt: str) -> str:
        if not self.responses:
            raise RuntimeError("mock provider has no responses left")
        return self.responses.pop(0)
