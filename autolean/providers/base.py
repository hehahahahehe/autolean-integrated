from __future__ import annotations

from typing import Protocol


class Provider(Protocol):
    def complete(self, prompt: str) -> str: ...
