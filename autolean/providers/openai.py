from __future__ import annotations

import json
import os
import urllib.request


class OpenAIProvider:
    def __init__(self):
        self.api_key = os.environ.get("OPENAI_API_KEY")
        self.base_url = os.environ.get("OPENAI_BASE_URL", "https://api.openai.com/v1").rstrip("/")
        self.model = os.environ.get("OPENAI_MODEL", "gpt-5-mini")
        if not self.api_key:
            raise RuntimeError("OPENAI_API_KEY is not set")

    def complete(self, prompt: str) -> str:
        payload = json.dumps({"model": self.model, "input": prompt}).encode("utf-8")
        request = urllib.request.Request(
            self.base_url + "/responses",
            data=payload,
            headers={"Authorization": f"Bearer {self.api_key}", "Content-Type": "application/json"},
            method="POST",
        )
        with urllib.request.urlopen(request, timeout=180) as response:
            data = json.load(response)
        if data.get("output_text"):
            return data["output_text"]
        chunks = []
        for item in data.get("output", []):
            for content in item.get("content", []):
                if content.get("type") == "output_text":
                    chunks.append(content.get("text", ""))
        return "".join(chunks)
